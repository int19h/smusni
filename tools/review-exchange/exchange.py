#!/usr/bin/env python3
"""Multi-model review exchange helper (protocol smusni-review-mail/v2).

Tracked control plane for the ignored message spool under review/exchange/.
Actors come from participants.toml; nothing here hard-codes a participant.

Commands:
  validate                       validate v1 history and every published v2 file
  status   --actor A             validate, warn about A's own drafts, list what A owes
  new      --actor A --to L|all --kind K --slug S [--issues ..] [--reply-to ID]
           [--supersedes ID] [--no-ack] [--model M] [--client C]
  publish  --actor A DRAFT       validate, expand `all`, publish atomically
  ack      --actor A ID --disposition TEXT   acknowledge a received message

Exit codes: 0 ok · 1 usage · 2 validation · 3 ownership/permission ·
4 collision/duplicate · 5 unknown reference.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import os
import re
import sys
import tomllib
from pathlib import Path

V1 = "smusni-review-mail/v1"
V2 = "smusni-review-mail/v2"
KINDS = {"request", "response", "finding", "proposal", "handoff", "decision-query"}
TIME_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")
SLUG_RE = re.compile(r"^[a-z0-9][a-z0-9-]*$")
ISSUES_RE = re.compile(r"^#\d+(,#\d+)*$")
V1_LEGACY_SENDERS = {"owner"}  # historical alias of the human partner

EXIT_USAGE, EXIT_VALIDATION, EXIT_OWNERSHIP, EXIT_COLLISION, EXIT_UNKNOWN = 1, 2, 3, 4, 5


class ExchangeError(Exception):
    def __init__(self, code: int, message: str):
        super().__init__(message)
        self.code = code


# ----------------------------------------------------------------- registry


class Registry:
    def __init__(self, root: Path):
        self.root = root
        path = root / "tools" / "review-exchange" / "participants.toml"
        if not path.exists():
            raise ExchangeError(EXIT_USAGE, f"registry not found: {path}")
        data = tomllib.loads(path.read_text())
        self.protocol = data.get("protocol", V2)
        self.spool = root / data.get("spool", "review/exchange")
        self.actors: dict[str, dict] = data.get("actors", {})
        if not self.actors:
            raise ExchangeError(EXIT_USAGE, "registry declares no actors")
        for name in self.actors:
            if not SLUG_RE.fullmatch(name):
                raise ExchangeError(EXIT_USAGE, f"bad actor name in registry: {name!r}")

    def is_actor(self, name: str) -> bool:
        return name in self.actors

    def active(self, name: str) -> bool:
        return bool(self.actors.get(name, {}).get("active", False))

    def broadcast_recipients(self) -> list[str]:
        return sorted(
            n for n, a in self.actors.items()
            if a.get("active", False) and a.get("broadcast_recipient", False)
        )

    def default_model(self, name: str) -> str:
        return str(self.actors[name].get("model", "unspecified"))

    def default_client(self, name: str) -> str:
        return str(self.actors[name].get("client", "unspecified"))

    def acknowledges(self, name: str) -> bool:
        """Whether this actor owes acknowledgements (the human partner does not)."""
        return bool(self.actors.get(name, {}).get("acknowledges", True))


BINDING_ENV = "SMUSNI_EXCHANGE_ACTOR"


def bound_actor(reg: "Registry", requested: str | None) -> str:
    """Resolve the acting actor for a mutating command.

    If SMUSNI_EXCHANGE_ACTOR is set (each launcher exports it), a different
    --actor is refused: this is an accidental-safety boundary for two actors
    sharing one client, not security against the shared account. Unset means
    the human driver is operating manually and --actor is trusted.
    """
    bound = os.environ.get(BINDING_ENV, "").strip() or None
    if bound and not reg.is_actor(bound):
        raise ExchangeError(EXIT_OWNERSHIP, f"{BINDING_ENV}={bound!r} is not a registry actor")
    if requested and bound and requested != bound:
        raise ExchangeError(EXIT_OWNERSHIP, f"this session is bound to actor {bound!r}; refusing --actor {requested!r}")
    actor = requested or bound
    if not actor:
        raise ExchangeError(EXIT_USAGE, f"--actor is required (or export {BINDING_ENV})")
    require_actor(reg, actor)
    return actor


# --------------------------------------------------------------- front matter


def front_matter(path: Path) -> tuple[dict[str, str], str, list[str]]:
    """Return (header, body, errors). Header is key: value, not general YAML."""
    errors: list[str] = []
    text = path.read_text()
    lines = text.splitlines()
    if not lines or lines[0] != "---":
        return {}, text, [f"{path}: missing opening ---"]
    try:
        end = lines.index("---", 1)
    except ValueError:
        return {}, text, [f"{path}: missing closing ---"]
    data: dict[str, str] = {}
    for number, line in enumerate(lines[1:end], start=2):
        if ":" not in line:
            errors.append(f"{path}:{number}: expected key: value")
            continue
        key, value = line.split(":", 1)
        key, value = key.strip(), value.strip()
        if not key or key in data:
            errors.append(f"{path}:{number}: missing or duplicate key {key!r}")
        data[key] = value
    body = "\n".join(lines[end + 1:])
    return data, body, errors


def render(header: list[tuple[str, str]], body: str) -> str:
    head = "\n".join(f"{k}: {v}" for k, v in header)
    return f"---\n{head}\n---\n{body}"


# ----------------------------------------------------------------- messages


class Message:
    def __init__(self, path: Path, data: dict[str, str], body: str, protocol: str):
        self.path, self.data, self.body, self.protocol = path, data, body, protocol

    @property
    def id(self) -> str:
        return self.data.get("id", "")

    @property
    def sender(self) -> str:
        return self.data.get("from", "")

    def recipients(self) -> list[str]:
        to = self.data.get("to", "")
        return [t.strip() for t in to.split(",") if t.strip()]

    @property
    def ack_required(self) -> bool:
        if self.protocol == V1:
            return True
        return self.data.get("ack_required", "true") == "true"


def _check_common(path: Path, data: dict[str, str], reg: Registry, *, protocol: str) -> list[str]:
    errors: list[str] = []
    message_id = data.get("id", "")
    if data.get("protocol") != protocol:
        errors.append(f"{path}: wrong protocol {data.get('protocol')!r}")
    if not message_id:
        errors.append(f"{path}: missing id")
    else:
        parts = message_id.split("-", 2)
        ok = (
            len(parts) == 3 and re.fullmatch(r"\d{8}T\d{6}Z", parts[0])
            and SLUG_RE.fullmatch(parts[2]) is not None
            and (reg.is_actor(parts[1]) or (protocol == V1 and parts[1] in V1_LEGACY_SENDERS))
        )
        if not ok:
            errors.append(f"{path}: malformed id {message_id!r}")
        elif parts[1] != data.get("from"):
            errors.append(f"{path}: id actor does not match from")
        if path.name != f"{message_id}.md":
            errors.append(f"{path}: filename does not match id")
    created = data.get("created_utc", "")
    if not TIME_RE.fullmatch(created):
        errors.append(f"{path}: malformed created_utc")
    elif message_id and not message_id.startswith(created.replace("-", "").replace(":", "")):
        errors.append(f"{path}: id timestamp does not match created_utc")
    if data.get("kind") not in KINDS:
        errors.append(f"{path}: invalid kind {data.get('kind')!r}")
    issues = data.get("github_issues", "")
    if issues != "none" and not ISSUES_RE.fullmatch(issues):
        errors.append(f"{path}: github_issues must be none or comma-separated #numbers")
    for field in ("in_reply_to", "supersedes"):
        if field not in data:
            errors.append(f"{path}: missing key {field!r}")
        elif data[field] == message_id and message_id:
            errors.append(f"{path}: {field} cannot name the message itself")
    return errors


def validate_v1(path: Path, reg: Registry, *, published: bool) -> tuple[Message | None, list[str]]:
    data, body, errors = front_matter(path)
    required = {"protocol", "id", "from", "to", "created_utc", "kind",
                "in_reply_to", "supersedes", "github_issues"}
    missing = sorted(required - data.keys())
    if missing:
        errors.append(f"{path}: missing keys {missing}")
    errors += _check_common(path, data, reg, protocol=V1)
    sender, to = data.get("from", ""), data.get("to", "")
    if not (reg.is_actor(sender) or sender in V1_LEGACY_SENDERS):
        errors.append(f"{path}: invalid sender {sender!r}")
    if not reg.is_actor(to) or to == "human":
        errors.append(f"{path}: invalid recipient {to!r}")
    if sender == to:
        errors.append(f"{path}: sender and recipient are identical")
    expected_dir = to if published else sender
    if expected_dir and path.parent.name != expected_dir:
        errors.append(f"{path}: {'recipient' if published else 'sender'} directory does not match header")
    return (Message(path, data, body, V1) if not errors else None), errors


def validate_v2(path: Path, reg: Registry, *, published: bool, name: str | None = None) -> tuple[Message | None, list[str]]:
    data, body, errors = front_matter(path)
    if name is not None:
        path = path.with_name(name)
    required = {"protocol", "id", "from", "to", "created_utc", "kind", "model",
                "client", "ack_required", "in_reply_to", "supersedes", "github_issues"}
    missing = sorted(required - data.keys())
    if missing:
        errors.append(f"{path}: missing keys {missing}")
    errors += _check_common(path, data, reg, protocol=V2)
    sender = data.get("from", "")
    if not reg.is_actor(sender):
        errors.append(f"{path}: invalid sender {sender!r}")
    if not published and path.parent.name != sender:
        errors.append(f"{path}: draft is not in its sender's draft directory")
    to = data.get("to", "")
    recipients = [t.strip() for t in to.split(",") if t.strip()]
    if to == "all":
        if published:
            errors.append(f"{path}: published message must carry an explicit recipient list, not 'all'")
    else:
        if not recipients:
            errors.append(f"{path}: empty recipient list")
        for r in recipients:
            if not reg.is_actor(r):
                errors.append(f"{path}: unknown recipient {r!r}")
        if len(set(recipients)) != len(recipients):
            errors.append(f"{path}: duplicate recipient")
        if sender in recipients:
            errors.append(f"{path}: sender cannot be a recipient")
        if recipients == ["human"] and sender == "human":
            errors.append(f"{path}: an actor cannot message itself")
    if data.get("ack_required") not in {"true", "false"}:
        errors.append(f"{path}: ack_required must be true or false")
    if data.get("audience", "direct") not in {"direct", "all"}:
        errors.append(f"{path}: audience must be direct or all")
    for field in ("model", "client"):
        if not data.get(field):
            errors.append(f"{path}: {field} must be non-empty provenance")
    if published:
        errors += body_errors(path, body)
    return (Message(path, data, body, V2) if not errors else None), errors


def body_errors(path: Path, body: str) -> list[str]:
    """A published message must carry real content, not the untouched template."""
    lines = [l.strip() for l in body.splitlines() if l.strip()]
    prose = [l for l in lines if not l.startswith("#")]
    if "YYYY" in body or "short-slug" in body or not prose:
        return [f"{path}: body is empty or still the template"]
    return []


def validate_ack(path: Path, reg: Registry) -> tuple[str | None, str, list[str]]:
    data, _, errors = front_matter(path)
    required = {"protocol", "acknowledges", "by", "created_utc"}
    missing = sorted(required - data.keys())
    if missing:
        errors.append(f"{path}: missing keys {missing}")
    actor = path.parent.name
    if data.get("protocol") not in {V1, V2}:
        errors.append(f"{path}: wrong protocol {data.get('protocol')!r}")
    if data.get("by") != actor or not reg.is_actor(actor):
        errors.append(f"{path}: acknowledgement ownership mismatch")
    acknowledged = data.get("acknowledges")
    if acknowledged and path.name != f"{acknowledged}.ack.md":
        errors.append(f"{path}: filename does not match acknowledges")
    if not TIME_RE.fullmatch(data.get("created_utc", "")):
        errors.append(f"{path}: malformed created_utc")
    return acknowledged, actor, errors


# ------------------------------------------------------------------- spool


class Spool:
    def __init__(self, reg: Registry):
        self.reg = reg
        self.base = reg.spool
        self.errors: list[str] = []
        self.published: dict[str, Message] = {}
        self.drafts: dict[str, Message] = {}
        self.acked: dict[str, set[str]] = {}  # message id -> actors
        self._load()

    def _iter(self, directory: Path, suffix: str):
        if not directory.exists():
            return []
        return sorted(p for p in directory.glob(f"*{suffix}") if not p.name.endswith(".tmp"))

    def _load(self) -> None:
        reg, base = self.reg, self.base
        # v1 history: per-recipient inboxes, read-only.
        for actor in reg.actors:
            for path in self._iter(base / "inbox" / actor, ".md"):
                msg, errs = validate_v1(path, reg, published=True)
                self.errors += errs
                if msg:
                    self._index(msg)
        # v2 canonical store.
        for path in self._iter(base / "messages", ".md"):
            msg, errs = validate_v2(path, reg, published=True)
            self.errors += errs
            if msg:
                self._index(msg)
        # drafts are private composition space: they never block the spool.
        # Problems are reported as warnings, and only for the requesting
        # actor's own drafts (see draft_warnings); other actors' drafts may be
        # half-written at any moment.
        self.draft_paths: dict[str, list[Path]] = {}
        for actor in reg.actors:
            self.draft_paths[actor] = self._iter(base / "drafts" / actor, ".md")
            for path in self.draft_paths[actor]:
                data, _, _ = front_matter(path)
                mid = data.get("id")
                if mid:
                    self.drafts[mid] = Message(path, data, "", data.get("protocol", V2))
        # referential integrity (published messages only)
        for msg in list(self.published.values()):
            for field in ("in_reply_to", "supersedes"):
                target = msg.data.get(field, "none")
                if target != "none" and target not in self.published:
                    self.errors.append(f"{msg.path}: {field} names unknown or unpublished message {target!r}")
        # acknowledgements
        for actor in reg.actors:
            for path in self._iter(base / "acks" / actor, ".ack.md"):
                acknowledged, by, errs = validate_ack(path, reg)
                self.errors += errs
                if not acknowledged:
                    continue
                msg = self.published.get(acknowledged)
                if msg is None:
                    self.errors.append(f"{path}: acknowledges unknown message")
                    continue
                if by not in msg.recipients():
                    self.errors.append(f"{path}: acknowledgement actor is not a recipient")
                self.acked.setdefault(acknowledged, set()).add(by)

    def draft_warnings(self, actor: str) -> list[str]:
        warnings: list[str] = []
        for path in self.draft_paths.get(actor, []):
            data, _, _ = front_matter(path)
            if data.get("protocol") == V1:
                _, errs = validate_v1(path, self.reg, published=False)
            else:
                _, errs = validate_v2(path, self.reg, published=False)
            warnings += errs
            mid = data.get("id")
            if mid and mid in self.published:
                warnings.append(f"{path}: draft id already published")
            for field in ("in_reply_to", "supersedes"):
                target = data.get(field, "none")
                if target != "none" and target not in self.published:
                    warnings.append(f"{path}: {field} must name a published message")
        return warnings

    def _index(self, msg: Message) -> None:
        if msg.id in self.published:
            self.errors.append(f"{msg.path}: duplicate id also in {self.published[msg.id].path}")
        self.published[msg.id] = msg

    def pending_for(self, actor: str) -> tuple[list[Message], list[Message]]:
        """Messages the actor still owes an acknowledgement for.

        An actor with `acknowledges = false` in the registry (the human
        partner) never owes one: everything addressed to it is returned by
        addressed_to() instead and is never pending.
        """
        if not self.reg.acknowledges(actor):
            return [], []
        direct, broadcast = [], []
        for msg in self.published.values():
            if actor not in msg.recipients() or not msg.ack_required:
                continue
            if actor in self.acked.get(msg.id, set()):
                continue
            (broadcast if msg.data.get("audience") == "all" else direct).append(msg)
        key = lambda m: m.id
        return sorted(direct, key=key), sorted(broadcast, key=key)

    def addressed_to(self, actor: str) -> list[Message]:
        return sorted((m for m in self.published.values() if actor in m.recipients()
                       and actor not in self.acked.get(m.id, set())), key=lambda m: m.id)


# ---------------------------------------------------------------- commands


def now_utc() -> _dt.datetime:
    return _dt.datetime.now(_dt.timezone.utc).replace(microsecond=0)


def stamp(t: _dt.datetime) -> tuple[str, str]:
    return t.strftime("%Y%m%dT%H%M%SZ"), t.strftime("%Y-%m-%dT%H:%M:%SZ")


def require_actor(reg: Registry, actor: str) -> None:
    if not reg.is_actor(actor):
        raise ExchangeError(EXIT_OWNERSHIP, f"unknown actor {actor!r}; registry actors: {', '.join(sorted(reg.actors))}")


def cmd_validate(reg: Registry) -> int:
    spool = Spool(reg)
    for e in spool.errors:
        print(f"ERROR {e}")
    acks = sum(len(v) for v in spool.acked.values())
    print(f"messages={len(spool.published)} drafts={len(spool.drafts)} acknowledgements={acks} errors={len(spool.errors)}")
    return EXIT_VALIDATION if spool.errors else 0


def cmd_status(reg: Registry, actor: str) -> int:
    require_actor(reg, actor)
    spool = Spool(reg)
    for e in spool.errors:
        print(f"ERROR {e}")
    acks = sum(len(v) for v in spool.acked.values())
    print(f"messages={len(spool.published)} drafts={len(spool.drafts)} acknowledgements={acks} errors={len(spool.errors)}")
    for w in spool.draft_warnings(actor):
        print(f"WARNING {w}")
    direct, broadcast = spool.pending_for(actor)
    print(f"pending_for_{actor}={len(direct) + len(broadcast)} direct={len(direct)} broadcast={len(broadcast)}")
    for m in direct:
        print(f"PENDING {m.id} {m.path}")
    for m in broadcast:
        print(f"PENDING-BROADCAST {m.id} {m.path}")
    if not reg.acknowledges(actor):
        for m in spool.addressed_to(actor):
            print(f"ADDRESSED {m.id} {m.path}")
    return EXIT_VALIDATION if spool.errors else 0


def cmd_new(reg: Registry, a: argparse.Namespace) -> int:
    actor = bound_actor(reg, a.actor)
    if not SLUG_RE.fullmatch(a.slug):
        raise ExchangeError(EXIT_USAGE, "slug must be lowercase ascii [a-z0-9-]")
    if a.kind not in KINDS:
        raise ExchangeError(EXIT_USAGE, f"kind must be one of {sorted(KINDS)}")
    issues = a.issues or "none"
    if issues != "none" and not ISSUES_RE.fullmatch(issues):
        raise ExchangeError(EXIT_USAGE, "issues must be like '#1,#2' or none")
    to = a.to.strip()
    if to != "all":
        recips = [t.strip() for t in to.split(",") if t.strip()]
        if not recips:
            raise ExchangeError(EXIT_USAGE, "empty recipient list")
        for r in recips:
            require_actor(reg, r)
        if actor in recips:
            raise ExchangeError(EXIT_USAGE, "sender cannot be a recipient")
        to = ",".join(recips)
    draft_dir = reg.spool / "drafts" / actor
    draft_dir.mkdir(parents=True, exist_ok=True)
    spool = Spool(reg)
    t = now_utc()
    for _attempt in range(120):  # advance one second per collision
        compact, iso = stamp(t)
        message_id = f"{compact}-{actor}-{a.slug}"
        if message_id in spool.published or message_id in spool.drafts:
            t += _dt.timedelta(seconds=1)
            continue
        path = draft_dir / f"{message_id}.md"
        try:
            fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
        except FileExistsError:  # lost a same-second race with a sibling process
            t += _dt.timedelta(seconds=1)
            continue
        os.close(fd)
        break
    else:
        raise ExchangeError(EXIT_COLLISION, "could not allocate a message id")
    header = [
        ("protocol", V2), ("id", message_id), ("from", actor), ("to", to),
        ("created_utc", iso), ("kind", a.kind),
        ("model", a.model or reg.default_model(actor)),
        ("client", a.client or reg.default_client(actor)),
        ("ack_required", "false" if a.no_ack else "true"),
        ("in_reply_to", a.reply_to or "none"), ("supersedes", a.supersedes or "none"),
        ("github_issues", issues),
    ]
    template = Path(__file__).resolve().parent / "MESSAGE_TEMPLATE.md"
    body = "\n" + template.read_text().split("---", 2)[2].lstrip("\n")
    tmp = path.with_name(f"{path.name}.{os.getpid()}.tmp")
    with open(tmp, "w") as fh:  # the reserved final name is empty until this rename
        fh.write(render(header, body))
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)
    print(path)
    return 0


def cmd_publish(reg: Registry, actor: str | None, draft: Path) -> int:
    actor = bound_actor(reg, actor)
    draft_dir = reg.spool / "drafts" / actor
    if not draft.exists() and "/" not in str(draft):
        # accept a bare draft id or filename, as `ack` accepts a bare id
        candidate = draft_dir / (draft.name if draft.name.endswith(".md") else f"{draft.name}.md")
        if candidate.exists():
            draft = candidate
    draft = draft.resolve()
    if not draft.exists():
        raise ExchangeError(EXIT_USAGE, f"draft not found: {draft} (pass the draft path, its filename, or its id)")
    if draft.parent != (reg.spool / "drafts" / actor).resolve():
        raise ExchangeError(EXIT_OWNERSHIP, f"{draft} is not in {actor}'s draft directory")
    data, body, errs = front_matter(draft)
    if data.get("protocol") == V1:
        raise ExchangeError(EXIT_VALIDATION, "v1 messages are history; publish only v2 messages")
    msg, errs2 = validate_v2(draft, reg, published=False)
    errs += errs2
    if errs:
        for e in errs:
            print(f"ERROR {e}")
        return EXIT_VALIDATION
    spool = Spool(reg)
    if msg.id in spool.published:
        raise ExchangeError(EXIT_COLLISION, f"message id already published: {msg.id}")
    if spool.errors:
        for e in spool.errors:
            print(f"ERROR {e}")
        raise ExchangeError(EXIT_VALIDATION, "spool has validation errors; fix them before publishing")
    for field in ("in_reply_to", "supersedes"):
        target = data.get(field, "none")
        if target != "none" and target not in spool.published:
            raise ExchangeError(EXIT_UNKNOWN, f"{field} names unknown message {target!r}")
    # Materialize the audience at publication so later registry changes never
    # alter whom an already published message is pending for.
    header = [(k, v) for k, v in data.items() if k != "audience"]
    if data["to"] == "all":
        recips = [r for r in reg.broadcast_recipients() if r != actor]
        if not recips:
            raise ExchangeError(EXIT_USAGE, "no active broadcast recipients")
        header = [(k, (",".join(recips) if k == "to" else v)) for k, v in header]
        header.insert(4, ("audience", "all"))
    else:
        header.insert(4, ("audience", "direct"))
    messages_dir = reg.spool / "messages"
    messages_dir.mkdir(parents=True, exist_ok=True)
    final = messages_dir / f"{msg.id}.md"
    tmp = messages_dir / f"{msg.id}.md.{os.getpid()}.tmp"
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    with os.fdopen(fd, "w") as fh:
        fh.write(render(header, body))
        fh.flush()
        os.fsync(fh.fileno())
    # Validate the fully materialized content under its final name BEFORE it
    # becomes observable; nothing invalid ever crosses the publication boundary.
    _, errs3 = validate_v2(tmp, reg, published=True, name=final.name)
    if errs3:
        os.unlink(tmp)
        for e in errs3:
            print(f"ERROR {e}")
        return EXIT_VALIDATION
    try:
        os.link(tmp, final)  # fails if another publication won the race
    except FileExistsError:
        os.unlink(tmp)
        raise ExchangeError(EXIT_COLLISION, f"message id already published: {msg.id}")
    os.unlink(tmp)
    os.unlink(draft)
    print(final)
    return 0


def cmd_ack(reg: Registry, actor: str | None, message_id: str, disposition: str) -> int:
    actor = bound_actor(reg, actor)
    spool = Spool(reg)
    if spool.errors:
        for e in spool.errors:
            print(f"ERROR {e}")
        raise ExchangeError(EXIT_VALIDATION, "spool has validation errors; fix them before acknowledging")
    msg = spool.published.get(message_id)
    if msg is None:
        raise ExchangeError(EXIT_UNKNOWN, f"unknown message {message_id!r}")
    if actor not in msg.recipients():
        raise ExchangeError(EXIT_OWNERSHIP, f"{actor} is not a recipient of {message_id}")
    ack_dir = reg.spool / "acks" / actor
    ack_dir.mkdir(parents=True, exist_ok=True)
    path = ack_dir / f"{message_id}.ack.md"
    _, iso = stamp(now_utc())
    header = [("protocol", msg.protocol), ("acknowledges", message_id), ("by", actor), ("created_utc", iso)]
    body = f"\nRead and disposition captured in: {disposition.strip()}\n"
    if path.exists():
        raise ExchangeError(EXIT_COLLISION, f"{actor} already acknowledged {message_id}")
    tmp = path.with_name(f"{path.name}.{os.getpid()}.tmp")  # unique: a stale .tmp from a crash never blocks
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    with os.fdopen(fd, "w") as fh:
        fh.write(render(header, body))
        fh.flush()
        os.fsync(fh.fileno())
    try:
        os.link(tmp, path)
    except FileExistsError:
        os.unlink(tmp)
        raise ExchangeError(EXIT_COLLISION, f"{actor} already acknowledged {message_id}")
    os.unlink(tmp)
    print(path)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", default=None, help="repository root (default: derived from this file)")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("validate")
    p = sub.add_parser("status"); p.add_argument("--actor", required=True)
    p = sub.add_parser("new")
    p.add_argument("--actor"); p.add_argument("--to", required=True)
    p.add_argument("--kind", required=True); p.add_argument("--slug", required=True)
    p.add_argument("--issues"); p.add_argument("--reply-to"); p.add_argument("--supersedes")
    p.add_argument("--no-ack", action="store_true"); p.add_argument("--model"); p.add_argument("--client")
    p = sub.add_parser("publish"); p.add_argument("--actor"); p.add_argument("draft")
    p = sub.add_parser("ack"); p.add_argument("--actor"); p.add_argument("message_id")
    p.add_argument("--disposition", required=True)
    a = parser.parse_args(argv)
    root = Path(a.root).resolve() if a.root else Path(__file__).resolve().parents[2]
    try:
        reg = Registry(root)
        if a.command == "validate":
            return cmd_validate(reg)
        if a.command == "status":
            return cmd_status(reg, a.actor)
        if a.command == "new":
            return cmd_new(reg, a)
        if a.command == "publish":
            return cmd_publish(reg, a.actor, Path(a.draft))
        if a.command == "ack":
            return cmd_ack(reg, a.actor, a.message_id, a.disposition)
    except ExchangeError as exc:
        print(f"ERROR {exc}", file=sys.stderr)
        return exc.code
    return EXIT_USAGE


if __name__ == "__main__":
    raise SystemExit(main())
