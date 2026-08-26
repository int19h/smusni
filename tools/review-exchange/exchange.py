#!/usr/bin/env python3
"""Multi-model review exchange helper (protocol smusni-review-mail/v3).

Tracked control plane for the ignored message spool under review/exchange/.
Models come from participants.toml; sessions register themselves in the
spool; nothing here hard-codes a participant.

Actors are sessions: `<model>_<generation>[.<n>]` (the first Fable session of
generation 1 is `fable_1`, a second concurrent one `fable_1.1`), plus the
fixed actor `human`. The current generation is `generation` in the registry.

Commands:
  join     --model M [--client C] [--note T]   register this session, print its id
  retire   --actor A [--note T]                 mark this session handed off
  sessions                                      list registered sessions
  validate                                      validate history, messages, sessions
  status   --actor A                            list what A owes
  new      --actor A --to L|all --kind K --slug S [--issues ..] [--reply-to ID]
           [--supersedes ID] [--no-ack] [--model M] [--client C]
  publish  --actor A DRAFT                      validate, expand `all`, publish atomically
  ack      --actor A ID --disposition TEXT      acknowledge a received message

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
V3 = "smusni-review-mail/v3"
KINDS = {"request", "response", "finding", "proposal", "handoff", "decision-query"}
TIME_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")
SLUG_RE = re.compile(r"^[a-z0-9][a-z0-9-]*$")
MODEL_RE = re.compile(r"^[a-z][a-z0-9]*$")
SESSION_RE = re.compile(r"^([a-z][a-z0-9]*)_(\d+)(?:\.(\d+))?$")
ISSUES_RE = re.compile(r"^#\d+(,#\d+)*$")
V1_LEGACY_SENDERS = {"owner"}  # historical alias of the human partner

EXIT_USAGE, EXIT_VALIDATION, EXIT_OWNERSHIP, EXIT_COLLISION, EXIT_UNKNOWN = 1, 2, 3, 4, 5


class ExchangeError(Exception):
    def __init__(self, code: int, message: str):
        super().__init__(message)
        self.code = code


def parse_session(name: str) -> tuple[str, int, int] | None:
    """`fable_1` -> ("fable", 1, 0); `fable_1.2` -> ("fable", 1, 2); else None."""
    m = SESSION_RE.fullmatch(name)
    if not m:
        return None
    return m.group(1), int(m.group(2)), int(m.group(3) or 0)


# ----------------------------------------------------------------- registry


class Registry:
    """participants.toml: the model allow-list, the fixed actors, the generation."""

    def __init__(self, root: Path):
        self.root = root
        path = root / "tools" / "review-exchange" / "participants.toml"
        if not path.exists():
            raise ExchangeError(EXIT_USAGE, f"registry not found: {path}")
        data = tomllib.loads(path.read_text())
        self.protocol = data.get("protocol", V3)
        self.spool = root / data.get("spool", "review/exchange")
        self.generation = int(data.get("generation", 1))
        if self.generation < 1:
            raise ExchangeError(EXIT_USAGE, "generation must be a positive integer")
        self.models: dict[str, dict] = data.get("models") or data.get("actors") or {}
        if not self.models:
            raise ExchangeError(EXIT_USAGE, "registry declares no models")
        for name in self.models:
            if not MODEL_RE.fullmatch(name):
                raise ExchangeError(EXIT_USAGE, f"bad model name in registry: {name!r}")
        # Fixed actors (`sessions = false`) are addressed by their model name.
        self.fixed: set[str] = {n for n, m in self.models.items() if m.get("sessions", True) is False}

    def is_model(self, name: str) -> bool:
        return name in self.models

    def model_active(self, name: str) -> bool:
        return bool(self.models.get(name, {}).get("active", False))

    def broadcast_model(self, name: str) -> bool:
        m = self.models.get(name, {})
        return bool(m.get("active", False) and m.get("broadcast_recipient", False))

    def default_model(self, name: str) -> str:
        return str(self.models[name].get("model", "unspecified"))

    def default_client(self, name: str) -> str:
        return str(self.models[name].get("client", "unspecified"))

    def acknowledges_fixed(self, name: str) -> bool:
        return bool(self.models.get(name, {}).get("acknowledges", True))


# ----------------------------------------------------------------- sessions


class Session:
    def __init__(self, path: Path, data: dict[str, str]):
        self.path, self.data = path, data

    @property
    def id(self) -> str:
        return self.data.get("session", "")

    @property
    def model(self) -> str:
        return self.data.get("model", "")

    @property
    def active(self) -> bool:
        return self.data.get("status") == "active"


class Sessions:
    """The spool's session registry: review/exchange/sessions/<id>.md."""

    def __init__(self, reg: Registry):
        self.reg = reg
        self.dir = reg.spool / "sessions"
        self.errors: list[str] = []
        self.by_id: dict[str, Session] = {}
        if not self.dir.exists():
            return
        for path in sorted(p for p in self.dir.glob("*.md") if not p.name.endswith(".tmp")):
            data, _, errs = front_matter(path)
            self.errors += errs
            sid = data.get("session", "")
            parsed = parse_session(sid)
            if data.get("protocol") != V3:
                self.errors.append(f"{path}: wrong protocol {data.get('protocol')!r}")
            if not parsed:
                self.errors.append(f"{path}: malformed session id {sid!r}")
                continue
            model, gen, idx = parsed
            if path.name != f"{sid}.md":
                self.errors.append(f"{path}: filename does not match session id")
            if not reg.is_model(model) or model in reg.fixed:
                self.errors.append(f"{path}: session model {model!r} is not a session-capable registry model")
            if data.get("model") != model:
                self.errors.append(f"{path}: model field does not match the session id")
            if data.get("generation") != str(gen) or data.get("index") != str(idx):
                self.errors.append(f"{path}: generation/index fields do not match the session id")
            if data.get("status") not in {"active", "retired"}:
                self.errors.append(f"{path}: status must be active or retired")
            if not TIME_RE.fullmatch(data.get("created_utc", "")):
                self.errors.append(f"{path}: malformed created_utc")
            if sid in self.by_id:
                self.errors.append(f"{path}: duplicate session id")
            self.by_id[sid] = Session(path, data)

    def get(self, sid: str) -> Session | None:
        return self.by_id.get(sid)

    def of_model(self, model: str) -> list[Session]:
        return [s for s in self.by_id.values() if s.model == model]

    def legacy_owner(self, model: str) -> str | None:
        """The earliest-joined session of a model inherits the model's v1/v2 mail."""
        owned = sorted(self.of_model(model), key=lambda s: parse_session(s.id)[1:])
        return owned[0].id if owned else None

    def active_broadcast(self) -> list[str]:
        return sorted(s.id for s in self.by_id.values() if s.active and self.reg.broadcast_model(s.model))

    def next_id(self, model: str, generation: int) -> str:
        taken = {parse_session(s.id)[2] for s in self.of_model(model) if parse_session(s.id)[1] == generation}
        if not taken:
            return f"{model}_{generation}"
        return f"{model}_{generation}.{max(taken) + 1}"


class Actors:
    """Who may send, receive, and acknowledge: fixed actors and registered sessions."""

    def __init__(self, reg: Registry, sessions: Sessions):
        self.reg, self.sessions = reg, sessions

    def is_actor(self, name: str) -> bool:
        return name in self.reg.fixed or self.sessions.get(name) is not None

    def is_legacy(self, name: str) -> bool:
        """A bare model slug: valid only in v1/v2 history and its acknowledgements."""
        return self.reg.is_model(name) and name not in self.reg.fixed

    def model_of(self, name: str) -> str | None:
        if name in self.reg.fixed:
            return name
        s = self.sessions.get(name)
        if s:
            return s.model
        return name if self.is_legacy(name) else None

    def acknowledges(self, name: str) -> bool:
        if name in self.reg.fixed:
            return self.reg.acknowledges_fixed(name)
        return True

    def describe_unknown(self, name: str) -> str:
        if self.is_legacy(name):
            return (f"{name!r} is a model, not a session: run "
                    f"`exchange.py join --model {name}` and use the printed session id")
        return f"unknown actor {name!r}; registered sessions: {', '.join(sorted(self.sessions.by_id)) or 'none'}; fixed: {', '.join(sorted(self.reg.fixed))}"


BINDING_ENV = "SMUSNI_EXCHANGE_ACTOR"


def bound_actor(actors: Actors, requested: str | None) -> str:
    """Resolve the acting actor for a mutating command.

    If SMUSNI_EXCHANGE_ACTOR is set, a different --actor is refused: an
    accidental-safety boundary for two sessions sharing one client, not
    security against the shared account. Unset means --actor is trusted.
    """
    bound = os.environ.get(BINDING_ENV, "").strip() or None
    if bound and not actors.is_actor(bound):
        raise ExchangeError(EXIT_OWNERSHIP, f"{BINDING_ENV}={bound!r}: {actors.describe_unknown(bound)}")
    if requested and bound and requested != bound:
        raise ExchangeError(EXIT_OWNERSHIP, f"this session is bound to actor {bound!r}; refusing --actor {requested!r}")
    actor = requested or bound
    if not actor:
        raise ExchangeError(EXIT_USAGE, f"--actor is required (or export {BINDING_ENV})")
    if not actors.is_actor(actor):
        raise ExchangeError(EXIT_OWNERSHIP, actors.describe_unknown(actor))
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


def write_exclusive(path: Path, content: str) -> None:
    """Create `path` atomically; fail if it exists (tmp + link, never rename over)."""
    tmp = path.with_name(f"{path.name}.{os.getpid()}.tmp")
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    with os.fdopen(fd, "w") as fh:
        fh.write(content)
        fh.flush()
        os.fsync(fh.fileno())
    try:
        os.link(tmp, path)
    except FileExistsError:
        os.unlink(tmp)
        raise
    os.unlink(tmp)


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
    def legacy(self) -> bool:
        return self.protocol in {V1, V2}

    @property
    def ack_required(self) -> bool:
        if self.protocol == V1:
            return True
        return self.data.get("ack_required", "true") == "true"


def _check_common(path: Path, data: dict[str, str], *, protocol: str, sender_ok) -> list[str]:
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
            and SLUG_RE.fullmatch(parts[2]) is not None and sender_ok(parts[1])
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


def _legacy_actor_ok(actors: Actors, name: str) -> bool:
    return actors.is_legacy(name) or name in actors.reg.fixed


def validate_v1(path: Path, actors: Actors, *, published: bool) -> tuple[Message | None, list[str]]:
    data, body, errors = front_matter(path)
    required = {"protocol", "id", "from", "to", "created_utc", "kind",
                "in_reply_to", "supersedes", "github_issues"}
    missing = sorted(required - data.keys())
    if missing:
        errors.append(f"{path}: missing keys {missing}")
    errors += _check_common(path, data, protocol=V1,
                            sender_ok=lambda n: _legacy_actor_ok(actors, n) or n in V1_LEGACY_SENDERS)
    sender, to = data.get("from", ""), data.get("to", "")
    if not (_legacy_actor_ok(actors, sender) or sender in V1_LEGACY_SENDERS):
        errors.append(f"{path}: invalid sender {sender!r}")
    if not actors.is_legacy(to):
        errors.append(f"{path}: invalid recipient {to!r}")
    if sender == to:
        errors.append(f"{path}: sender and recipient are identical")
    expected_dir = to if published else sender
    if expected_dir and path.parent.name != expected_dir:
        errors.append(f"{path}: {'recipient' if published else 'sender'} directory does not match header")
    return (Message(path, data, body, V1) if not errors else None), errors


def validate_v2(path: Path, actors: Actors, *, published: bool, name: str | None = None) -> tuple[Message | None, list[str]]:
    """v2 history: bare model slugs as actors. Read-only after the v3 cut-over."""
    data, body, errors = front_matter(path)
    if name is not None:
        path = path.with_name(name)
    required = {"protocol", "id", "from", "to", "created_utc", "kind", "model",
                "client", "ack_required", "in_reply_to", "supersedes", "github_issues"}
    missing = sorted(required - data.keys())
    if missing:
        errors.append(f"{path}: missing keys {missing}")
    errors += _check_common(path, data, protocol=V2, sender_ok=lambda n: _legacy_actor_ok(actors, n))
    sender = data.get("from", "")
    if not _legacy_actor_ok(actors, sender):
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
            if not _legacy_actor_ok(actors, r):
                errors.append(f"{path}: unknown recipient {r!r}")
        if len(set(recipients)) != len(recipients):
            errors.append(f"{path}: duplicate recipient")
        if sender in recipients:
            errors.append(f"{path}: sender cannot be a recipient")
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


def validate_v3(path: Path, actors: Actors, *, published: bool, name: str | None = None) -> tuple[Message | None, list[str]]:
    data, body, errors = front_matter(path)
    if name is not None:
        path = path.with_name(name)
    required = {"protocol", "id", "from", "to", "created_utc", "kind", "model",
                "client", "generation", "ack_required", "in_reply_to", "supersedes", "github_issues"}
    missing = sorted(required - data.keys())
    if missing:
        errors.append(f"{path}: missing keys {missing}")
    errors += _check_common(path, data, protocol=V3, sender_ok=actors.is_actor)
    sender = data.get("from", "")
    if not actors.is_actor(sender):
        errors.append(f"{path}: invalid sender {sender!r}: {actors.describe_unknown(sender)}")
    else:
        session = actors.sessions.get(sender)
        expected_gen = str(parse_session(sender)[1]) if session else "0"
        if data.get("generation") != expected_gen:
            errors.append(f"{path}: generation must be the sender's ({expected_gen})")
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
            if not actors.is_actor(r):
                errors.append(f"{path}: unknown recipient {r!r}: {actors.describe_unknown(r)}")
        if len(set(recipients)) != len(recipients):
            errors.append(f"{path}: duplicate recipient")
        if sender in recipients:
            errors.append(f"{path}: sender cannot be a recipient")
    if data.get("ack_required") not in {"true", "false"}:
        errors.append(f"{path}: ack_required must be true or false")
    if data.get("audience", "direct") not in {"direct", "all"}:
        errors.append(f"{path}: audience must be direct or all")
    for field in ("model", "client"):
        if not data.get(field):
            errors.append(f"{path}: {field} must be non-empty provenance")
    if published:
        errors += body_errors(path, body)
    return (Message(path, data, body, V3) if not errors else None), errors


def body_errors(path: Path, body: str) -> list[str]:
    """A published message must carry real content, not the untouched template."""
    lines = [l.strip() for l in body.splitlines() if l.strip()]
    prose = [l for l in lines if not l.startswith("#")]
    if "YYYY" in body or "short-slug" in body or not prose:
        return [f"{path}: body is empty or still the template"]
    return []


def validate_ack(path: Path, actors: Actors) -> tuple[str | None, str, list[str]]:
    data, _, errors = front_matter(path)
    required = {"protocol", "acknowledges", "by", "created_utc"}
    missing = sorted(required - data.keys())
    if missing:
        errors.append(f"{path}: missing keys {missing}")
    actor = path.parent.name
    if data.get("protocol") not in {V1, V2, V3}:
        errors.append(f"{path}: wrong protocol {data.get('protocol')!r}")
    if data.get("by") != actor or not (actors.is_actor(actor) or actors.is_legacy(actor)):
        errors.append(f"{path}: acknowledgement ownership mismatch")
    acknowledged = data.get("acknowledges")
    if acknowledged and path.name != f"{acknowledged}.ack.md":
        errors.append(f"{path}: filename does not match acknowledges")
    if not TIME_RE.fullmatch(data.get("created_utc", "")):
        errors.append(f"{path}: malformed created_utc")
    return acknowledged, actor, errors


def ack_counts_for(msg: Message, by: str, actors: Actors) -> bool:
    """Does an acknowledgement by `by` discharge `msg` for one of its recipients?"""
    if by in msg.recipients():
        return True
    if msg.legacy:
        model = actors.model_of(by)
        return model is not None and model in msg.recipients()
    return False


# ------------------------------------------------------------------- spool


class Spool:
    def __init__(self, reg: Registry):
        self.reg = reg
        self.base = reg.spool
        self.sessions = Sessions(reg)
        self.actors = Actors(reg, self.sessions)
        self.errors: list[str] = list(self.sessions.errors)
        self.published: dict[str, Message] = {}
        self.drafts: dict[str, Message] = {}
        self.acked: dict[str, set[str]] = {}  # message id -> acknowledging actors
        self._load()

    def _iter(self, directory: Path, suffix: str):
        if not directory.exists():
            return []
        return sorted(p for p in directory.glob(f"*{suffix}") if not p.name.endswith(".tmp"))

    def _subdirs(self, directory: Path) -> list[str]:
        if not directory.exists():
            return []
        return sorted(p.name for p in directory.iterdir() if p.is_dir())

    def _load(self) -> None:
        reg, base, actors = self.reg, self.base, self.actors
        # v1 history: per-recipient inboxes, read-only.
        for actor in self._subdirs(base / "inbox"):
            for path in self._iter(base / "inbox" / actor, ".md"):
                msg, errs = validate_v1(path, actors, published=True)
                self.errors += errs
                if msg:
                    self._index(msg)
        # canonical store: v2 history and v3 messages side by side.
        for path in self._iter(base / "messages", ".md"):
            data, _, _ = front_matter(path)
            if data.get("protocol") == V2:
                msg, errs = validate_v2(path, actors, published=True)
            else:
                msg, errs = validate_v3(path, actors, published=True)
            self.errors += errs
            if msg:
                self._index(msg)
        # drafts are private composition space: they never block the spool.
        self.draft_paths: dict[str, list[Path]] = {}
        for actor in self._subdirs(base / "drafts"):
            self.draft_paths[actor] = self._iter(base / "drafts" / actor, ".md")
            for path in self.draft_paths[actor]:
                data, _, _ = front_matter(path)
                mid = data.get("id")
                if mid:
                    self.drafts[mid] = Message(path, data, "", data.get("protocol", V3))
        for msg in list(self.published.values()):
            for field in ("in_reply_to", "supersedes"):
                target = msg.data.get(field, "none")
                if target != "none" and target not in self.published:
                    self.errors.append(f"{msg.path}: {field} names unknown or unpublished message {target!r}")
        for actor in self._subdirs(base / "acks"):
            for path in self._iter(base / "acks" / actor, ".ack.md"):
                acknowledged, by, errs = validate_ack(path, actors)
                self.errors += errs
                if not acknowledged:
                    continue
                msg = self.published.get(acknowledged)
                if msg is None:
                    self.errors.append(f"{path}: acknowledges unknown message")
                    continue
                if not ack_counts_for(msg, by, actors):
                    self.errors.append(f"{path}: acknowledgement actor is not a recipient")
                self.acked.setdefault(acknowledged, set()).add(by)

    def draft_warnings(self, actor: str) -> list[str]:
        warnings: list[str] = []
        for path in self.draft_paths.get(actor, []):
            data, _, _ = front_matter(path)
            proto = data.get("protocol")
            if proto == V1:
                _, errs = validate_v1(path, self.actors, published=False)
            elif proto == V2:
                _, errs = validate_v2(path, self.actors, published=False)
            else:
                _, errs = validate_v3(path, self.actors, published=False)
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

    def _acked_for(self, msg: Message, actor: str) -> bool:
        acks = self.acked.get(msg.id, set())
        if actor in acks:
            return True
        if msg.legacy:
            model = self.actors.model_of(actor)
            return any(self.actors.model_of(a) == model for a in acks)
        return False

    def _addressed(self, msg: Message, actor: str) -> bool:
        if actor in msg.recipients():
            return True
        if msg.legacy:
            model = self.actors.model_of(actor)
            return (model in msg.recipients()
                    and self.sessions.legacy_owner(model) == actor)
        return False

    def pending_for(self, actor: str) -> tuple[list[Message], list[Message]]:
        """Messages the actor still owes an acknowledgement for.

        A fixed actor with `acknowledges = false` (the human partner) never
        owes one. A session also inherits its model's v1/v2 mail if it is the
        model's earliest-joined session.
        """
        if not self.actors.acknowledges(actor):
            return [], []
        direct, broadcast = [], []
        for msg in self.published.values():
            if not msg.ack_required or not self._addressed(msg, actor):
                continue
            if self._acked_for(msg, actor):
                continue
            (broadcast if msg.data.get("audience") == "all" else direct).append(msg)
        key = lambda m: m.id
        return sorted(direct, key=key), sorted(broadcast, key=key)

    def addressed_to(self, actor: str) -> list[Message]:
        return sorted((m for m in self.published.values() if self._addressed(m, actor)
                       and not self._acked_for(m, actor)), key=lambda m: m.id)


# ---------------------------------------------------------------- commands


def now_utc() -> _dt.datetime:
    return _dt.datetime.now(_dt.timezone.utc).replace(microsecond=0)


def stamp(t: _dt.datetime) -> tuple[str, str]:
    return t.strftime("%Y%m%dT%H%M%SZ"), t.strftime("%Y-%m-%dT%H:%M:%SZ")


def cmd_validate(reg: Registry) -> int:
    spool = Spool(reg)
    for e in spool.errors:
        print(f"ERROR {e}")
    acks = sum(len(v) for v in spool.acked.values())
    print(f"generation={reg.generation} sessions={len(spool.sessions.by_id)} messages={len(spool.published)} drafts={len(spool.drafts)} acknowledgements={acks} errors={len(spool.errors)}")
    return EXIT_VALIDATION if spool.errors else 0


def cmd_sessions(reg: Registry) -> int:
    spool = Spool(reg)
    print(f"generation={reg.generation}")
    for sid in sorted(spool.sessions.by_id, key=lambda s: (parse_session(s)[0], parse_session(s)[1], parse_session(s)[2])):
        s = spool.sessions.get(sid)
        print(f"{sid} model={s.model} client={s.data.get('client')} status={s.data.get('status')} joined={s.data.get('created_utc')}"
              + (f" retired={s.data.get('retired_utc')}" if s.data.get("retired_utc") else "")
              + (f" note={s.data.get('note')}" if s.data.get("note") else ""))
    return EXIT_VALIDATION if spool.errors else 0


def cmd_join(reg: Registry, model: str, client: str | None, note: str | None) -> int:
    if not reg.is_model(model):
        raise ExchangeError(EXIT_USAGE, f"unknown model {model!r}; registry models: {', '.join(sorted(reg.models))}")
    if model in reg.fixed:
        raise ExchangeError(EXIT_USAGE, f"{model!r} is a fixed actor; it has no sessions")
    if not reg.model_active(model):
        raise ExchangeError(EXIT_OWNERSHIP, f"model {model!r} is not active in the registry")
    sessions_dir = reg.spool / "sessions"
    sessions_dir.mkdir(parents=True, exist_ok=True)
    for _attempt in range(50):  # a same-second sibling may take the id first
        sessions = Sessions(reg)
        sid = sessions.next_id(model, reg.generation)
        _, gen, idx = parse_session(sid)
        _, iso = stamp(now_utc())
        header = [("protocol", V3), ("session", sid), ("model", model),
                  ("client", client or reg.default_client(model)),
                  ("model_name", reg.default_model(model)),
                  ("generation", str(gen)), ("index", str(idx)),
                  ("created_utc", iso), ("status", "active")]
        if note:
            header.append(("note", note.strip()))
        try:
            write_exclusive(sessions_dir / f"{sid}.md", render(header, "\n"))
        except FileExistsError:
            continue
        print(sid)
        return 0
    raise ExchangeError(EXIT_COLLISION, "could not allocate a session id")


def cmd_retire(reg: Registry, actor: str | None, note: str | None) -> int:
    spool = Spool(reg)
    actor = bound_actor(spool.actors, actor)
    session = spool.sessions.get(actor)
    if session is None:
        raise ExchangeError(EXIT_USAGE, f"{actor!r} is not a session")
    if not session.active:
        raise ExchangeError(EXIT_COLLISION, f"{actor} is already retired")
    _, iso = stamp(now_utc())
    header = [(k, v) for k, v in session.data.items() if k not in {"status", "retired_utc", "note"}]
    header += [("status", "retired"), ("retired_utc", iso)]
    if note or session.data.get("note"):
        header.append(("note", (note or session.data.get("note")).strip()))
    tmp = session.path.with_name(f"{session.path.name}.{os.getpid()}.tmp")
    with open(tmp, "w") as fh:
        fh.write(render(header, "\n"))
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, session.path)  # a session rewrites only its own file
    print(f"{actor} retired")
    return 0


def cmd_status(reg: Registry, actor: str) -> int:
    spool = Spool(reg)
    if not spool.actors.is_actor(actor):
        raise ExchangeError(EXIT_OWNERSHIP, spool.actors.describe_unknown(actor))
    for e in spool.errors:
        print(f"ERROR {e}")
    acks = sum(len(v) for v in spool.acked.values())
    print(f"generation={reg.generation} sessions={len(spool.sessions.by_id)} messages={len(spool.published)} drafts={len(spool.drafts)} acknowledgements={acks} errors={len(spool.errors)}")
    session = spool.sessions.get(actor)
    if session:
        print(f"session={actor} model={session.model} generation={session.data.get('generation')} status={session.data.get('status')}")
    for w in spool.draft_warnings(actor):
        print(f"WARNING {w}")
    direct, broadcast = spool.pending_for(actor)
    print(f"pending_for_{actor}={len(direct) + len(broadcast)} direct={len(direct)} broadcast={len(broadcast)}")
    for m in direct:
        print(f"PENDING {m.id} {m.path}")
    for m in broadcast:
        print(f"PENDING-BROADCAST {m.id} {m.path}")
    if not spool.actors.acknowledges(actor):
        for m in spool.addressed_to(actor):
            print(f"ADDRESSED {m.id} {m.path}")
    return EXIT_VALIDATION if spool.errors else 0


def cmd_new(reg: Registry, a: argparse.Namespace) -> int:
    spool = Spool(reg)
    actors = spool.actors
    actor = bound_actor(actors, a.actor)
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
            if not actors.is_actor(r):
                raise ExchangeError(EXIT_OWNERSHIP, actors.describe_unknown(r))
        if actor in recips:
            raise ExchangeError(EXIT_USAGE, "sender cannot be a recipient")
        to = ",".join(recips)
    session = spool.sessions.get(actor)
    model = actors.model_of(actor)
    draft_dir = reg.spool / "drafts" / actor
    draft_dir.mkdir(parents=True, exist_ok=True)
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
        ("protocol", V3), ("id", message_id), ("from", actor), ("to", to),
        ("created_utc", iso), ("kind", a.kind),
        ("model", a.model or (session.data.get("model_name") if session else reg.default_model(model))),
        ("client", a.client or (session.data.get("client") if session else reg.default_client(model))),
        ("generation", str(parse_session(actor)[1]) if session else "0"),
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
    spool = Spool(reg)
    actors = spool.actors
    actor = bound_actor(actors, actor)
    draft_dir = reg.spool / "drafts" / actor
    if not draft.exists() and "/" not in str(draft):
        candidate = draft_dir / (draft.name if draft.name.endswith(".md") else f"{draft.name}.md")
        if candidate.exists():
            draft = candidate
    draft = draft.resolve()
    if not draft.exists():
        raise ExchangeError(EXIT_USAGE, f"draft not found: {draft} (pass the draft path, its filename, or its id)")
    if draft.parent != draft_dir.resolve():
        raise ExchangeError(EXIT_OWNERSHIP, f"{draft} is not in {actor}'s draft directory")
    data, body, errs = front_matter(draft)
    if data.get("protocol") in {V1, V2}:
        raise ExchangeError(EXIT_VALIDATION, "v1/v2 messages are history; compose a new v3 draft with `new`")
    msg, errs2 = validate_v3(draft, actors, published=False)
    errs += errs2
    if errs:
        for e in errs:
            print(f"ERROR {e}")
        return EXIT_VALIDATION
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
    # Materialize the audience at publication: the active sessions of every
    # broadcast model, minus the sender. Later joins or retirements never
    # change whom an already published message is pending for.
    header = [(k, v) for k, v in data.items() if k != "audience"]
    if data["to"] == "all":
        recips = [r for r in spool.sessions.active_broadcast() if r != actor]
        if not recips:
            raise ExchangeError(EXIT_USAGE, "no active broadcast sessions (has anyone joined?)")
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
    _, errs3 = validate_v3(tmp, actors, published=True, name=final.name)
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
    spool = Spool(reg)
    actors = spool.actors
    actor = bound_actor(actors, actor)
    if spool.errors:
        for e in spool.errors:
            print(f"ERROR {e}")
        raise ExchangeError(EXIT_VALIDATION, "spool has validation errors; fix them before acknowledging")
    msg = spool.published.get(message_id)
    if msg is None:
        raise ExchangeError(EXIT_UNKNOWN, f"unknown message {message_id!r}")
    if not spool._addressed(msg, actor):
        raise ExchangeError(EXIT_OWNERSHIP, f"{actor} is not a recipient of {message_id}")
    ack_dir = reg.spool / "acks" / actor
    ack_dir.mkdir(parents=True, exist_ok=True)
    path = ack_dir / f"{message_id}.ack.md"
    _, iso = stamp(now_utc())
    header = [("protocol", msg.protocol), ("acknowledges", message_id), ("by", actor), ("created_utc", iso)]
    body = f"\nRead and disposition captured in: {disposition.strip()}\n"
    if path.exists():
        raise ExchangeError(EXIT_COLLISION, f"{actor} already acknowledged {message_id}")
    try:
        write_exclusive(path, render(header, body))
    except FileExistsError:
        raise ExchangeError(EXIT_COLLISION, f"{actor} already acknowledged {message_id}")
    print(path)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", default=None, help="repository root (default: derived from this file)")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("validate")
    sub.add_parser("sessions")
    p = sub.add_parser("join"); p.add_argument("--model", required=True); p.add_argument("--client"); p.add_argument("--note")
    p = sub.add_parser("retire"); p.add_argument("--actor"); p.add_argument("--note")
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
        if a.command == "sessions":
            return cmd_sessions(reg)
        if a.command == "join":
            return cmd_join(reg, a.model, a.client, a.note)
        if a.command == "retire":
            return cmd_retire(reg, a.actor, a.note)
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
