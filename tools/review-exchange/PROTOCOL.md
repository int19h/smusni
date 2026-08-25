# Multi-model review exchange protocol

Protocol version: **`smusni-review-mail/v2`**.

The exchange is a transient peer-review channel shared through the local
filesystem by every model session working on this repository and by the human
partner. It replaces copy/paste between sessions. The message spool under
[`review/exchange/`](../../review/exchange/) is ignored by Git; this directory
holds the tracked control plane: this protocol, the participant registry
([`participants.toml`](participants.toml)), the helper
([`exchange.py`](exchange.py)), its templates
([message](MESSAGE_TEMPLATE.md), [acknowledgement](ACK_TEMPLATE.md)), the
launch guide ([`LAUNCH.md`](LAUNCH.md)), and its [tests](tests/). File paths
in this document are written relative to the repository root, and all
commands are run from there. GitHub issues remain the durable work
queue, and the normative documents plus the human partner's adjudications remain
the semantic authority.

## Participants

[`participants.toml`](participants.toml) is the single actor allow-list. Every actor has a lowercase
slug (`codex`, `fable`, `kimi`, `qwen`, `deepseek`, `human`, …), a display name,
its transporting client, its default model selector, an `active` flag, and a
`broadcast_recipient` flag. Actor identity is distinct from client and model:
Qwen and DeepSeek are separate actors even though both are transported by the
`qwen` client. Adding a reviewer is an edit to the registry, never a code
change. Inactive actors remain valid historical senders but never enter a new
broadcast audience.

The human partner is the actor `human`: may address any actor and may be
addressed directly (a `decision-query`, say), adjudicates semantic forks, is
never a broadcast recipient, and never owes an acknowledgement — the registry
marks it `acknowledges = false`, so messages addressed to `human` are reported
by `status --actor human` as `ADDRESSED`, never as pending, and no validation
ever expects a human acknowledgement (one may still be written). Each named actor is one accountable model session; hidden
subagents, teams, or swarms are not used unless the human partner expressly
authorizes them, and any authorized use is disclosed in the message.

## Scheduling: no predetermined order

Sessions do not poll. The human partner wakes a session, and that session
processes whatever is pending for its actor. **The protocol imposes no turn
order** — not round-robin, not hub-and-spoke, not "everyone answers before
anyone replies." A message is addressed to the audience the sender actually
needs; the human partner decides who is woken next, and may hand a question
first to whichever actor seems best placed to answer it so that the discussion
starts from the strongest premise. Nothing in the pending sets or
acknowledgements encodes or requires a sequence.

## Layout

Paths relative to the repository root:

```text
tools/review-exchange/            tracked control plane
  PROTOCOL.md  participants.toml  exchange.py  MESSAGE_TEMPLATE.md
  ACK_TEMPLATE.md  tests/

review/exchange/                  ignored spool
  messages/                       every published v2 message, stored once
  drafts/<actor>/                 unpublished messages of that actor
  acks/<actor>/                   acknowledgements authored by that actor
  inbox/codex/, inbox/fable/      immutable v1 history (read-only)
```

Each actor writes only its own draft and acknowledgement directories and
publishes only its own messages. No actor edits or moves another actor's files,
and published files are never edited.

**Actor binding.** Each launcher exports `SMUSNI_EXCHANGE_ACTOR=<slug>` before
starting a session. When it is set, `new`/`publish`/`ack` refuse any other
`--actor` (exit 3) and default to the bound actor when `--actor` is omitted.
This is an accidental-safety boundary — two actors share the `qwen` client —
not security against the shared account; leaving it unset is the human
driver's manual escape.

**Drafts are private.** Only the sender's own `status` reports problems in its
drafts, as `WARNING` lines; other actors' drafts may be half-written at any
moment and never block validation, publication, or acknowledgement.

## Messages

Filename and `id` are identical except for `.md`:
`YYYYMMDDTHHMMSSZ-<actor>-<short-slug>.md` (UTC; slug lowercase ASCII). The
header is simple `key: value` front matter, not general YAML:

```text
---
protocol: smusni-review-mail/v2
id: 20260825T120000Z-qwen-example
from: qwen
to: codex,fable,kimi,deepseek
audience: all
created_utc: 2026-08-25T12:00:00Z
kind: finding
model: qwen3.8-max-preview
client: qwen/0.22.0
ack_required: true
in_reply_to: none
supersedes: none
github_issues: #24,#25
---
```

- `to` is a comma-separated actor list. In a **draft** it may be `all`; at
  publication the helper expands `all` to the active broadcast recipients other
  than the sender and records `audience: all`. A published message therefore
  always names its recipients explicitly, so a later registry change never
  alters whom an already published message is pending for.
- A sender is never its own recipient. Direct and subset addressing are the
  same mechanism as broadcast; choose the audience the message needs.
- `ack_required: true` makes every recipient pending until its own
  acknowledgement exists; `false` publishes an immutable FYI that is never
  pending.
- `model` and `client` are required provenance on every message; the helper
  fills them from the registry unless overridden. Session identifiers are not
  recorded in messages.
- `kind` ∈ `request`, `response`, `finding`, `proposal`, `handoff`,
  `decision-query`. `in_reply_to` and `supersedes` each name one published
  message or `none`; branching discussion is normal and no linear thread is
  imposed.
- Body contract, unchanged from v1: **Context** (live files/sections, commit or
  dirty-tree boundary, issues), **Claims or findings** (separated from settled
  human-partner decisions), **Evidence** (exact lines, terms, countermodels,
  source excerpts, commands), **Questions or objections** (bounded), and
  **Requested disposition** (a gate, not "review this"). Keep quotation
  minimal; cite prior message IDs. Never place secrets in the spool.

## Publication and immutability

Compose with `exchange.py new`, edit the draft, then `exchange.py publish`.
The helper validates the draft and the published spool, materializes the
audience, writes and fsyncs a temporary file, validates that final content
under its final name, and only then links it into `messages/` atomically; a
lost race on the same id fails with a collision code rather than overwriting,
and nothing invalid ever crosses the boundary. A body that is empty or still
the template is refused. `new` reserves the final draft name exclusively with
an empty file (retrying on a same-second collision) and then fills it by
renaming a per-process temporary file over it; the momentarily empty draft is
harmless because drafts are private and never spool errors. Acknowledgements
and published messages are written through per-process temporary files and
linked exclusively, so no final name in `acks/` or `messages/` is ever
observable in a partial state. Appearance
in `messages/` is the observable publication boundary. A correction is a new
message with `supersedes`; a reply is a new message with `in_reply_to`. Files
ending in `.tmp` are invisible to validation.

## Acknowledgements

`exchange.py ack --actor <a> <id> --disposition '…'` writes a temporary file
and links it exclusively as `acks/<a>/<id>.ack.md`. Only a recipient may acknowledge, once.
Acknowledgement means **read and disposition captured** — in a reply, a GitHub
issue or comment, or a short explicit explanation — never "agreed" and never
"queued work completed." A message may be acknowledged with a concise
no-objection disposition. Do not acknowledge a request whose required response
or durable issue update was silently skipped.

## Discussion discipline

- No vote, quorum, majority, silence, or acknowledgement count ever becomes
  consensus. Convergence is recorded by naming reviewers and their exact
  positions; a genuine semantic fork is adjudicated by the human partner.
- When a docket goes to several reviewers, name them and name **one** durable
  recorder who promotes the outcome to GitHub; others do not race to edit the
  same issue.
- Read what is pending for you, its reply ancestors, and what you are
  explicitly pointed at — not the whole historical spool.
- The spool is coordination, not authority. Actionable work goes to a GitHub
  issue in the same turn; a proposed semantic change stays in review until the
  human partner authorizes it.
- Implementation assignments use separate worktrees/branches; a review names
  the exact commit under review.

## Commands

Run from the repository root:

```sh
python3 tools/review-exchange/exchange.py status --actor <actor>   # start and end of a turn
python3 tools/review-exchange/exchange.py new --actor <actor> --to all|a,b --kind <kind> \
    --slug <slug> [--issues '#1,#2'] [--reply-to <id>] [--supersedes <id>] [--no-ack]
python3 tools/review-exchange/exchange.py publish --actor <actor> <draft>
python3 tools/review-exchange/exchange.py ack --actor <actor> <id> --disposition '…'
python3 tools/review-exchange/exchange.py validate
python3 -m unittest discover -s tools/review-exchange/tests
SMUSNI_EXCHANGE_ACTOR=<actor> python3 -m unittest discover -s tools/review-exchange/tests
```

Run the suite both unbound and bound (the second form, as a launched tab would
run it); both must pass.

Exit codes: 0 ok · 1 usage · 2 validation · 3 ownership/permission ·
4 collision/duplicate · 5 unknown reference.
[`review/exchange_check.py`](../../review/exchange_check.py)` <actor>`
remains as a thin compatibility wrapper around `status`; it lives in the
ignored `review/` directory on purpose (it exists only so sessions started
under the v1 charter keep seeing traffic until they reload), while everything
that defines behaviour is tracked here.

## v1 history

Messages under `review/exchange/inbox/<actor>/` and their acknowledgements are
the immutable v1 record. The helper validates them read-only, counts their
unacknowledged messages as pending for their recipient, and refuses to publish
new v1 messages. The v1 sender alias `owner` is accepted only in that history.
