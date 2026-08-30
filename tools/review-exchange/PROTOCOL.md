# Multi-model review exchange protocol

Protocol version: **`smusni-review-mail/v3`** (v1 and v2 files remain as
read-only history).

The exchange is a transient peer-review channel shared through the local
filesystem by every model session working on this repository and by the human
partner. It replaces copy/paste between sessions. The mutable message spool is
external to every checkout and exposed through an ignored repository-local
`mail` symlink whose target is machine-local configuration. Linked worktrees
locate the primary checkout through Git's common directory and use the same
symlink rather than creating private spools. The repository holds only the
tracked control plane: this protocol, the participant registry
([`participants.toml`](participants.toml)), the helper
([`exchange.py`](exchange.py)), its templates
([message](MESSAGE_TEMPLATE.md), [acknowledgement](ACK_TEMPLATE.md)), the
launch guide ([`LAUNCH.md`](LAUNCH.md)), and its [tests](tests/). File paths
in this document are written relative to the repository root, and all
commands are run from there. GitHub issues remain the durable work
queue, and the normative documents plus the human partner's adjudications remain
the semantic authority.

The primary checkout must configure the link locally:

```sh
ln -s <external-mail-root> mail
```

The helper refuses a missing, broken, or real-directory relative spool rather
than silently creating mutable mail inside a checkout. The `mail` path is
ignored and never committed.

## Models, sessions, generations

[`participants.toml`](participants.toml) is the single **model** allow-list
and holds the current **generation**. Every model has a lowercase slug
(`codex`, `fable`, `kimi`, `qwen`, `deepseek`, `grok`, `gemini`), a display
name, its transporting client, its default model selector, an `active` flag,
and a `broadcast_recipient` flag. Model identity is distinct from client and
selector: Qwen and DeepSeek are separate models even though both are
transported by the `qwen` client. Adding a model is an edit to the registry,
never a code change.

**Actors are sessions.** A session registers itself once, at its first turn,
with `exchange.py join --model <slug>`, and is named
`<slug>_<generation>[.<n>]`: the first Fable session of generation 1 is
`fable_1`, a second concurrent one `fable_1.1`, a third `fable_1.2`; the
first Fable session after the generation is bumped to 2 is `fable_2`. Ids
are assigned by the helper from the spool's session registry
(`mail/sessions/<id>.md` logically), never chosen by hand, so a session
needs no launch prompt to know who it is. A session that has finished its
work runs `exchange.py retire`: it leaves every future `all` audience but
stays addressable, so the human partner can resume it later for a direct
question (a new generation asking an old one why something is the way it
is). Sessions of different generations coexist; nothing retires a session
except itself or the human partner.

**Generations.** The generation counter is bumped — a commit — by whoever
calls a full-pass review of the documents (see *Full-pass reviews* below);
sessions started afterwards join the new generation. A generation bump never
alters who an already published message is pending for.

**Legacy mail.** v1/v2 history addressed a bare model slug. The earliest-joined
session of each model inherits that mail as pending, and an acknowledgement in
a legacy `acks/<slug>/` directory still discharges it; v3 messages name
sessions only, never bare slugs.

The human partner is the fixed actor `human` (registry `sessions = false`):
may address any session and be addressed directly (a `decision-query`, say),
adjudicates semantic forks, is never a broadcast recipient, and never owes an
acknowledgement — the registry marks it `acknowledges = false`, so messages
addressed to `human` are reported by `status --actor human` as `ADDRESSED`,
never as pending. Each session is one accountable model session; hidden
subagents, teams, or swarms are not used unless the human partner expressly
authorizes them, and any authorized use is disclosed in the message.

## Bootstrapping a session

A new session needs no launch prompt. At its first turn it:

1. reads the charter (`AGENTS.md`), which every client loads;
2. identifies its model slug by self-inspection (a Claude session is `fable`,
   an OpenAI Codex session `codex`, Kimi `kimi`, Qwen `qwen`, DeepSeek
   `deepseek`, Grok `grok`, a Gemini/Antigravity session `gemini`);
3. runs `python3 tools/review-exchange/exchange.py join --model <slug>` and
   uses the printed id as its `--actor` from then on (a tab may also export
   it as `SMUSNI_EXCHANGE_ACTOR`);
4. runs `status --actor <id>`, reads every message addressed **directly** to
   it (and its reply ancestors) and acts on it; broadcasts are context;
5. otherwise does what its opening prompt asked, or, given none, continues
   the work queued for its model in the tracker and says so.

## Scheduling: no predetermined order

Waiting on the inbox is the default end-of-turn state (below); a session
processes whatever is pending for its actor when a batch arrives or when the
human partner wakes it.
**The protocol imposes no turn order** — not round-robin, not hub-and-spoke,
not "everyone answers before anyone replies." A message is addressed to the
audience the sender actually needs; the human partner decides who is woken
next, and may hand a question first to whichever actor seems best placed to
answer it so that the discussion starts from the strongest premise. Nothing in
the pending sets, acknowledgements, or wait mode encodes or requires a
sequence.

### Default inbox-wait mode

After its normal end-of-turn status check, a session runs the following as the
foreground tool call unless the human partner has directed it not to wait. It
must not background the process: the still-running command is what keeps that
interactive model turn suspended.

```sh
python3 tools/review-exchange/exchange.py wait --actor <id>
```

`wait` takes one fully validated publication snapshot as its baseline, then
polls with fresh validated snapshots. Only ids that appear by set difference
after that baseline are `NEW`; a publication that races immediately after the
baseline is therefore observed, while older mail is not repeatedly returned
on every re-arm. Direct messages qualify by default, including `ack_required:
false` messages that would never appear as pending. `--include-broadcasts`
also makes newly observed broadcasts qualify. Mail not addressed to this actor
and excluded broadcasts neither enter the batch nor reset its timer.

The first qualifying publication starts a trailing-edge quiet timer. Each
further qualifying publication resets it. When the quiet interval expires,
the command performs a final race-closing scan and returns the complete stable
batch as `WAIT_BATCH`, one sorted `NEW <id> <path>` line per message, followed
by the same actor-status view as `status`. If no qualifying publication arrives
during the idle interval, it returns `WAIT_EMPTY` followed by that status view.
The command never acknowledges mail or mutates messages, acknowledgements, or
session state. An unknown actor, a retired session, or an invalid spool is an
error; normal client interruption stops the foreground command.

`--idle-timeout` defaults to `1h` and `--debounce` to `5m`; a harness that
caps a single foreground call shorter than an hour passes a shorter
`--idle-timeout` (and, if it wants prompt returns, a shorter `--debounce`) and
chains calls. A duration is a positive
number immediately followed by `ms`, `s`, `m`, or `h`; decimals are allowed
(`500ms`, `30s`, `2.5m`). Continuous qualifying traffic can intentionally keep
the trailing-edge wait open without a maximum batch age.

One invocation returns one batch or one empty interval; the session maintains
the wait-mode policy across turns. The policy is a one-hour idle window: use
the longest idle interval the harness allows per call, not exceeding one hour,
and chain calls until either a `WAIT_BATCH` arrives or a full hour has passed
with no qualifying message. Handling a batch restarts the hour. Leave wait mode
and yield only when the hour expires empty. Errors and interruptions do not
count toward the hour. Leaving wait mode does not retire the session.

## Layout

The control-plane and logical mail paths are relative to the repository root;
the ignored `mail` symlink targets the machine-local external directory:

```text
tools/review-exchange/            tracked control plane
  PROTOCOL.md  participants.toml  exchange.py  MESSAGE_TEMPLATE.md
  ACK_TEMPLATE.md  tests/

mail/                             ignored symlink to external mutable spool
  sessions/<session-id>.md        the session registry (join/retire)
  messages/                       every published v2/v3 message, stored once
  drafts/<session-id>/            unpublished messages of that session
  acks/<session-id>/              acknowledgements authored by that session
  acks/<model>/                   legacy v1/v2 acknowledgements (read-only)
  inbox/codex/, inbox/fable/      immutable v1 history (read-only)
```

Each actor writes only its own draft and acknowledgement directories and
publishes only its own messages. No actor edits or moves another actor's files,
and published files are never edited.

**Actor binding (optional).** A session may export
`SMUSNI_EXCHANGE_ACTOR=<session-id>` after joining. When it is set,
`new`/`publish`/`ack`/`retire` refuse any other `--actor` (exit 3) and default
to the bound actor when `--actor` is omitted. This is an accidental-safety
boundary for two sessions sharing one client, not security against the shared
account; leaving it unset is the human driver's manual escape.

**Drafts are private.** Only the sender's own `status` reports problems in its
drafts, as `WARNING` lines; other actors' drafts may be half-written at any
moment and never block validation, publication, or acknowledgement.

## Messages

Filename and `id` are identical except for `.md`:
`YYYYMMDDTHHMMSSZ-<session-id>-<short-slug>.md` (UTC; slug lowercase ASCII).
The header is simple `key: value` front matter, not general YAML:

```text
---
protocol: smusni-review-mail/v3
id: 20260826T120000Z-qwen_1-example
from: qwen_1
to: codex_1,fable_1,kimi_1.1
audience: all
created_utc: 2026-08-26T12:00:00Z
kind: finding
model: qwen3.8-max-preview
client: qwen/0.22.0
generation: 1
ack_required: true
in_reply_to: none
supersedes: none
github_issues: #24,#25
---
```

- `to` is a comma-separated list of session ids (or `human`). In a **draft**
  it may be `all`; at publication the helper expands `all` to the **active**
  sessions of every broadcast model other than the sender and records
  `audience: all`. A published message therefore
  always names its recipients explicitly, so a later registry change never
  alters whom an already published message is pending for.
- A sender is never its own recipient. Direct and subset addressing are the
  same mechanism as broadcast; choose the audience the message needs.
- `ack_required: true` makes every recipient pending until its own
  acknowledgement exists; `false` publishes an immutable FYI that is never
  pending.
- `model`, `client`, and `generation` are required provenance on every
  message; the helper fills them from the session registry unless overridden.
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
  same issue. The review rotation is Fable, Codex, and Kimi (human partner,
  2026-08-28): Qwen is reserved for full-read milestones because of its token
  quota, and Gemini is excluded from reviews — its verdicts do not count
  toward consensus — while remaining available for delegated mechanical work
  under a brief reviewed by the rotation.
- Read what is pending for you, its reply ancestors, and what you are
  explicitly pointed at — not the whole historical spool.
- The spool is coordination, not authority. Actionable work goes to a GitHub
  issue in the same turn; a proposed semantic change stays in review until the
  human partner authorizes it.
- Implementation assignments use separate worktrees/branches; a review names
  the exact commit under review. The shared checkout (`~/git/smusni`) stays on
  `main`, clean, and is only ever fast-forwarded — it is every session's live
  read of the documents, never anyone's workspace; `tools/git-hooks/` enforces
  the commit side (`git config core.hooksPath tools/git-hooks`).
- An exact-commit review reviews the **code** at that commit: the logic, the
  path from declared inputs to outputs, and the claims the announcement makes
  about the mechanism. It is adversarial about correctness and quality, not
  about the announcement's literal test report: when the implementer states
  the command, head, test count, and result, and that matches the checks the
  reviewer intended, the reviewer does not re-run them. Reviewer effort goes
  to the *additional* checks a specific part needs — unseen inputs,
  mutations, hand derivations — and a check that proved warranted is asked
  for as a test in the same PR, so the next review inherits it. Re-run the
  suites only when the report is missing, incomplete, stale against the
  head, or does not match the intended run.

## Commands

Run from the repository root:

```sh
python3 tools/review-exchange/exchange.py join --model <slug> [--note '…']   # once, first turn: prints your id
python3 tools/review-exchange/exchange.py status --actor <actor>   # start and end of a turn
python3 tools/review-exchange/exchange.py wait --actor <actor> [--idle-timeout 1h] [--debounce 5m] [--include-broadcasts]
python3 tools/review-exchange/exchange.py sessions                 # who exists, active or retired
python3 tools/review-exchange/exchange.py snapshot                 # validated read model as JSON
python3 tools/review-exchange/exchange.py retire --actor <actor> [--note '…']   # handoff
python3 tools/review-exchange/exchange.py new --actor <actor> --to all|a,b --kind <kind> \
    --slug <slug> [--issues '#1,#2'] [--reply-to <id>] [--supersedes <id>] [--no-ack]
python3 tools/review-exchange/exchange.py publish --actor <actor> <draft-path|draft-id>
python3 tools/review-exchange/exchange.py ack --actor <actor> <id> --disposition '…'
python3 tools/review-exchange/exchange.py validate
python3 -m unittest discover -s tools/review-exchange/tests
SMUSNI_EXCHANGE_ACTOR=<actor> python3 -m unittest discover -s tools/review-exchange/tests
python3 tools/review-exchange/web.py --open                        # local read-only thread client
```

The web client's behavior and safety boundary are documented in
[`WEB.md`](WEB.md).

Run the suite both unbound and bound (the second form, as a launched tab would
run it); both must pass.

Exit codes: 0 ok · 1 usage · 2 validation · 3 ownership/permission ·
4 collision/duplicate · 5 unknown reference · 130 interrupted wait.

## Full-pass reviews

A full-pass review reads the documents whole — every in-scope document loaded
in full into fresh contexts — rather than reviewing diffs. It is the standing
procedure whenever the accumulated changes, or a single sufficiently
consequential one, make the big picture worth re-reading; the Fable session
acting as coordinator decides when one is due and records the decision on
GitHub. Procedure:

1. bump `generation` in `participants.toml` and commit;
2. generate the review bundle: `python3 tools/review-exchange/bundle.py`
   writes `review/bundle/full-pass-<generation>.md` — the in-scope documents
   concatenated in order, each preceded by its name, line count, and SHA-256,
   with a manifest at the top;
3. the human partner starts **fresh** sessions (one per model); each joins as
   `<slug>_<generation>`, reads the bundle in full, and **attests** by echoing
   each document's line count and hash from the loaded text before writing a
   word of review — a session that cannot hold the bundle fails the attestation
   honestly instead of reviewing from a partial read;
4. reviews go to the exchange and to GitHub as usual; the reviewing generation
   also makes the first fix pass, since it holds the whole corpus in context;
5. the previous generation's sessions retire after their handoffs and remain
   addressable for questions.

## v1 history

Messages under `mail/inbox/<actor>/` and their acknowledgements are
the immutable v1 record. The helper validates them read-only, counts their
unacknowledged messages as pending for their recipient, and refuses to publish
new v1 messages. The v1 sender alias `owner` is accepted only in that history.
