# Launching a reviewer session

Paths below are relative to the repository root; commands are run from there.
See [`PROTOCOL.md`](PROTOCOL.md) for the exchange rules and
[`participants.toml`](participants.toml) for the actor slugs.

Each mailbox actor is one accountable model session that the human partner
wakes. The clients below were checked on 2026-08-25 (`kimi` 0.38.0,
`qwen` 0.22.0). Nothing here is protocol state; session ids may be kept in an
ignored note such as `review/exchange/sessions.txt` — only needed if a tab has
to be resumed.

## Before the first launch

- The working tree must contain the current [`AGENTS.md`](../../AGENTS.md)
  and this directory (commit or at least keep them checked out); the clients
  read the charter from the working tree at startup.
- Do not run reviewers with blanket auto-approval (`kimi -y`, Qwen YOLO
  modes). Approve the helper ([`exchange.py`](exchange.py), invoked as
  `python3 tools/review-exchange/exchange.py …` from the repository root)
  and read-only repository tools; deny tracked-file edits unless the session
  is an assigned implementer in its own worktree.

## Normal operation: one interactive tab per actor

Run each actor as a persistent interactive session in its own terminal tab and
switch between tabs to give turns; that is the whole scheduler. Starting the
tabs:

```sh
cd ~/git/smusni
SMUSNI_EXCHANGE_ACTOR=kimi     kimi -m kimi-code/k3                             # Kimi K3
SMUSNI_EXCHANGE_ACTOR=qwen     qwen -m qwen3.8-max-preview -i "<first prompt>"  # Qwen 3.8 Max
SMUSNI_EXCHANGE_ACTOR=deepseek qwen -m deepseek-v4-pro   -i "<first prompt>"  # DeepSeek V4 Pro
```

The environment variable binds the tab to its actor: the helper then refuses
any other `--actor`, which is what prevents the two Qwen-backed tabs from
writing as each other by accident. Export it for the Codex and Fable tabs too.

Paste the first prompt below into each tab.

## If a tab dies: resume the exact session

```sh
kimi -S            # picker; or kimi -m kimi-code/k3 -S <id>
qwen sessions list # then: qwen -m qwen3.8-max-preview -r <id>
                   #       qwen -m deepseek-v4-pro   -r <id>
```

Never use `-c`/`--continue` for Qwen or DeepSeek: they share one cwd-scoped
history, so `--continue` resumes whichever of the two ran most recently.
(Non-interactive use exists — `kimi … -p … --output-format stream-json`,
`qwen … -p … -o json` — but is not needed for tab-based operation.)

## First prompt (replace ACTOR and the docket)

The prompt is text for a session started in the repository root, so its paths
are root-relative on purpose.

> You are the review-exchange actor `ACTOR` (see
> `tools/review-exchange/participants.toml`). Read `AGENTS.md` in full — it is
> the project charter — and `tools/review-exchange/PROTOCOL.md`. Confirm in
> one line which protocol version the exchange uses and which actor slug you
> are. Then run `python3 tools/review-exchange/exchange.py status --actor ACTOR`,
> read every pending message and its reply ancestors, and respond through the
> helper (`new` → edit the draft → `publish`; `ack` after your disposition is
> captured). Your docket this turn: DOCKET. Do not edit tracked files; do not
> use subagents; cite live file paths and sources you have actually read.

The one-line confirmation is the charter-discovery check: a session that
cannot name the protocol version and its slug did not load `AGENTS.md`.

## Every later prompt

> Your turn as `ACTOR`: run `exchange.py status --actor ACTOR`, process what is
> pending, reply and acknowledge through the helper. [Optional: the question or
> docket this turn.]

## First round trip (pilot)

Send each new actor one non-normative message (direct or `all`), wake it, and
confirm with `exchange.py status --actor <actor>` that it went from pending to
acknowledged with a published reply, and that `exchange.py validate` is clean.
Only then hand it a semantic docket, naming the reviewers and one durable
recorder.
