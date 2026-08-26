# Launching a session

Sessions bootstrap themselves from the charter; there is no launch prompt to
paste. Start the client in the repository root and give the session whatever
task you have — or nothing. See [`PROTOCOL.md`](PROTOCOL.md) for the session
model (`<slug>_<generation>[.<n>]`), generations, and full-pass reviews.

## What a fresh session does on its own

1. Reads `AGENTS.md` (the client loads it; Antigravity through the workspace
   rule `.agents/rules/smusni-charter.md`).
2. Identifies its model slug and runs
   `python3 tools/review-exchange/exchange.py join --model <slug>`; the printed
   id (`fable_1`, `codex_1.1`, …) is its actor from then on.
3. Runs `status --actor <id>`, reads what is addressed directly to it, and acts
   on that; otherwise acts on your opening prompt; otherwise continues the
   work queued for its model in the tracker.

## Per client

- **Terminal tabs (Claude Code, Codex, Kimi, Qwen, DeepSeek):** one tab per
  session; after joining, a tab may `export SMUSNI_EXCHANGE_ACTOR=<id>` so
  the helper refuses any other actor. Resume a tab with the client's own
  resume/continue command; never `--continue` for the two Qwen-transported
  models (it would resume the wrong model's transcript).
- **Antigravity (Gemini):** open the repository root as the workspace; the
  always-on rule loads the charter pointer. Antigravity terminals do not keep
  an exported variable between commands, so spell the actor on every helper
  call: `SMUSNI_EXCHANGE_ACTOR=<id> python3 tools/review-exchange/exchange.py … --actor <id>`.

## Several sessions of one model

`join` hands out `fable_1`, then `fable_1.1`, `fable_1.2`, … in the current
generation. Use extra sessions for work that benefits from a clean context;
they are peers, not subagents, and each is accountable for its own messages.

## Handing off and retiring

A session that is done runs `exchange.py retire --actor <id> --note '…'`
after leaving an addressed handoff. Retired sessions drop out of `all` but
stay addressable: resume the client session and it can answer a direct
message from a later generation.

## Full-pass review

Bump `generation` in `participants.toml` (commit), run
`python3 tools/review-exchange/bundle.py`, then start fresh sessions — one per
model — whose first instruction is: *read `review/bundle/full-pass-<generation>.md`
in full and attest by echoing each document's line count and SHA-256 from the
loaded text before reviewing*. The rest follows `PROTOCOL.md`.
