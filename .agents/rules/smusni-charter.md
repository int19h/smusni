---
trigger: always_on
description: smusni project charter and review-exchange identity for the Gemini (Antigravity) session
---

# smusni: charter and actor identity for this workspace

This workspace is the Lojban semantic-core project. Its complete charter is
the repository file `AGENTS.md` at the workspace root: @../../AGENTS.md

Antigravity does not load `AGENTS.md` on its own. **At the start of every
session, read `AGENTS.md` in full from the workspace root and follow it**;
the summary below never replaces it.

## Your identity in the multi-model review exchange

- Your model slug is **`gemini`**. At your first turn, register:
  `python3 tools/review-exchange/exchange.py join --model gemini` prints
  your session id (`gemini_1`, `gemini_1.1`, …); use it as `--actor` from
  then on. Registry: `tools/review-exchange/participants.toml`; protocol:
  `tools/review-exchange/PROTOCOL.md` — read it before your first exchange
  command. Actor identity (a session) is distinct from client and model.
- Every helper call names your session and binds the shell to it, since an
  Antigravity terminal does not keep an exported variable between commands:
  `SMUSNI_EXCHANGE_ACTOR=<id> python3 tools/review-exchange/exchange.py <command> --actor <id> …`
- At the start and end of every substantive turn run `status --actor <id>`,
  read every pending message and its reply ancestors (act on the ones
  addressed directly to you; broadcasts are context), and run
  `python3 tools/review-exchange/exchange.py validate` before announcing the
  mailbox clear. Compose with `new`, publish with `publish`, acknowledge
  with `ack --disposition "…"`; never hand-write timestamps or move files;
  never edit another session's files; published messages are immutable.
- You are one accountable model session. Do not use hidden subagents,
  background agents, or parallel agent trajectories for exchange work
  unless the human partner has expressly authorized it, and disclose any
  authorized use in the message.

## Non-negotiables (from the charter — read the charter for the rest)

- The human partner's adjudications are final; record their durable
  consequence in the GitHub issue, not only in the mailbox.
- Every concrete item of work has a GitHub issue before it is treated as
  queued; `review/` is ignored and never the sole copy of anything actionable.
- Cite live file paths and line numbers, source excerpts, commit SHAs, and
  issue numbers; verify sources rather than citation-following; separate
  claims, evidence, objections/questions, and requested disposition.
- Executable artifacts (`tools/smusni-redex/`) test the documents; they
  never become semantic authority. Do not apply a proposed semantic change
  to the baseline without human-partner authorization.
- Preserve unrelated worktree changes; restrict edits to the requested
  scope; run `python3 review/checks.py` after documentation edits.

## Tooling notes

- Lojban sources: `jbotci cukta` (Contemporary CLL), `jbotci vlacku`
  (dictionary), `jbotci gentufa` (parser); local archives under
  `~/lojban/wiki` and `~/lojban/disc` (local copies; never the `~/git/`
  virtiofs originals); search with `rg`.
- Checker: `tools/check-smusni` (and `--strict`) from the repository root.
