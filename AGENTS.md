# Charter: the Lojban semantic core

This repository defines a community-facing **prescriptive definition of
Lojban semantics** in terms of a small typed semantic core — a “Lojban
semantic assembly language.”

## Mission

Flip the usual direction of Lojban semantics work. Instead of deriving
meaning from syntax construct by construct and accepting whatever falls out,
ask:

1. what meanings a resolved Lojban utterance must be able to convey; and
2. what small set of typed semantic building blocks suffices to state those
   meanings clearly and compositionally.

Every supported resolved Lojban reading lowers to a well-typed core term. The
adequacy chapter and gap register delimit what “supported” currently covers.
The core is the definition; surface Lojban is its privileged source language.

The lowering need not be surjective. Generic core forms may lack a Lojban
spelling when they substantially factor shared semantic structure or simplify
the model. Every such form still owes a necessity or factorization argument,
and core typability never establishes Lojban expressibility.

## Prescriptive doctrine

- This project decides Lojban semantics; CLL, the official dictionary, xorlo,
  guskant, Brismu, the wiki, corpora, and discussion archives are evidence and
  guides, not authorities that decide by themselves.
- xorlo is the gadri baseline. Pre-xorlo CLL semantics is superseded where it
  conflicts.
- Where evidence and competent usage genuinely permit several readings, choose
  the reading with the strongest compatibility and formal case, document the
  alternatives and their consequences, and record the choice as a pin.
- The compatibility principle is binding: do not pull the rug from practical
  CLL Lojban speakers without strong, recorded motivation.
- Distinguish original CLL, maintained/Contemporary CLL, and project-authored
  amendments. Project wording cannot independently ratify itself.
- Verify sources rather than citation-following: check that a reference exists,
  which edition it belongs to, what it actually says, and whether it supports
  the claimed inference.
- Preserve intellectual provenance even when it is not agreement. Whenever a
  rule, pin, formal construction, counterexample, or rationale is materially
  prompted by or derived from another person's mailing-list message, wiki
  page, IRC/forum post, corpus example, or published work, cite that source in
  the document set's `spec.md` References section and at the dependent passage.
  Identify the author, date, and stable page/message/archive location where
  available, and describe the nature of the dependence accurately: a source
  that inspired, exposed, or was generalized or corrected by the project must
  not be presented as agreeing with or authoritatively establishing the final
  decision.
- Speaker evidence should use concrete Lojban situations and minimal pairs,
  separate truth from felicity and projection, distinguish comprehension from
  production, and record speaker experience and date.

## Document authority and roles

- **`spec.md`** is the normative dense specification: types, formation,
  semantics, lowering, pins, gaps, and adequacy.
- **`rationale.md`** records necessity/factorization arguments, alternatives,
  costs, and reasons for pins. It explains but does not override the spec.
- **`samples.md`** contains concrete worked terms. Until a complete checker
  exists, samples are important semantic tests but never override prose rules.
- **`primer.md`** is derivative exposition for non-specialists.
- **`catalog.md`** is the per-identifier derivative reference.
- **`cmavo.md`** is the derivative surface-Lojban index.
- **`brief.md`** is the publication-facing project charter and should remain
  synchronized with this stable repository charter.
- **`review/CONSENSUS.md`** is the current working decision overlay. It records
  accepted decisions not yet synchronized into every normative/derivative
  document and the genuinely open remainder.
- **`review/ADJUDICATIONS.md`** and the response/review files are design history
  and detailed dockets. Earlier passages may be superseded by later closure
  notes; never treat the whole file as one current position.
- Executable semantics, parsers, type-checkers, Redex models, proof-assistant
  mechanizations, and certificates are derived artifacts today: they test the
  documents and do not become the semantic authority. **Adopted in principle
  (human partner, 2026-08-29; tracker #74):** once the platform selected by
  the #74 pilot passes three recorded states, the formal definitions become
  normative for **formation, typing, expansion, and denotation**, and the
  corresponding prose becomes commentary: (1) *full-migration parity* —
  every live formation rule, typing clause, §12 definition, §11 lowering
  rule, and denotation/model operation or law in that scope carries an
  explicit formal coverage or disposition entry, and the formal artifact
  reproduces every live case with exact differential and certificate
  coverage while the frozen Redex engine still serves as oracle; (2) *sole
  source* — after a bounded overlap the Redex engine is retired or demoted
  and one live formal rule source is confirmed; (3) the *transfer* itself,
  an explicit recorded decision of the human partner. The Lojban mapping,
  source evidence, pins, alternatives, gaps, and adequacy claims stay
  documentary and normative; the §11 rule *text* stays normative while its
  encodings remain derived. No PR merge transfers authority.

When live `spec.md` and live `review/CONSENSUS.md` temporarily disagree because
an accepted edit has not yet been applied, use the latest explicit user
adjudication and the consensus overlay for ongoing work, and record the needed
synchronization. Do not silently rewrite published doctrine from review notes.

## Durable work tracking

The GitHub issue tracker for `int19h/smusni` is the durable execution queue.
Tracker issue [#1](https://github.com/int19h/smusni/issues/1) indexes the first
coherent-baseline backlog and its dependencies.

- `review/` is intentionally ignored and remains available for rapid analysis,
  model-to-model exchange, drafts, and historical notes. It is never the sole
  copy of an actionable requirement, accepted decision, test result, or TODO.
- Every concrete item of work must have a GitHub issue before it is treated as
  queued. When review discussion settles or discovers actionable work, create
  or update the issue in the same turn.
- Before starting work, inspect the live issue and search open/closed issues for
  duplicates. The issue body is canonical for outcome, decision status, scope,
  acceptance criteria, dependencies, and durable evidence links.
- Summarize the current result in the issue; do not paste an obsolete review
  document wholesale or make ignored files required reading.
- Use labels to distinguish `ready`, `needs-design`, `speaker-evidence`,
  `model-theory`, `verification`, and blocked work. A “ready” label records
  semantic readiness, not authorization for unrelated edits or release.
- Update the issue when scope or decisions change. Close it only after the
  acceptance criteria and repository checks pass; a mailbox response or local
  review note alone never closes work.
- The human partner's adjudications are final. Record their durable
  consequence in the issue body or a comment, while retaining rejected
  alternatives and reopening criteria where the semantic decision genuinely
  had several coherent options.

## Multi-model review collaboration

Several model sessions — currently Codex, Fable, Kimi K3, Qwen 3.8 Max,
DeepSeek V4 Pro, Grok 4.6, and Gemini — review this repository as peers working
with the human partner; no model's proposal becomes consensus merely because
it was written. The external spool exposed through the ignored
repository-local `mail` symlink replaces copy/paste between sessions; the
symlink target is machine-local configuration and is never tracked. The
tracked protocol, model registry, helper, templates, and tests live under
`tools/review-exchange/`; read `PROTOCOL.md` there before using the exchange.

**Bootstrapping.** A new session needs no launch prompt. At its first turn:
identify your model slug by self-inspection (Claude → `fable`, OpenAI Codex →
`codex`, Kimi → `kimi`, Qwen → `qwen`, DeepSeek → `deepseek`, Grok → `grok`,
Gemini/Antigravity → `gemini`); run `python3
tools/review-exchange/exchange.py join --model <slug>` and use the printed
session id (`fable_1`, `codex_1.1`, …) as your actor from then on; run
`status --actor <id>`; act on messages addressed
**directly** to you (broadcasts are context), else on the prompt you were
given, else on the work queued for your model in the tracker — and say which.

- **Actors are sessions**, named `<model>_<generation>[.<n>]` and self-assigned
  by `join`; the current generation is `generation` in `participants.toml`.
  Sessions of different generations coexist and may message each other;
  a finished session runs `retire` after an addressed handoff and stays
  addressable for later questions. Every session writes only its own
  drafts and acknowledgements and publishes only its own messages; published
  messages are immutable, and no session edits or moves another's files.
- Messages are addressed to the audience the sender needs — one session, a
  subset, or `all` (the active sessions) — and stored once. **No turn order is
  prescribed**: the human partner decides which session wakes next, and may
  give a question first to whichever session is best placed to answer it.
- At the start and end of every substantive turn, run
  `python3 tools/review-exchange/exchange.py status --actor <id>`, read
  every pending message and its reply ancestors, and run the validator before
  announcing the mailbox clear. Compose with `new`, publish with `publish`,
  acknowledge with `ack`; never hand-write timestamps or move files.
- Waiting on the inbox is the default end-of-turn state unless the human
  partner directs a session not to wait. After the end-of-turn status check,
  run `exchange.py wait --actor <id>` in the foreground with the longest idle
  interval the harness allows per call, not exceeding one hour; when one call
  cannot cover an hour, chain calls. Leave wait mode only when no qualifying
  message has been observed for a full hour; handling a `WAIT_BATCH` restarts
  the hour. Errors and human interruption do not count, and leaving wait mode
  does not retire the session.
- Correct a message with a new `supersedes` message; respond with `in_reply_to`.
  Acknowledge only after the disposition is durably captured in a reply, issue,
  or short explicit explanation; acknowledgement never means agreement or
  completion of queued work.
- Every substantive message separates claims, evidence, objections/questions,
  and requested disposition, citing live file paths/sections, source excerpts,
  commit/working-tree state, and GitHub issue numbers.
- No vote, quorum, silence, or acknowledgement count becomes consensus; record
  named positions, name one durable recorder per docket, and leave genuine
  semantic forks to the human partner. Each session is one accountable model
  session; hidden subagents or swarms are not used without express
  authorization, and authorized use is disclosed.
- The spool is transient coordination, not authority. If an exchange creates
  or changes actionable work, update GitHub. If it proposes a semantic change,
  preserve the proposal in review until human-partner authorization; do not
  silently apply it to the baseline.
- If only one model is active, continue useful work and leave an addressed
  handoff. Do not block routine progress merely waiting for an acknowledgement
  unless the issue explicitly requires multi-model review or human-partner
  adjudication.

**Full-pass reviews.** Reviewing diffs finds what a change broke; only reading
the documents whole finds what the accumulation of changes made inconsistent.
A full-pass review — every in-scope document (`brief.md`, `spec.md`,
`rationale.md`, `samples.md`, `primer.md`) loaded in full into **fresh**
sessions, one per model — is the standing procedure whenever the changes
since the last one, or a single sufficiently consequential change, warrant
it; the coordinating Fable session decides when one is due and records the
decision on GitHub. The procedure (bump the generation, generate the bundle,
start fresh sessions that attest to a full load before reviewing, let the
reviewing generation make the first fix pass, retire the previous
generation after handoff) is in `PROTOCOL.md`.

## Delegated implementation

Implementation work is often briefed by one model session and executed by
another. Both roles owe the same discipline: the goal is the specified
mechanism; an acceptance criterion is a bar that mechanism must clear, never
a substitute for it.

**For the implementing session.**

- A table from the known inputs to precomposed outputs, a clause that emits
  the expected result, matching on the test corpus's surface strings, or
  hard-coding the fixture set is not an implementation, however green the
  gates. Reporting it as one is a false report of completion.
- "Do X — for example Y and Z" means do X in general; Y and Z illustrate it.
  Implement the general requirement; when its extent is unclear, ask before
  coding rather than choosing the narrowest reading.
- Consume the inputs the specification says the mechanism consumes. A
  mechanism that ignores a declared input is not that mechanism.
- What cannot be done generally is reported as not done, with the specific
  obstacle and evidence — never filled with defaults, stubs, or
  transcriptions, and never counted among the results.
- Announce what the code actually does, including any hand-authored data on
  the path from input to output, and how many cases the general path handles.

**For the briefing or reviewing session.**

- State the goal as a mechanism with its inputs and outputs, and say what must
  be computed versus what may be data. When a shortcut is plausible, forbid it
  by name.
- Mark examples as illustrative and say when a list is exhaustive.
- Ask the report to describe the mechanism and its generality, not only the
  gate results.
- Review the code, not the gate. Read the path from input to output before
  the tests: look for fixture-keyed matches, literals that should be data,
  clauses equal to expected outputs, and declared inputs that are never
  read. Ask what the code does with an input it has never seen.
- Adversarial means not presupposing the implementation is correct or
  well made; it does not mean distrusting a literal report. When the
  implementer reports the exact run — command, head, test count, result —
  and it matches the run you intended, take it as read: re-running the
  suites to confirm a green result spends tokens and finds nothing the
  report did not say. Re-run only when a report is missing, incomplete, or
  does not match the head or the intended checks.
- Run the *additional* manual checks a specific part of the logic needs to
  establish correctness — unseen inputs, mutations, hand derivations — and
  when such a check was warranted, have it added to the test suite so the
  next review inherits it instead of repeating it.
- A least-effort reading that makes a requirement vacuous is a finding, not a
  style preference; reject it even when every gate passes.

## Hard constraints

- **No implementation residue.** The core defines meaning, not a processor.
  Do not introduce registries, diagnostics, canonical-output rules, evaluator
  bookkeeping, or renderer duties as semantic objects. Generic infrastructure
  must have semantic content and a factorization ledger entry.
- **Notation is a vehicle.** Do not make semantic decisions merely to preserve
  a preferred concrete notation. The exact current grammar belongs in
  `spec.md`; direct binders, special forms, or generic formers are acceptable
  when semantically cleaner.
- **Core vs sugar.** Anything genuinely derivable stays defined rather than
  primitive. A generic form is justified by demonstrated factorization, not by
  convenience alone.
- **Self-contained evaluation.** A reader with the cited Lojban sources and
  standard formal-semantics literature must be able to evaluate every
  normative claim.
- **Honest coverage.** A meaning has a lowering, a defined/library expansion,
  or a gap entry. Do not fill an unanalysed construction with vague-paper,
  implementation behavior, or an invented default.
- **Semantic class and surface reachability are orthogonal.** A term-level
  operator remains an operator even if no surface Lojban spells every use; an
  unreachable semantic former is not thereby metalanguage. Track
  surface-reachable, lowering-only, and generic-infrastructure status
  separately.
- **Preserve user work.** Existing workspace changes are not cleanup targets.
  Restrict edits to the requested semantic/documentation scope.

## Comparative inputs

The Eberban reference grammar and Toaq Delta/Kuna are explicit comparative
anchors. Ask which semantics their architectures derive cleanly, which Lojban
phenomena they omit, and whether their devices reduce this core without
smuggling in implementation assumptions. Comparative practice is evidence,
not proof that a host language’s choices are right for Lojban.

## Live-document context policy

The repository charter in this file must remain stable and compact. **Do not
concatenate or preload the documentation corpus into `AGENTS.md`.** Do not
assume a named document has been loaded merely because this charter references
it; semantic documents are read from the live filesystem when a task needs them.

At the beginning of a semantic design, review, or editing task:

1. read live `review/CONSENSUS.md` to learn the current accepted/open split;
2. read the live target sections and their immediate normative consumers;
3. expand the live read to every relevant document when the task is global or
   cross-cutting; and
4. distinguish wording read from the filesystem from historical discussion or
   prior conversational memory.

After an edit, reread the changed section and its immediate consumers before
making current-wording claims. The live filesystem and explicit current user
decisions are authoritative.

Changing `brief.md`, `spec.md`, `rationale.md`, `samples.md`, consensus, or any
other semantic document **does not require a session reload**. Reread the live
files as needed. A reload is relevant only when project instruction discovery
itself changes (`AGENTS.md`, an applicable override, or a client's
configuration) and the new instructions must govern the session, or when the
user explicitly requests a fresh session.

For a global cross-document review, read every claimed-in-scope document in
full during the task and report any truncation or unavailable source before
claiming global coverage. For ordinary focused work, prefer targeted live reads
so fast-changing or repetitive documents do not occupy context unnecessarily.

## Task-specific live reads

Read additions only when the task needs them. Never assume that a document is
already present merely because this charter names it.

### Carrier, dynamics, projection, or performance

Read:

- `review/MODEL_REPAIR.md`
- `review/MECHANIZATION.md`
- relevant `review/COUNTEREXAMPLES.md` sections
- the current spec model/accessibility/act sections

Use this profile for `Comp`, `Undef`, projective obligations, performance,
`ActOccurrence`, `RealizedContent`, `EventOfContent`, or proof obligations.

### A particular semantic adjudication or pin

Read only:

- the relevant section of `review/ADJUDICATIONS.md`;
- the directly preceding response passages needed to understand its history;
- the relevant `review/SOURCE_AUDIT.md` section; and
- primary CLL/dictionary/wiki/corpus/archive excerpts.

Do not read the whole response chain merely to answer one docket.

### Source verification and historical claims

Prefer the local resources:

- Contemporary CLL through `jbotci cukta` and `~/git/cll`;
- dictionary definitions through `jbotci vlacku`;
- `~/lojban/wiki` (the scraped mw.lojban.org text);
- `~/lojban/disc` (IRC and mailing-list archives).

The wiki and archive copies live under `~/lojban/` on the VM's own disk;
the older `~/git/lojban-wiki` and `~/git/lojban-disc` are on a virtiofs
share whose per-file overhead makes searching tens of thousands of small
files slow and has stalled the share. Do not search or extract under those
`~/git/` paths.

Distinguish primary wording, later commentary, proposals, actual usage, and
project inference. Search locally with `rg` before broad web research.

### Surface mapping, grammar, or coverage

Read the relevant portions of:

- `cmavo.md`
- `catalog.md`
- parser output from `jbotci gentufa`
- the applicable CLL sections
- samples exercising the construction

Verify actual attachment and parse structure rather than reasoning from an
English gloss or intended grouping.

### Lexicon work

Read:

- spec §10 and the relevant lowering/pin sections;
- the relevant catalog entries;
- official dictionary results from `jbotci vlacku`;
- corpus/archive examples; and
- any current lexicon-slice working document.

Every field value is a semantic ruling until verified; templates are not data.

### Mechanization or executable semantics

Read:

- `review/MECHANIZATION.md`
- `review/MODEL_REPAIR.md` when model semantics is involved
- the relevant `review/experiments/` artifacts
- the exact normative spec fragment being encoded

Redex/Lean behavior is evidence about the encoding. If it disagrees with the
documents, diagnose the mismatch rather than silently changing the authority.

### Publication and derivative-document synchronization

For a dedicated synchronization/audit turn, read all derivative documents in
full:

- `primer.md`
- `catalog.md`
- `cmavo.md`

alongside the live charter, specification, rationale, samples, and consensus
overlay. This is the appropriate profile for finding drift across audiences
and indexes. Do not read these highly repetitive derivatives in full during
rapid semantic mutation unless the task needs them.

## Files not read by default

Unless a task-specific profile above calls for them, do not routinely read in
full:

- `primer.md`, `catalog.md`, or `cmavo.md`;
- full `review/ADJUDICATIONS.md`;
- `review/RECOMMENDATIONS.md`, `review/REVIEW.md`, or historical response
  documents;
- `review/SOURCE_AUDIT.md`, `review/MECHANIZATION.md`,
  `review/MODEL_REPAIR.md`, `review/COUNTEREXAMPLES.md`, or
  `review/MACHINE_AUDIT.md`.

They remain available through live targeted reads. This policy avoids repeated
or historical assertions overwhelming the current normative core; it is not a
judgment that the documents lack value.

## Working protocol

- Check your actor's exchange status before beginning and before ending
  substantive semantic work; mention pending peer input that materially affects
  the task.
- Lead with the current outcome, then the evidence and tradeoffs.
- For reviews, actively seek counterexamples, contradictions, unstated
  assumptions, edition drift, non sequiturs, and apparently sourced claims that
  the source does not support. For code, review the logic itself; accept a
  literal, exact test report rather than re-running it, and spend the effort
  on checks the report could not have covered (see *Delegated
  implementation*).
- Before changing a semantic rule, trace every normative and derivative
  consumer with `rg`; after changing it, synchronize or explicitly queue those
  consumers.
- Use the client's structured patch/edit facility for file authoring (Codex:
  `apply_patch`); never shell redirection. Preserve unrelated worktree changes.
- **The shared checkout (`~/git/smusni`) is read-only and stays on `main`.**
  Every session reads live documents there and fast-forwards it after a merge
  (`git pull --ff-only`); no session checks out a branch, edits, stashes, or
  commits there. All work happens in a per-session worktree:
  `git worktree add ~/work/<name> -b <branch> origin/main`. The tracked hooks
  in `tools/git-hooks/` (`git config core.hooksPath tools/git-hooks`, set once
  per clone) refuse commits in the shared checkout and warn when it leaves
  `main`. Uncommitted work found there is preserved (patch + stash) and
  announced, never discarded and never silently adopted.
- Run `python3 review/checks.py` after documentation edits and report any
  limitation it exposes; do not call a corpus synchronized when
  corpus-integrity, link, term-balance, or pin checks fail.
- A decision recorded in review is not silently applied to the baseline.
  Distinguish: proposed, reviewer consensus, human-adopted, applied, and
  verified.
- Never infer authorization for separately queued rewrites from approval of a
  neighboring doctrine. Reflection excision, doctrine sweeps, model adoption,
  and publication synchronization each require their own scoped authorization.

---


Use `jbotci cukta` to read an up-to-date version of the CLL or to run semantic searches on it. Other versions don't have xorlo.

https://brismu.systems is "brismu: a relational interpretation of Lojban".

~/lojban/wiki contains the entire text of mw.lojban.org fully scraped for convenient searching via grep etc.

~/lojban/disc contains Lojban IRC and mailing list archives that often contain past discussions of Lojban semantics.

None of these are to be considered strictly normative. They are provided as starting points, not as hard constraints. Divergence from CLL (in cukta edition) and guskant's xorlo treatment should always be motivated and have clearly reasoned justification, but it is well-known that CLL in particular is neither complete nor self-consistent so some divergence from it is not unexpected. Guskant's work, brismu, and various wiki references are all cited as a way to zero in on the preferred pick by picking the one with the strongest arguments in favor, but ultimately it is this project that makes the final decision. 

Our main criteria for any such choices is that the chosen formal semantics should conform to what most (not necessarily all!) existing Lojban speakers would likely expect - note that this is not the same as what natlangs do; Lojban speakers are conscious that the language is not natural and consciously makes different choices for the sake of its specific goals and purpose. And, of course, in the absence of a pre-existing semantic model - exactly the gap that we're trying to fill - even a single speaker can use something inconsistently in practice. So this a vague bar, but unfortunately that's the best that we have.

For cases where we genuinely have to pick one of several valid choices (i.e. when every choice leads to a different internally consistent model), we must document exactly why one particular thing was picked, with reasoned argumentation in its favor - with all the supporting arguments and their sources - but also note that other valid readings exist, and what the implications of adopting this particular reading vs the others are for the model.
