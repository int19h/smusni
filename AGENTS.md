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

The GitHub issue tracker for `int19h/smusni` is the durable execution queue for
tracked actionable work. Tracker issue
[#1](https://github.com/int19h/smusni/issues/1) indexes the first
coherent-baseline backlog and its dependencies.

- `review/` is intentionally ignored and remains available for rapid analysis,
  model-to-model exchange, drafts, and historical notes. It is never the sole
  copy of a tracked actionable requirement, accepted decision, test result, or
  TODO.
- Ad hoc research, diagnosis, discussion, and other untracked tasks may proceed
  directly from the human prompt or addressed Collab mail. Do not create an
  issue merely to answer such a task.
- For an issue-backed task, inspect the live issue and search open and closed
  issues for duplicates before starting. The issue body is canonical for
  outcome, decision status, scope, acceptance criteria, dependencies, and
  durable evidence links.
- When work should become durable backlog, or when discussion settles an
  actionable requirement or accepted decision, create or update the issue in
  the same turn. Summarize the current result there; do not paste an obsolete
  review document wholesale or make ignored files required reading.
- Use labels to distinguish `ready`, `needs-design`, `speaker-evidence`,
  `model-theory`, `verification`, and blocked work. A “ready” label records
  semantic readiness, not authorization for unrelated edits or release.
- Update a tracked task's issue when scope or decisions change. Close it only
  after the acceptance criteria and repository checks pass; a mailbox response
  or local review note alone never closes work.
- The human partner's adjudications are final. Record their durable
  consequence in the relevant issue body or comment, creating a decision issue
  when needed, while retaining rejected alternatives and reopening criteria
  where the semantic decision genuinely had several coherent options.

## Multi-session review collaboration

Sessions review this repository as peers working with the human partner; no
session's proposal becomes consensus merely because it was written. Durable
coordination uses the external Herdr Collab project whose explicit id is
`smusni`:

```sh
export HERDR_COLLAB_PROJECT=smusni
```

The project id or an explicit `--project smusni` must select every mailbox
operation. Never infer a mailbox from the checkout, current directory,
worktree, or the project's diagnostic root path. Herdr Collab supplies durable
sessions, groups, messages, replies, and acknowledgements; it does not define
participants, roles, generations, workflows, turn order, review gates, issue
policy, or authority. Tailor those conventions to the task; when it is tracked,
record its lasting scope and acceptance criteria in GitHub.

- Give sessions and groups descriptive task-specific handles. Use
  `herdr-collab agent spawn <handle> --kind <agent-kind> ...` to create a new
  visible Herdr session. `herdr-collab session join` only registers a
  participant that was started manually; it does not create a Herdr session.
  Capture the returned UUID and set `HERDR_COLLAB_SESSION` for acting commands.
- Check `herdr-collab inbox --pending` and `herdr-collab status` at natural
  turn boundaries. Use `herdr-collab show <message-id>` to read a complete
  message and its referenced ancestors. Do not impose polling, a forced model
  turn, or a standing end-of-turn wait; use the finite foreground `wait` only
  when the current task actually calls for it.
- Publish task assignments, findings, questions, decisions, and handoffs with
  durable `send` or `reply`. A direct `agent prompt` is only a transient wakeup
  or alert and is never the sole copy of load-bearing content. Acknowledge with
  `ack --disposition ...` only after recording the disposition; acknowledgement
  means read and disposition captured, not agreement or completion.
- Every substantive message separates claims, evidence, objections/questions,
  and requested disposition, citing live file paths/sections, source excerpts,
  commit/working-tree state, and GitHub issue numbers. Correct immutable mail
  with a same-sender superseding message rather than editing it.
- Use only `herdr-collab` commands to change collaboration state. Never edit,
  move, or delete external state records by hand. Run `herdr-collab validate`
  when diagnosing state or before claiming that a task's durable mailbox is
  clear.
- No vote, quorum, silence, group membership, or acknowledgement count becomes
  consensus. Record named positions and one durable recorder per docket, and
  leave genuine semantic forks to the human partner. If collaboration creates
  or changes actionable work, update GitHub; if it proposes a semantic change,
  preserve the proposal in review until human-partner authorization.
- If only one session is active, continue useful work and leave an addressed
  durable handoff. Do not block routine progress merely waiting for an
  acknowledgement unless the issue requires independent review or
  human-partner adjudication.

**Resumable pauses.** Before an anticipated long pause, first persist every
load-bearing decision, exact head, important path, unresolved finding with its
location, and open question in durable mail or a handoff file. The coordinating
session may then request native compaction while the context is still likely
cached, explicitly naming what the lossy summary must retain. Do not compact
automatically or on a timer, and preserve full loaded context when that detail
is the session's main value, such as a reviewer comparing exact heads or an
implementer mid-change. After requested compaction, run
`herdr-collab session show "$HERDR_COLLAB_SESSION" --live`; normal liveness
confirms the stored and live identities still match. If it reports
`unavailable`, use deliberate `session refresh` or `agent adopt`, never a
guessed reference. If an already-idle session later shows a cache-expired
choice, inspect that exact dialog and continue its full context by default;
never generalize this into unattended input for blocked trust, permission, or
unrelated prompts.

**Full-pass reviews.** Reviewing diffs finds what a change broke; only reading
the documents whole finds what accumulated changes made inconsistent. When a
task calls for a full pass, create a fresh, task-tailored set of sessions and
load every in-scope document (`brief.md`, `spec.md`, `rationale.md`,
`samples.md`, `primer.md`) in full. The generation label, handles, optional
recipient group, review allocation, handoff, and retirement plan are project
conventions for that run, not Herdr Collab protocol or enforced state. Generate
a manifest-bearing bundle with `tools/full-pass-review/bundle.py`; see the
README there for the historical label and an example convention.

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
