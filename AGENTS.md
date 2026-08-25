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
- Executable semantics, parsers, type-checkers, Redex models, Lean
  mechanizations, and certificates are derived artifacts. They test the
  documents; they do not become the semantic authority.

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

## Codex–Fable collaboration

Codex and Fable are peer reviewers working with the human partner; neither
model's proposal becomes consensus merely because it was written. The ignored
mailbox under `review/exchange/` replaces ad hoc copy/paste when both models can
access this filesystem. The full protocol and templates are in
`review/EXCHANGE_PROTOCOL.md`.

- Messages are immutable Markdown files addressed by directory:
  `review/exchange/inbox/codex/` and `review/exchange/inbox/fable/`.
- Compose under `review/exchange/drafts/<sender>/`, validate, then atomically
  move the finished file into the recipient inbox. Appearance in an inbox is
  the observable publication boundary; never edit it there.
- Filenames and IDs are
  `YYYYMMDDTHHMMSSZ-<sender>-<short-slug>.md`, using UTC. Each message header
  declares protocol version, ID, sender, recipient, creation time, kind,
  reply/supersession links, and relevant GitHub issues.
- Codex writes only messages addressed to Fable and acknowledgements under
  `review/exchange/acks/codex/`; Fable writes only messages addressed to Codex
  and acknowledgements under `review/exchange/acks/fable/`. Never edit or move
  another participant's published message.
- Correct a message with a new `supersedes` message. Respond with a new file
  whose `in_reply_to` names the earlier ID. Acknowledge only after the message
  has been read and any requested durable action has been answered or captured
  in a GitHub issue.
- Acknowledgement means the disposition is durably captured in a reply, issue,
  or short explicit explanation; it does not require completing queued work.
- At the start and end of every substantive semantic turn, run
  `python3 review/exchange_check.py codex` (Fable uses `fable`), read all pending
  messages, and run the validator before announcing that the mailbox is clear.
- Every substantive message separates claims, evidence, objections/questions,
  and requested disposition. Cite live file paths/sections, source excerpts,
  commit/working-tree state where relevant, and GitHub issue numbers.
- The mailbox is transient coordination, not authority. If an exchange creates
  or changes actionable work, update GitHub. If it proposes a semantic change,
  preserve the proposal in review until human-partner authorization; do not
  silently apply it to the baseline.
- If only one model is active, continue useful work and leave an addressed
  handoff. Do not block routine progress merely waiting for an acknowledgement
  unless the issue explicitly requires two-model review or human-partner
  adjudication.

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
concatenate or preload the documentation corpus into `AGENTS.md`.** Codex does
not follow document references from this file; semantic documents are read from
the live filesystem when a task needs them.

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
itself changes (`AGENTS.md`, an applicable override, or Codex configuration)
and the new instructions must govern the session, or when the user explicitly
requests a fresh session.

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
- `~/git/lojban-wiki`;
- `~/git/lojban-disc` IRC and mailing-list archives.

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

- Check the Codex mailbox before beginning and before ending substantive
  semantic work; mention pending Fable input that materially affects the task.
- Lead with the current outcome, then the evidence and tradeoffs.
- For reviews, actively seek counterexamples, contradictions, unstated
  assumptions, edition drift, non sequiturs, and apparently sourced claims that
  the source does not support.
- Before changing a semantic rule, trace every normative and derivative
  consumer with `rg`; after changing it, synchronize or explicitly queue those
  consumers.
- Use `apply_patch` for edits. Preserve unrelated worktree changes.
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

~/git/lojban-wiki contains the entire text of mw.lojban.org fully scraped for convenient searching via grep etc.

~/git/lojban-disc contains Lojban IRC and mailing list archives that often contain past discussions of Lojban semantics.

None of these are to be considered strictly normative. They are provided as starting points, not as hard constraints. Divergence from CLL (in cukta edition) and guskant's xorlo treatment should always be motivated and have clearly reasoned justification, but it is well-known that CLL in particular is neither complete nor self-consistent so some divergence from it is not unexpected. Guskant's work, brismu, and various wiki references are all cited as a way to zero in on the preferred pick by picking the one with the strongest arguments in favor, but ultimately it is this project that makes the final decision. 

Our main criteria for any such choices is that the chosen formal semantics should conform to what most (not necessarily all!) existing Lojban speakers would likely expect - note that this is not the same as what natlangs do; Lojban speakers are conscious that the language is not natural and consciously makes different choices for the sake of its specific goals and purpose. And, of course, in the absence of a pre-existing semantic model - exactly the gap that we're trying to fill - even a single speaker can use something inconsistently in practice. So this a vague bar, but unfortunately that's the best that we have.

For cases where we genuinely have to pick one of several valid choices (i.e. when every choice leads to a different internally consistent model), we must document exactly why one particular thing was picked, with reasoned argumentation in its favor - with all the supporting arguments and their sources - but also note that other valid readings exist, and what the implications of adopting this particular reading vs the others are for the model.
