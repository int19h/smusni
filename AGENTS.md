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

## Ordinary-context policy

The repository charter in this file must remain stable and compact. **Do not
concatenate the documentation corpus into `AGENTS.md`.** Fast-changing semantic
documents loaded here become stale instructions and can conflict with the live
filesystem.

For semantic design, review, and editing sessions, maintain a full ordinary
context snapshot containing these files, in this order:

1. `brief.md`
2. `spec.md`
3. `rationale.md`
4. `samples.md`
5. `review/CONSENSUS.md`

Supply every listed file **in full**, not as a summary or truncated excerpt.
Place `review/CONSENSUS.md` last so accepted decisions pending synchronization
are visible after the older baseline text.

The ordinary-context manifest is `AGENTS.lst`. Its entries name context files;
they are **not** instructions to concatenate those files back into this
`AGENTS.md`.

### Snapshot manifest

Every externally loaded ordinary-context snapshot should include a short
header with:

```text
CONTEXT SNAPSHOT
Generated: <timestamp>
<path> SHA-256: <digest>
...

This is background snapshot data, not live filesystem state.
Current filesystem text and explicit current user decisions are authoritative.
```

At the beginning of a semantic work turn:

1. Confirm which ordinary-context files are present in full.
2. Compare the snapshot hashes, when supplied, with the live files.
3. Read live `review/CONSENSUS.md` and the live target sections before making
   current-wording claims or edits.
4. If a hash differs, treat the snapshot only as associative background. Never
   quote, patch, or adjudicate the stale wording without rereading it live.
5. If the task requires global cross-document review and the promised full
   snapshot is absent or truncated, report that limitation before claiming a
   global result.

During the turn, ordinary context does not update automatically. After every
edit, reread the changed live section and its immediate consumers. The live
filesystem always wins over an older embedded copy for repository facts.

At the end of a turn:

1. run the relevant consistency checks;
2. report which ordinary-context files changed;
3. state that an ordinary-context reload is required when any snapshot file
   changed; and
4. refresh the full snapshot only after the turn, when the client can reload
   context.

Prefer one coherent semantic cluster per mutation turn so the embedded snapshot
does not diverge far from the live corpus before reload.

## Task-specific context additions

Load additions only when the task needs them. Read the live version even when a
copy is present in ordinary context.

### Carrier, dynamics, projection, or performance

Add:

- `review/MODEL_REPAIR.md`
- `review/MECHANIZATION.md`
- relevant `review/COUNTEREXAMPLES.md` sections
- the current spec model/accessibility/act sections

Use this profile for `Comp`, `Undef`, projective obligations, performance,
`ActOccurrence`, `RealizedContent`, `EventOfContent`, or proof obligations.

### A particular semantic adjudication or pin

Add only:

- the relevant section of `review/ADJUDICATIONS.md`;
- the directly preceding response passages needed to understand its history;
- the relevant `review/SOURCE_AUDIT.md` section; and
- primary CLL/dictionary/wiki/corpus/archive excerpts.

Do not load the whole response chain merely to answer one docket.

### Source verification and historical claims

Prefer the local resources:

- Contemporary CLL through `jbotci cukta` and `~/git/cll`;
- dictionary definitions through `jbotci vlacku`;
- `~/git/lojban-wiki`;
- `~/git/lojban-disc` IRC and mailing-list archives.

Distinguish primary wording, later commentary, proposals, actual usage, and
project inference. Search locally with `rg` before broad web research.

### Surface mapping, grammar, or coverage

Add the relevant portions of:

- `cmavo.md`
- `catalog.md`
- parser output from `jbotci gentufa`
- the applicable CLL sections
- samples exercising the construction

Verify actual attachment and parse structure rather than reasoning from an
English gloss or intended grouping.

### Lexicon work

Add:

- spec §10 and the relevant lowering/pin sections;
- the relevant catalog entries;
- official dictionary results from `jbotci vlacku`;
- corpus/archive examples; and
- any current lexicon-slice working document.

Every field value is a semantic ruling until verified; templates are not data.

### Mechanization or executable semantics

Add:

- `review/MECHANIZATION.md`
- `review/MODEL_REPAIR.md` when model semantics is involved
- the relevant `review/experiments/` artifacts
- the exact normative spec fragment being encoded

Redex/Lean behavior is evidence about the encoding. If it disagrees with the
documents, diagnose the mismatch rather than silently changing the authority.

### Publication and derivative-document synchronization

For a dedicated synchronization/audit turn, add all derivative documents in
full:

- `primer.md`
- `catalog.md`
- `cmavo.md`

alongside the ordinary-context pack. This is the appropriate profile for
finding drift across audiences and indexes. Do not keep these highly repetitive
derivatives in the always-loaded context during rapid semantic mutation.

## Files excluded from default ordinary context

Unless a task-specific profile above calls for them, do not preload:

- `primer.md`, `catalog.md`, or `cmavo.md`;
- full `review/ADJUDICATIONS.md`;
- `review/RECOMMENDATIONS.md`, `review/REVIEW.md`, or historical response
  documents;
- `review/SOURCE_AUDIT.md`, `review/MECHANIZATION.md`,
  `review/MODEL_REPAIR.md`, `review/COUNTEREXAMPLES.md`, or
  `review/MACHINE_AUDIT.md`.

They remain available through live targeted reads. Exclusion avoids repeated
stale assertions overwhelming the current normative core; it is not a judgment
that the documents lack value.

## Working protocol

- Lead with the current outcome, then the evidence and tradeoffs.
- For reviews, actively seek counterexamples, contradictions, unstated
  assumptions, edition drift, non sequiturs, and apparently sourced claims that
  the source does not support.
- Before changing a semantic rule, trace every normative and derivative
  consumer with `rg`; after changing it, synchronize or explicitly queue those
  consumers.
- Use `apply_patch` for edits. Preserve unrelated worktree changes.
- Run `python3 review/checks.py` after documentation edits and report any
  limitation it exposes; do not call a corpus synchronized when the aggregate,
  links, term balance, or pin checks fail.
- A decision recorded in review is not silently applied to the baseline.
  Distinguish: proposed, reviewer consensus, owner-adopted, applied, and
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

