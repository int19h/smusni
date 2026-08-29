# Charter: the Lojban semantic core

This repository defines a community-facing **prescriptive definition of
Lojban semantics** in terms of a small typed semantic core — a "Lojban semantic
assembly language".

## Mission

Flip the usual direction of Lojban semantics work. Instead of deriving
meaning from syntax construct by construct, we ask: **what meanings should a
Lojban utterance be able to convey**, and **what minimal set of typed
building blocks suffices to express all of them** — however verbose the
result, since syntactic sugar can always be layered on later. Every Lojban
utterance, under a resolved reading, is to denote a term of this core —
the specification's adequacy chapter states how far that claim presently
reaches, with its gap register bounding the remainder; the core is
the definition, and Lojban surface syntax becomes one (privileged) way to
spell its terms.

The lowering need not be surjective. Generic core forms may lack a Lojban
spelling when they substantially factor shared semantic structure or
simplify the model; every such form still owes a necessity or
factorization argument, and core typability never establishes Lojban
expressibility (specification §1.1).

Every resolved declarative clause exposes one `ClauseContent` eventuality
before force closes it. Event-licensed lexical clauses use their lexical
event directly; identity, mathematics, negation, quantified/generic claims,
and compound claims use typed holding/joint states. This is what lets tense,
CAhA, ROI, ZAhO, and `nu` apply uniformly while identity and mathematical
functions retain their ordinary reusable signatures.

This is a *definition*, not a description:

- Where a meaning is genuinely **soritically vague** — no fact fixes a
  threshold, cutoff, tolerance edge, or loose boundary — the core contains
  explicit typed precisification machinery rather than pretending context
  selects an exact value.
- Where the surface leaves an **intended value underspecified** — tanru,
  `tu'a`, bare `jai`, or topic links — the core uses constrained contextual
  recovery. The listener need only recover a value equivalent enough for the
  discourse purpose; surface underdetermination is not speaker-side
  existential choice.
- Where CLL is merely **underspecified** — where vagueness is an accident of
  the text, not a design intent — we pin the most useful interpretation and
  record why. The pin list and its justifications are first-class
  deliverables.
- xorlo is baseline (<https://mw.lojban.org/papri/How_to_use_xorlo>); CLL's
  pre-xorlo gadri semantics is superseded where they conflict.
- Sources — CLL, the official dictionary, the xorlo page, guskant's gadri
  commentary, Brismu (<https://brismu.systems/>) — are *guides*, not
  authorities; the specification's
  doctrine chapter states how they are weighed, and the compatibility
  principle that governs departures: a practical speaker of CLL Lojban
  must never have the rug pulled without strong, recorded motivation.
- Provenance is preserved even where it is not agreement: a rule, pin,
  formal construction, or counterexample materially prompted by another
  person's work cites it and states the nature of the dependence; a source
  the project corrected, generalized, or amended — including the
  Contemporary CLL edition's project-authored passages — is never presented
  as independently ratifying the result.

## The documents

At the repository root:

1. **`spec.md`** — the dense, formally precise specification. Audience:
   readers comfortable with formal semantics (typed lambda calculi,
   generalized quantifiers, dynamic semantics, speech-act theory). Complete
   and normative: types, term formers, well-formedness, semantics
   (denotational where possible, dynamic/effectful where needed), and the
   principles mapping Lojban constructs to core terms. Focused strictly on
   the semantic core: how and why it is **necessary and sufficient** to
   cover Lojban.
2. **`primer.md`** — the same content for fluent Lojbanists and amateur
   conlangers who are *not* semanticians. Terminology is unpacked and
   motivated rather than dropped: each technical notion gets a plain-language
   explanation, worked Lojban examples, and pointers for further reading so a
   motivated reader can graduate to the dense version.
3. **`rationale.md`** — for every major construct: why it is primitive (what
   meaning cannot be expressed without it), and why it is shaped this way
   rather than the plausible-looking alternatives. Ties into concrete
   examples.
4. **`samples.md`** — worked specimens: Lojban sentences with their full
   core terms, organized to walk the specification's chapters.
5. **`catalog.md`** — one entry per named identifier: informal
   definition, formal definition where one exists, purpose with an
   example, and links — split into true primitives (defined only by
   prose and axioms) and the forms defined in terms of them.
6. **`cmavo.md`** — the cmavo-centric index: one entry per treated
   cmavo (and per multi-cmavo grammatical unit) with a Lojban
   example, its core term, and links into the specification; its
   final section collects the documented no-mappings and the open
   adjacencies the cmavo-centric view makes visible.

## Hard constraints

- **No implementation residue.** The core is a definition of meaning, not
  of any processor: no registries, no reduction rows, no error taxonomies,
  no canonical-output rules, no duties for a renderer. The reader must
  never need to know any implementation exists. Where a rule would exist
  only to serve an implementation, it is out; where a construct's shape
  could only be explained by an internal model detail, it is reshaped on
  semantic merits.
- **The S-expression notation** — parenthesized application/operator
  forms, the direct `λ`/`Let`/`Bind` special forms written
  `{λ [$x :: T] body}` (braces mark the form, brackets its telescope, the
  body is bare), PascalCase named core forms, lowercase lexical predicates,
  `$variables`, and `;` comments — is a vehicle, not the subject. Delimiter
  shape is non-semantic; braces and brackets are punctuation, not quoted
  core code. The notation
  is kept because it is readable and avoids bikeshedding; PascalCase names
  mark the placeholder status the specification assigns them.
- **Core vs sugar.** The core may be verbose. Anything derivable stays out
  of the core (or is explicitly marked as a derived form with its
  definition). Necessity arguments belong in the rationale.
- **Self-contained.** A reader with CLL, the xorlo page, and standard
  formal-semantics literature must be able to evaluate every claim. Cite
  CLL chapters/sections and the literature where a construct follows or
  departs from an established treatment.
- **Honest coverage.** A meaning has a lowering, a defined/library
  expansion, or a gap entry; no unanalysed construction is filled with
  vague prose, implementation behavior, or an invented default.
- **Semantic class and surface reachability are orthogonal.** A term-level
  operator remains an operator even if no surface Lojban spells every use,
  and an unreachable semantic former is not thereby metalanguage;
  surface-reachable, lowering-only, and generic-infrastructure status are
  tracked separately (specification §1.1, §16).

## Comparative inputs (explicitly citable)

Unlike CLL, the reference grammars of two younger loglangs already define
much of their semantics formally. Both are cited in the deliverables, and
both repay study even where their solutions do not transfer:

- **Eberban** (<https://github.com/eberban/eberban>; reference grammar at
  <https://eberban.github.io/eberban/>). Custom higher-order logic;
  three-valued (true/false/unknown); every predicate threads an implicit
  *context argument* used to implement tense and similar meaning without
  surface verbosity; particles have per-family compositional definitions;
  a set-typed dictionary with explicit per-place distributivity marking;
  and the "Eberban from scratch" chapter reconstructs the practical
  vocabulary from a deliberately minimal core (pairs, sets, lists, maps,
  time) — exactly the core-plus-sugar architecture this project wants.
  Relevant chapters: Logic framework, Chaining, Explicit binding,
  Sentences, Logical primitives, Predicate transformations, Default
  arguments, Dictionary conventions, Eberban from scratch.
- **Toaq** (Delta; <https://toaq.net/>, refgram
  <https://toaq.net/refgram/introduction/>) and its reference
  implementation **Kuna**
  (<https://github.com/toaq/kuna>). Kuna's semantics is a simply-typed
  λ-calculus with an inventory of *effect* type constructors composed
  algebraically: intension `Int`, scope-taking continuation `Cont`,
  plurality `Pl`, Heim-style indefinites `Indef`, questions `Qn`,
  supplement pairing `Pair` (appositives — compare our `Supplement`),
  discourse-binding export/consume `Bind`/`Ref` (compare our accessibility
  story), deixis `Dx`, and speech acts `Act`.

Questions worth asking against both: what do they get for free that we
build by hand (Eberban's context argument vs our explicit event/tense
predications; Kuna's effect rows vs our explicit binders and force
constructors)? What do they *fail* to cover that Lojban needs? Which of
their formal devices would make our core smaller or crisper without
smuggling in an implementation?

## Derived artifacts

The documents are the definition today; anything executable or
machine-checked is a **derived artifact** until the recorded authority
transfer described below. A Redex-based checker
(`tools/smusni-redex`, run by `tools/check-smusni`) already extracts the
specimens from the specification and samples, type-checks them against a
fixture lexicon, and exercises the model-profile fixtures; it tests the
documents, reports its own known debts, and decides no meaning. A **Lean 4**
mechanization is the next line: the core as an extensible typed DSL, direct
core binders elaborating to Lean binding syntax, sample terms as checked
objects rather than prose, with a bounded Redex-to-Lean pilot queued in the
tracker. Lojban text could later be fed in through an independently
specified parsing and reading-resolution layer, and a **Metamath
cross-check** against Brismu's derivations would test the pin list from
the opposite direction. Each is started only on explicit decision. The project has adopted in
principle (2026-08-29) that, after a platform pilot selects a host, that
host reproduces every live formation rule, typing clause, library
definition, lowering rule, and denotation law with exact differential and
certificate coverage against the frozen checker, and the checker is then
retired so that one formal rule source remains, the formal definitions become the normative
statement of formation, typing, expansion, and denotation, with the prose
as commentary — while the Lojban mapping, evidence, pins, alternatives,
gaps, and adequacy claims remain documentary and normative. That transfer
is an explicit recorded decision; until it happens, nothing executable is a
place where the definition lives.

## Coverage

The specification's adequacy chapter carries the full coverage matrix —
every CLL construct family mapped to its analysis or to an honest entry
in the gap register. In outline, the core covers: predication over typed
places with contextual defaulting; place conversion and deletion; universal
clause eventualities with direct lexical events or holding states, and
tense/modal facets as ordinary predicates over the current clause event;
sorts (entities, eventualities and their subsorts, sets, groups, lists,
signs, utterances, amounts, scales, …), functions, and first-class act
values; lambdas;
inert `Let` vs effectful `Bind`; reference (descriptions, names,
generics) and the specificity triad; relative clauses; generalized
quantifiers with explicit import, witness export, and presupposition;
plural reference with subreference and join; cardinality under a
counting basis; termsets; logical connectives and typed `joi` constitution
(with `joi nai`, termset connection, missing property bases, compound
performance, and mekso-operand joiks honestly gap-registered), all with a
normative dynamic-
accessibility table; abstraction relations and their
numeric crossings; questions and answerhood; de re / de dicto; quotation,
signs, and utterance tokens; speech acts and discourse structure;
reusable act packages distinguished from token-specific realized performance
content; indicators and evidentials; typed soritical vagueness, intended-value
contextual computations (including tanru and scalar contrast domains), and
supplements; linguistic quotation and signs; and mex to the extent Lojban ties
it to meaning. A staged
core-self-description extension was designed and set aside; it is future
design history, not baseline coverage.
