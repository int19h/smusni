# Design brief: the Lojban semantic core ("smusni core")

This folder hosts a new, self-contained subproject: a community-facing
**definition of Lojban semantics** in terms of a small typed semantic core —
the "Lojban semantic assembly language". It grows out of the smusni v0
notation work (repository root: `spec.md`, `samples.md`) but is a distinct
product with a different audience and different obligations.

## Mission

Flip the usual direction of Lojban semantics work. Instead of deriving
meaning from syntax construct by construct, we ask: **what meanings should a
Lojban utterance be able to convey**, and **what minimal set of typed
building blocks suffices to express all of them** — however verbose the
result, since syntactic sugar can always be layered on later. Every Lojban
utterance, under a resolved reading, denotes a term of this core; the core is
the definition, and Lojban surface syntax becomes one (privileged) way to
spell its terms.

This is a *definition*, not a description:

- Where CLL is **explicit** that meaning is vague (e.g. the tanru
  modification relation), the core must contain machinery for *explicit,
  typed* vagueness — the vagueness is represented, not ignored.
- Where CLL is merely **underspecified** — where vagueness is an accident of
  the text, not a design intent — we pin the most useful interpretation and
  record why. The pin list and its justifications are first-class
  deliverables.
- xorlo is baseline (<https://mw.lojban.org/papri/How_to_use_xorlo>); CLL's
  pre-xorlo gadri semantics is superseded where they conflict.

## Deliverables

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
   examples (reuse/adapt the samples).
4. **`samples.md`** (adapted) — worked specimens with their Lojban sources,
   cleaned of anything implementation-flavored.

## Hard constraints

- **No implementation residue.** The v0 spec at the repository root is raw
  material, *not* authority. It is written around a renderer/projector: it
  talks about registries, reduction rows, projection failures, error ids,
  canonical output, "the graph", MUST/MUST NOT duties for a renderer. None
  of that may appear here. Where a v0 rule exists only to serve an
  implementation (e.g. failure taxonomies, registry coordinates, canonical
  printing rules), it is dropped or re-derived from semantic first
  principles. Where a v0 construct is shaped by an internal model detail, it
  is reshaped on its merits. The audience must never need to know any
  implementation exists.
- **Keep the S-expression notation and the broad strokes of the v0 surface**
  (typed binders, PascalCase operators, lowercase lexical predicates,
  `$variables`, `;` comments). It is readable and avoids bikeshedding. The
  notation is a vehicle, not the subject.
- **Core vs sugar.** The core may be verbose. Anything derivable stays out
  of the core (or is explicitly marked as a derived form with its
  definition). Necessity arguments belong in the rationale.
- **Self-contained.** A reader with CLL, the xorlo page, and standard
  formal-semantics literature must be able to evaluate every claim. Cite
  CLL chapters/sections and the literature where a construct follows or
  departs from an established treatment.

## Comparative inputs (explicitly citable)

Unlike CLL, the reference grammars of two younger loglangs already define
much of their semantics formally. Both may be cited in the deliverables, and
both repay study even where their solutions do not transfer:

- **Eberban** (<https://github.com/eberban/eberban>; reference grammar at
  <https://eberban.github.io/eberban/>). Custom higher-order logic;
  three-valued (true/false/unknown); every predicate threads an implicit
  *context argument* used to implement tense and similar meaning without
  surface verbosity; particles have per-family compositional definitions;
  and the "Eberban from scratch" chapter reconstructs the practical
  vocabulary from a deliberately minimal core (pairs, sets, lists, maps,
  time) — exactly the core-plus-sugar architecture this project wants.
  Relevant chapters: Logic framework, Chaining, Explicit binding,
  Sentences, Logical primitives, Predicate transformations, Default
  arguments, Eberban from scratch.
- **Toaq** (Delta; <https://toaq.net/>, refgram
  <https://toaq.net/refgram/>) and its reference implementation **Kuna**
  (<https://github.com/toaq/kuna>). Kuna's semantics is a simply-typed
  λ-calculus with an inventory of *effect* type constructors composed
  algebraically: intension `Int`, scope-taking continuation `Cont`,
  plurality `Pl`, Heim-style indefinites `Indef`, questions `Qn`,
  supplement pairing `Pair` (appositives — compare our `Supplement`),
  discourse-binding export/consume `Bind`/`Ref` (compare our accessibility
  story), deixis `Dx`, and speech acts `Act`. A local survey of Kuna's
  model and a comparison against the v0 approach are provided in the
  dispatch inputs directory.

Questions worth asking against both: what do they get for free that we
build by hand (Eberban's context argument vs our explicit event/tense
predications; Kuna's effect rows vs our explicit binders and force
constructors)? What do they *fail* to cover that Lojban needs? Which of
their formal devices would make our core smaller or crisper without
smuggling in an implementation?

## What the core must cover (v0 inventory, to be audited, not inherited)

Predication over typed places with contextual defaulting; conversion-free
place selection; event semantics with facet predications joined by `Joi`;
modals/tenses as ordinary predicates over events; type system with
referent sorts (entities, eventualities and their subsorts, sets, groups,
lists, signs, acts, utterances, amounts, scales, …) and functions;
lambdas; inert `Let`/`LetRec` vs effectful `Bind`; reference computation
(`Refer`, descriptions, names, typical/stereotypical); relative-clause
composition; generalized quantifiers with explicit import/effect
semantics, witnesses, and presupposition; plurality (`Among`, `Combine`,
plural covers), sets vs pluralities vs masses; exact cardinality;
simultaneous termsets; logical and non-logical connectives with dynamic
accessibility; abstraction crossings (propositions, properties, amounts,
experiences, concepts, `su'u`-generic with categorizer); questions and
answerhood (polar/open, tuples, exhaustivity, `kau`); de re / de dicto and
opacity; quotation and signs; utterance tokens and speech-act structure
(assert/ask/command/express, performance, discourse transitions);
indicators/attitudinals; explicit-vagueness machinery (tanru former,
scalar negation, contextual computations, supplements); math/mex to the
extent Lojban ties it to meaning.

## Round-1 assignment (each panelist, independently)

Deliver a structured position paper answering:

- **Q1 — De-implementation audit.** Walk the v0 spec. Produce a
  keep/derive/drop table: *keep* (core primitive), *derive* (expressible;
  give the derivation; belongs in sugar or in a derived-forms appendix),
  *drop* (exists only for implementation reasons). Justify each row in one
  or two sentences. Flag every place where v0's shape smells of the
  renderer rather than of Lojban.
- **Q2 — Necessity witnesses.** For each proposed primitive: a concrete
  meaning (ideally with a Lojban sentence) that cannot be expressed
  without it. If you cannot produce one, say so and move it to *derive*.
- **Q3 — Sufficiency hunt.** Find Lojban meaning the proposed core cannot
  express. Concrete sentences, please: attitudinal gradation and scales
  (`.ui nai cai`), evidentials, discursives, metalinguistic negation
  (`na'i`), `si`/`sa`/`su` self-repair, MEX corners, letterals as
  referents, dialectal `xorxes`-isms — whatever you can break the core
  with. Each gap: propose the smallest fix (new primitive vs new derived
  form vs explicit out-of-scope ruling with rationale).
- **Q4 — Pin list.** Enumerate the underspecification points that need a
  pinned semantics; for each give candidate readings, your
  recommendation, and what it costs. Seed list (extend it): default inner
  and outer quantifiers under xorlo; `ro` import; `lo` kinds vs pluralities
  (Carlson vs plural-logic readings); distributivity/cover defaults;
  `loi`/`lo'i` object sorts; donkey anaphora normalization; `noi` under
  negation/questions; tense defaulting and `ki` stickiness; `kau`
  exhaustivity; `le` specificity; `lo'e`/`le'e`; implicit `ce'u` placement
  in `ka`; `du'u` vs `ka` vs `nu` coercions and `su'u` categorizer; `tu'a`
  raising; `zo'e` vs unfilled places; anaphora resolution obligations
  (`ri`/`ra`/`ru`, `ko'a` assignment); termset simultaneity; connective
  scope ambiguities; UI scope/target selection.
- **Q5 — Explicit-vagueness machinery.** Which constructs need *typed
  underspecification* (tanru relation, contextual choices, scalar
  `na'e`-family, supplements, vague quantities), and what is the cleanest
  implementation-free formulation of each?
- **Q6 — Presentation.** Proposals for structuring the three documents;
  in particular how the primer should scaffold the jargon (worked-example
  strategy, glossary, reading list) and how the rationale should argue
  necessity (per-construct "why not X instead?" pattern).

Where you rely on CLL, cite chapter and section. Where you rely on
Eberban/Toaq, cite the chapter or the Kuna survey. Argue your positions;
you will get a reconciliation document back and are expected to push back
where you disagree, or concede explicitly and say why.

## Process

- Lead/editor: the lead session authors all deliverables; panelists design,
  critique, and review through persistent sessions that keep their context
  across rounds.
- Round 1: independent position papers (this assignment).
- Round 2: lead reconciliation + skeleton; panelists rebut.
- Round 3+: lead drafts `spec.md`; panel reviews; iterate. Then `primer.md`
  and `rationale.md` under the same loop.
- Reports are files, not chat: write your paper to the path given in your
  dispatch prompt. Keep IRC for short signals only.
