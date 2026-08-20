# Charter: the Lojban semantic core

This repository defines a community-facing **definition of Lojban
semantics** in terms of a small typed semantic core — a "Lojban semantic
assembly language".

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
- Sources — CLL, the official dictionary, the xorlo page, guskant's gadri
  commentary, Brismu (<https://brismu.systems/>) — are *guides*, not
  authorities; the specification's
  doctrine chapter states how they are weighed, and the compatibility
  principle that governs departures: a practical speaker of CLL Lojban
  must never have the rug pulled without strong, recorded motivation.

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

## Hard constraints

- **No implementation residue.** The core is a definition of meaning, not
  of any processor: no registries, no reduction rows, no error taxonomies,
  no canonical-output rules, no duties for a renderer. The reader must
  never need to know any implementation exists. Where a rule would exist
  only to serve an implementation, it is out; where a construct's shape
  could only be explained by an internal model detail, it is reshaped on
  semantic merits.
- **The S-expression notation** — `()` for function application and
  nothing else, `{…}` quoting the core's own notation (binder telescopes
  and bodies included, so binders are ordinary sign-consuming words),
  PascalCase operators, lowercase lexical predicates, `$variables`,
  `;` comments — is a vehicle,
  not the subject. It is kept because it is readable and avoids
  bikeshedding; the PascalCase operators are explicit placeholders under
  the specification's content-word program.
- **Core vs sugar.** The core may be verbose. Anything derivable stays out
  of the core (or is explicitly marked as a derived form with its
  definition). Necessity arguments belong in the rationale.
- **Self-contained.** A reader with CLL, the xorlo page, and standard
  formal-semantics literature must be able to evaluate every claim. Cite
  CLL chapters/sections and the literature where a construct follows or
  departs from an established treatment.

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
  <https://toaq.net/refgram/>) and its reference implementation **Kuna**
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

## Derived artifacts (future)

The documents are the definition; anything executable or machine-checked
is a **derived artifact**, never the authority. Two lines look
promising once the core stabilizes. A **Lean 4** mechanization: Lean's
`Expr`-and-elaborator architecture is the same staged, typed,
no-reification shape as the core's reflection layer, and its extensible
syntax means elaborator macros could plausibly *interpret the core
notation directly* — or even normalized Lojban text (normalization is
roughly: spaces between words, no dots or commas) — making sample terms
type-checked objects rather than prose. A **Metamath cross-check**
against Brismu's derivations would test the pin list from the opposite
direction. Both are future work items, started only on explicit
decision; neither may ever become a place where the definition lives.

## Coverage

The specification's adequacy chapter carries the full coverage matrix —
every CLL construct family mapped to its analysis or to an honest entry
in the gap register. In outline, the core covers: predication over typed
places with contextual defaulting; place conversion and deletion; event
semantics with tense/modal facets as ordinary predicates over events;
sorts (entities, eventualities and their subsorts, sets, groups, lists,
signs, acts, utterances, amounts, scales, …) and functions; lambdas;
inert `Let` vs effectful `Bind`; reference (descriptions, names,
generics) and the specificity triad; relative clauses; generalized
quantifiers with explicit import, witness export, and presupposition;
plural reference with subreference and join; cardinality under a
counting basis; termsets; logical and non-logical connectives with a
normative dynamic-accessibility table; abstraction relations and their
numeric crossings; questions and answerhood; de re / de dicto; quotation,
signs, and utterance tokens; speech acts and discourse structure;
indicators and evidentials; typed vagueness (the tanru former, scalar
operators, contextual computations, supplements); core reflection
(quotation of the core's own notation, with binders as sign-consuming
words — the basis of the language's self-description); and mex to the
extent Lojban ties it to meaning.
