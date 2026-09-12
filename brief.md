# Charter: the Lojban semantic core

This project defines Lojban semantics through a small typed core. A supported,
resolved Lojban reading lowers to a well-typed core term. The core defines
the reading's meaning; Lojban is its primary source language.

## Mission

The project identifies the meanings Lojban must express and the semantic
operations needed to express them compositionally. The specification's
adequacy chapter states the supported coverage. Its gap register records
meanings whose analysis or construction remains incomplete.

Lowering need not be surjective: some core terms may have no Lojban spelling.
A generic form is justified when it factors shared semantic structure or
simplifies the model. Each such form requires a necessity or factorization
argument. A well-typed core term does not, by itself, establish that Lojban
can express it. See specification §1.1.

Every resolved declarative clause has a `ClauseContent` stage with an
eventuality parameter before force closes it. Event-licensed lexical clauses
use their lexical event. Other clauses use the specified holding, joint or
compound-event construction. This interface supports tense, CAhA, ROI, ZAhO
and `nu` without adding event arguments to reusable identity and mathematical
functions. The event projection is partial when a computation returns no
continuation value. The corresponding model and definedness obligations
remain explicit.

## Semantic decisions and evidence

The specification is prescriptive. It distinguishes three kinds of uncertainty:

- Soritical vagueness has no intended exact boundary. Typed precisification
  represents thresholds, cutoffs and tolerances of this kind.
- An underspecified intended value is recovered contextually under constraints.
  Examples include tanru, `tu'a`, bare `jai` and topic links. Recovery need
  only be sufficiently equivalent for the discourse purpose; it does not
  introduce a speaker-side existential choice.
- An incomplete source description requires a reasoned semantic decision,
  recorded as a pin with its alternatives and consequences. It is not
  automatically represented as contextual or soritical vagueness.

[xorlo](https://mw.lojban.org/papri/How_to_use_xorlo) is the gadri baseline;
it supersedes pre-xorlo CLL semantics where they conflict. CLL, the official
dictionary, guskant's gadri commentary, [Brismu](https://brismu.systems/),
corpora and discussion archives provide evidence. None determines this
project's decisions independently of the stated criteria. Departures from
practical CLL usage require strong, documented reasons.

Citations record intellectual dependence, not only agreement. A rule,
construction or counterexample prompted by another author's work identifies
that source and explains what was retained, generalized or corrected.
Project-authored amendments, including those in Contemporary CLL, are not
independent evidence that the project's result is correct.

## Documents and authority

| Document | Role |
|---|---|
| [spec.md](spec.md) | Normative types, formation, semantic laws, lowering rules, pins, gaps and adequacy claims. Intended for readers familiar with typed calculi and formal semantics. |
| [rationale.md](rationale.md) | Reasons for the major constructions and decisions, including alternatives, costs and concrete examples. Architectural assumptions must be distinguished from general impossibility claims. |
| [samples.md](samples.md) | Worked Lojban readings and core terms, organized by specification topic. These are semantic tests, not an authority over the rules. |
| [primer.md](primer.md) | Exposition for readers without a formal-semantics background, with terminology, examples and pointers to the specification. |
| [catalog.md](catalog.md) | Per-identifier reference distinguishing primitives from defined forms and linking their signatures, purposes and definitions. |
| [cmavo.md](cmavo.md) | Index of treated cmavo and grammatical units, with examples, mappings and explicit gaps. |
| [decisions.md](decisions.md) | Current decisions, remaining work and disposition of earlier review findings. |
| `review/CONSENSUS.md` | Working overlay for accepted decisions awaiting synchronization. Historical entries must be read against later explicit adjudications; it is not the sole durable record of a decision or TODO. |

Historical review reports remain evidence. They neither introduce normative
rules nor reopen decisions subsequently settled by the human partner.
Where accepted edits await synchronization, the latest explicit human
adjudication and the working overlay guide that work. Their durable
consequences belong in the issue tracker; old overlay wording does not
override later decisions.

## Design constraints

- Define meaning, not a processor. Registries, diagnostics, canonical-output
  requirements and renderer responsibilities do not belong in the semantic
  core. Generic infrastructure requires semantic content and a factorization
  argument.
- Treat notation as a representation choice. The core uses S-expressions,
  direct binders such as `λ`, `Let`, `Bind` and `PerformSource`, PascalCase
  core names, lowercase lexical predicates, `$variables` and `;` comments.
  Braces and brackets mark structure but do not quote code or change meaning.
  The exact formation rules are in the specification.
- Define derivable forms in terms of existing operations. Primitive status
  requires a necessity or factorization argument within stated assumptions.
- Make claims independently assessable using the cited Lojban sources and
  formal-semantics literature. Identify the relevant editions and passages.
- State coverage explicitly. Each supported meaning needs a lowering or
  defined expansion; an incomplete analysis needs a gap entry, not an invented
  default or an appeal to implementation behavior.
- Separate semantic class from surface reachability. A term-level operator
  remains an operator even if some uses lack a Lojban spelling. Track
  surface-reachable, lowering-only and generic-infrastructure uses separately.

## Comparative inputs

The following languages provide architectural comparisons. Their treatments
are evidence about possible designs, not requirements for Lojban.

- [Eberban](https://github.com/eberban/eberban) and its
  [reference grammar](https://eberban.github.io/eberban/) use higher-order
  logic, true/false/unknown values, an implicit context argument, compositional
  particle definitions and explicit per-place distributivity conventions.
  The “Eberban from scratch” chapter develops vocabulary from core structures
  including pairs, sets, lists, maps and time. Relevant chapters also include
  Logic framework, Chaining, Explicit binding, Sentences, Logical primitives,
  Predicate transformations, Default arguments and Dictionary conventions.
- [Toaq Delta](https://toaq.net/refgram/introduction/) and its reference
  implementation [Kuna](https://github.com/toaq/kuna) provide a typed
  effect-based comparison. Kuna's constructors include intension `Int`,
  scope-taking continuation `Cont`, plurality `Pl`, indefinites `Indef`,
  questions `Qn`, supplement pairing `Pair`, discourse binding `Bind`/`Ref`,
  deixis `Dx` and speech acts `Act`.

Comparisons should identify which meanings follow from each architecture,
which Lojban phenomena it does not cover, and whether its constructions can
reduce this core without introducing processor-specific assumptions.

## Derived artifacts and possible authority transfer

Executable and machine-checked artifacts currently test the documents; they
do not define additional semantics. The Redex checker in
`tools/smusni-redex`, run by `tools/check-smusni`, extracts specimens,
checks them against a fixture lexicon and exercises bounded semantic
fixtures. Its reports distinguish verified coverage from remaining work.
Lean provides typed syntax, checking, proofs and auxiliary model constructions
within the scopes recorded in the tracker.

A future Lojban input layer requires its own parsing and reading-resolution
specification. A Metamath comparison with Brismu is another possible check,
not an existing result or an automatic work commitment.

The human partner approved a possible authority transfer in principle on
2026-08-29. It requires three recorded stages under tracker #74:

1. Full migration parity: the selected host covers every live formation,
   typing, library-expansion, lowering and denotation rule in the transfer
   scope, with explicit dispositions and the required differential and
   certificate evidence against the frozen checker.
2. A sole formal rule source: after a bounded overlap, the old checker is
   retired or demoted so that competing formal definitions do not remain live.
3. Explicit transfer: the human partner records the authority change.

Only then do the corresponding formal definitions become normative for
formation, typing, expansion and denotation, with their prose as commentary.
Lojban mapping text, evidence, pins, alternatives, gaps and adequacy remain
documentary and normative. A merge or passing test does not perform the
transfer.

## Coverage and remaining work

Specification §15 gives the coverage matrix; §14 gives the gaps. The document
set addresses typed predication and place operations, clause events, reference
and plurality, contextual dependencies, relative clauses, quantification,
logical and non-logical composition, abstraction, questions, quotation,
speech acts, indicators, vagueness and relevant mathematical expressions.
The supported fragments differ across these topics. Their inclusion in this
list is not a claim of complete analysis or implementation.

The current baseline includes the following decisions:

- Ordinary `su'o` quantifies over individuals. Core plural quantifiers and
  selections remain separate.
- Descriptions may have bound-variable dependencies, including Skolem-like
  `lo`; invariant descriptions are a special case.
- Description references persist under `na` according to C25.
- P43 uses conservative accessibility over a plural-capable core. It retires
  P42's additional numerical-group and dependent-family export while retaining
  ordinary existential continuity and independently bound references.
- Standard finite exact, range and complement quantifiers count individual
  qualifiers. Bare and restricted `ro` are non-importing; explicit descriptions
  retain their separate reference conditions.
- Bare `me'i` defaults to `ro`, meaning not-all, under P44. Explicit
  `me'i pa` means zero.
- P45 permits otherwise pure properties to contain reference introductions
  confined to a negation test. It removes no other effect or obligation.
- F01 supplies a bounded one-description assertion-continuation construction;
  its full model integration and general source factoring remain work.

Remaining work includes delayed de-dicto consumers, general dependent-reference
interfaces, recurring-state episodes, occurrence-sensitive deixis, effectful
focus and discursive constructions, vague numeric/cardinal interfaces, and
joint model, force and event obligations. Explicit experimental/full-plural
mappings remain distinct from standard-language defaults. Pure `Only` is
defined, but its broader lexical and effectful interfaces are incomplete.

The decision ledger distinguishes settled behavior from missing constructions
and genuinely undecided readings. Remaining interface work does not reopen
the settled distinctions above. Core self-description and reflection were
considered and set aside; they are not baseline coverage.
