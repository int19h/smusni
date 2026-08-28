# The Lojban semantic core

*A definition of Lojban meaning in terms of a small typed semantic
language.*

This document defines a semantic core for Lojban: a typed language of
meanings such that every Lojban utterance, under a resolved reading,
denotes a term of the core — within the analyzed coverage §15 states,
the gap register (§14) bounding the remainder. It is a **definition**,
not a description. When one resolved meaning has a genuinely soritical
boundary, the core represents its admissible sharpenings with typed
machinery. When an occurrence instead has an intended but unspoken value,
the core represents one contextually recovered value. When the source record
leaves the semantic rule itself unsettled, this document selects an
interpretation and records the choice as a numbered ruling. The
baseline for gadri and quantification is xorlo
(<https://mw.lojban.org/papri/How_to_use_xorlo>) — which the
Contemporary Lojban Language edition of CLL ratifies in-text (CLL 6.2;
editions and all other sources are listed in the References section) —
and pre-xorlo gadri semantics is superseded where older texts conflict.

The intended audience of this document is a reader comfortable with formal
semantics: typed lambda calculi, generalized quantifiers, dynamic semantics,
multidimensional/projective meaning, and speech-act theory. A companion
[primer](primer.md) presents the same content for fluent Lojbanists who are
not semanticians; a [rationale](rationale.md) argues, construct by
construct, why the core is shaped as it is and not otherwise;
[samples](samples.md) gives worked specimens with their Lojban sources;
and the [catalog](catalog.md) carries one reference entry per named
form — primitives and defined forms, each with prose, formal
definition, example, and links.

Two other engineered languages have formally specified fragments of their
semantics and are cited as comparative anchors where instructive: Eberban
(higher-order logic base, an implicit threaded context argument, and a
"from scratch" chapter that rebuilds practical vocabulary over a minimal
core; <https://github.com/eberban/eberban>) and Toaq Delta with its
reference implementation Kuna (a simply-typed λ-calculus with algebraic
effect constructors for scope, plurality, indefinites, questions,
supplements, discourse binding, deixis, and speech acts;
<https://toaq.net/>, <https://github.com/toaq/kuna>). The rationale
discusses what this core adopts from each and what it deliberately
declines.

## 1. Doctrine and judgments

### 1.1 The direction of definition

The core is meaning-first. Rather than assigning a denotation to each
syntactic construct of Lojban and hoping the assignments compose, the core
fixes an inventory of expressible meanings — typed terms — and then states,
in the mapping annex (§11), how Lojban surface constructs spell those
terms. Surface Lojban is one privileged concrete syntax for the core;
nothing in the core's semantics depends on it. The core may be verbose:
anything derivable is defined in the library (§12) rather than added to
the kernel, and syntactic sugar over the core is always possible later.
This is the same architecture Eberban's "from scratch" chapter demonstrates:
a deliberately small logical core, with the practical vocabulary
reconstructed over it as definitions.

**Expressive direction.** The core is an intermediate semantic
language, not an alternative surface syntax with exactly Lojban's
expressive image. Two guarantees are normative: **lowering
totality/soundness** — every supported resolved Lojban reading maps
to a well-typed core term (the analyzed coverage of §15) — and
**semantic definition** — every well-typed core term has defined
semantics. The converse surface direction is **not** guaranteed:
well-typed core terms may have no Lojban spelling, and generic
formers are admitted where they factor shared semantic structure
across constructs or substantially simplify the model — each still
owing its necessity-or-factorization argument in the rationale. Core
typability never establishes Lojban expressibility. This names
existing practice as much as it grants new license: the joint-locus
normal forms of §5.6 and the library's metalanguage (§12) already
live outside the surface image. Absence of a Lojban spelling creates,
by itself, no content-word obligation: surface reachability is
tracked independently of §16.1's semantic classes, and a generic
former remains classified by what it denotes or structurally does —
Class M's exemption covers exactly structural and metalanguage machinery,
while an unreachable former of any other class simply acquires no coinage duty from its
unreachability. The catalog shall mark each form as
surface-reachable, lowering-only, or generic infrastructure.

### 1.2 Sources, compatibility, and the two programs

**Guides, not authorities.** This specification is the normative
definition; its sources are interpretations that *guide* it. That
includes CLL itself — which has well-known internal inconsistencies —
the official dictionary, the xorlo baseline, guskant's gadri commentary
("gadri: an unofficial commentary from a logical point of view"), and
Brismu's relational interpretation. Where the guides conflict or fall
silent, this document decides, and records the decision as a pin.

**The compatibility principle.** A speaker who does not know or care
about formal semantics but already speaks CLL Lojban in practice must
not have the rug pulled from under them: this document defines *Lojban*,
not a successor language. Some backwards incompatibility is unavoidable —
no coherent definition can cover every interpretation in circulation —
but a deviation from established reading or practice is acceptable only
when strongly motivated: it resolves a contradiction, or it buys a
substantially simpler model where the alternative is convoluted for no
real gain. Gratuitous deviation is a defect. Every deviation is a pin
that names its motivation against this principle.

**The lexicon program.** The wider project includes a revision of the
official gismu list to give entries defined semantics. This
specification may therefore *propose* redefinitions of existing words —
marked as proposals with exact wording, decided by the project's human
committee, never silently applied — where an existing word is almost
right and a minor diff unlikely to affect real usage would make it
exactly right.

**The content-word program.** The end state has **only content words as
object-language predicates**. PascalCase names visibly mark provisional
core vocabulary, but their content-word obligations depend on semantic
class (§16): genuine predicates seek an existing word, proposed
redefinition, or coinage; executing operators retain their semantic role
and may have separate content-word *shadow relations*; structural and
metalanguage forms owe no word merely because the notation names them.
The catalog records the definition, reachability, fit, and see-also
evidence for each case. One boundary governs the whole program: a word
that describes an operator's result does not thereby execute the binding,
sequencing, interpretation, or force operation that produced it.

### 1.3 Resolved readings

The core denotes **resolved readings**. Processes that turn a text into a
reading — anaphora resolution (which antecedent `ri` takes), erasure
(`si`/`sa`/`su`), elliptical expansion (`go'i`, `no'a`), sticky-tense
propagation (`ki`), indicator target selection — are **text-to-reading
rules**. They are normative (the mapping annex states them, and their
outcomes form the resolved-reading datum `RR` of §11; a conforming
reading of a Lojban text must obey them) but they contribute no term
constructors: the calculus sees their *results* — variable bindings, token
identities, expanded content — never the processes themselves. A
syntactically well-formed text whose resolution fails (an anaphor with no
accessible antecedent, an unassigned assignable with no discourse key) has
no resolved reading; that is a statement about the mapping, not an error
object in the semantics.

### 1.4 Three ways not to be specific

The single most load-bearing distinction in this document is between three
things a meaning can do short of full specificity. They are distinct term
formers with distinct semantics (§5.3), and confusing them is the
characteristic mistake this core is designed to prevent:

- **Reference** (`Refer`): introduce a discourse referent satisfying a
  descriptive condition. A referent is new, veridically described (for
  `lo`), and available to subsequent anaphora.
- **Contextual resolution** (`Context`): retrieve a contextually salient
  value. Nothing is asserted about it and no referent is introduced. The
  speaker has an occurrence-specific intended value; a cooperative hearer is
  expected to recover one equivalent enough for the discourse purpose, not
  necessarily an identical private articulation. Omitted places, `zo'e`,
  `co'e`, `do'e`, tanru links, `tu'a`, bare `jai`, topic links, deictic
  grounds, and salient scales are of this kind.
- **Soritical vagueness** (`Vague`): a typed, constrained family of
  admissible sharpenings of one concept or boundary, with **no fact of the
  matter** fixing the cutoff. The term never chooses. Vague quantity
  thresholds, gradable cutoffs, approximate-number tolerances, and loose span
  boundaries are of this kind; discrete alternative meanings are not.

The operational test — the **recovery test** — is printed with the full
classification in §6.1.

A fourth possibility is **absence**: the meaning simply lacks a dimension.
A bare `kau` answerhood makes no
exhaustivity claim; unmarked plural predication makes no distributivity
claim; a tenseless bridi on its habitual/gnomic readings makes no
temporal claim (its episodic readings instead carry a `Context` time —
ruling P8). Absence is represented by absence — no hole, no parameter, no
covert operator. Where a dimension is absent, the truth conditions are
those of the weakest reading, and strengthenings enter only lexically,
pragmatically, or by explicit marking. (Rulings P8, P9, P4.)

### 1.5 Ambiguity is upstream

Grammatical ambiguity — a text with several parses, or a parse with several
resolutions — yields several resolved readings, each a distinct core term.
The core never encodes disjunctions of readings; it is downstream of
disambiguation. In particular, a construct is never classified `Vague`
merely because a text is ambiguous: `Vague` is a property of one reading's
meaning, not of the reader's uncertainty between readings. (Where a
construction's readings genuinely differ — e.g. implicit `ce'u` with
several unfilled places — the mapping annex says "distinct readings," never
"contextual vagueness"; ruling P12.)

### 1.6 Well-formedness, not failure

The core is defined by formation rules and typing judgments. An ill-typed
combination is not a term; a construction whose side conditions fail (e.g.
closure over a non-defaultable place, §4.6) is undefined at that point.
This document has no failure codes, no diagnostics, and no processing
model. Meanings this core deliberately does not analyze are listed in the
gap register (§14) with the reason no analysis is assigned; a gap is a
statement about this specification, not a runtime event.

### 1.7 Two truth values

At-issue content is two-valued. Partiality (undefined operations,
presupposition failure) is handled by the projective machinery (§5.5): a
partial operation carries a definedness condition that projects like any
presupposition. There is no third truth value; the phenomena a three-valued
logic would bundle — contextually unresolved values, question force,
presupposition failure — are kept apart by `Context`, the question types,
and `Presuppose` respectively. (Eberban's true/false/unknown is declined;
see the rationale.) Deliberate vagueness does not breach this: bivalence
holds **at every precisification** of a `Vague` parameter, and "supertruth"
over admissible precisifications (§5.3) is a metalogical consequence
notion, not an object-language truth value — borderline vagueness yields no
third value, only a family of bivalent readings.

## 2. Notation

Core terms are written as S-expressions:

- `(operator operand …)` — ordinary application and operator forms;
  PascalCase spellings mark named provisional core forms (§1.2, §16),
  while lowercase names are lexical predicates (dictionary words:
  `klama`, `gerku`). A small set of mathematical glyphs (`¬ ∧ ∨ → ↔ ⊕
  ∀ ∃ = ∈ ⊆ ∪ ∩ × ≤ < ≥ > + − ÷ ⊤`) name the logical and mathematical
  operators (`⊤` is the trivially true content — the empty conjunction,
  `∧`'s unit; `×` is numeric product on `Number` and, by its operands'
  sorts, the set product `pi'u` denotes).
- Parenthesis shape is **non-semantic**: `(...)`, `[...]`, and `{...}`
  denote the same list term, as they do in Redex. A special form is
  recognized by its reserved head atom and positional operands, never by
  delimiter shape: `(λ binders body)`, `(Let binder value body)`, and
  `(Bind binder computation … body)`. The style convention — not a
  formation condition — writes applications/predications with `(...)`,
  special forms with `{...}`, and binder/type syntax with `[...]`, e.g.
  `{Let [$x :: Referents Entity] $y (klama $x $y)}`.
- `$name` — variables, always introduced by a binder with an explicit
  type ascription. A binder group contains one or more variables, `::`,
  and one type, e.g. `[$x $y :: Referents Entity]`; a telescope is a
  list of groups, e.g. `[[$x :: Entity] [$r :: Referents Entity]]`.
  `::` is the type-ascription keyword, and every form that requires a
  type annotation requires it.
- A compound type is a generic instantiation. Ordinary type constructors
  use a flat spine after `::`: `[$r :: Referents Entity]`, with
  parentheses only for a nested instantiation
  (`[$sets :: Referents (Set Entity)]`). Function types have the one
  reader-compatible spelling `Fn (A B) C` / `EFn (A B) C`, with a
  parenthesized parameter-type list followed by the result; `Fn () C`
  has zero parameters. Angle-bracket signatures such as `Fn<(A), B>`
  remain metalanguage.
- Rows used as object-language type indexes are written `(RowOf H)` for
  the row of lexical entry `H`, `(Row (1 T1) (2 T2) …
  (Eventuality Te))` for a literal row, and `(RowMinus row label)` for
  row deletion. `Record row`, `PredTerm row`, `Label row`, and
  `CompatibleLabel row T` consume those indexes. Row metavariables such
  as `ρ` and display tables such as `⟨…⟩` remain metalanguage and occur
  only in schema/expansion displays.
- `:label value` — a labelled place fill inside a predication (§4.2).
  Ordinary labels are numerals (`:1`, `:2`, …); `:Eventuality` names the
  distinguished event place. The same labels are bare numerals or
  `Eventuality` when passed to `At`, `DropPlace`, `Label`,
  `CompatibleLabel`, or written in `Row`. Positional fills follow numeral
  order. `::` similarly marks the following material as a type.
- `; text` — comments, to end of line; consumed as whitespace. By
  convention a specimen's first comment line is its Lojban source.
- `"…"` — `Text` literals (used by name signs, quoted text, and sign
  facts).
- The term grammar has atoms and list forms. `λ`, `Let`, and `Bind` are
  direct special forms, syntactically distinct from ordinary application
  by their reserved head atoms and governed by §4.4/§5.2. `Bind` remains
  variadic by alternation: `{Bind [$x :: T] c1 [$y :: S] c2 … body}`.
  Bodies are bare term operands; delimiter shape never adds a wrapper or
  quotation.
- Commas do not occur in `lisp` fences: Racket reads them as `unquote`.
  Constraint families and schema holes use ordinary applications, e.g.
  `(GroupBasisConstraint loi Entity)` and `(C $v)`. ASCII apostrophe is
  likewise a reader delimiter; the sole sanctioned pre-read step replaces
  an identifier-internal Lojban apostrophe (as in `te'a`) with a same-width
  safe marker outside comments/strings and restores it after `read-syntax`.
  Identifiers never end in apostrophe; use `$e2`, not `$e'`.

Notation conventions — elision of inferable types, the writing of `Close`
(§4.6), currying conventions, pretty-printing — are non-semantic: two
spellings that denote the same term per this document's rules are the same
meaning, and no unique canonical spelling is defined or required. This
chapter is the only place notation is normative, and only to the extent
that a reader must be able to parse the examples.

One clause shorthand preserves older compact specimens: where a
Content-taking force boundary is shown with a complete, eventless Content c
and no `ClauseContent` wrapper, c stands for
`(CloseClause (ActualClause (StateClause c)))` in that specimen's resolved
actual CAhA mode. A displayed `Close P` uses §4.6's
type-directed cases instead. This shorthand never wraps an already formed
`ClauseContent`, never creates a second lexical event, and may always be
expanded when the clause event matters. Other CAhA readings must show their
own clause former; the shorthand creates no surface default.

## 3. Types

### 3.1 Sorts of individuals

The domain of first-order individuals is sorted. `Entity` is the top
first-order sort. Beneath it:

```text
Entity
├─ Eventuality       events and states of affairs; subsorts:
│      Achievement, Process, Activity, State, Experience,
│      Locution (an uttering event)
├─ Location
├─ Time
├─ Amount            (positions on scales)
├─ Scale
├─ Epistemology
├─ TruthValue
├─ Concept
├─ AbstractNature
├─ Proposition       (reified content, §9)
├─ Question          (reified queries, §8)
├─ Number            with Natural <: Number and, embedded through the
│                    finite cardinalities, Cardinal <: Number
├─ Text              (uninterpreted character sequences)
├─ Set<T>  Group<T>  List<T>    (collection objects, §4.9)
├─ Sign<K>  SignToken<K>        (signs, §7.5; K a sign kind)
├─ UtteranceToken               (utterance tokens, §7.4)
└─ Ground            (deictic grounds, §5.1)
```

All sorts under `Entity` above are pairwise siblings except where a
subsort line says otherwise
(`Time` is not a `Location`, `Epistemology` is not a `Scale`,
`AbstractNature` not a `Concept`).
`Bool` is the two-element answer type for polar questions (§8.1), distinct
from the epistemology-relative `TruthValue` sort.

Subsorting is subset inclusion in every model; a term of a subsort may
stand wherever the supersort is required (covariantly, through `Referents`
as well), and never conversely. The sort hierarchy makes lexical selection
expressible — `barda` selects an `Amount`-bearing argument where `fasnu`
selects an `Eventuality` — and underwrites the no-coercion ruling (P13):
no implicit conversions exist between sorts; every crossing is an explicit
operator or lexical relation.

The hierarchy is open at the leaves in one deliberate way: `Entity` admits
kind-like referents where a model and the lexicon's kind-admitting places
allow them. There is no `Kind` sort and no automatic kind reading of any
description; see ruling P3. One further opening is **reserved**, not
present: §9.1's reified-predicate family would, if adopted, add an
indexed first-order sort family beside `Set<T>`/`Sign<K>`, each member
an ordinary first-order domain for equality, `Referents`,
descriptions, and typed quantifiers, with `Proposition` retrospectively
its row-⟨⟩ member; in the baseline only `Proposition` exists.

### 3.2 Plural reference

`Referents<T>` is the type of **plural references**: nonempty,
number-neutral pluralities of `T`s. It is not `Set<T>` (a set is a single
first-order object with membership; a plurality is not an object over and
above its members), not a mereological sum, and not a group. Its algebra
(§4.8) has exactly a join (`Combine`) and the induced subreference order
(`Among`); no atomicity, no distributivity, and no covers are assumed.
`Referents<T>` is covariant in `T`, and a single `T` lifts implicitly to a
singleton `Referents<T>` at referential positions (a typing rule, not an
operator). The same lift reads binder ascriptions in the §7.4/§7.5
entry notations, which ascribe the token *sort* while their
definitions bind at the singleton-lifted reference type.

Nonemptiness is part of the type: there is no empty plural reference.
(Consequences for `lo no broda` are drawn in ruling P22.)

### 3.3 Relations, functions, and rows

A **place row** ρ is a finite sequence of labelled, typed places, e.g. for
`klama`:

```text
(RowOf klama) =
  (Row (1 (Referents Entity)) (2 (Referents Entity))
       (3 (Referents Entity)) (4 (Referents Entity))
       (5 (Referents Entity)) (Eventuality (Referents Eventuality)))
```

The `Eventuality` place is distinguished: it is present exactly on lexical
entries whose §10 clause-event mode is `DirectEvent(Eventuality)`, and is filled with
`:Eventuality`. Holding-state entries have no such row field; their clause
event comes from `StateClause` after ordinary fills.

- `PredTerm ρ` — the type of relations over row ρ. It is a **transparent
  alias** for the row-function type `Record ρ → Content`: partial filling
  is abstraction over the residual row, place selection is record
  projection, and two relations equal on all row records are the same
  relation. A relation over the exhausted row is its content:
  `PredTerm (Row)` applied at the empty record is `Content`, and the
  notation writes that final application invisibly. The alias is retained pervasively in signatures because
  labelled places are the load-bearing Lojban-specific structure (free
  place order, `zi'o`, conversion, place questions all speak in labels).
- `Fn (A …) B` — ordinary functions with positional parameters, the type
  of λ-abstractions. Properties are `Fn (T) Content`; the library's
  generalized quantifiers (§12) take a pure restrictor `Fn (T) Content`
  and a nuclear scope that may be effectful (`EFn`).
- `Label ρ` — the finite type of ρ's place labels; the domain of place
  questions (§8.3).

Purity is tracked in the function space: `Fn` is the **pure** arrow — a
function whose body, *when its result is evaluated*, performs no dynamic
effects (§5): no introductions, no contextual retrievals, no projective
emissions — and `EFn` the effectful arrow. Positions that demand purity
are exactly **set comprehension (§4.9), quantifier and `Generic`
restrictors (§4.10, §5.8), selection restrictors (§5.6), and the
member-level `Refer` lift (§5.3)**; a body with unhoisted effects simply
fails to have the pure type. Nuclear scopes, `OpenQ` bodies, `Generic`'s
nuclear operand, and `Refer`'s reference-level restrictor (§5.3) are
`EFn` — they may close places contextually and introduce referents, with
the accessibility table governing what escapes. This is the whole of the purity discipline:
a typing fact, not an algorithm. `PredTerm ρ`, `Fn`, and `EFn` are types
and appear freely in variable annotations, λ parameter lists, and
`Context`/`Vague` type arguments.

One signature convention holds document-wide: `→` marks total
operations; `⇀` marks partial ones, whose definedness condition
projects (§5.5); and a `RefComp`/`PerfComp`/`Comp` result type marks the
operations that consult context or otherwise carry effects. The three
spellings are exclusive — a signature never expresses contextual
recovery with `⇀` or projective partiality with `→`.

### 3.4 Control types

```text
Content            evaluable (dynamic) propositional content
ClauseContent      event-open declarative content, definitionally
                   EFn ((Referents Eventuality)) Content
RefComp<T>         reference/contextual computations returning T
Act<F>             speech acts of force F ∈ ⟨Assertion, Question,
                   Directive, Expressive, Address⟩
ActOccurrence<F>   opaque handle for one performance of an Act<F>
PerfComp<T>        performance-level computations returning T
Discourse          definitionally PerfComp<Unit>: performed discourse
                   (sequences of acts and transitions)
Query<A>           questions with answer domain A
```

`Content` is the type of what can be asserted, questioned, negated, and
embedded. Its denotation (§5.1) has a world-indexed context-change run and
the §9.3 clause-event intension; neither world nor lineage indices appear in
the term language. `Act<F>`
values are first-class: constructing an act and performing it are
different things (§7.1), which is what keeps quotation and reported speech
from performing their contents. An act is a pure *value*, not a
computation: only `Perform` injects it into the dynamic carrier and returns an
opaque `ActOccurrence<F>` handle (§5.1, §7.1). The handle exposes no
capture or evaluator state; it exists so occurrence-relative display can
target the performance it modifies.

`ClauseContent` is a transparent effectful-function alias, not a first-order
sort and not a second proposition type. It is the stage at which one
distinguished clause eventuality remains available to tense, aspect, tags,
CAhA, ROI, and event abstraction. A consumer that needs ordinary `Content`
uses `CloseClause` (§4.6). Thus every declarative clause has an eventuality
while `=` and mathematical functions retain their reusable non-clausal
signatures.

### 3.5 Index and composite types

Beside the sorts and the function space, the type language carries a
small stock of **index and composite formers**, each already used by a
named construct and normative for exactly those uses:

- **Closed enumerations** — finite, equality-bearing index types,
  declared with their constructs: `Bool` (§3.1), `Proximity` (§5.1),
  the force index of `Act<F>`, the pure/effectful function classes of §3.3,
  `OccurrenceRole` (§7.1: `Host | AttachedDisplay | AttachedAddress`),
  `ThresholdKind`, `Direction`, `BasisKind`, `DefectKind`,
  `EnumerationLevel`, the intensity regions (§7.6), and the
  place-label types `Label<ρ>`. `=` is available at every enumeration
  (§4.5); the eliminator is the finite equality-guarded disjunction —
  the §4.7 computed-label case split.
- **Closed unions** — finitely-tagged sums declared with their
  constructs: `TopicResolution<ρ,T>` (§12) and the indicator target
  type `Target` (§7.6). A union value is built by its named injection
  and consumed by the same finite equality-guarded disjunction.
  `Target` is fixed here once: a `Proposition`, an act value or
  `ActOccurrence` handle of *some* force (the force index existential and
  erased; act members can be recovered through the partial
  `InterpretAct<F>`/`RealizedAct<F>` family, while occurrence handles have no
  baseline inspector), a plural reference at *some* sort, or a sign of *some*
  kind. The same force-erasure reading types `Realizes u a` (§7.4):
  its act operand is force-existential. Sort-polymorphic fact
  relations (`Denotes`, §7.5) are metalanguage families — one
  relation per sort — not union-typed operators.
- **Structured contrast domains** — `ContrastDomain<ρ>` and
  `ContrastRegion<ρ>` (§6.3), the typed domain and region interfaces against
  which a row-ρ predicate is contrasted. Domain and region values are not
  first-order sets of predicates. A domain interpretation supplies universe
  and region membership, relative complement, and optional
  polarity/betweenness structure. (`Region<Scale>` is the separate gradable
  region former used by `Grade`, §6.4.)
- **Constitution interfaces** — `DecompositionBasis<W,C>` (§4.9) is a
  non-first-order interface whose values supply a granularity-relative cover
  of `C`-components for `W`-wholes; `ContributionBasis<ρ>` is its
  function-typed analogue for mixed row-`ρ` properties. Neither is an object,
  set of objects, or inspectable implementation record. `Family⁺<A>` is the
  nonempty finite family used only as
  `Family⁺<PredTerm<ρ>>` by that property interface: `(Family a …)` constructs
  one; permutation/rebracketing are immaterial, and at that sole baseline
  instantiation duplicate predicates at §4.4 contextual equality collapse.
  There is no general
  eliminator or surface claim that arbitrary values can be massed.
- **Tuples** — finite products: multi-parameter quantifier loci
  (§4.5), open-question answer domains (§8.1), `TupleAnswer`
  payloads (§8.2). Projection is positional and total.
- **List construction** — `(List a …)` builds `List<T>` values
  (§4.9); elimination is metalanguage recursion over list structure
  (§12's `ZipWith` and `xi`), never a term-level recursion former
  (§4.4).

Nothing else is composite: `Record ρ` stays the row-record theory of
§3.3, and set-builder or record displays remain metalanguage (§2).

## 4. The static core

### 4.1 Lexical predication

A lexical predicate applied to fills for its row yields `Content`:

```lisp
; mi klama ti
(klama Speaker This)
```

Fills are positional by default, following the row order; a labelled fill
`:n value` selects a place out of order, and subsequent positional fills
continue from the place after `n`:

```lisp
; klama fe ti tu        — place 2 = ti; place 3 = tu; place 1 unfilled
(klama :2 This Yonder)
```

The event place is filled as `:Eventuality e`. Unfilled places do not
default silently; they are closed by `Close` (§4.6) into explicit
contextual computations, or abstracted by λ, or genuinely absent only
under `DropPlace`.

**All fill notation is sugar over one former.** The single-place fill
`(At R ℓ v)` with a literal label (§4.7) fills place ℓ and yields the
relation over the residual row; every multi-place fill desugars to
nested single fills, with the positional and `:n`-continuation rules
above merely computing which labels are used:

```lisp
(klama :2 This Yonder)
  ≝ (At (At klama 2 This) 3 Yonder)
(klama Speaker This)
  ≝ (At (At klama 1 Speaker) 2 This)
```

Fills are values — effectful arguments are bound by `Bind` before they
reach a fill position — so distinct-label fills **commute**
(definitionally: `(At (At R ℓ₁ v₁) ℓ₂ v₂) ≡ (At (At R ℓ₂ v₂) ℓ₁ v₁)`
— a metatheoretic equation, since object-language `=` does not apply
at row-function types). That commutation
is the semantic fact beneath Lojban's free surface order: FA
reordering and `se`-conversion are notation precisely because the
order of *fills* never was part of the meaning. Two things surface
order still governs, upstream of the term: effectful argument
computations `Bind` in source order before any fill forms, and the
⊳ anaphora-resolution rules (`ri`'s recency counting, CLL ch. 7) read
the *text's* sumti order — so reordering a sentence can change which
term the mapping produces, while never changing what any one term
means. Descriptions and names are the computations this sentence orders;
quantified sumti are ordered among themselves and against them by §11
L5.30 (P41). And `At` itself is no
new primitive: with `PredTerm` a transparent alias (§3.3), the literal
fill is partial application of the row function —
`(At R ℓ v) ≝ {λ [$rest :: Record (RowMinus ρ ℓ)]
(R ⟨the ρ-record extending $rest with ℓ = v⟩)}` — so the
whole fill apparatus bottoms out in λ and labelled records.

### 4.2 Place conversion

`se`/`te`/`ve`/`xe` and FA tags are consumed by the mapping: a converted
predication is the base predication with fills routed to their base
places. A converted relation escaping into a function position is the
λ-abstraction over the permuted row:

```lisp
; se tavla as a first-class binary relation
{λ [$new1 $new2 :: Referents Entity]
  (tavla $new2 $new1)}
```

No `Se` operator exists in the core.

### 4.3 Place deletion

`(DropPlace R n) : PredTerm (RowMinus ρ n)` is the relation ρ with place `n`
removed — the meaning of `zi'o`. Deletion is semantic surgery on the
relation, not omission of a fill: `mi klama ti zi'o ti ti` predicates a
relation that *has no origin role*, which neither `zo'e` nor closure can
express. A lexical entry states which deletions are meaningful (§10).

### 4.4 Functions and binding

`{λ Δ body}` is a direct binding form. If the telescope `Δ` extends
the current typing context by parameters `x₁:T₁ … xₙ:Tₙ` and the body
has type `B`, the abstraction has type `Fn (T₁ … Tₙ) B` when the body
is pure and `EFn (T₁ … Tₙ) B` otherwise (§3.3). Bound occurrences are
resolved lexically; α-renaming is meaning-preserving; substitution is
capture-avoiding. Application to value arguments satisfies the ordinary
β-law, evaluating the body once with those values substituted. If the
result is a computation, substitution constructs that computation; it does
not itself run it. η holds at the pure function type where it does not
change effects or site structure.

`{Let [$x :: T] v body}` is the direct inert-sharing form, defined as
immediate value application,
`{Let [$x :: T] v body} ≝ ({λ [$x :: T] body} v)`, and the
spelling for several shared values is explicit nesting. Its active operand
must be a value of type `T`; if `body` has type `B` under `$x:T`, the whole
form has type `B`. It does not run a reference computation or share an
effectful evaluation. Effectful computations are sequenced and shared by
`Bind` (§5.2). `Let` is retained for legibility and to make the identity of
a value used twice explicit (`goi` aliasing and act targets).

Binder formation assigns `Context`/`Vague` site identities to written
occurrences in the body, invariant under α-renaming. Sharing one bound
function or body preserves those sites; copying its text creates new
occurrences and therefore new sites. There is no recursion former in the
term language; recursive definitions occur only in the library's
metalanguage (§12).

### 4.5 Connectives and quantifiers

The logical operators are `¬ ∧ ∨ → ↔ ⊕` over `Content` and the
quantifiers `∀ ∃` over typed λ-bodies, with (multi-parameter) joint loci:

```lisp
(∀ {λ [$x $y :: Entity] …})
```

Statically they have classical truth conditions. Dynamically each carries
an accessibility row (§5.4) that is part of its meaning; `↔` and `⊕` are
primitive precisely because their classical rewrites duplicate operands,
and duplication re-runs dynamic effects. Multi-parameter loci are the
normal form of donkey configurations (§5.6) and simultaneous termsets
(ruling P17).

Equality `=` is primitive at every first-order sort and at the discrete
index types (`Bool`, place labels, the closed enumerations);
it is never available at the plural reference type, where `CoRef`
(mutual `Among`) is the equivalence. `du` maps to `=` between
first-order individuals and to `CoRef` between plural sumti.

### 4.6 Clause formation and closure

Every resolved declarative clause first forms `ClauseContent`. Two routes are
required, and they must not be conflated:

- `(DirectClause P) : ClauseContent` is the defined route for an
  event-licensed row. It leaves the lexical event place as the clause
  parameter and contextually fills only the other defaultable places.
- `(StateClause c) : ClauseContent` is the primitive holding-state route for
  already complete content with no surviving lexical event parameter —
  identity, mathematics, negation, quantified/generic claims, and the
  non-disjunctive compound forms below. It evaluates `c` exactly once and
  exposes the state of that content holding. Its denotation and
  `EventOfContent` laws are §9.3; it neither returns a truth value nor exposes
  syntax.

For an event-licensed row with unfilled defaultable places p₁…pₖ,

```lisp
(DirectClause P) ≝
{λ [$e :: Referents Eventuality]
  {Bind [$v1 :: T1] (Context) … [$vk :: Tk] (Context)
    (P :p1 $v1 … :pk $vk :Eventuality $e)}}
```

When k = 0 and P contains no other effects, this function refines to the pure
`Fn` arrow. Otherwise it is effectful; no caller may
silently use it where purity is demanded — a selection restrictor, the
member-level `Refer` lift (§5.3), or a `SetOf` comprehension — while a
reference-level `Refer` restrictor may carry it (§5.3).

The distinguished parameter is then closed only when ordinary content is
needed:

```lisp
CloseClause : ClauseContent → Content
```

The **run projection** of `(CloseClause C)` is exactly the run of
`(∃ {λ [$e :: Referents Eventuality] (C $e)})`. Its structured
Content denotation additionally carries that branch's locally bound `$e` as
the clause-event projection (§9.3). `CloseClause` is therefore primitive:
plain `∃` can reproduce its truth and dynamic effects but cannot attach the
chosen witness to Content without an additional event-construction operation.
The witness remains local, and each candidate branch evaluates `(C $e)` with
the ordinary quantifier discipline.

`Close` remains the convenient derived spelling at predication sites, now
with three type-directed cases:

```text
(Close P)                         ≝
  (CloseClause (ActualClause (DirectClause P)))
  ; event-licensed row, resolved actual CAhA mode
(Close (P :Eventuality e))        ≝
  (CloseClause
    {λ [$e2 :: Referents Eventuality]
      (∧ (CoRef $e2 e) ((ActualClause (DirectClause P)) e))})
  ; explicit/shared lexical event; no second event is introduced
(Close P_eventless)               ≝
  Bind ordinary defaults, then CloseClause(ActualClause(StateClause(P_filled)))
```

In the explicit-event case, the local closure witness `$e2` is constrained to
co-refer with the already supplied e; it therefore records that same event in
the structured Content without adding another event. Plain application
`((ActualClause …) e)` has the same at-issue run but, because
`ClauseContent` is a transparent function alias, does not itself overwrite
the returned Content's independently composed event (§9.3).

The last case is what lets `du`, mathematical relations, and genuinely
eventless lexical rows form clauses; it does not retype the underlying relation
with a lexical event place. Each omitted ordinary place remains a *distinct* `Context` computation
(P15), with §5.3 site/dependency identity. `Close` is undefined when a
remaining place is not defaultable. `Close` names the common **actual-mode**
closure, not a surface default: an unmarked bridi whose resolved CAhA mode is
capable/unrealized/demonstrated uses the corresponding §12 clause former
instead (P24).

Logical composition at the clause layer is defined without losing the
eventuality interface:

```text
(ClauseNot C)       ≝ (StateClause (¬ (CloseClause C)))
(ClauseAnd C D)     ≝ (StateClause (∧ (CloseClause C) (CloseClause D)))
(ClauseOr C D)      ≝ {λ [$e :: Referents Eventuality] (∨ (C $e) (D $e))}
(ClauseImp C D)     ≝ (StateClause (→ (CloseClause C) (CloseClause D)))
(ClauseIff C D)     ≝ (StateClause (↔ (CloseClause C) (CloseClause D)))
(ClauseXor C D)     ≝ (StateClause (⊕ (CloseClause C) (CloseClause D)))
```

Conjunction therefore has a jointly constituted state; disjunction retains
the successful disjunct's event branch; negation has a negative holding state.
The remaining Boolean compounds take the state of the complete truth-
functional claim. Each operand occurs once, so contextual sites, dynamic
accessibility, and projective emissions are exactly those of the underlying
`Content` operator. Facet conjunction over one already shared event stays
plain `∧` inside a single `ClauseContent`; it is not `ClauseAnd`.

### 4.7 Place questions

`Label ρ` (§3.3) types questions over places. `At` is the
single-place fill former: with a **literal** label, `(At R ℓ v)` is
partial application of the row function at field ℓ (§4.1 — every fill
notation desugars to it). With a **computed** label —
`$p : CompatibleLabel ρ T` for a fill `v : T`, the `fi'a` case —
`(At R $p v)` abbreviates the finite case split over the compatible
labels, each branch a literal fill:

```lisp
(∨ (∧ (= $p ℓ1) (C (At R ℓ1 v))) … (∧ (= $p ℓn) (C (At R ℓn v))))
```

(`C` the containing predication through its closure — the
computed-label form is licensed exactly where that closed context
exists, so every branch is `Content`). The domain is the
**compatible-label refinement** `CompatibleLabel ρ T` (declared with
the topic interface, §12): the labels whose place sort accepts the
fill — a heterogeneous row contributes no ill-typed branch — and the
event place is excluded (no FA tag reaches it; surface place
questions ask over the lexical x-places). When **two or more**
computed fills occur in one predication, the case split ranges over
the assignments in which the computed labels are **pairwise
distinct** (two fills never answer one place); a single computed
fill — the ordinary `fi'a` — carries no such condition. `(Label R)`
abbreviates `Label<ρ(R)>`, and a computed-fill domain
`(CompatibleLabel R T)` likewise. `fi'a` maps to an open question
over its compatible-label domain (§8.3); an open relation question
(`mo`) binds a `PredTerm`-typed variable directly and needs no
special row machinery.

### 4.8 The plural algebra

`Combine : Referents<T> × Referents<T> → Referents<T>` is plural join
(associative, commutative, idempotent — `jo'u`), and
`Among : Referents<T> × Referents<T> → Content` is the subreference
order. Both are primitive at the plural type and axiomatized together
(`Among x y` holds exactly when `Combine x y` and `y` co-refer — the
library's `CoRef`, §12; typed
equality `=` itself stays at the first-order sorts, so the axiom is
stated as co-reference, not object equality). Singular `T`s lift to
singleton references at referential positions.

The bridge from pluralities to collection objects is **basis
extraction**: for a pure `P : Fn<(T), Content>`,

```text
(UnitSet P r) : Set<T>   —  the set of P-satisfying units among r:
                             x ∈ (UnitSet P r)  iff  P(x) ∧ Among(x, r)
(CardBasis r P) ≝ (Card (UnitSet P r))
```

`CardBasis` is how inner cardinality is stated: counting is always
counting units *under a description* within a reference (pin P1's
source-licensed unit basis).

For a pure unit property `P : Fn<(T), Content>`, the defined no-residue
condition is:

```text
(CoveredBy P r) ≝
  (∧ (Distrib P r)
     (∀ {λ [$r2 :: Referents T]
       (→ (Among $r2 r)
          (∃ {λ [$x :: T]
            (∧ (P $x) (Overlap $x $r2))}))}))
```

Thus every represented unit satisfies P and every subreference overlaps some
P-unit. The second conjunct is substantive when a reference has no atomic
bottom: it excludes residue without requiring P-units themselves to be atoms.
`Overlap` and `Distrib` are the §12 definitions. Selection witnesses and the
lexical unit profiles of §10 use this one condition (P39).

That is the whole plural kernel. No atoms are assumed: nothing requires
references to bottom out in singletons, and guskant's Condition₁ proof and
divisible-bread reading motivated that boundary. No distributivity operator is
covert, and no cover parameter attaches to predication: a lexical
predicate applied to a plural reference holds or fails of that plurality,
and which configurations verify it is the predicate's lexical business
(the lexicon may declare per-place plurality behavior, §10). Marked
readings are explicit: the library's `Distrib` (from `∀`/`Among`) for
each-reading, group objects (§4.9) for collective packaging, and `lu'a`
(§12) when a resolved reading commits to structure.
(Rulings P4; the design follows plural logic — Boolos, Oliver & Smiley —
rather than covert-operator theories.)

**Representation note (non-normative).** Under the discipline **D** —
nonempty, atomistically generated, singleton-separated, singleton-prime
(a unit below a join is below one of the operands) pluralities with
extensional identity by units (discourse-introduction identity carried
outside the extension), every nonempty unit set represented (with the
infinite joins that requires), natural under subsorts — the quotient
`Referents<T>/CoRef` is isomorphic to the nonempty sets over `T`:
`Combine` is union, `Among` is subset, the singleton lift sends each
individual to its singleton set. A set-backed implementation of that fragment is therefore
legitimate, and set-typed lexicons (Eberban's nonempty `tce` places)
are intertranslatable with this one inside D. The specification does
not adopt D: atomistic generation is exactly what the no-atoms clause
declines, and representation sets must in any case stay distinct from
the first-order `Set<T>` objects of §4.9 (ruling P25; the full
argument, including why the re-spec was declined, is the rationale's
sets essay).

### 4.9 Collections and mathematics

Collection *objects* are first-order individuals distinct from plural
references:

- `(SetOf P) : Set<T>` for pure `P : Fn<(T), Content>` — extensional
  comprehension; `∈` is membership; `Card : Set<T> ⇀ Cardinal` is
  defined at the finite sets, its definedness projective (§5.5) — the
  comparisons built on it (`Most`, `GlobalExactly`, the ROI schema)
  inherit the finiteness condition.
  (`CardBasis`, §4.8, is the corresponding operation for plural
  references: it counts units under a description within a reference.)
- `Group<T>` objects are related to their components by the layered
  constitution interface below. The official `gunma` row uses its
  non-exhaustive layer (x2 plural — ruling P5); group-forming `joi` and
  `loi`/`lei`/`lai` use the complete strengthening. `Set<T>` objects are
  related to their members by exact `selcmi`. `loi`/`lo'i` descriptions
  refer to those objects (§11 L3); neither unwraps implicitly to its members.
- `List<T>` objects carry order (`ce'o`); indexing and `ZipWith` (the
  `fa'u` analysis) are library forms over list recursion (§12).
- `Number` and its subsorts carry the arithmetic operators
  `+ − × ÷ < ≤` (with `a > b ≝ b < a` and `≥` likewise); partial
  operations (division, non-total roots) carry
  projective definedness conditions (§5.5). Intervals are comprehensions
  with endpoint conditions; further mathematics (exponentiation, bases,
  arrays) is library and gap-register material.

#### Constitution at a decomposition basis

One indexed programme supplies group, event, and compatible-property
constitution without pretending that a group of `T`s is itself a `T`:

```text
DecompositionBasis<W,C>
BasisUnitAt<W,C> : DecompositionBasis<W,C> × Referents<C>
                     × Referents<C> → Content
PeerUnitAt<W,C> : DecompositionBasis<W,C> × Referents<C>
                    × Referents<W> → Content
GunmaAt<W,C> : DecompositionBasis<W,C> × Referents<W>
                 × Referents<C> → Content             (defined below)
CompleteGunmaAt<W,C> : DecompositionBasis<W,C> × Referents<W>
                         × Referents<C> → Content       (defined below)
ComponentAt<W,C> : DecompositionBasis<W,C> × C
                     × Referents<W> → Content           (defined below)
Aggregate<T> : DecompositionBasis<Group<T>,T> × Group<T> → Content
                                                       (primitive classification)

ContributionBasis<ρ>
MixAt<ρ> : ContributionBasis<ρ> × Family⁺<PredTerm<ρ>>
             × Record ρ → Content
ContributesAt<ρ> : ContributionBasis<ρ> × PredTerm<ρ>
                     × Family⁺<PredTerm<ρ>> × Record ρ → Content
GunmaPredAt<ρ> : ContributionBasis<ρ> × PredTerm<ρ>
                   × Family⁺<PredTerm<ρ>> → Content   (defined below)
```

`W` and `C` are first-order sorts in the first three signatures. The two
baseline instances are
`DecompositionBasis<Group<T>,T>` and
`DecompositionBasis<Eventuality,Eventuality>`; the component argument stays
an ordinary plural reference in both. Predicate components are functions, so
only `GunmaPredAt` uses the generic, non-first-order `Family⁺` carrier. This
keeps `Group<PredTerm<ρ>>` out of the first-order hierarchy and creates no
predicate objects (§9.1).

A value `κ : DecompositionBasis<W,C>` is semantic structure consumed through
two pure primitive interface relations:

- `BasisUnitAt κ u Cs`: the nonempty reference `u : Referents<C>` is one peer unit
  in κ's cover of the component reference `Cs`; and
- `PeerUnitAt κ u w`: `u` is one peer component unit of the whole reference `w` at
  that same basis.

`PeerUnitAt` is the basis's total peer-component field, not an observation sample:
every substantive component of `w` at κ is represented by at least one such
unit, and co-referent wholes have the same field. A basis that cannot state
that coverage is not admissible for `CompleteGunmaAt`.

For every non-null `Cs`, its units are nonempty subreferences of `Cs`, stable
under `CoRef`, and **cover without atomizing** it:

```text
BasisUnitAt(κ,u,Cs) → Among(u,Cs)
Among(r,Cs) → ∃u.(BasisUnitAt(κ,u,Cs) ∧ Overlap(r,u))
```

Units need not be singletons, disjoint, minimal, or material parts. A basis
may use people in a team, temporal phases in an event, or another declared
peer granularity; arbitrary subreferences and logical consequences are not
thereby components. A basis may declare a null component only with an
explicit identity law; the conjunction basis below is the sole baseline
case.

A basis offered to `JoiGroup`, `JoiEvent`, or `JoiClause` is admissible for a
particular flattened operand partition `X₁,…,Xₙ` only if it **respects that
partition**:

```text
BasisUnitAt(κ,u,Xᵢ) → BasisUnitAt(κ,u,Combine(X₁,…,Xₙ))   for every i.
```

The speaker's articulation into `joi` operands is therefore preserved at the
selected peer granularity. A basis that merges away an operand-boundary unit
(for example, maximal contiguous phases that merge two adjacent events) is
not admissible for that partition; it cannot make the mapping silently
unsatisfiable.

`GunmaAt` is now an actual definition over that interface, deliberately
**non-exhaustive** so `w` may have other peer units. The complete strengthening
adds the converse:

```text
(GunmaAt κ w Cs) ≝
  ∀u.(BasisUnitAt κ u Cs →
        ∃v.(PeerUnitAt κ v w ∧ CoRef u v))

(CompleteGunmaAt κ w Cs) ≝ (GunmaAt κ w Cs)
  ∧ ∀v.(PeerUnitAt κ v w →
          ∃u.(BasisUnitAt κ u Cs ∧ CoRef u v))

(ComponentAt κ x w) ≝ (GunmaAt κ w x)
```

In the last line `x : C` takes §3.2's singleton lift. A plural surface x2,
including ordinary converted `se gunma`, uses `GunmaAt` directly; conversion
never changes the relation. Thus `mi se gunma le mi lanzu` can state partial
componenthood without a `components(w)` projection or special `se`
semantics. `ComponentAt` has the formation condition that x is not a
basis-declared null component; the null is absorbable, not an ordinary
component of everything. A complete construction rules out an unmentioned peer at
the selected basis. Neither layer licenses component-to-whole or
whole-to-component property inheritance.

For a declared null cover, `GunmaAt κ w null` is deliberately vacuous; only
the basis's explicit null-whole/identity law can make it complete, and no
surface `ComponentAt` exposes the vacuous partial relation.

`GroupBasis<T>` abbreviates `DecompositionBasis<Group<T>,T>`. Each mapped
group-forming occurrence retrieves a constrained `GroupBasis<T>` through
`Context`, with the resolved reading declaring its dependency profile. The
lexicon declares the admissible bases: “team”, “committee”, “material
aggregate”, and the like are not an unconstrained choice left to a model.
`(GroupBasisConstraint k T)`, `(EventBasisConstraint k)`, and
`(ContributionBasisConstraint k ρ)` are metalanguage names for the pure
constraint property supplied by the lexicon/mapping for construction class
`k`; they are not term constructors or a closed enumeration of possible
bases. A displayed `Context` uses the applicable property, whose free outer
variables obey §5.3's dependency rule.
General `gunma` lowers to `GunmaAt`; `joi`, the group descriptors, and the
group clause of `MeiRel` lower to `CompleteGunmaAt` (§11–§12).

`Aggregate κ g` is the primitive, rigid model classification of a **bare
aggregate device** at group basis κ. It is not inferred merely because an
organization's membership happens never to change. Its interpretation is
situation-invariant: `StateClause` and every other situation shift leave the
classification unchanged. The following laws hold at the situation of
evaluation; `CompleteGunmaAt` gains no situation argument, because §5.7
already supplies the evaluation boundary:

```text
(R) Aggregate κ g → ∃C. at every model situation s,
                         CompleteGunmaAt κ g C at s

(E) for every admissible κ and nonempty C, at every situation s,
      ∃g. Aggregate κ g ∧ CompleteGunmaAt κ g C

(A) Aggregate κ g ∧ Aggregate κ h
      ∧ CompleteGunmaAt κ g C ∧ CompleteGunmaAt κ h C → g = h

(F) CompleteGunmaAt κ g C ∧ CompleteGunmaAt κ g D → CoRef C D
```

`R` is one-way: a fixed-roster committee, corporation, or named duo may
remain distinct from the canonical aggregate of the same people. `A` gives
one aggregate per basis/cover, not one group of every kind. `F` makes the
complete cover of any group functional at one basis and situation. These
laws leave cross-basis identity model-given and leave the null cover to §14/#23.

The event-basis existence/extensionality clause below is the event instance
of the same complete-cover pattern: every admitted operand cover has a whole;
two event wholes complete over one cover at one basis co-refer; and one event
whole has one complete cover up to `CoRef`. Events need no `Aggregate`
classification because the event-construction clauses themselves fix the
whole kind and identity interface.

An event basis additionally supplies total model-level aggregation clauses
for temporal trace, participants by semantic role, and causal profile. For
`CompleteGunmaAt κ j Es`:

1. the trace and role-indexed participant profile of `j` are exactly κ's
   declared aggregation of the peer events' traces and participants;
2. every non-null peer event contributes to that aggregation, and no event
   outside the complete cover contributes at the same peer level;
3. κ's causal aggregation determines the whole's causal profile. A joint
   cause may cause an outcome without any component causing it alone, and no
   causal or participant fact is inherited in either direction unless that
   basis's clause states it; and
4. the complete whole is actual at a world exactly when all of its non-null
   peer events are actual there.

Every admitted event basis must state those three aggregation functions and
their contribution laws; saying only “the model chooses a mixture” is not an
instance. Temporal union/closure, joint causal contribution, and role-wise
participant union are common admissible shapes, not one universal formula
forced on every event kind. A basis admitted for `JoiEvent`/`JoiClause` also
has **complete-cover existence and extensionality**: for every mapped operand
cover it supplies a complete whole, and any two complete whole references for
that cover co-refer. Thus the clause parameter is one joint whole up to
reference identity rather than an accidental plurality of rival events.
Together with the earlier congruence law that co-referent wholes have the same
`PeerUnitAt` field, this also blocks a plural reference to rival partial
wholes from masquerading as the complete joint event: extensionality would
force it to co-refer with the genuine whole, while field congruence would then
force the incompatible peer fields to agree.

The model carries one distinguished event basis `κ∧` for conjunction.
`joint_M(e₁,…,eₙ)` is, up to `CoRef`, the unique complete event whole under
`κ∧` whose non-null peer cover is the flattened cover of `e₁,…,eₙ` and to
which every non-null operand contributes. The basis is transparent to its
own complete wholes. Its temporal trace is the union of the non-null peer
traces, its participant value at each semantic role is their role-wise plural
union, and its causal profile contains exactly the links licensed by the
model's **joint-cause relation over that complete peer cover**—never a
component link merely copied upward. The joint-cause relation must be
permutation-invariant, require every listed peer to contribute, and be
associative under κ∧ flattening; this is a semantic model relation, not a
surface `rinka` rewrite. Nesting therefore flattens, and

```text
joint_M(joint_M(e₁,e₂),e₃)  CoRef  joint_M(e₁,joint_M(e₂,e₃)).
```

`hold_M(⊤)` is `κ∧`'s declared null whole/component: it has no substantive
peer unit, is the unique complete all-null whole, and adjoining it does not
change the other cover. Hence `joint_M(e,hold_M(⊤))` co-refers with `e`.
This is a constitution law, not a claim that the plural reference
`Combine(e,hold_M(⊤))` co-refers with `e`. These clauses exhibit the
`joint_M` required by §9.3 rather than positing a second notion of joint
state.

For property constitution, primitive `MixAt κ F a` is the pure realization
condition a declared `κ : ContributionBasis<ρ>` supplies for nonempty family
`F` at total row record `a : Record ρ`; `ContributesAt κ P F a` is its
operand-contribution relation.
The interface is admissible only when:

- `MixAt` is invariant under permutation, rebracketing, and duplicate collapse
  of `F`;
- whenever it holds, every family member P satisfies
  `ContributesAt κ P F a` nontrivially at
  the basis κ declares—spatial region, temporal phase, constitutive origin,
  phenomenal/intentional aspect, or another lexically specified mode;
- those listed contributions are jointly sufficient for `MixAt κ F a`: no
  family member is a free rider and no additional unlisted peer contribution
  is needed at that basis; and
- the generic interface licenses neither inference from contribution to
  satisfaction nor to non-satisfaction of an operand at whole-argument
  granularity. A particular declared basis may add either law when its row
  warrants it; neither is inherited by default.

Each basis declaration must spell `ContributesAt` through a typed witness
domain and pure realization relation appropriate to that mode (region,
phase, origin, aspect, …), or through an equivalent extensional clause. An
uninterpreted always-true contribution flag is not an admissible instance.
The witness type is per basis because forcing origins and phenomenal aspects
into one first-order “part” sort would recreate the rejected universal mass
former.

Then

```text
(GunmaPredAt κ R F) ≝
  ∀a : Record ρ. (R(a) ↔ MixAt κ F a)
```

Only pure, already-lowered common-row predicates may enter `F`; contextual
sites are bound before family construction. Each usable row needs a curated
lexical/per-row basis declaration. A color-region basis can validate a
blue/red ball without making the whole wholly blue or red; an origin basis
can validate a lion/tiger hybrid without lion-only or tiger-only material
parts; an aspect basis can validate blended desire/fear without pure emotion
parts. These are different declared contribution modes, not licenses for an
empty universal “some relation” analysis.

### 4.10 Cardinal quantification

Bare-PA terms denote **witness-set selection** (rulings P1, P17): `ci
gerku cu bajra` selects a three-unit witness reference of dogs and
predicates running of it —

```lisp
; ci gerku cu bajra — the default (witness-set) reading
{Bind [$w :: Referents Entity]
        (SelectExactly 3 {λ [$x :: Entity] (gerku $x)})
  (Close (bajra $w))}
```

— the shape the library's `Exactly n` (§12) realizes. Two things about
this reading. **Exactness attaches to the selected witness**: its units
number exactly three under the `gerku` basis (`CardBasis`, §4.8), and
nothing is said about dogs outside it, so a fourth runner does not
falsify the sentence. **The nuclear predication is neutral** (P4): the
claim is of the witness plurality, and how the dogs satisfy `bajra` —
severally here, since running is lexically distributive-capable, but
jointly for `ci prenu cu jmaji`, where only the three *together*
gather — is the predicate's lexical business; the each-reading is the
marked `Distrib`/`lu'a` form, never an operator smuggled in by the
quantifier. The **global** exact reading — "the dog-runners number
exactly three, and no others" —

```lisp
; ci gerku cu bajra — under the marked global reading
; the marked global strengthening (not the bare-PA default); bajra's
; surface/limbs/gait sites are hoisted outside the comprehension (L0.1)
{Bind [$surface :: Referents Entity] (Context)
      [$limbs :: Referents Entity] (Context)
      [$gait :: Referents Entity] (Context)
  (= (Card (SetOf {λ [$x :: Entity]
              (∧ (gerku $x) (Close (bajra $x $surface $limbs $gait)))})) 3)}
```

is a distinct, stronger meaning, named `GlobalExactly` in the library and
available where a reading commits to it. CLL ch. 16 §6's own account of
bare numeric quantification is both global ("exactly two things, no more
or less", Example 16.34) and singular-variable — "`PA broda` … is
shorthand for `PA da poi broda`" (16.6), which distributes; pin P17
records, as one documented divergence with its argument, that this
specification takes neutral witness-set selection as the default — the
reading dominant in xorlo-era usage, the one that composes with witness
export (§5.6) and termsets, and the only one under which collective
predicates remain expressible beneath quantifiers at all (`su'o prenu cu
jmaji`).

## 5. Dynamics

### 5.1 Model theory

A model supplies a set of worlds W, sorted domains, world-indexed lexical
interpretations, and **information states**: sets of world–assignment
pairs. The dynamic layer is built over one algebraic computation carrier;
Content additionally carries the semantically required clause-event
intension:

```text
Comp<A>    =  InformationState → P( InformationState × A × Obligations )
ContentRun =  Comp<Unit>          RefComp<T> = Comp<T>
ClauseEventIntension
           =  defined world/assignment/precisification/branch index
              ⇀ Referents<Eventuality>
Content    =  ⟨ run : ContentRun, event : ClauseEventIntension ⟩
PerfComp<A> = Comp<A> at the performance level (its effect vocabulary
              adds commitment/performance operations)
Discourse  =  PerfComp<Unit>
Act<F>      =  the pure force-tagged package of §7.1, NOT a
              computation; it enters PerfComp only through Perform
bind       :  Comp<A> × (A → Comp<B>) → Comp<B>   (the carrier's
              sequencing operation — the direct `Bind` form of §5.2
              supplies its scoped continuation)
```

where `Obligations` collects the pending projective commitments
(presupposition conditions, supplement sides with their anchors and
handlers) accumulated but not yet discharged, and information states
additionally carry the discourse-segment structure (the current
segment and the suspended-topic stack) that keyed retrieval (§5.3)
and the §7.2 transitions consult. A computation, run on a
state, yields the possible output states (nondeterminism carries plural
and witness selection — success of *some* branch is success), each with
a returned value and its obligations; lexical truth at a world filters
states; assignment extension is referent introduction; `bind` sequences,
threading state and unioning obligations. `Vague` parameters are **not**
this nondeterminism: a term with `Vague` parameters denotes the *family*
of computations indexed by admissible precisification profiles (§6.5,
VC2–VC3) — formally, the denotation function is profile-indexed,
⟦t⟧π : Comp, with π assigning one admissible precisification to each
`Vague` site (VC3's consistency), and the unindexed ⟦t⟧ abbreviating
the π-family — and truth simpliciter, where invoked, is supertruth
over the family — existential collapse of precisifications into branches would
make one admissible reading's success suffice, which VC1 forbids. Each named operation of this chapter (`Refer`,
`Local`, `Context`, `Vague`, `Presuppose`, `Supplement`, the selections of §5.6,
the connectives' state-passing, §9.3's `StateClause`/`CloseClause`/
`EventOfContent` interface, and §7's performance/realized-content
interface) is an operation of this algebra, and its
clause consists of two parts with two homes: **what escapes and what is
accessible is stated once, in the accessibility table (§5.4)** — nothing
elsewhere may restate it — while return values, truth filtering, and
obligation discharge are fixed by the carrier above and the operation's
own paragraph.

The performance level additionally supplies a semantic transcript of
**act occurrences**. Each execution of `Perform a` creates a fresh
`ActOccurrence<F>` associated with the current transcript token/span and
returns its opaque handle. The model record pairs the reusable act value a with an extensional capture of
that performance's utterance context and contextual resolver. A capture is a
semantic closure, not a trace, cache, or diagnostic record: it is identified
only by the values it supplies to the package's context projections and
`Context` sites at their declared dependency tuples; unrelated resolver
behavior is ignored. For each captured site, this is the original resolver's
**partial function over the site's whole declared dependency domain**, not the
finite graph of tuples that the performed run happened to visit. If later
template reuse reaches a previously unvisited tuple, it consults that captured
partial function: a defined value is reused, while undefinedness projects in
the ordinary way. The caller's resolver is never substituted merely because
the tuple is new. The assertion member of such an occurrence therefore
has a structured Content value interpreted under that capture. Performing the
same a twice creates two occurrences and may yield two realized contents;
neither performance mutates a or changes `(ActContent a)`. Section 7.1 fixes
the performance law and §7.4 exposes only the partial `RealizedContent`
projection needed by Lojban anaphora. The occurrence handle is lowering-only
generic infrastructure: it may be passed as an indicator `Target`, but no term
constructs one except `Perform` or inspects its act, token, or capture.

The displayed `ContentRun` equation is the **run projection** of content. A
conforming Content algebra supplies the clause-event projection
interpreted by `EventOfContent` (§9.3), world- and evaluation-branch-relative
where disjunction branches. (A branch index exists even when its described
event is nonactual; it is not restricted to successful outcomes.) This projection is semantic structure, not
processor bookkeeping: content identity and hence `Reify` identity include
both the dynamic run (including projective/site structure) and this event
intension. `StateClause`, `CloseClause`, and the clause connectives of §4.6
give the projection its laws. `EventOfContent` merely projects the object; it
does not evaluate its Content operand, return `Bool`, or expose syntax.

The eventuality domain contains described eventualities that need not be
actual at the evaluation world. `fasnu e` is the world-relative claim that e
occurs there. Each `State` supplies a partial situation within a world and the
model's verification relation `s ⊩_w c` for c's at-issue facts; this index is
what `StateClause` uses for state-scoped descriptions and value projections.
It is neither a term-level world nor the hypothetical-world shift reserved for
`da'i`. A direct episodic lexical interpretation obeys the occurrence
law

```text
R_w(fills…, e) → fasnu_w(e)
```

at the world in which R is evaluated. Capability operators evaluate their
event properties in capability worlds, so such an event may satisfy `fasnu`
there while failing it at the actual world. A `StateClause c` similarly has
an actual holding-state at a world when that state, at its own temporal/
situational location, verifies c. This does **not** require c to hold at the
utterance time. A temporally invariant equality may make the tense redundant
or pragmatically odd, but a description/value projection scoped inside the
state may vary there (§5.7); the grammar remains typed in either case.
This names, rather than adds, the nonactual-event ontology already required by
`nu'o` (§12).

CLL 10.19 prevents one further overgeneralization: missing CAhA does not force
the actual reading. It is reading-multiple among the four CAhA modes, selected
upstream from context with no default (P24). Thus ordinary episodic `mi citka`
may select the actual mode, while CLL's bare `ro datka cu flulimna` and `ta
jelca` may select capability. Explicit `ca'a` fixes the actual mode and adds
`fasnu` at issue; it is truth-conditionally near-redundant with an already
resolved actual episode but contrasts overtly with the other modes.

The world index supports the intensional facts of §5.7 (de re/de dicto,
opacity) and the subordinated contents of §7.6; **no world variable or
world type appears in the term language**. Counterfactual and hypothetical
mood (`da'i`) is a registered gap (§14) whose future treatment will live
in this index.

**The utterance context** is a typed record:

```text
ctx = ⟨ speaker  : Referents<Entity>,   audience : Referents<Entity>,
        time     : Time,                place    : Location,
        ground   : Ground,
        token    : Referents<UtteranceToken> ⟩

Speaker, Audience : ctx → Referents<Entity>
MiAOthers, MaAOthers, DoOOthers : ctx ⇀ Referents<Entity>
Now : ctx → Time            Here : ctx → Location
CurrentToken : ctx → Referents<UtteranceToken>
Proximity          = Proximal | Medial | Distal   (a closed type)
GroundDescription  : the sort of ground specifications (an orientation
                     center with its perspective facts; `Ground` values
                     are constructed from them)
Deictic       : Proximity × Ground → Referents<Entity>
ShiftedGround : GroundDescription → Ground        (constructs — §6.1)
InContext     : Content × Ground → Content
```

The three “others” projections are partial current-token context values,
nonempty when defined by their output type. They are not mandatory fields on
every utterance context and not an English-pronoun shortcut. Their exact
definedness conditions are the role constraints: `MiAOthers` does not overlap
Speaker, and `Combine Speaker MiAOthers` does not overlap Audience;
`DoOOthers` does not overlap Audience, and `Combine Audience DoOOthers` does
not overlap Speaker; `MaAOthers` does not overlap
`Combine Speaker Audience`. Using the corresponding pro-sumti projects this
definedness in the ordinary §1.7/P21 way. Nothing requires the three
projections to co-refer with one another.

Demonstratives (`This`/`That`/`Yonder`, i.e. `ti`/`ta`/`tu`) are
`Deictic` at the three proximities against the context's ground:
`This ≝ (Deictic Proximal g)`, `That ≝ (Deictic Medial g)`,
`Yonder ≝ (Deictic Distal g)`, with `g` the `ctx` record's ground.
`CurrentToken` is the current entry or compound span (the model value that
surface `dei` binds); it lets `Perform` associate an occurrence without a
global "last act" constant.
For a current entry, the context projections cohere with its transcript facts:
`SpeakerOf(CurrentToken,Speaker)`, `AudienceOf(CurrentToken,Audience)`,
`DeicticTimeOf(CurrentToken,Now)`, and `DeicticPlaceOf(CurrentToken,Here)`
hold (component entries supply the corresponding facts when `CurrentToken` is
a compound span). A conforming current-entry interpretation requires this
coherence; a conflicting transcript description cannot silently override the
occurrence context.

`ShiftedGround` **constructs** a ground (never a contextual resolution),
and `InContext` evaluates content with deictic projections taken from the
given ground — the explicit form of context shift (`ra'o`; §11 L8.7).
`InContext` shifts the utterance **ground** only; it does not change
`CurrentToken`, occurrence identity, or the captured values of an already
realized content. Shifting the *evaluation
world* (hypothetical mood) would be a sibling index-shift operator —
`InContext` is currently the sole member of that family — and awaits the
`da'i` gap entry (§14).

### 5.2 Effectful binding

`{Bind [$x :: T] comp body}` is the direct effectful binding form: it
runs a value-returning `comp : Comp<T>` in its declared computation category
(`RefComp<T>` for reference/context effects, `PerfComp<T>` for performance)
and binds its result for `body`, sequencing
effects left to right. The whole form has the effect join of comp and body:
a `RefComp` may sequence into Content, another reference computation, or a
performance computation, while a `PerfComp` operand requires a
performance-level body and keeps the whole `PerfComp`. Thus no performance
effect can be hidden in Content. Denotationally `Bind` is the computation carrier's
`bind` operation (§5.1) with the body as its continuation. The sequencing is
the eliminator for computation values and cannot be β-reduced away: the computation
may introduce referents, consult context, or project obligations. `Let`
(§4.4) is its pure degenerate case. A multi-binding
`{Bind [$x₁ :: T₁] c₁ [$x₂ :: T₂] c₂ … body}` is left-to-right nesting —
`{Bind [$x₁ :: T₁] c₁ {Bind [$x₂ :: T₂] c₂ …}}` — so later computations
may consume earlier results. The honest gloss: `Bind` is
function application under mandatory call-by-value at computation
types, made visible — the λ-fragment stays pure so that β-equality
holds unconditionally, and every effect-sequencing point is a `Bind`
node the accessibility table can see (rationale §1.14).

`Bind` is **uniform across the computation categories**: `PerfComp` and
`RefComp` use the same carrier algebra as `Content` (§5.1; their effect
vocabularies and admissible result categories differ), and the binding scopes
the returned value over the compatible body. An act is a pure *value* (§7.1), not a
computation: a bare act written as a `Bind` body stands, by §7.1's
display coercion, for the one-act discourse performing it, and a
computation that returns an act package as a value is typed
`RefComp<Act F>` like any other value-returning computation. This is
what lets a description or
selection introduced before an act sequence remain bound across it
(`{Bind [$x :: Referents T] (Refer P) (Do a₁ a₂)}` — the ordinary
spelling of
cross-sentence reference).

`(Local comp) : RefComp<A>` is the reference-level accessibility delimiter.
It runs `comp : RefComp<A>` once and returns the same branch value, preserves
the operand's world filtering, contextual choices, and projective
obligations, but existentially projects from each output information state
exactly the fresh discourse-assignment slots introduced while `comp` ran.
Incoming assignments and all later introductions remain. The returned value
is still available to an enclosing `Bind`; it is simply not an anaphoric
discourse introduction. Any projective obligation emitted inside `comp`
closes over the selected semantic values before projection, so preservation
does not leave a dangling assignment index. Outcomes with the same projected
state but different returned values remain distinct branches for the
continuation. `Local` cannot take a `PerfComp`, hide a performance,
or turn an effectful computation pure.

The principal lowering witness is an internal collection base:

```lisp
{Bind [$base :: Referents T] (Local (Refer P))
  … construct and introduce the one surface group/set from $base …}
```

The hidden base has ordinary non-maximal `Refer` selection and truth
filtering, while only the surface collection survives as a discourse
referent. Without this delimiter `lo'i ratcu` would introduce both rats and
their set, contradicting the `ri` count in CLL Example 6.52. This cross-construction
accessibility job is the factorization argument for the lowering-only generic
form; it is not a renderer or evaluator convenience.

### 5.3 The specificity triad

Three primitive computations answer §1.4:

- `(Refer P) : RefComp<Referents<T>>`, for `P : EFn<(Referents<T>), Content>`
  a property of references (pure `Fn` refines it) — introduces a **new
  discourse referent**: a nonempty, number-neutral plurality satisfying `P`
  veridically, fixed for its force segment, and accessible to later anaphora
  per §5.4. `P`'s effects run under `Refer`, once per candidate witness
  against the incoming state (§5.4). This is the xorlo semantics of
  descriptions (ruling P1): no implicit outer quantifier, no uniqueness,
  no default cardinality.

  **Member-level restrictors.** A restrictor written over the member sort,
  `Q : Fn<(T), Content>`, is admitted only through the defined **lift**
  `(Refer Q) ≝ (Refer {λ [$r :: Referents T] (CoveredBy Q $r)})` — every
  unit of the referent satisfies `Q` and no subreference escapes `Q`'s units
  (§4.8): P39's lexical equation and `MaxRefer`'s pattern (§12), stated once
  for every member property, lexical or not (L3.6's `CompleteGunmaAt κ g
  base` included). The lift is a purity-demanding position (§3.3): a member
  property whose formation needs contextual sites has them bound outside the
  `Refer` and shared by the hoisting rule L0.1 (§11) — and an effectful
  member-level restrictor is not a term. A
  member-level λ therefore always displays a *unit* property; a row whose
  plural satisfaction is collective, kind-like, or substance-like is written
  at reference level with its own lexical extension (§10, P39). The
  singleton-only, some-member, `Distrib`-only, and reference-level-only
  readings are the rejected lifts (rationale §1.7b).
- `(Context P? deps…) : RefComp<T>` — retrieves a contextually salient
  value of type `T`, constrained by an optional pure admissibility property
  `P : Fn<(T), Content>` and by its declared dependencies (the governing
  binder values with which this occurrence may covary). The unconstrained,
  dependency-free spelling is `(Context)`; a constrained site is written
  `(Context P deps…)`. It asserts nothing and introduces nothing. The speaker
  has one intended value at the occurrence, while successful communication
  requires only recovery to relevance-equivalence for the discourse purpose.
  The resolved core term nevertheless contains one exact returned value; the
  pragmatic tolerance is not an object-language equivalence relation or a
  family of semantic branches. Failure is graded in conversation, with repair
  possible; only failure to recover any discourse-sufficient value leaves the
  text without that resolved reading.

  A resolved reading declares the dependency profile explicitly: a site may
  covary only with the listed binders and never inherits every enclosing
  governor automatically. Thus a `tu'a` under `ro prenu` may be governor-
  invariant (empty profile) or person-dependent (the person listed), according
  to the resolved reading. As a formation condition, every variable bound
  outside the site and occurring free in `P` must appear in `deps…`; omitting
  such a variable does not create an invariant reading but an ill-formed term.
  Extra dependencies are permitted when the intended value may covary even
  though the admissibility property does not mention the governor.
  **Site/key identity:** each syntactic occurrence
  is one site; it retrieves once per distinct dependency tuple per performance
  (once total for an empty profile), so re-applications of a shared λ reuse the
  value exactly when their listed dependencies agree. Keyed uses (unassigned KOhA,
  ruling P16) retrieve once per key per discourse segment, every
  occurrence of the key consuming the same value. Site keys are assigned
  by direct term formation, invariant under α-renaming and independent of
  bound-variable spelling. Copying a written occurrence creates a new
  site; sharing one term through `λ` or `Let` preserves it. Resolution
  never rekeys a formed term.
- `(Vague P) : RefComp<T>` — denotes the nonempty set of **admissible
  soritical precisifications** of type `T` satisfying the constraint `P`, with
  no fact of the matter fixing one boundary. Formation is licensed only when
  `P` is declared to structure sharpenings of one soritical concept; an
  arbitrary family of discrete alternatives is not a `Vague` domain.
  Composition law: precisification sets
  lift pointwise through all operators, and a complete interpretation
  chooses one precisification per parameter per binding site,
  consistently; truth simpliciter, where needed, is supertruth over
  admissible choices. The term never chooses.

### 5.4 The accessibility table

The table below is normative: it states, per operator, what each operand's
computation may see and what survives the whole. "Introductions" are
discourse referents from `Refer`, quantifier witnesses (§5.6), and token
binders (§7.4).

| Form | Dynamic rule |
|---|---|
| `∧`, `Do` | Left to right; each operand sees all preceding successful introductions; introductions of both survive. Facet conjunctions over a shared event (tense/modal joining, §11 L6.2) are ordinary `∧`. |
| `∨` | Operands each see the incoming state; branch-local introductions do not escape the disjunction. |
| `¬` | Operand sees the incoming state; nothing escapes. |
| `→` | Antecedent sees the incoming state; consequent sees the antecedent's successful introductions; nothing escapes the conditional. The joint-locus reading selection of §5.6 applies when the resolved reading binds a consequent anaphor to an antecedent introduction. |
| `↔`, `⊕` | Each operand evaluated exactly once against the incoming state; nothing escapes. (Hence primitive: rewrites would duplicate evaluation.) |
| `∃`, `∀`, GQs | The restrictor is pure (`Fn`); body introductions are local to each instantiation. **Witness export:** a successful evaluation of an exporting quantifier introduces its witness referent(s) — see §5.6, including the dependent case. |
| `Refer` | Introduces its referent into the current force segment; fixed there (no re-selection under `¬` or across facets). Its restrictor's effects run against the incoming state, once per candidate witness; introductions made inside the restrictor survive with the referent (as under `∧`) unless a `Local` encloses the `Refer`, which projects them with the base (§5.2). The member-level lift (§5.3) is pure and introduces nothing. |
| `Local` | Its operand sees the incoming state and runs normally; only discourse-assignment slots freshly introduced by that operand are projected from its output. Truth filtering, returned values, contextual resolution, and projective obligations survive. |
| `Context` | Consults the incoming context and introduces nothing. Logical embedding never turns retrieval into quantification over admissible values: site/dependency identity is exactly §5.3's, while the consuming content—not the recovered value—is negated, questioned, or connected. |
| `StateClause`, `CloseClause` | Applying `StateClause c` evaluates c exactly once on its one matching holding-state lineage; c's ordinary introductions and projectives obey their own rows. `CloseClause` keeps its event witness local: the witness is recoverable through `EventOfContent` but is not a discourse introduction. |
| `Presuppose` | See §5.5: the condition projects to the nearest legal commitment boundary; the at-issue operand sees the incoming state. Introductions inside the condition are local to the condition check; nothing escapes from it. |
| `Supplement` | See §5.5: side content is committed once at its handler, projectively; the at-issue operand's value passes through. |
| Force constructors, `Perform` | Constructing an act is inert. Each `Perform` takes a fresh occurrence capture, associates the occurrence with `CurrentToken`, runs that occurrence's force payload, and returns only its opaque handle; act boundaries close force segments. Binding the handle introduces no discourse referent and exposes no capture. Referents introduced inside a constructed-but-unperformed act are not accessible outside it; performed acts in `Do` chain normally. Re-performing one act creates a new occurrence and a new per-performance resolution, never a mutation of the act package. |
| `ActContent`, `RealizedAct`, `RealizedContent`, `RealizedDiscourse` | Inert projections: they introduce nothing and run no projected payload. `ActContent` returns the raw package. The `Realized*` definedness conditions project; `RealizedContent` returns the selected occurrence's captured Content, not a re-evaluation in the caller's context. |
| Quotation, `Reify`, `EventOfContent` | Opaque/inert at construction: nothing crosses a sign boundary; `Reify` and `EventOfContent` run no Content operand, so no introduction, retrieval, or obligation occurs at either projection site. `Holds` (§9.1) evaluates represented content at its own occurrence, governed by the surrounding operators — never retroactively by `Reify` or the event projection. |

### 5.5 Projective content

`(Presuppose π body)` imposes `π` as a projective condition: it must hold
at the nearest boundary that can commit it (accommodating contexts may add
it), and it survives `¬`, `∨`, `→`, and question force. Its type is
polymorphic over the computation categories —
`Presuppose : Content × Comp<A> → Comp<A>`: the condition is content,
the body any computation (§12's `MaxRefer` uses it at a reference
computation). It is the mechanism of quantifier import (ruling P2), definedness of partial
operations (§1.7), and lexically triggered presuppositions.

`(Supplement anchor side body)` contributes `side` as a **non-at-issue
commitment about `anchor`** while the at-issue value is `body`'s. The side
commitment projects: under negation only `body` is negated, under question
force only `body` is questioned. A supplement whose `side` depends on a
quantifier-bound variable attaches at a handler inside that binder —
committed per instantiation, projective to that scope's top (ruling P7).
`noi`, parentheticals (`sei`, `to…toi`), and non-restrictive material
generally land here. Presuppositions may be satisfied or accommodated;
supplements are always new commitments — the two are not interchangeable.

### 5.6 Quantifier witnesses, donkey configurations, anaphora

**Selections and witness export.** Quantified terms whose witnesses can
be referred back to are built from **selection computations** — the
quantifier-strength members of the `Refer` family:

```text
SelectExactly n P : RefComp<Referents<T>>   ; an n-unit witness set of P
SelectAtLeast n P : RefComp<Referents<T>>   ; ditto, at least n
SelectSome P      ≝ SelectAtLeast 1 P       ; ≥ 1 (su'o) — defined
```

(restrictor `P` pure). The witness laws: a selection's witness `w`
satisfies `(CoveredBy P w)` and `(= (CardBasis w P) n)` (`SelectExactly`)
or `(≤ n (CardBasis w P))` (`SelectAtLeast`); and the **dependence
law**: under governing binders, a selection introduces one witness per
value of the governors (where `Refer` introduces a single
governor-invariant constant — the §5.6 boundary note below). A
selection introduces its witness reference —
explicitly bound by `Bind`, like every computation — and the nuclear
content then predicates of it:

```lisp
; ci gerku cu bajra .i ri tatpi
{Bind [$dogs :: Referents Entity]
        (SelectExactly 3 {λ [$x :: Entity] (gerku $x)})
  (Do (Assert (Close (bajra $dogs)))
      (Assert (Close (tatpi $dogs))))}
```

The library's GQ forms (`Exactly`, `AtLeast`, `Some`, … — §12) are
defined over selections; forms whose success is grounded in absence or an
upper bound (`No`, `AtMost`, `FewerThan`) select nothing and export
nothing. `Every` exports the full restrictor reference. Binding a witness
never re-evaluates a selection; distinct selections introduce
**distinct discourse referents** (introduction identity — their
witness *values* may still co-refer); and a witness is accessible exactly where the accessibility
table lets its `Bind` scope reach (so nothing here is a free-variable
convention — the binder is visible in the term).

**Dependent witnesses.** A selection in the scope of a quantifier is a
*dependent* selection — one witness per value of each governing binder.
The compositional table does not export that witness beyond its governor, so
an outside anaphor is otherwise inaccessible. For the supported strong
anaphoric reading, the resolver selects a joint-locus construal and the
mapping lowers **that reading** one level up: the selection and governor form
a joint locus, both restrictions form the antecedent (with the description
quantifier's import preserved — the `Presuppose` wrapper carries over), and
the anaphor's content joins the consequent — **conjoined with the governing
sentence's own assertion, which the selected lowering must not erase**: the
first sentence claimed the ownership, and a conditional alone would be
vacuously true of a dogless person. Fixture: `ro prenu cu ponse ci
gerku .i ri tatpi` has the selected strong lowering

```lisp
; truth-condition artifact for the two Host occurrences
(Presuppose (∃ {λ [$x :: Entity] (prenu $x)})
  (∧
    ; sentence 1's claim; preserved:
    (∀ {λ [$p :: Entity]
      (→ (prenu $p)
         (∃ {λ [$d :: Referents Entity]
           (∧ (Distrib {λ [$x :: Entity] (gerku $x)} $d)
              (= (CardBasis $d {λ [$x :: Entity] (gerku $x)}) 3)
              (Close (ponse $p $d)))}))})
    ; the anaphoric continuation; at the joint locus (strong reading):
    (∀ {λ [[$p :: Entity] [$d :: Referents Entity]]
      (→ (∧ (prenu $p)
            (Distrib {λ [$x :: Entity] (gerku $x)} $d)
            (= (CardBasis $d {λ [$x :: Entity] (gerku $x)}) 3)
            (Close (ponse $p $d)))
         (Close (tatpi $d)))})))
```

The display is the strong reading's truth-condition artifact, not its force
packaging: the two `.i`-separated sentences remain two `Host` occurrences.
The selected cross-sentence constraint must not collapse their act/token
identity.

— each person owns three dogs, and each person's dogs are tired; no
single plural of all dogs is asserted,
and the summation reading is expressible only by explicit collection,
never automatic. This strong joint-locus term is **not** an
equivalence-preserving rewrite of the original selection computation: a model
may offer two qualifying dog witnesses, only one tired, so the computation can
succeed through that witness while the universal joint-locus term is false.
The cost of the current reading selection is therefore retroactive
strengthening: sentence one's construal depends on the later anaphor. Section
14 records plural-information states as the principled model upgrade and the
weak selected-witness alternative as rejected absent a Lojban surface
selector. Two boundary notes: an embedded xorlo *description*
(`ro prenu cu bevri lo pipno`) is a referential constant shared across the
governor's values, not a dependent witness — only genuinely
quantificational selections depend; and anaphora to a witness that does
not escape its governor is simply inaccessible — a reading the table
correctly refuses.

**Donkey reading selection** (ruling P6). When the resolved strong reading
binds an anaphor to an introduction made inside a restrictor (`ro prenu poi
ponse su'o xasli cu darxi ri`), that reading lowers to the governing quantifier's joint
multi-parameter locus, with the description's import preserved and the
indefinite's variable at the plural type (its witness is a plural
reference; the atomic-pair spelling is the distributive strengthening):

```lisp
(Presuppose (∃ {λ [$x :: Entity] (∧ (prenu $x)
              (∃ {λ [$y :: Entity] (∧ (xasli $y) (Close (ponse $x $y)))}))})
  (∀ {λ [[$p :: Entity] [$d :: Referents Entity]]
    (→ (∧ (prenu $p)
          (Distrib {λ [$z :: Entity] (xasli $z)} $d)
          (Close (ponse $p $d)))
       (Close (darxi $p $d)))}))
```

(The `Distrib` conjunct restores the indefinite selection's own
witness law — the joint locus quantifies exactly the donkey-witness
pluralities, not references with non-donkey residue.) The
restrictor's relational conjunct ties the parameters; no E-type
description or choice function is invoked. Bare mathematical `ro da`
uses the same selected joint locus without the `Presuppose` — the import belongs to description
quantifiers only (pin P2). Configurations beyond the supported fragment
(anaphora out of disjunctive restrictors, stacked indefinites with split
anaphora) are gap-registered.

**Anaphora generally** (ruling P16): the calculus sees bindings. `ri`,
`ra`, `ru`, `vo'a`-series, `ke'a`, and `go'i`-family resolution — CLL
ch. 7's counting discipline applied over the *accessible* referents of
this chapter — are text-to-reading rules in the mapping annex. `goi`
assignment is discourse-scoped binding; an unassigned KOhA is a keyed
`Context` (one retrieval per key, §5.3).

### 5.7 De re, de dicto, opacity

A lexical place is marked in the lexicon as extensional, intensional, or
opaque (§10). Reference placement does the rest: a `Refer` bound inside an
intensional argument is de dicto (evaluated at the attitude's worlds); a
binder placed outside is de re; opaque places (quotation-like) admit no
external binding at all. `mi djica lo nu mi pilno lo karce` receives both
readings by binder placement alone; no world variables appear (§5.1). The
lexicon's marks plus the world-indexed model are jointly what make the
distinction denotational rather than merely structural.

`StateClause` adds the analogous situation boundary. A description or
state-sensitive value projection formed **inside** its Content operand is
evaluated relative to the holding state; a value bound outside is de re and
stays fixed. Purity means “no dynamic effects,” not “rigid across states.”
Thus a physical quantity's value can equal X in a current state and differ in
a future or distant state when its value description/projection is scoped
inside each `StateClause`. If the compared operands are rigidly bound outside,
binary `=` correctly cannot change. Numeric constants and the arithmetic
operations themselves are rigid; variation belongs to the state-sensitive
quantity/value interface, not to addition or identity.

### 5.8 Genericity

`(Generic mode holder? restrictor nuclear) : Content`, with
`mode ∈ ⟨Typical, Stereotypical⟩` and `holder` present exactly for the
stereotype reading (`le'e`: the Speaker, grammatically fixed), is the
axiomatic generic quantifier — restrictor `Fn<(T), Content>` and
nuclear scope `EFn<(T), Content>`, both member-level like the library
GQ restrictors (§12): it relates the pure restrictor and nuclear
scope through a normality ordering **that may depend on the nuclear
predicate**. It is not `∀`, not `∃`, and yields no referent: `lo'e cinfo
cu se kerfa lo clani` and `lo'e cinfo cu jbena lo cinfo` are supported by
different normality classes (adult males; adult females), which is why no
fixed "typical lion" reference exists to verify both. Generic anaphora
(`lo'e mlatu … .i ri …`) is gap-registered. The operator is frankly
axiomatic — its normality structure is constrained, not defined; the
rationale records why this honesty beats both a fixed-prototype reference
and a silent lexical relation.

## 6. Intended underspecification and soritical vagueness

### 6.1 The recovery test and the classification

The decision rule for §5.3's triad, applied to every underspecified
construct in Lojban:

> **The recovery test.** If the speaker has an occurrence-specific intended
> value, the construct is `Context`: a cooperative hearer is expected to
> recover a value equivalent enough for the discourse purpose. Exact
> intersubjective identity is not required, and misunderstanding or repair is
> graded and pragmatic. If there is instead one soritical concept whose cutoff
> has no fact of the matter, the construct is `Vague`. If the meaning simply
> lacks the dimension, it is **absence** (§1.4) and gets no machinery at all.

The normative classification:

| Construct | Class | Notes |
|---|---|---|
| omitted places, `zo'e` | `Context` | one distinct site per omission (P15) |
| `co'e` (elliptical selbri), `do'e` (elliptical tag) | `Context` | the ellipsis family conveys an intended relation/tag; no baseline no-particular-value reading is generated |
| `zu'i` | `Context` | with a typicality constraint |
| deictic grounds; demonstrative grounds | `Context` | `ShiftedGround` values are constructed, never resolved |
| scale or `ContrastDomain` of gradable/scalar predication | `Context` | which dimension/universe (beauty, price, relevant alternatives) is intended and recoverable |
| soritical **cutoffs/regions** on a scale | `Vague` | includes `no'e`'s neutral-region width, riding a `Context` scale |
| loose temporal/spatial extent or span boundary | `Vague` | ZI/ZEhA magnitudes, ROI's default interval extent, and `do'i` token-span edges (P28/P35) |
| tanru modification link | constrained `Context` | one intended admissible link per occurrence; convention supplies resolver priors, not lexicalization |
| `tu'a` | constrained `Context` | intended host-sorted abstraction; shape + `srana`-aboutness constrain recovery (P14) |
| topic `zo'u` link | constrained `Context` | one intended place fill or coarse `About` value for a single-bridi comment (P26); compound place-linking is a gap |
| constitution-bearing `joi` loci | constrained `Context` basis + typed constitution | group/event/property instances select one intended declared basis; missing property instances, `pe'e joi`, `joi nai`, and compound performance are bounded gaps (§14) |
| vague-quantity thresholds (`so'i`, `so'e`, …; `ji'i` tolerance) | `Vague` | sorites: no fact fixes the boundary |
| `du'e` / `mo'a` / `rau` | `Vague` threshold **constrained by** a `Context` standard/purpose | two parameters; the purpose is recoverable, the boundary is not |
| `na'i`'s defect dimension | `Context` | the hearer is expected to see what is defective |
| bare `jai` (no tag) | constrained `Context` | retrieves the intended admissible raised-role relation at `Fn<(Referents<T>, Referents<A>), Content>`, with raised sort T and old-x1 sort A fixed by the resolved reading; `jai`+tag specifies the role exactly (P14) |
| bare-`kau` exhaustivity; unmarked distributivity | **absence** | no hole, no parameter (P9, P4) |
| tenselessness | reading-multiple (P8) | episodic readings carry a `Context` time; habitual/gnomic readings carry nothing; never a default — the reading is chosen upstream |

A `Vague` formation in the analyzed baseline must be licensed by one of the
three families represented above (cutoff/region, loose extent/span, or vague
quantity/approximation), together with the corresponding library predicate.
Merely exhibiting a nonempty family of alternatives is insufficient.

A coarse intention is still an intention: topic `About` and scalar
`OtherThan` need not hide a finer selected relation. The baseline therefore
contains no `SomeAdmissible` computation. Its existential-choice shape is
recorded in §14 solely as a reopening path if evidence finds a construction
whose speaker genuinely intends no particular discrete value.

### 6.2 Tanru

`(Tanru M H) : PredTerm (RowOf H)` — modification of head `H` by modifier
`M`; a **defined** operator, the expansion below being its definition
(only `TanruAdmissible` inside it is primitive).
The result's row is the head's row (CLL ch. 5: the tanru's places are the
tertau's). Its semantics: the head predication holds, and an admissible
modification link relates `M` to that predication —

```lisp
((Tanru M H) fills…) ≝
{Bind [$link :: PredTerm (RowOf H)]
        (Context
          {λ [$r :: PredTerm (RowOf H)] (TanruAdmissible M H $r)}
          deps…)
  (∧ (H fills…) ($link fills…)) }
```

Here `deps…` is the dependency profile declared by the resolved reading; it
may be empty and never defaults to all enclosing binders. One occurrence
retrieves one intended link. A listener need only recover a link equivalent
enough for the discourse purpose, but negation and questioning operate on that
one recovered link—not existentially over every admissible relation.

`TanruAdmissible` is part of tanru's meaning, not a lookup: it requires
that the link make `M` modify *something* in the head predication (the
event's manner, a participant, a purpose, a source, …) and nothing
stronger — no x1-sharing, no intersectivity. The library's named links are
common exact recoveries; a lujvo lexicalizes a link.

Surface grouping (`bo`, `ke…ke'e`) and inversion (`co`) are ⊳
text-to-reading: `A co B` ≡ `ke B ke'e A`, with any trailing sumti
routed to the seltau's places as `be`-fills — hence invisible to
`vo'a`/`go'i`, which see only bridi places (CLL 5.8); multiple `co`
right-group. Jek-connected units lower through `TanruLinkConnect`
(§12, pin P33).

The gismu `tanru` is this operator's shadow relation (§16.5), and an
exact one: its official x4 ("giving meaning ⟨4⟩") and x5 ("in
usage/instance ⟨5⟩") places support an occasion-specific intended meaning,
rather than a fixed lexical link or a no-fact-of-the-matter family. Its
operand places are officially typed "both text or both si'o concept" — inert
operands in the program's sense (§16.2).

### 6.3 Scalar operators

`ContrastDomain ρ` is the typed interface of relevant alternatives for a
predicate row ρ: it supplies the universe against which a predicate's region
is interpreted and, optionally, polarity and betweenness structure. It is a
declared domain former with region/membership laws, not a first-order set or a
`Group (PredTerm ρ)` object. The applicable domain is lexically fixed where the
dictionary provides one and otherwise recovered by constrained `Context`.
Soritical boundaries inside its regions remain `Vague` per §6.1.

More exactly, `ContrastRegion ρ` is the associated region type. Each model's
interpretation of a value `D : ContrastDomain ρ` supplies the following
*semantic-interface* operations; the subscripted notation here is
metalanguage, not additional core syntax:

```text
universe_D(r)        : Content                         (r : Record ρ)
cell_D(P)            : ContrastRegion ρ                (P : PredTerm ρ)
member_D(r, A)       : Content                         (A : ContrastRegion ρ)
complement_D(A)      : ContrastRegion ρ
opposite_D(A)        : ContrastRegion ρ                 (partial)
between_D(A)         : ContrastRegion ρ                 (partial)
```

It obeys, for every record `r`, predicate `P`, and region `A`,

```text
member_D(r, cell_D(P))       ↔ (universe_D(r) ∧ P(r))
member_D(r, complement_D(A)) ↔ (universe_D(r) ∧ ¬ member_D(r, A))
```

and, whenever the optional operations are defined, their regions are
contained in `complement_D(A)`. On a declared polar pair, opposite is
involutive extensionally, the between-region is pole-symmetric, and it is
separate from the opposite pole:

```text
member_D(r, opposite_D(A))            → member_D(r, complement_D(A))
member_D(r, between_D(A))             → member_D(r, complement_D(A))
member_D(r, between_D(A))             → ¬ member_D(r, opposite_D(A))
member_D(r, opposite_D(opposite_D(A))) ↔ member_D(r, A)
member_D(r, between_D(A))              ↔ member_D(r, between_D(opposite_D(A)))
```

These are membership laws; the core neither assumes nor needs equality at
`ContrastRegion ρ`.

`OtherThan` therefore needs neither an ordering nor a partition into fine
alternatives. `Opposite` requires the polarity operation and `Neutral` the
betweenness operation; absence of the required operation is a projective
definedness condition under §4.9.

`(Scalar k D P) : PredTerm ρ`, for `D : ContrastDomain ρ` and
`k ∈ ⟨OtherThan, Opposite, Neutral⟩`, is the `na'e`/`to'e`/`no'e`
family. The Lojban mapping binds a lexically fixed or constrained-`Context`
domain before applying `Scalar`, so the retrieval site and dependencies stay
visible. Its denotation at a complete record `r` is fixed by

```text
(Scalar OtherThan D P)(r) ↔ member_D(r, complement_D(cell_D(P)))
(Scalar Opposite  D P)(r) ↔ member_D(r, opposite_D(cell_D(P)))
(Scalar Neutral   D P)(r) ↔ member_D(r, between_D(cell_D(P)))
```

Thus each operator **denies `P`'s stated region and positively asserts a
directly denoted contrasting region** — CLL 15.4: a selbri negation
"asserts that a relationship exists other than that stated", and "the
result of `na'e` negation remains an assertion of some specific truth" —
so all three entail `¬P` at the stated region. In the denotational
metalanguage, `OtherThan` is the recovered domain minus `P`'s region; this
complement remains well-defined when fine alternatives overlap and requires no
partition or hidden selected alternative. `Opposite` denotes the antipodal
region and is projectively undefined where the domain supplies no polarity;
`Neutral` denotes the between-region and is likewise partial where no
betweenness structure exists. Scalar negation is therefore *stronger* than
`¬`, not weaker: `ta na'e melbi` denies beauty and directly asserts location
in the other-than-beautiful region of the intended aesthetic domain. The
`Opposite` operator doubles as the documented fallback for indicator
polarity where the lexicon names no `nai`-pole (§7.6; CLL 15.7 applies
scalar negation's opposite-end rule to indicators).

### 6.4 Gradable predication and vague quantities

Gradable predication exposes its two parameters through the library's
`Grade` schema:

```text
Grade : GradableRel ρ ℓ × Scale × Region Scale → PredTerm ρ
```

with the scale obtained by `Context` when not lexical (which dimension —
size, price, beauty — is recoverable) and the region boundary by `Vague`
(no fact fixes the cutoff). `ta barda` is `Grade(barda, Context-scale,
Vague-region)` applied. A gradable lexical entry may derive its
`ContrastDomain` interpretation from that scale, but the domain and scale are
distinct typed values and there is no implicit crossing between them.

The degree quantifiers (`Many`, `Few`, `TooMany`, `TooFew`, `Enough`,
`Most`; §12) are cardinal comparisons against thresholds whose
admissibility predicates are declared with them (§12), each with an
axiomatic nonemptiness clause discharging VC1: the threshold is `Vague`,
and for the purpose-relative kinds (`du'e`/`mo'a`/`rau`) it is
constrained by a `Context`-recovered standard/purpose. The
region-admissibility predicate for gradables (`AdmissibleCutoff`, §12)
carries the same nonemptiness clause. `ji'i n` is `Vague` tolerance about
a stated `n` — a different shape from `so'i`'s vague threshold. None of
these rounds to an exact number, and none fails: `so'i prenu cu klama`
has exactly the truth conditions its vagueness permits — the family of
precisified denotations over admissible thresholds (§5.3, §6.5).

### 6.5 The composition law for `Vague`

Normative, and complete — no operator interacts with precisification sets
in any way not stated here:

- **VC1 (Denotation).** A `Vague` computation denotes the nonempty set of
  its admissible soritical precisifications and no choice among them; a reading
  containing a `Vague` parameter denotes the family of precisified
  denotations. Nonemptiness is a **static proof obligation of the formation
  judgment**: `(Vague P)` is well-formed at `A` only under a discharged
  judgment `⊢ ∃a:A. P(a)` — supplied by the construct's definition (the
  library's admissibility predicates are defined nonempty) or by the
  mapping when it introduces the parameter. The formation evidence must also
  establish that `P` describes ordered or overlapping sharpenings of one
  soritical concept rather than unrelated discrete alternatives; an empty
  admissibility set is
  thereby a failure to form the term, never an evaluation outcome.
- **VC2 (Pointwise lifting).** Every operator — application, `Bind`, the
  logical operators, quantifiers, force constructors, question formers,
  abstraction crossings — lifts pointwise over precisification sets.
  `na so'i prenu cu klama` denotes the family, over admissible thresholds
  t, of "not more than t people go"; an act built from vague content is a
  family of acts; a question over a vague domain ranges over precisified
  alternatives.
- **VC3 (Consistency).** One precisification per parameter per binding
  site: occurrences of one parameter under one binder take the same
  precisification; occurrences under distinct binders are independent;
  distinct parameters are independent unless identity is expressed. (The
  `Vague` analogue of `Context`'s site/key identity, §5.3 — the spec
  states them adjacently on purpose.)
- **VC4 (Effects ride the lift).** Presupposition triggers and supplement
  sides emitted under a `Vague` parameter lift pointwise with their
  content; handler placement is a fact about term structure, never about
  the precisification choice.
- **VC5 (No resolution).** A `Vague` parameter is never resolved by
  `Context` and never coerced inside the core. A reading that fixes a
  soritical boundary says so explicitly, with an exact value that itself
  passes the recovery test. Intended but underspecified discrete values use
  constrained `Context`; a genuinely no-particular-value discrete use has no
  baseline former (§14); absence of the dimension is nothing at all (§1.4).

## 7. Speech acts and discourse

### 7.1 Acts and forces

Force constructors turn content into first-class acts:

```text
Assert  : Content → Act<Assertion>      Ask      : Query<A> → Act<Question>
Command : Referents<Entity> × Content → Act<Directive>
Express : Content → Act<Expressive>     Vocative : Referents<Entity> → Act<Address>
Mention : T → Act<Expressive>           (use/mention: displays a value)
```

Constructing an act does not perform it. The typing discipline:

```text
Perform : OccurrenceRole × Act<F> → PerfComp<ActOccurrence<F>>
Do      : Discourse × Discourse × … → Discourse
          (flattening, associative; zero operands = empty discourse)
```

Unary `(Perform a)` is the defined Host shorthand
`(Perform Host a)`. Attached display/address lowerings write their roles
explicitly; role is therefore part of the core term, never remembered from
surface provenance.

Denotationally, an `Act<F>` value is a **force-tagged content package**:
the force `F` together with the content computation (for `Ask`, the
query; for `Command`/`Vocative`, the addressee too), constructed
inertly — building it runs nothing. In particular, context projections such
as `Speaker`/`Now` and written `Context` sites inside the payload are not
consulted by the force constructor; they are interpreted under a `Perform`
occurrence's capture. `Perform` injects the package into
the performance level: the content's computation runs there with `F`'s
commitment effects (assertion commits, question raises, and so on). Act
identity is term identity — acts compared, quoted, or anaphorically
targeted are the `Let`-bound values the terms visibly share.

Performance does not add captured values to that identity. At the model
level, each execution creates

```text
ActOccurrence<F> = ⟨ act     : Act<F>,
                     token   : Referents<UtteranceToken>,
                     role    : Host | AttachedDisplay | AttachedAddress,
                     capture : the extensional occurrence environment ⟩
```

where token is `CurrentToken` and capture fixes this performance's utterance
context projections and `Context` resolver (including dependency-sensitive
site values) for the package. For an assertion occurrence, interpreting the
raw `(ActContent act)` under capture yields its **realized Content**. This is a
semantic closure: creating or projecting it runs no content, and calling it
later cannot substitute the caller's speaker, time, ground, or contextual
answers. `Vague` remains the same profile-indexed family — capture does not
choose a sharpening — and dynamic `Refer`/selection outcomes are not silently
frozen. A referent meant to survive into a reusable act remains visibly bound
outside that act, as the mapping and samples already require.

The transcript role is semantic because it determines attachment and partial
projection: the ordinary performed clause is `Host`; a UI/COI/vocative act
introduced beside it is `AttachedDisplay`/`AttachedAddress`; a future
compound plan still has one `Host` occurrence — its constructed component
acts are not occurrences merely because component spans realize them.
`RealizedContent` selects the `Host`, never an attached display merely because
it shares the token. `RealizedAct` may independently select a raw component
package through transcript structure; #6 owns any component-content projection
inside the one compound occurrence. The surface-to-discourse mapping supplies
the explicit `OccurrenceRole`; no term inspects it after `Perform` constructs
the occurrence.
A standalone display, COI, or vocative utterance has no distinct host to
attach to and is therefore its entry's `Host`; `AttachedDisplay` and
`AttachedAddress` are used only beside another Host occurrence.

`Perform` first creates the occurrence/capture, then runs that captured
payload, handles its presuppositions and supplements, and only then applies
the force update on each surviving lineage; its ordinary result is the same
opaque occurrence handle for a `Bind` continuation. This fixes relative
phasing without deciding #11's branch/Undef, occurrence-only continuation,
and accommodation policies. An uttered but contextually uninterpretable
act can therefore have a performance occurrence while lacking a defined
realized Content. Two executions of one act value always create distinct
occurrences, even when their captures happen to agree. Capture has no
object-language inspector, and `ActOccurrence` has no pure constructor:
only `Perform` effectfully produces a handle, which may be `Bind`-bound and
passed as a `Target`. They factor performance identity and support the token projection
of §7.4 without exposing evaluator state.

The occurrence association entails the transcript fact
`(Realizes CurrentToken a)`. The converse is deliberately false: a pure
quoted/transcript-description `Realizes` fact can name a package without any
`Perform` or occurrence. This one-way law is what lets `RealizedAct` serve
both descriptions while `RealizedContent` remains performance-only.

At a `Discourse` position, a value-returning performance computation p is
notation for monadic discard,
`{Bind [$ignored :: T] p (Do)}`; the empty `Do` is the performance unit.
Thus all existing `(Do (Perform a) …)` and bare-act spellings remain concise.
Where the occurrence matters — notably an act-level indicator — the lowering
instead writes `{Bind [$o :: ActOccurrence F] (Perform Host a) body}` and targets
`$o`. This is an exact expansion, not a mutable "last occurrence" lookup.

A document denotes one `Discourse`, whose top-level `Do` sequence is
called the **spine**; an `Act` written directly in a `Do` operand —
or anywhere a `Discourse` is required, a `Bind` body included — is
notation for its `Perform` (the coercion is notational, §2, never
semantic), and a specimen displayed as a bare act denotes the one-act
discourse performing it. `Do` sequences with the `∧`-row's accessibility. `Discourse`
never embeds where `Content` is required — in particular never under
`Reify`. Reported speech mentions constructed acts (`mi cusku lu ko klama
li'u` describes a directive without issuing it); only `Perform` executes.

### 7.2 Discourse structure

`NewTopic, Resume : Discourse → Discourse` are the `ni'o`/`no'i`
transitions — discourse-structural operations with no truth
conditions but with stated effects on the **segment structure** the
information state carries (§5.1): a state holds the current discourse
segment and a stack of suspended ones. `NewTopic` suspends the
current segment onto the stack and opens a fresh one — keyed
`Context` retrievals (§5.3) are per-segment, so keys re-retrieve
after it, and the segment-bounded ⊳ rules (`ki` stickiness, `go'i`
reach) reset — while `Resume` pops the most recently suspended
segment and reopens it for keyed retrieval. NIhO depth grades the
reset (CLL 19.3): the assignment-clearing level — `ni'o` spoken,
`ni'o ni'o` written — clears the resolver's assignment stores with
the new segment (the ⊳ face of `da'o`), and the next level up
(CLL's "drastic change") additionally resets tenses and indicators;
further depth marks larger topic scale only. `no'i` resumes what its
`ni'o` dropped — assignments and, at the drastic level, tense — along
with the suspended segment. The spoken/written level shift is ⊳
text-to-reading. Discourse
*relations* (contrast `ku'i`, addition `ji'a`, parallel `si'a`,
elaboration `no'u`, …) are library relations over occurrence handles by
default, because they relate performed discourse positions rather than every
performance of a reusable package. Prior/current occurrences are ordinary
`Bind`-bound results of `Perform` (no prior/following-discourse constants
exist); a metalinguistic relation about a raw act can still target its
`Let`-bound package explicitly. Constituent-level additive/exclusive focus (`ji'a` on a
sumti, `po'o`) derives via `Presuppose` over alternatives (§12).

### 7.3 Metalinguistic rejection

`na'i` is a derived discourse act: an objection targeting a prior
utterance token or performed occurrence by default (a raw act package may be
chosen explicitly), predicating a defect whose dimension is a `Context`
parameter (§6.1), with the objected content not performed. It is neither
`¬` (no truth-conditional negation occurs) nor `Scalar` (no scale is
invoked); the three-way `na`/`na'e`/`na'i` contrast is thereby three
different operators.

### 7.4 Utterance tokens

`(Utterance {$u :: UtteranceToken} {fact…})` is the **transcript-entry
notation**: a token variable with facts about it — ordinary
predicates: `SpeakerOf`, `AudienceOf`, `LocutionOf`, `DeicticTimeOf`,
`DeicticPlaceOf`, `TextOf`, `Realizes` (the token realizes an act
value of whatever force — the force index is existential here),
`Utters` (agent utters token). It is **defined**, and its definition
is a λ, not a computation:

```lisp
(Utterance {$u :: UtteranceToken} {fact…})
  ≝ {λ [$u :: Referents UtteranceToken] (∧ fact…)}
```

(The entry notation ascribes the token *sort*; the definition binds at
the singleton-lifted reference type, §3.2 — specimens keep the sort
spelling.) The following projections serve utterance anaphora (§11 L8.8–L8.9):

```text
RealizedAct<F> : Referents<UtteranceToken> ⇀ Act<F>
   ; the act the selected token/span realizes — defined (projectively,
   ; §5.5) where transcript attachment/role selects exactly one act of
   ; force F (default broad-span selection is Host; a component/display may
   ; be explicitly selected): the force partiality lives HERE.
RealizedDiscourse : Referents<UtteranceToken> ⇀ Discourse
   ; the sibling for spans realizing act sequences.
ActContent : Act<Assertion> → Content
   ; total and inert at its assertion-indexed domain: the RAW content
   ; the constructor packaged, with no performance capture.
RealizedContent : Referents<UtteranceToken> ⇀ Content
   ; the captured content of the one performed, context-resolved
   ; assertion occurrence selected by the token/span.
```

`RealizedAct` returns the reusable package, whether the token describes an
unperformed/quoted act or realizes a performed one; it never folds a
performance context into act identity. `ActContent` is correspondingly the
pure raw-package projection and never consults the transcript.

`RealizedContent u` is defined projectively exactly when transcript
attachment/role selects one performed host assertion occurrence
whose capture determines the asserted payload. Associated expressive displays
and vocatives do not compete with their host; two Host assertion occurrences
with no narrower selected host span do. It returns that
occurrence's structured Content under the captured utterance context and
resolver. The projection itself is inert: it neither performs the act nor
runs the Content. A token that merely occurs inside a quotation or transcript
description with a `Realizes` fact has no performance occurrence and therefore
no `RealizedContent`, even though its raw `RealizedAct`/`ActContent` route may
be defined. Conversely, two tokens/spans may realize the same act value while
their two `RealizedContent` values differ because the performances resolved
speaker/deixis/`Context` sites differently.

The capture boundary is deliberately narrower than a replay log. It fixes
utterance-context projections and `Context` resolution, including the
resolved clause template used by default `go'i`; it does not freeze dynamic
truth filtering, `Refer` outcomes, projective discharge, or a single `Vague`
sharpening. `ra'o` selectively reopens the antecedent pro-assign sites it
marks: the mapping rebuilds those sites from the raw package/template under
the new performance context while retaining the occurrence capture at every
unmarked site (§11 L8.7). It is not a wholesale raw-package replay.
If a reuse override introduces a dependency tuple the antecedent run never
visited, the capture uses §5.1's full-domain partial-function rule; it neither
freshly resolves in the caller's context nor fails merely because the tuple
was unvisited.

The `Utterance` λ above is a *pure token-description property*. It suspends
the facts by nature (nothing is performed, nothing introduced — quoted material
introduces no discourse referents), and `StructuredQuote` (§7.5)
consumes exactly this property type, supplying the sign boundary's
opacity itself: the primitivity in this neighborhood belongs to the
sign constructors, not to the entry notation. (A `Bind`/`Refer`
spelling, by contrast, would be a computation — the wrong category
for a value behind an opaque boundary.) What likewise needs no
special form is performed-level token talk: asserting facts about an
utterance token in open discourse is ordinary reference introduction
at the token sort. The `Sign` entry notation of §7.5 is the same
defined λ at the sign-token sort. Transcript entries carry unperformed
acts.

### 7.5 Signs and quotation

`Sign<K>` classifies signs by kind `K` (Name, Sentence, Word, Letteral,
Quotation, MathExpression, Structured, Opaque, Text, and Connective).
Constructors: `(OpaqueQuote text)` (`lo'u…le'u`, `zoi`),
`(StructuredQuote entry)` (`lu…li'u` — the operand a pure
token-description property, §7.4; the constructor supplies the opaque
boundary),
`(NameSign text)`, `(SentenceSign content)`, `(LetteralSign text)`,
`(WordSign text)`. `(Sign {$s :: SignToken K} {fact…})` describes sign
tokens with facts (`TextOf`, `Quotes`, `Denotes`) — the §7.4 defined
entry notation at the sign-token sort. Interpretation is explicit and
typed: `(InterpretContent sign) : Content` and the force-indexed
partial family `InterpretAct<F> : Sign<K> → Act<F>` — defined exactly
when the sign's realized (or intended) act has force `F`, since a
sign does not carry its force — the `la'e` crossings; `lu'e` is the inverse sign-of crossing.
On a transcript entry (a structured quote whose token realizes an act),
`InterpretAct` yields that act, and `InterpretContent` is defined
exactly when the realized act is an assertion, yielding its content —
the raw `ActContent` projection; other forces have no content projection and
interpret only as acts. A quoted/transcript-description `Realizes` fact is not
a performance, so interpretation never invokes `RealizedContent` merely
because an act is represented. "Raw" here means *not occurrence-captured*:
the sign interpretation still supplies the represented token's intended
utterance context for its deictics/sites. It never substitutes the later
caller's context merely because the package lacks a performance. Quotation boundaries are opaque to dynamics
(§5.4).

### 7.6 Indicators: attitudes, evidentials, discursives

Indicators (UI) are **lexical relations in the displayed-content family**,
not generated wrappers. (The specimens' placeholder names for these
relations — `Happiness`, `Unhappiness`, `Desire`, `EvidentialBasis` —
are §16 placeholders like any other PascalCase name; the audit maps
them to the `-nmo` indicator-emotion family, §16.5.) Display has two
spellings, by the level of its
target — no dedicated operator is needed:

- **Act-level** (the surface target is a performed act; the core target is its
  occurrence — the top-level case): the
  display is an `Express` act beside the host on the discourse spine. The
  lowering binds the occurrence handle returned by the host performance and
  applies the indicator relation to that handle:
  `{Bind [$o :: ActOccurrence Assertion] (Perform Host $a)
     (Do (Perform AttachedDisplay
            (Express (Close (i-rel Speaker $o degree)))))}`.
  Expressive force is itself non-at-issue commitment, and the family
  **force clause** holds: an evidential displayed this way *grounds* the
  host act — a mode of commitment, not a second claim — and a host-force
  profile (below) may subordinate the host instead of performing it. The
  bound `$o` makes the grammatical target survive lowering: re-performing
  `$a` later creates another occurrence handle, and the earlier display does
  not ground or modify it. A relation about the reusable act package can
  still target `$a` explicitly; it is not the top-level UI default.
- **Content-level** (the target is embedded content, a referent, or a
  sign): the display is a `Supplement` whose anchor is the target's
  first-order object — for content, its reification — and whose side is
  the indicator predication of that object. The content occurs **once**,
  under a pure `Reify` shared by `Let`, and is evaluated through the
  primitive `Holds` (`Reify`'s inverse, §9.1):

  ```lisp
  {Let [$p :: Proposition] (Reify c)
    (Supplement $p (Close (i-rel Speaker $p degree)) (Holds $p))}
  ```

  so anchor, side, and evaluated body all speak of the same content with
  the same contextual sites; the side projects per §5.5.

Targets are always bound terms or pure object-formers — never free
names. Each indicator's lexicon entry (§10) provides:

- its relation with typed roles — for attitudes: experiencer, a
  first-class **target** at the closed union type `Target` — a
  `Proposition` (content targets go through `Reify`), an act value, an opaque
  `ActOccurrence` handle, a plural reference, or a sign, with the mapping
  resolving which — and
  a **degree** place on the library's intensity scale, whose named
  regions are `Intense` (`cai`), `Strong` (`sai`), `Moderate`
  (unmarked), `Weak` (`ru'e`), and `Neutral` (`cu'i`);
- its **`nai`-pair**: `nai` selects the lexically paired polar indicator
  (`.uinai` is unhappiness, a named emotion — not "other than happy"), and
  all other modifiers compose over the *pair* in surface order — `.uinai
  cai` is intense unhappiness (degree selects the pair's scale region),
  `dai` shifts the pair's experiencer, `cu'i` selects the neutral region
  of whatever relation it reaches. CLL's own mechanism (13.4, 15.7,
  13.8) is polar: `nai` refers the indicator to the **opposite end of
  its scale**, and the pair lexeme is the lexicon *naming* that pole
  (`.uinai` = unhappiness). Where no pair is listed, the documented
  fallback is therefore `(Scalar Opposite D R)` over the relation and the
  entry's fixed or contextually bound domain D — the antipode,
  exactly CLL's rule — and lexicon review prefers naming the
  pole. Every grammatical `nai` attachment thus has a denotation, by
  named pole or antipode, exhaustively and exclusively.
  The pair carries its own host-force profile, inheriting the entry's
  profile family where it declares none; `nai` never flips a host-force
  profile;
- its **host-force profile**: whether displaying it leaves the host
  content asserted (pure emotions: `.ui do klama` asserts the going and
  displays joy), **subordinated** (propositional attitudes, CLL 13.3:
  `.au mi sipna` displays a desire and does not assert sleeping — the
  content is evaluated at the attitude's worlds, §5.1), metalinguistically
  voided (`na'i`, §7.3), or performative (`ca'e`, COI greetings — the act
  is constituted by its performance);
- for **evidentials** (`za'a`, `ti'e`, `ka'u`, `se'o`, `ba'a`, `pe'i`,
  `ju'a`): the relation experiencer × target × basis-kind — the
  basis-kind values are the closed `BasisKind` enumeration declared
  with the family
  (`Observation`, `Hearsay`, `CulturalKnowledge`, `InternalExperience`,
  `Expectation`, `Opinion`, `BareAssertion`) — with the family
  force clause: when the target is the content of the enclosing performed
  act, the evidential **grounds that act** — the basis of asserting or of
  asking, a mode of commitment, not a second at-issue claim; at embedded
  targets (`mi jinvi lo du'u ti'e do klama`) it displays the speaker's
  basis for the local content. `Assert`-with-basis spellings are library
  sugar for the top-level case.

`dai` shifts the experiencer role; `pei` forms an `OpenQ` over the
attitude or degree; `ba'e` is sign-level focus. Indicator target selection
is a text-to-reading rule (mapping annex; `FUhE`/`FUhO` delimit extended
scope).

### 7.7 Reserved extension: core self-description

A staged reflection extension for quoting and interpreting the core's own
notation was designed and then removed from the baseline: no current Lojban
meaning requires it, and making direct binders into sign-consuming functions
added staging, capture, and evaluation machinery without reducing the
semantic core. Braces in baseline terms are binder punctuation only (§2);
there are no `Expression` or `Telescope` sign kinds, core-code quotation,
`Interpret` family, or `Make*` facades. Ordinary Lojban quotation and the
linguistic sign crossings of §7.5 are unaffected. The abandoned design and
the conditions for reconsidering a properly stage-indexed extension are
recorded as design history in the rationale (§2.9) and review archive.

## 8. Questions and answers

### 8.1 Query formation

`(Polar c) : Query<Bool>` (`Bool` the two-element answer type, §3.1);
`(OpenQ f) : Query<A>` for `f : EFn<(A…), Content>` — typed answer
domains, including tuples (`ma klama ma`), relation variables (`mo` — the
one-place row shown in samples is the common case; the general domain
quantifies over rows accepting the fill), place labels (`fi'a`, §4.7),
connectives and operators by domain enumeration, tags (`cu'e`), and
attitudes/bases (`pei`, `ju'apei`). `(Ask q)` makes the question act;
`(QuestionOf q) : Question` reifies a query as an embeddable
object — the path for question-*object*-selecting lexical places (a
`preti`-shadow object one can utter, translate, or repeat), distinct
from the `kau` answerhood path below, which builds a `Proposition`
through `Answer`.
(Embedded question objects in Lojban carry `kau` — `lo du'u ma kau
cortu`. A bare interrogative inside `du'u` is **not** an embedded
question: CLL 11.8 is explicit that "`ma` always signals a direct
question", so `mi djuno le du'u ma pu klama le zarci` means "Who is it
that I know goes to the store?" — the mapping gives bare interrogatives
utterance-level scope, turning the whole act into the question; only
`kau` builds the question object.)

### 8.2 Answers

`Answer : Query<A> × Selection<A> → Content` pairs a query with a
selection from its typed answer domain. The query formers are kept as
named primitives with denotation clauses rather than reduced to bare
function types — deliberately: spelling `(Polar c)` as a λ over `Bool`
would copy `c` textually into both branches (two contextual sites,
doubled handlers — the `↔` lesson of §4.5), and the named `Query` type
keeps question denotations a distinct, inspectable kind. The
denotations: a query is its
**answer-content function** — `(Polar c)` sends `Yes ↦ c` and
`No ↦ (¬ c)`; `(OpenQ f)` sends each domain tuple `a` to `(f a…)` —
and `Answer` applies it: `(Answer q (TupleAnswer a))` is the content
`q`'s function assigns to `a`, evaluated as ordinary content (its
dynamics are its operators'; nothing question-specific is added), and
`(Answer q (PolarAnswer s))` likewise at `Bool`. The baseline
`Selection<A>` family has only
`(PolarAnswer Yes|No) : Selection<Bool>` and
`(TupleAnswer tuple) : Selection<A>`. `MentionSome` is removed: it was
extensionally identical to the unmarked form and has no Lojban exponent.
`Exhaustive` is demoted to the gap register rather than left as prose: a
definition would require a pure answer-content function **and** typed
selection membership/equivalence at every answer domain, neither of which the
general `Query<A>` interface supplies. `ContextualAnswer` — the
semantics of bare `kau` — is licensed only as `Answer`'s second
operand, and the *composite* is the defined form making the
contextual retrieval explicit:

```text
(Answer q ContextualAnswer) ≝                     ; open q : Query<A>
  {Bind [$a :: A] (Context) (Answer q (TupleAnswer $a))}
(Answer q ContextualAnswer) ≝                     ; polar q : Query<Bool>
  {Bind [$a :: Bool] (Context) (Answer q (PolarAnswer $a))}
```

— the retrieval is at the query's answer domain, and the selection
constructor follows that domain: `TupleAnswer` at open domains,
`PolarAnswer` at `Bool` (the `xu kau` case); no exhaustivity marker
either way (absence, per P9). `Answer` yields `Content` and
so embeds under `Reify` as any content does. **Exhaustivity is absent**
(ruling P9): unmarked answerhood carries no
exhaustivity conjunct — truth-conditionally the weakest (mention-some-
compatible) reading — and strengthenings enter only by a separately stated
claim or lexically (an embedding predicate such as `djuno` may contribute its own
completeness presupposition through §5.5; it never rewrites the answer).
Lojban has no grammatical exhaustivity marker for `kau`, so no `Vague`
parameter is posited: a decision point the language cannot express is
silence, not vagueness. A speaker can still state a separate completeness
claim, and the recorded `Exhaustive` proposal may return only if its purity and
answer-domain structure are supplied.

### 8.3 Place and relation questions

`fi'a` asks over the compatible-label refinement of `Label<ρ>`
(§4.7); `mo` binds a `PredTerm`-typed
variable; both are ordinary `OpenQ` at their domains. No dedicated
question machinery exists beyond typed domains.

## 9. Abstractions

### 9.1 One primitive bridge

`(Reify c) : Proposition` is the single primitive content-to-object
crossing — `du'u`. A proposition is a first-order object standing in a
representation relation to the content's intension; it is what `djuno`,
`krici`, `cusku` embed, quantify over, and identify. Its inverse is the
primitive `(Holds p) : Content` — the content the proposition object
represents — with the axiom pair that evaluating `(Holds (Reify c))`
is evaluating `c`, and `(= (Reify (Holds p)) p)` for every
proposition: each proposition represents exactly the content `Holds`
returns for it. The pair is the sole Proposition↔Content bridge (the
sign and event crossings — `SentenceSign`, `EventOfContent` — cross
to *other* sorts). The axiom pair speaks at evaluation: `Reify`
itself is inert — constructing the object runs nothing and introduces
nothing (the §5.4 opacity row) — while evaluating `(Holds p)` runs
the represented content at the `Holds` occurrence, its contextual
sites those fixed when the represented term was formed (§5.3) and its dynamic
escapes governed by the operators around the `Holds`.

**The bridge's shape generalizes** — a reservation, not a baseline
commitment. Nothing in the pair is special to the empty row: for any
row ρ one can posit a reified-predicate sort with its own
crossing pair and row-wise round-trip axiom, making `Proposition` the
row-⟨⟩ member of a family rather than a one-off (Chierchia & Turner's
nominalization pair, analogically) — this is what property *objects*
(referents for `lo ka` where discourse-referent behavior is wanted,
property anaphora, predicate quantification) would be. The baseline
defines only row ⟨⟩; the rest is a registered gap (§14). The
experimental cmavo pair `me'ei`/`me'au` (turn a selbri into an
abstract-predicate sumti; use such a sumti as a selbri of the
referent's arity) is the attested surface exponent of the two
directions. At the propositional case `me'au` is `Holds` in selbri
position, defined — like the numeric crossings of §9.2 — at the
reference type `lo du'u` actually yields, under a **singleton
condition** with singularity projective. The remark's precise shape:

```text
(Meau0 r) ≝
(Presuppose
  (∃ {λ [$p :: Proposition]
    (∧ (CoRef r $p)
       (∀ {λ [$q :: Proposition] (→ (CoRef r $q) (= $q $p))}))})
  (∃ {λ [$p :: Proposition]
    (∧ (CoRef r $p)
       (∀ {λ [$q :: Proposition] (→ (CoRef r $q) (= $q $p))})
       (Holds $p))}))
```

(the member `$p` singleton-lifts at the referential `CoRef`
positions, §3.2; the uniqueness conjunct makes the representative
single-valued outright — §4.8 deliberately assumes no atomicity, so
bare co-reference with *some* proposition would not by itself
guarantee one). For `abu` a singleton
reference to a prior `lo du'u c`, `(Meau0 abu)` is extensionally
`(Holds p)` at the sole member, so `me'au abu gi'a me'au by` is the
content-level disjunction of the two claims (contrast
`abu jetnu gi'a by jetnu`, two truth-predicate
claims *about* the objects — truth-conditionally aligned by the axiom
pair, structurally distinct). A non-singleton proposition reference
has **no baseline reading**: silent distribution would violate P4's
no-default-distributivity stance, so the plural case is registered in
§14 (the universal reading — `Holds` distributed over the members —
is the recorded candidate). Conversely `me'ei` at the propositional
case is `Reify` in the sumti-forming direction; beyond arity zero
both belong to the reserved family.

**What the axioms fix, and what stays open.** The round-trip pair
makes `Reify` and `Holds` mutual inverses at row ⟨⟩: proposition
identity is exactly content identity — identity of the model's structured
dynamic denotation: state transformation, projective/site structure, and the
§9.3 clause-event intension. It is finer than logical equivalence (contents
differing only in presuppositions, effects, or non-coreferent clause events
reify distinctly) — and this is **fixed by the axioms, not model-supplied**.
Likewise any future row's crossing is a function
over the extensional `PredTerm<ρ>` (§3.3 identifies relations equal
on every row record), so β/η- and pointwise-equal predicates would
reify identically — the family is extensional over `PredTerm` by
construction. What remains open is only the adoption-shape question:
whether each reserved row takes the same bijective shape, and the
design of any row-isomorphism or cross-row operators (cross-row
identity is not even formable until typed). No normative statement
decides those today.

### 9.2 The abstraction relations

Every other abstractor is a **named abstraction relation with a labelled
row**, parameterized by the abstracted content — CLL's own shape: CLL
assigns these abstractors place structures (CLL ch. 11 §3 for the event
types, §5 for `ni`, §6 for `jei`, §9 for `li'i`/`si'o`/`su'u`):

```text
(NiRel c)   : PredTerm (Row (1 (Referents Amount)) (2 (Referents Scale)))
(JeiRel c)  : PredTerm (Row (1 (Referents TruthValue)) (2 (Referents Epistemology)))
(LihiRel c) : PredTerm (Row (1 (Referents Experience)) (2 (Referents Entity))) ; experiencer
(SihoRel c) : PredTerm (Row (1 (Referents Concept)) (2 (Referents Entity))) ; mind
(SuhuRel c) : PredTerm (Row (1 (Referents AbstractNature)) (2 (Referents Entity))) ; category
(PuhuRel c) : PredTerm (Row (1 (Referents Process)) (2 (Referents Eventuality))) ; stages
(ZuhoRel c) : PredTerm (Row (1 (Referents Activity)) (2 (Referents Eventuality))) ; repeated actions
(DuhuRel c) : PredTerm (Row (1 (Referents Proposition))
                            (2 (Referents (Sign Sentence))))
```

`DuhuRel` is derived — formally: `((DuhuRel c) x1 x2) ≝
(∧ (CoRef x1 (Reify c)) (Distrib {λ [$s :: Sign Sentence] (CoRef
(Reify (InterpretContent $s)) (Reify c))} x2))` — its x1 the reified
content, its x2 sentence signs whose interpretation reifies the same
(CLL 11.7's x2 and `se du'u`); the others are the
family proper. `DuhuRel` — and with it `se du'u` — is defined only
for the 0-adic case: under explicit-`ce'u` extraction (§11 L9.1) the
`du'u` abstraction is a λ, not a content, and sentence signs express
closed sentences (`InterpretContent` is defined for sentence signs,
not open properties), so `se du'u` under extraction has no baseline
reading. A future treatment would require a typed linguistic or core-code
sign for open expressions; no such sign kind exists in the baseline, so
this remains reserved-family territory (§14). Reference applies
**outside** the relation, exactly as for
any selbri: `lo ni mi klama` is `Refer` over
`{λ [$a :: Referents Amount] (Close ((NiRel …) $a))}` — so the
`lo`/`le` contrast, outer quantification,
and relative clauses all work on abstractions for free, and an omitted x2
is ordinary closure into `Context` (the `su'u` categorizer's contextual
default — CLL 11.9's "type x2" — is this general rule, not a special
one). Event abstraction (`nu` and its one-place sort refinements
`mu'e`/`za'i`) is `Refer` directly over the inner `ClauseContent`: a direct
lexical clause contributes its one lexical event, while an eventless or
compound clause contributes its holding State. This is CLL 11.2's event or
state of the bridi considered as a whole, and it handles `lo nu ta du …`
without retyping the binary identity relation. Contextual/reference effects
inside the ClauseContent keep their written sites and run under `Refer`'s
ordinary effect sequencing. `pu'u`/`zu'o`, having real x2s, live in the relation family
above, and `li'i` is its own abstractor (`LihiRel`), not an event
refinement. `ka` is not in this family: property abstraction is `λ`
(implicit `ce'u` pinned in P12). Sort discipline and no-coercion (P13)
are unchanged; adjacent-sort recastings are explicit named operators in
the library. The baseline's numeric abstraction crossing is

```text
AmountValue     : Referents<Amount> × Referents<Scale> ⇀ Number
```

(defined at the reference type `lo ni` actually yields, projectively at
singleton amount and scale references; CLL 11.5: a `ni`
sumti is semantically a number, and `mo'e` maps to `AmountValue`, so
`li pa vu'u mo'e le ni …` type-checks). `JeiRel`, by contrast, yields an
epistemology-relative `TruthValue`. P38 removes the formerly optional numeric
`TruthValueDegree` crossing from the baseline: CLL 11.6 records [0,1] as a
first-edition proposal whose conventions were never worked out and whose
number-valued reading never became established. The exact proposed crossing
is preserved in §14 as a possible future pin, never as per-reading optional
truth conditions.

### 9.3 Clause eventualities and `EventOfContent`

`StateClause`, `CloseClause`, and `EventOfContent` are the coupled primitive
interface that makes §3.4's universal clause eventuality substantive:

```text
StateClause   : Content → ClauseContent
CloseClause   : ClauseContent → Content
EventOfContent: Content → Referents<Eventuality>
```

`StateClause` preserves the operand's effect profile: with effect-free c its
result refines to the pure `Fn` arrow; otherwise it is effectful.

The Content operand of `EventOfContent` is **inert**: the crossing projects
the eventuality intension carried by that content and does not run the
content. `StateClause`, conversely, is active when its result is applied: it
evaluates its Content operand exactly once and exposes a `State` of that
content holding. Neither operation returns truth, inspects syntax, or permits
same-stage evaluation. The names `hold_M` and `joint_M` below are model-level
semantic operations, not extra term forms; `StateClause` is their sole term
interface for constructing a holding-state clause.

The event projection is constructed compositionally by the following
**precedence-ordered table**. Write `event(c)` for the world-, profile-, and
branch-relative eventuality intension carried by `c`; its projection as a
term is `EventOfContent c`. Defined forms use their expansions, and ordinary
β-reduction and `Let` substitution remain valid. The first applicable row
wins:

| Content-producing form | Clause-event intension |
|---|---|
| `(CloseClause C)` | On each candidate/event branch, the locally bound witness `$e` used to evaluate `(C $e)`. Truth filtering may reject the branch; it does not replace its described event. |
| `((StateClause c) e)` | `$e` on the sole possible satisfying co-reference class; a non-`hold_M(c)` candidate has no satisfying lineage and does not evaluate `c`. |
| `{Bind [$x] computation body}` when the body returns Content | The event of the selected continuation body on that outcome branch. `Let` is already covered by ordinary application/β. |
| `(Presuppose π body)`; `(Supplement anchor side body)` when the body is Content | The at-issue body's event. Projective conditions and side commitments remain part of Content identity but do not replace the at-issue eventuality. |
| `(InContext c g)` | `event(c)` evaluated with the same shifted utterance ground `g`; this shifts the projection rather than constructing a new holding state. |
| `(Holds p)`; `(ActContent a)`; `(RealizedContent u)`; `(InterpretContent s)` | The event of the represented, raw-packaged, occurrence-captured, or interpreted Content. This preservation is required respectively by the `Reify` round trip and by the content-projection clauses of §7; none of these projections constructs a new holding state. |
| `(Answer q selection)` | The event of the answer-content selected by q; baseline answerhood adds no completeness conjunct. |
| `(∧ c₁ … cₙ)`, n > 0 | `joint_M(event(c₁), …, event(cₙ))`, in source association order and up to `CoRef`. |
| `(∨ c₁ … cₙ)` | Branch-relative: a cᵢ-lineage carries `event(cᵢ)`; no fused event or exported choice is added. |
| `(¬ c)` | The negative State `hold_M(¬ c)`, not `event(c)`. |
| Ordinary `Fn`/`EFn` application returning Content | The event of the returned Content, with no type-directed overwrite; apply the appropriate row to that result. This includes functions whose exact type is the transparent `ClauseContent` alias: the alias imposes no hidden refinement, so `((λ e. ⊤) x)` has the same event as `⊤`, as ordinary β-equality requires. Surface clause closure gets its argument event from the explicit `CloseClause` row, not from application. |
| Atomic predication, `=`, `⊤`, the remaining Boolean forms, ordinary `∀`/`∃` and GQs, `Generic`, and every other Content constructor not assigned a preserving or composing row above | Its own holding State `hold_M(c)`. In particular, an ordinary quantified claim does not inherit one arbitrary instantiation's event. Every new Content-producing primitive must either state an explicit row or affirm this default. |

This table closes F1's otherwise ambiguous case deliberately: application at
the transparent function alias is ordinary application. Giving every such
application its argument as event would make
`({λ [$e] ⊤} x)` and its β-reduct `⊤` differ in Content identity,
contradicting §4.4. `CloseClause` is the semantically explicit point at which
the locally selected clause witness becomes the event of the closed Content.

The table is exhaustive; the following laws constrain its nontrivial rows:

1. **Closure witness / no double indexing.** On each live evaluation lineage
   of `(CloseClause C)`, `EventOfContent (CloseClause C)` co-refers with that
   closure's local event witness. If C came from `DirectClause`, this is the
   lexical event itself — no state-of-the-event-occurring is added. The
   closure row carries e regardless of the independently compositional event
   of `(C e)`; facet conjunctions therefore still target that same explicit e
   without changing the closed clause's projection. The witness remains
   locally quantified and is not thereby discourse-accessible. “One” means
   one distinguished witness per live outcome lineage, not a uniqueness claim
   that only one matching event exists in the model.
2. **Holding state.** `(StateClause c)` has the uniform `ClauseContent`
   parameter type `Referents<Eventuality>`, but only arguments lying in the
   `State` subdomain can satisfy it. A non-coreferent candidate fails without
   evaluating c; at the unique co-reference class of the model's `hold_M(c)`
   State, c's at-issue facts are evaluated relative to that state's situation,
   while contextual/dynamic effects run exactly once on the current lineage.
   A satisfying State is actual (`fasnu`) at that world. If no actual State
   verifies c, a described nonactual counterpart may remain in the domain but
   does not satisfy the clause. `EventOfContent (CloseClause (StateClause c))`
   co-refers with `hold_M(c)`; content constructors with no direct, joint, or
   branch event use the same holding-state projection by default. This is the
   route for identity, mathematics, quantifier/generic results, implication,
   and the other eventless cases.
   No finiteness or boundedness law is imposed: a holding State may occupy an
   unbounded temporal or spatial extent, including an all-time interval.
   Tense on such a State remains well-typed; whether `purci`, `cabna`, or a
   spatial facet holds follows the declared relation, not a ban on infinity.
3. **Conjunction.** On a lineage where c and d hold,
   `hold_M(∧ c d)` is the jointly constituted State of `EventOfContent c` and
   `EventOfContent d`. Section 4.9 now exhibits this `joint_M` as the unique
   complete `GunmaAt` event witness at the distinguished conjunction basis
   `κ∧`; it is actual exactly when both non-null components are actual. The
   basis's self-flattening law gives associativity up to `CoRef`, while
   `hold_M(⊤)` is its declared null component and unit. No commutativity of
   dynamic evaluation is inferred: the event cover is insensitive to operand
   order, but `∧` still evaluates its Content operands in source order.
4. **Disjunction.** The event of `(CloseClause (ClauseOr C D))` is
   branch-relative: a live C-lineage carries C's event and a live D-lineage
   carries D's. If both disjuncts hold, both lineages are available; no covert
   choice is exported through §5.4 and no fused event is asserted. This is
   exactly `ClauseOr`'s shared event parameter.
5. **Negation and the remaining compounds.** `hold_M(¬ c)` is a State of c's
   non-holding, actual exactly where c is false; it is not c's positive event
   and negation is not partial merely to avoid negative states. Implication,
   biconditional, exclusive-or, quantified claims, and other content with no
   preserved single lexical event use their `StateClause`/`hold_M` state.
6. **Congruence.** Content identity preserves the event projection: contents
   with non-coreferent event intensions are not identical merely because their
   at-issue world filters coincide. This event component therefore participates
   in `Reify`/`Holds`'s §9.1 content identity and in the future carrier
   construction, rather than being renderer metadata.

These clauses borrow a useful architecture, not a linguistic conclusion,
from truthmaker semantics: conjunction is constituted from both component
states and disjunction is verified by an alternative, while negation requires
an explicit falsity/negative-state policy. The project chooses the negative
holding-state policy because its adopted coverage includes negative clauses;
speaker compatibility, not that literature, is the authority for the choice.

## 10. The lexicon interface

The core is parameterized over an external, curated lexicon. This chapter
fixes only the **schema** of lexical knowledge — what a dictionary entry
must provide for the core to interpret predications over it:

| Field | Content |
|---|---|
| row | the labelled, typed place row (§3.3); a direct-event entry includes the distinguished event label, while a holding-state entry does not acquire one |
| clause-event mode | `DirectEvent(ℓ)` identifies the clause parameter with lexical place ℓ; `HoldingState` routes the complete predication through `StateClause` (§4.6, §9.3) |
| defaultability | per place: whether closure (§4.6) may introduce a `Context` there; non-defaultable places must be filled or abstracted |
| scope policy | per place: extensional / intensional / opaque (§5.7) |
| situation behavior | whether the relation/value projection is rigid or is evaluated relative to a surrounding `StateClause` situation (§5.7); physical value-bearing entries must declare this, while numeric constants and arithmetic are rigid |
| plurality behavior | per place and resolved reference mode: how the relation composes with plural arguments — lexical knowledge, never a covert operator (§4.8). A place either declares the pure unit profile below or supplies its exact direct plural condition; silence is not permission for a model-chosen reading. Two further independent facts may be declared per place: **subreference-monotone** (satisfaction is preserved under subreference — `Among r' r` and `P … r …` entail `P … r' …` at that place; the pluralization of Eberban's subset-monotonicity star) and **collective-capable** (jointly satisfiable configurations are admissible). Either may be affirmed or denied where its lexical entailment is known (P4, P39) |
| unit profile | optional, per place and resolved reference mode: a pure `unit_Rℓ : Fn<(T), Content>`. With every other operand fixed and every non-head retrieval hoisted, the resulting pure lexical property `R_p` obeys `R_p(r) ↔ CoveredBy(unit_Rℓ, r)`. For an ordinary count profile, `unit_Rℓ` is the freely interpreted singleton restriction of `R_p`; the equation then determines larger plural references rather than recursively defining the singleton base. Cumulative/divisible substance units, singleton-container units, and other licensed unit notions state their own property. A collective, kind-like, or otherwise directly plural mode instead omits this field and supplies its exact ordinary plural truth condition. The alternatives are lexical data, not readings chosen at application time; per-row values remain the lexicon programme's obligation (#12) |
| constitution behavior | for a whole/component row or a `joi`-compatible result: the pure admissible-basis constraint; group/event bases declare peer granularity and, for events, trace/role-participant/causal/actuality aggregation; a property row declares its `ContributionBasis<ρ>` `MixAt`/`ContributesAt` instance. Absence means the corresponding constitution reading is unmapped, never model-chosen (§4.9) |
| deletions | which `DropPlace` deletions are meaningful, with the deleted role's semantic characterization (§4.3) |
| degree | optional: for gradable entries, the graded place label ℓ and degree projection `deg_R` consumed by `Grade` (§6.4) |
| kind admission | whether a place admits kind-like referents (ruling P3) |
| abstraction sorts | for places selecting abstractions: which sorts (§9), with drift cases adjudicated in the dictionary, not coerced |
| tag reductions | for tense/modal cmavo: the clause-event-predicate expansion (`pu` → `purci(e, anchor)`, BAI → their gismu relations with the current clause-event link), consumed by the mapping annex |
| indicator entries | for UI: relation, roles, degree place, `nai`-pair (with `Scalar Opposite` fallback where unpaired — §7.6, §6.3), host-force profile, evidential basis-kind where applicable (§7.6) |

Adopted collection entries (P5): official `gunma` already takes its
components as x2 and explicitly glosses itself as only partially specified;
its row lowers through a constrained `Context` basis to non-exhaustive
`GunmaAt`. `CompleteGunmaAt` is the defined strengthening used where the
surface says the listed/base components constitute the whole. The lightly
attested community lujvo `mulgunma` independently spells that complete
strengthening, but is corroboration rather than a required surface exponent.
`selcmi` — a community lujvo (xorxes), which
the Contemporary CLL edition itself now uses and glosses in its
set-descriptor expansion (ch. 6) — already takes its members as x2;
both are adopted with plural
x2 read as plural references. `selcmi`'s member relation is exact; unlike
general `gunma`, it does not admit unlisted members. (The genuine defect in this area is
official `cmima`'s x2 being glossed as a *set*; the library avoids
`cmima`, and the lexicon program may propose broadening its x2.) The resolved
official-row clause is:

```lisp
; gunma g Cs — deps selected by this resolved occurrence
{Bind [$κ :: GroupBasis T]
      (Context (GroupBasisConstraint gunma T) deps…)
  (GunmaAt $κ g Cs)}
```

`(GroupBasisConstraint k T)` is lexicon data, not one unconstrained universal
predicate. When `gunma` occurs inside a position requiring a pure property
(a selection restrictor, the member-level `Refer` lift, or a `SetOf`
comprehension — §3.3), the mapping hoists this κ binding outside that
property and shares the captured value (L0.1); it never hides `Context` in a
`Fn`.

The working dictionary wording for the adopted group row is: **“x1 is a
jointly constituted group/team/aggregate whole with x2 among its components
at the contextually relevant decomposition basis; x2 need not exhaust the
peer components. The whole has its own properties; no property is inherited
between whole and components without a lexical law.”** The proposed event
overload replaces `Group<T>`/`T` by `Eventuality`/`Eventuality` and requires
the event-instance aggregation laws of §4.9. It is an extension for the
content-word programme, not evidence that the present official row already
spells every event/property use. No surface property overload is proposed:
`PredTerm<ρ>` is not first-order, and property `joi` remains the generic
`GunmaPredAt` interface. The complete wording (“x2 are all peer components at
that basis”) is the `CompleteGunmaAt`/`mulgunma` layer used by `joi` and the
descriptors. `jo'u` never invokes either row; it is only plural `Combine`.
The
`le`-description relation is **`skicu` itself** — official row "x1 tells
about/describes x2 (object/event/state) to audience x3 with description
x4 (property)", an
exact fit place-for-place, and the analysis the community's formal gadri
commentary has used all along (guskant: `le broda` = `zo'e noi mi ke'a
do skicu lo ka ce'u broda`). The describing event is anchored by the
mapping annex's clause (§11 L3.2): it is the current utterance's own locution
— saying `le broda` *is* the describing, so the anchor holds by
construction through the token machinery (§7.4). `voi` goes through
`SpeakerDescribesUnaddressed` (§12) restrictively — the same locution
anchor with the audience place deleted, `(DropPlace skicu 3)` being that
form's inner relation; the deletion is semantic (no audience role exists
in a `voi` description), per pin P10 (#49).

## 11. Mapping annex: Lojban constructs to core terms

Normative lowering schemas, one line each; the cited pins carry the
arguments. Text-to-reading rules (marked ⊳) resolve before the calculus
and contribute no term constructors.

Each mapping-annex clause below is a numbered rule `Ln.m` — n the paragraph, m the
position — so that samples, the coverage matrix, and the checker can cite
one rule by id, as pins are cited by id (#9). An id carries no meaning; the
rule text is the schema. An unmarked rule is a **lowering judgment** and
belongs to the supported fragment F₀; a rule marked *(gap)* records a
documented no-mapping, *(note)* an explanatory consequence, and *(reading)*
a text-to-reading decision that the resolved-reading datum owns (#9). A
specimen cites the lowering judgments whose schemas it instantiates as its
focal claims, never every rule its sub-terms touch, and never a gap, note,
or reading rule.

**The resolved-reading datum** (`RR`; #9). Every lowering judgment below is
relative to a resolved reading: a finite record `RR` attached to one
utterance in a transcript, whose fields are exactly the ⊳ decisions the
rules mark and the resolver stores §5.4–§5.6 presuppose. It is pure data —
it carries no world, information state, or capture (those are §5's
carriers; in particular the segment stack that `NewTopic`/`Resume` operate
on, §5.1 and §7.2, of which `RR` records only the resolver's selections) —
and it never occurs free in a lowered term: a term mentions
only core forms, lexical constants, and the values `RR` selected (a label,
a row, a binder width), never `RR` itself. Its fields, each with the rules
that consume it:

| Field | Content | Consumers |
|---|---|---|
| `parse` | the resolved parse after `si`/`sa`/`su` erasure (L1.9) — an input to the relation, never a normalization the calculus defines | every rule |
| `attach` | UI target selection (L11.1), `vu'o` widening (L4.9), `xi` indexing (L12.9), `ce'u goi`/`ce'u xi` (L9.3), `.i TAG bo` grouping (L5.15) | L4, L5, L9, L11, L12 |
| `readings` | per site: the tenseless reading (L6.4), the CAhA mode (L6.6), `bi'i` normalization (L5.19), `ji'i` position (L12.17), `n mai`/`mo'o` level (L11.14), `tu'a`'s sort by host place (L9.11) | L5, L6, L9, L11, L12 |
| `rows` | the resolved lexical row per selbri occurrence with its conversion routing (L1.1, L1.4); the fixed row per `bu'a` variable (L5.5) | L1, L5 |
| `stores` | KOhA assignments (L8.3), letteral bindings (L12.4), `cei`/`go'i` templates (L5.6, L8.4), the active `do` (L8.10), the resolver's segment selections — the `ni'o` level opened and the segment a `no'i` resumes (L8.12), never §5.1's semantic stack itself — and `da'o` cancellations (L8.11) | L2, L5, L8, L12 |
| `sites` | for every `Context`/`Vague` site: the dependency profile beyond §5.3's computed minimum, the source of its admissibility constraint (lexicon or reading), and its binder width (§12's export contract) | L1.6, L1.10, L2.2, L6.10, L8.3, L8.8, L9.11, L9.13, L11.14, L12.13, L12.16 |
| `anaphora` | `ri`/`ra`/`ru` counting results (L8.1), `di'u`-series spans (L8.8), `ra'o` reopening marks (L8.7) | L8 |
| `force` | the nearest performed clause per `ko` (L2.4); the force of each sentence-level connection host (L5.12) | L2, L5 |

Three boundaries keep the table exact. Mechanical ⊳ rewrites — the
affirmer override (L5.10, P31), numeral syntax (L12.15), implicit `ce'u` at
the first unfilled place (L9.7, P12), and the utterance-level scope of bare
interrogatives (L10.2) — have no choice to record and are premises of the
rules that consume them, not fields. Story time (L6.5) contributes nothing
to any lowered term and has no field; a tense anchor it informs arrives as
an ordinary `readings` value. `sites` carries declared extras only: §5.3
computes the minimum profile as a formation condition, and every dependence
beyond it — for an unconstrained `(Context)`, every dependence — must be
in `RR`. Reading selection, which `RR` a text receives, is not decided by
the relation: where a rule says reading-multiple with no default, the
relation takes each `RR` separately.

Each rule is a typed judgment relative to `RR` — `RR ⊢ sumti ⇝ c :
RefComp (Referents T)` (or a first-order value for `li`/`me'o`), `RR ⊢
selbri ⇝ p : PredTerm ρ`, `RR ⊢ bridi ⇝ C : ClauseContent`, `RR ⊢
sentence ⇝ a : Act F`, `RR ⊢ text ⇝ d : Discourse`, `RR ⊢ term-list ⇝
fills over ρ` — whose side conditions are the formation conditions this
document already states (`Close` undefined at a non-defaultable place,
§4.6; a force conflict has no resolved reading, L5.12; incompatible `bu'a`
rows, L5.5). A constituent with no derivable conclusion has no lowering:
the relation is partial by construction, and no rule produces an `Undef`,
a diagnostic, or a placeholder term. That partiality is resolution failure
only; denotational partiality (§1.7, P21) stays in the semantics and is
never converted into the absence of a derivation. The supported fragment
F₀ is defined extensionally by the rule table — a construction is in F₀
exactly when a lowering judgment maps it under some `RR` — and §15's
adequacy claim quantifies over constituents in F₀ after `RR` resolution.

**Hoisting** (L0; #9).

- **L0.1** Before a property enters a pure position — a `SetOf`
  comprehension, a selection restrictor (§5.6), a quantifier or `Generic`
  restrictor (§4.10, §5.8), or the member-level `Refer` lift (§5.3) — every
  `Context` and `Vague` site it would contain — an omitted defaultable
  place, a tanru link, a basis, a contrast domain, a scale, a cutoff or
  threshold — is bound outside that position by `Bind`, with the dependency
  profile `RR.sites` declares, and the event place is closed by `Close`,
  whose `DirectClause` with no remaining defaultable place is pure (§4.6).
  Writing `s₁ … sₖ` for those site computations (each a `(Context …)` or a
  `(Vague …)`) and `ℓ₁ … ℓⱼ` for the omitted places among them:

  ```text
  RR ⊢ P whose formation would contain the sites s₁ … sₖ
  ──────────────────────────────────────────────────────
  {Bind [$v₁ :: T₁] s₁ … [$vₖ :: Tₖ] sₖ
    ⟨pure position over {λ [$x :: T] (Close (P :ℓ $x :ℓ₁ $v₁ … :ℓⱼ $vⱼ …))}⟩}
  ```

  where a `$v` bound for a non-place site stands at that site's use (the
  link, basis, domain, scale, or region operand). Hoisted sites may depend
  on binders outside the pure position, never on `$x`; a site that would
  depend on `$x` makes the position ill-formed — correctly, since such a
  comprehension has no pure meaning. The `Bind`s are ordered by dependency:
  a site whose constraint or profile mentions another hoisted site's value
  is bound inside that site's `Bind` (a `Vague` cutoff riding a `Context`
  scale, §6.4, binds after the scale); independent hoists commute. Hoisting
  preserves meaning because both kinds of site are functions of their
  dependency tuple alone: a `Context` site retrieves once per distinct
  tuple per performance and introduces nothing (§5.3), and a `Vague` site
  takes one precisification per parameter per binding site, independent of
  everything it does not depend on (VC3, §6.5) — so with `$x` excluded, a
  site's value or precisification is the same at every instantiation of the
  pure position, and binding it once outside changes its place, not its
  tuple. Introductions are not hoisted: a property that would introduce a
  referent (`Refer`, a selection) inside a pure position has no pure form,
  and its reference must already be bound outside (§12). `Close` here fixes
  the **actual mode** for restrictor-internal predications — a
  description's or comprehension's restrictor predicates in its own actual
  mode and is not under the host clause's CAhA, which governs the main
  predication only (P24); the alternative, inheriting the host's clause
  former, is recorded as rejected (rationale §2.11). A reference-level
  `Refer` restrictor is `EFn`, not a pure position, and keeps its sites
  inside (§5.3; L9.6 for `nu`). A lexical predicate written bare in a pure
  position — `{λ [$x :: Entity] (gerku $x)}` — abbreviates this hoisted
  form for the row the specimen assumes, the display convention the samples
  book declares in its preamble.

**Predication and places** (L1).

- **L1.1** A bridi first forms `ClauseContent`: a direct-event lexical row
  uses `DirectClause`; an eventless row or `du`/MEX claim uses `StateClause`
  after its ordinary fills.
- **L1.2** Tense, tags, CAhA, ROI, and `nu` consume that open clause; an
  assertion or any other Content-taking consumer applies `CloseClause`.
- **L1.3** `Close` remains §4.6's abbreviation for the common resolved
  actual-mode predication-to-content cases.
- **L1.4** FA/conversion → labelled fills / row routing (§4.2).
- **L1.5** `zi'o` → `DropPlace`.
- **L1.6** `zo'e`/omission → per-site `Context` (P15).
- **L1.7** `fi'a` → `OpenQ` over the compatible-label refinement
  `CompatibleLabel<ρ,T>` of `Label<ρ>` (§4.7, §8.3).
- **L1.8** `co'e`/`do'e` → `Context` at relation/tag type.
- **L1.9** *(reading)* ⊳ `si`/`sa`/`su` erase before reading; quoted text
  preserves them.
- **L1.10** Tanru (`sutra klama`) → `(Tanru M H)`: the head asserted once and
  one intended `TanruAdmissible` link retrieved at a constrained `Context`
  site (§6.2).

**Prenexes, topics, imperatives** (L2; P26, P27).

- **L2.1** Quantifier prenex (`… zo'u`): prenexed `PA da [poi …]` terms lower
  to the quantifier/selection prefix in **surface order — prenex order is
  scope order** (P18's surface-scope doctrine; CLL 16.2), scoping across an
  I-connected tail and across a `tu'e…tu'u` group when the syntax makes that
  group the matrix; bare selbri variables take the implicit `su'o` of the
  `bu'a` row.
- **L2.2** Topic `zo'u` → the `Topic` schema (§12): the topic binds normally,
  and a constrained `Context` retrieves one intended `TopicResolution` — an
  admissible unfilled place of a single-bridi open comment frame, or coarse
  `srana`-aboutness to the closed comment (CLL 19.4's fish; pin P26). The
  surface does not determine which resolution was intended; the core preserves
  it as one typed `Context` site, not an existential disjunction over every
  admissible resolution.
- **L2.3** *(gap)* Cross-clausal place-linking is gap-registered; no
  segment-state effect (`ni'o` owns segments).
- **L2.4** `ko` → fills its place with the **active addressee** (the
  `doi`-updated `do` binding, falling back to the utterance's Audience) and ⊳
  marks the **nearest performed clause** as the command force (§7.1, addressee
  = the same active value); quotation and content abstractions are inert — `lo
  nu ko klama` constructs content, commands nothing (pin P27); CLL 14.13's
  obedience gloss is a remark, not machinery.

**Descriptions** (L3; P1, P10, P11, P39).

- **L3.1** `lo P` → `(Refer P)`, literally: veridical and number-neutral, with
  no second description-only condition. Where the resolved lexical place
  declares a unit profile, P already has §10's `CoveredBy` plural extension;
  collective, kind-like, and substance modes use their own declared lexical
  extensions.
- **L3.2** `le P` → `Refer` through the defined form `SpeakerDescribes`
  (§12): the reference property is `{λ [$r :: Referents Entity]
  (SpeakerDescribes $r P)}`, whose definition anchors the describing event to
  this utterance's own locution — the locution fact holds at the utterance's
  own token `CurrentToken` (the `dei` value, §7.4). One spelling, one
  denotation: `le` specimens display `SpeakerDescribes` itself, never a
  weaker core term standing in for it (#41). The speaker's commitment that
  the audience can identify the referent is a cooperative-use commitment
  stated here in prose, not machinery; non-veridical, speaker-identifying.
- **L3.3** `la N` → `Refer` via naming (`Named`/`NameSign`).
- **L3.4** `lo'e P`/`le'e P` → `Generic(Typical|Stereotypical, [Speaker], P,
  ·)` at their predication (§5.8).
- **L3.5** `loi`/`lo'i` first bind an ordinary **non-maximal** `(Local (Refer
  P))` base (P5) — under the §5.3 lift, literally `lo P`'s restrictor. `Local` keeps that lowering-internal base out of the
  discourse store.
- **L3.6** `loi` then retrieves a constrained `GroupBasis<T>` and `Refer`s to
  a `Group<T>` satisfying `CompleteGunmaAt κ g base`; `lo'i` `Refer`s to the
  exact `selcmi` set over the same base. In both cases the outer `Refer`
  restrictor is a property of one `Group<T>`/`Set<T>` object, entering through
  the §5.3 member-level lift: the outer reference is `CoveredBy` that
  property, so a number-neutral outer reference may contain several
  qualifying objects, but each qualifies individually rather than several
  partial objects qualifying only collectively.
- **L3.7** *(note)* Thus bare `lo'i gerku` may be a set of the contextually
  selected dogs, not necessarily all dogs, but the hidden dog reference does
  not become a second antecedent: in CLL Example 6.52 `ri` denotes the set. The
  maximal reading remains available when context selects that base or when
  explicit `ro`/`MaxRefer` requires it; bare collection gadri do not add it.
- **L3.8** *(note)* Completeness here forbids components beyond the selected
  base; whether the base itself has external residue is already decided by its
  resolved lexical extension (P39).
- **L3.9** Inner PA → unit count of the selected base (`CardBasis`); outer PA
  → witness-set selection / subreference selection (P1, §4.10).
- **L3.10** Inner `no` → the zero-count schema, never `Refer` (special case,
  P22).
- **L3.11** A leading possessor sumti in a description (`le mi ratcu`) is the
  `pe`-associator restriction (CLL 8.7: `le mi ratcu` ≈ `le ratcu pe mi`) — a
  restrictive `srana` conjunct beside the description head.
- **L3.12** `lei`/`le'i` → the P10 `skicu` base bound first under `Local`,
  then `Refer` to the complete-`GunmaAt` group / exact-`selcmi` set object
  over it;
- **L3.13** `lai`/`la'i` → the naming base likewise — `Group<T>`, `Set<T>`,
  and `Referents<T>` stay distinct, inner PA constrains the base, outer PA
  counts the objects (P5's two sites).
- **L3.14** `lu'a`/`lu'o`/`lu'i`/`vu'i` → the type-directed LAhE collection
  crossings of §12 (`Distrib`/members/`components_κ`; `Massify`; the exact
  `selcmi` set; the ordered `List`), at a constrained basis site where one is
  required (P5, #25).
- **L3.15** Inner PA's counting basis → the resolved place's declared
  `unit_Rℓ` (§10) where the row has a unit profile, otherwise an explicitly
  resolved pure basis at a `Context` site; for the `le` family (`le`, `lei`,
  `le'i`) the basis is the describing property's speaker-described units,
  not actual R-units (P10); the count is `CardBasis` over that basis (P39,
  §12).
**Relative clauses** (L4).

- **L4.1** `poi` → conjunct in the reference property;
- **L4.2** `noi` → `Supplement` anchored at the referent (P7);
- **L4.3** `voi` → `SpeakerDescribesUnaddressed` (§12: the audience-deleted
  `skicu`, `(DropPlace skicu 3)`, anchored to this utterance's own locution
  exactly as `le` is, P10; #49) as a restrictive conjunct in the reference
  property;
- **L4.4** `goi` → discourse-scoped binding;
- **L4.5** `ke'a` → the property's parameter.
- **L4.6** Outer `poi` after `ku` → restriction on the outer selection;
  maximal-subreference readings are explicit library content, not defaults.
- **L4.7** GOI associators (CLL 8.3's own expansions, nested as CLL nests
  them): `pe X` → restrictive `(srana ke'a X)` conjunct; `po X` → restrictive
  `se steci srana`; `po'e X` → restrictive `jinzi ke se steci srana` (nested,
  not conjoined); `po'u X` → restrictive P23 identity (`=`/`CoRef` as sort
  dictates); `ne`/`no'u` → the incidental (`Supplement`) counterparts; `X` is
  computed and bound before the pure restriction forms.
- **L4.8** `zi'e` → restrictives conjoin in the reference property,
  incidentals stack as separate `Supplement`s; order-insensitive
  **truth-conditionally** — bindings and supplements keep source order at the
  effect level.
- **L4.9** `vu'o` → ⊳ widens attachment to the whole connected sumti: an
  incidental clause anchors at the joint unit but predicates **once of each
  immediate connectee** (`(∧ (Q r₁) (Q r₂))` — never of the `Combine`
  collectively, never member-distributed into a plural connectee); a
  restrictive clause restricts each operand under the connective's structure;
  a group-forming joik instead supports the clause on the resultant object
  (CLL 8.8 attests the incidental case; the restrictive rule is this
  specification's extension; pin P34).

**Quantification and connectives** (L5; P2, P17, P18, P41).

- **L5.1** `ro` over descriptions → the library's importing `Every` (§12:
  `MaxRefer`'s presupposed nonemptiness, member-level `Distrib`, and export
  of the maximal witness); bare `ro da` → `∀`.
- **L5.2** PA-quantifiers → library cardinal GQs over a counting basis.
- **L5.3** Termsets (`ce'e`, `nu'i`) → co-selected witness sets at one joint
  locus with the full product; no coordinate maximality (the coordinate-closed
  profile is a named strengthening).
- **L5.4** `da'a n` → the `SelectAllBut` selection (§12; default n = 1).
- **L5.5** `bu'a`/`bu'e`/`bu'i` → **typed quantification at `PredTerm<ρ>`** —
  predicate-typed variables, not predicate objects (the §9.1 reserved family
  is untouched; pin P30): the row ρ is ⊳ fixed consistently across every
  occurrence (the exact resolved row; incompatible uses = no resolved
  reading); bare `bu'a` carries implicit `su'o`, and any other quantifier
  requires the prenex (CLL Example 16.107); restrictions must be pure and already
  typed at `PredTerm<ρ>` — an ordinary first-order `ke'a` clause on a
  predicate variable does not type (reserved-family territory, §14).
- **L5.6** `cei` + `broda`-series → ⊳ **bridi-template** binding (CLL 7.5):
  the template stores fills, tense, and negation, and expansion applies the
  documented later-fill override before lowering — the `go'i` machinery, not a
  bare `PredTerm` value; unassigned `broda`-series words are CLL's schematic
  sample predicates, not contextual retrievals.
- **L5.7** When a quantifier or `Generic` takes a nuclear `C_x :
  ClauseContent`, it closes each instantiation locally and lifts the complete
  quantified claim: `(StateClause (Q P {λ [$x] (CloseClause C_x)}))`. It
  never passes one shared lexical event through all quantifier instantiations.
- **L5.8** Declarative logical connection uses
  `ClauseNot`/`ClauseAnd`/`ClauseOr`/`ClauseImp`/ `ClauseIff`/`ClauseXor`
  (§4.6), whose underlying Content operators remain `¬ ∧ ∨ → ↔ ⊕` with the
  surface grammar fixing structure.
- **L5.9** `na` ≡ left-edge `naku`; `naku` movement flips quantifiers per CLL
  ch. 16;
- **L5.10** `ja'a`/`je'a` → identity at their loci — transparent (`na je'a
  broda` ≡ `na broda`) — except that an affirmer ⊳ **overrides inherited
  negation** in a pro-bridi expansion (`ja'a go'i` over a negative template
  removes the `na`; pin P31); `Scalar` gains no fourth kind, emphasis is
  absence or `ba'e` focus.
- **L5.11** Applied `na'e`/`to'e`/`no'e P` bind the applicable domain visibly:
  `((NAhE P) fills…) ↦ {Bind [$d :: ContrastDomain ρ(P)] (Context
  domain-constraint deps…) ((Scalar OtherThan|Opposite|Neutral $d P)
  fills…)}`; the constraint and dependency profile come from the lexical
  entry and resolved reading (§6.3).
- **L5.12** Sentence-level **logical** connection (`.i je`, `.i ja`, …) →
  **one performance of the connected clause** — `(Assert (CloseClause
  (ActualClause (ClauseOr C₁ C₂))))` for `.i ja` in the actual mode (the
  resolved CAhA former is never elided, P24), which forces the uniform rule; the host's
  single force is shared by the connection (a force conflict has no resolved
  reading); the schema is stated for the content-taking forces (`Assert`,
  `Command`) — an interrogative host queries the connected content; UI
  targeting distinguishes the compound act from its clauses (pin P32).
- **L5.13** The event/content contribution of constitution-bearing `.i joi` is
  now `JoiClause` (§12);
- **L5.14** *(gap)* its **compound performance** and the other non-logical
  ijoik performance cases remain gap-registered pending the `ConnectionPlan`
  clauses (§14).
- **L5.15** `.i TAG bo` → the same single performance, with component
  ClauseContents exposing both events inside an outer state: `(Assert
  (CloseClause (StateClause (∃e₁ (∧ C₁(e₁) (∃e₂ (∧ C₂(e₂) (tag e₂ e₁))))))))`
  — never closed component contents beside free event variables.
- **L5.16** Jek at the tanru-unit locus → `TanruLinkConnect` (§12; pin P33):
  shared head asserted once, one constrained-`Context` intended link per
  conjunct, connective over the link applications; distinct-head units connect
  as whole predications.
- **L5.17** Plain `joi` at either tanru locus uses `JoiPred` over the
  already-lowered common-row properties;
- **L5.18** *(gap)* missing common rows/bases and the other unmapped joiks
  remain gaps.
- **L5.19** BIhI: `X bi'o Y` → the ordered `Interval` (a `Set` object) with
  GAhO endpoint kinds; `bi'i` → ⊳ symmetrization (normalize endpoint order
  with their kinds) then the same; `mi'i` → `MetricBall` (§12 — no endpoint
  arithmetic); `bi'o nai` → `RegionComplement` in a Context universe; joigik
  forethought = the same units; the region object fills the host place, whose
  lexical semantics does the rest.
- **L5.20** *(gap)* BIhI at tanru and sentence loci: **no standard resolved
  mapping exists** (CLL 14.16 says no meanings have been found) — a documented
  no-mapping, and an implementation must not invent one.
- **L5.21** Non-logical: `jo'u` → `Combine`; `ce` → set; `ce'o` → list; `fa'u`
  → `ZipWith`; exact tag/facet `joi` joining → `∧` where it merely conjoins
  facets over an already shared event.
- **L5.22** Constitution-bearing `joi` dispatches by the resolved result type
  (§4.9, §12): ordinary sumti form a complete `Group<T>`; Eventuality operands
  in an Eventuality-demanding place form a complete joint event; common-row
  tanru/property operands form a `JoiPred` property satisfying `GunmaPredAt`
  (`JoiTanru` keeps a shared head separate); afterthought and forethought
  clause connection form `JoiClause`.
- **L5.23** A homogeneous `joi` chain is flattened before one complete cover
  is formed; `se joi` is the same symmetric relation.
- **L5.24** *(note)* There is no fallback `Vague` connecting relation.
- **L5.25** *(gap)* Mixed-row property uses, `pe'e joi` termsets, compound
  ijoik performance, and `joi nai` remain explicit gaps (§14).
- **L5.26** *(gap)* Official `ju'e` likewise has no baseline lowering pending
  its separate vague-connective adjudication (§14).
- **L5.27** `ku'a`/`jo'e`/`pi'u` → `∩`/`∪`/`×`.
- **L5.28** Threshold quantities (`so'i`, `so'e`, …) → the §6.4 degree GQs
  over a `Vague` threshold; the purpose-relative forms (`du'e`, `mo'a`, `rau`)
  additionally bind a `Context` standard (§6.1, §6.4).
- **L5.29** Gradable predication (`ta barda`) → `Grade` over a
  `Context`-recovered scale and a `Vague` cutoff region (§6.4).
- **L5.30** In-situ scope (P41), by lowering category. (i) **Descriptions
  and names** — `lo`/`le`/`la` with any nonzero inner PA (L3.1–L3.3, L3.9) — are
  formed at clause level, outside every in-situ quantifier, in source order
  among themselves (§4.1). (ii) **Quantified sumti** — bare PA under the
  default witness-set reading (L5.2, P17), `ro` (L5.1), inner `no` (L3.10),
  the thresholds (L5.28), and the marked global reading (L5.2, §4.10) —
  scope in surface order, the leftmost outermost, over the clause body
  (original CLL 16.7's grouping; P26 for prenexes): a witness-set form
  (`Exactly`/`AtLeast`/`MoreThan`/`Some`, §12) places its selection `Bind`
  at that point of the body with the body abstracted at the place as its
  reference-level nuclear scope, and a place-absorbing former (`Every`,
  `No`, `GlobalExactly`; `AtMost`/`FewerThan` as negations) takes the body
  abstracted at the quantified place as its nuclear scope, with L0.1
  hoisting where the former is a pure position. (iii) Ungrouped quantifiers
  only: a termset's co-selected quantifiers keep L5.3's joint scope.
  Hence `ro gerku cu tavla lo mlatu` has one contextual cat plurality,
  `ro gerku cu tavla su'o mlatu` lets the cats vary with the dog, and
  `ci gerku cu tavla ro mlatu` selects the three dogs before `ro` applies.
  A description co-varies only when it sits syntactically inside a
  quantifier's restrictor or nuclear predicate (a relative clause, an
  abstraction).

**Events, tense, modals** (L6; P8, P24).

- **L6.1** Every declarative clause is `ClauseContent`. A direct lexical
  episode uses its lexical event as the clause parameter; identity,
  mathematics, negation, quantified/generic claims, and other eventless
  compositions use a holding state.
- **L6.2** Tense/aspect/spatial cmavo and BAI conjoin their event predicates
  to that current parameter: `C ↦ λe.(C(e) ∧ facet(e))`; no second event is
  introduced.
- **L6.3** Tense chains (`pu pu`) compose as anchor paths.
- **L6.4** Tenseless bridi → per the selected reading (P8): episodic → a
  `Context`-anchored temporal facet; habitual/gnomic → no temporal conjunct
  and an outer holding-state clause.
- **L6.5** *(reading)* ⊳ Reading selection is upstream; `ki` stickiness
  propagates resolved tense by source order; ⊳ story time (CLL 10.14) supplies
  narrative sequencing as reading inference, not semantics.
- **L6.6** CAhA applies the §12 ClauseContent formers: `ca'a` →
  `ActualClause`; `ka'e` → `CapableClause`; `nu'o` → `UnrealizedClause`;
  `pu'i` → `DemonstratedClause`. Missing CAhA is reading-multiple among these
  modes with no default (CLL 10.19; P24), so bare capability uses do not
  falsely assert an actual-world event.
- **L6.7** *(gap)* ZAhO boundary relations consume the same current clause
  event (gap-registered until their lexical rows are filled).
- **L6.8** `n roi` → `RoiClause` (§12), **replacing** `CloseClause C` with the
  holding state of the count over C-events in the `During` interval; all
  surface arguments and the interval bind before the pure `SetOf`.
- **L6.9** `roi nai` negates the count condition before the state lift;
  subjective counts reuse the threshold- GQ policy.
- **L6.10** The default interval is the Context-recovered anchor with `Vague`
  extent (CLL 10.9), overridable by explicit ZEhA/`ze'e` forms (P35).
- **L6.11** `fi'o P` uses P as a tag with the lexicon's current clause-event
  link.

**Composite personal pro-sumti** (L7; P40).

- **L7.1** These are ordinary neutral plural references, not logical sentence
  connection and not constituted group objects. Their complete lowerings and
  result types are:

  ```text
  mi'o ↦ (Combine Speaker Audience)                     : Referents<Entity>
  mi'a ↦ (Combine Speaker MiAOthers)                    : Referents<Entity>
  do'o ↦ (Combine Audience DoOOthers)                   : Referents<Entity>
  ma'a ↦ (Combine (Combine Speaker Audience) MaAOthers) : Referents<Entity>
  ```
- **L7.2** *(note)* The §5.1 context constraints make `mi'a` exclude Audience,
  `do'o` exclude Speaker, and every “others” value genuinely other than the
  included role values.
- **L7.3** *(note)* Each displayed result fills one place in one predication.
  In particular, `mi'o klama` has one x1 reference and one omitted-x2
  `Context` site; it does not expand to paired speaker/listener journeys or
  two omitted sites.
- **L7.4** `mi .e do broda` instead connects two separately instantiated
  clauses; `mi jo'u do broda` has the same argument denotation as `mi'o
  broda`; and `mi joi do broda` first constructs §12's canonical
  `Group<Entity>`. No component property inherits to that group (P5).
- **L7.5** *(gap)* Positive `mi'o … mei` does not alter this lowering: the
  separate plural-carrier instance problem remains #24, never a covert second
  group denotation.

**Anaphora** (L8; P16).

- **L8.1** ⊳ `ri`/`ra`/`ru` by CLL ch. 7 counting over accessible referents
  (§5.6);
- **L8.2** `vo'a`-series → bridi-place bindings;
- **L8.3** KOhA assigned → bound variable; unassigned → keyed `Context`;
- **L8.4** ⊳ cross-performance `go'i`/`go'e`/`go'a`/`go'o` expansion uses the
  antecedent occurrence's capture — the resolved template's utterance-context
  projections and `Context` answers stay fixed. For a whole-content assertion
  reuse this is `(RealizedContent u)`; place/negation overrides apply to the
  same captured template rather than reconstructing its sites.
- **L8.5** Other-force pro-bridi reuse has the analogous resolved template but
  no assertion-only `RealizedContent` projection.
- **L8.6** `nei`/`no'a`, and any pro-bridi inside unperformed material, have
  no prior performance requirement: they reuse the already resolved current or
  outer template environment directly.
- **L8.7** `ra'o` selectively discards the inherited capture only at the
  antecedent pro-assign sites it marks. For a performed assertion antecedent,
  the mapping obtains the raw source template through `ActContent (RealizedAct
  u)`, substitutes newly interpreted pro-sumti/pro-bridi at those sites under
  the new performance context, and retains the occurrence-captured values at
  omitted places, tanru links, and other unmarked `Context` sites.
  `InContext`/`ShiftedGround` makes any requested ground shift for the
  reopened material explicit (§5.1). Wholesale raw `ActContent` replay is
  valid only when every context-sensitive site in the template is marked for
  reopening. CLL 7.6 supplies the linguistic discriminator: ordinary GOhA
  repetition is of concepts, its antecedent pro-sumti normally keep their
  meanings, and `ra'o` repeats/reinterprets those pro-assigns in the new
  context. This specification preserves the rest of the resolved template
  rather than silently broadening `ra'o` to unrelated contextual omissions.
- **L8.8** The `di'u` series → utterance anaphora at
  `Referents<UtteranceToken>` (a selected transcript span): ⊳ recency
  resolution over the transcript at three distances, past
  (`di'u`/`de'u`/`da'u`) and future (`di'e`/`de'e`/`da'e`); `dei` → the
  current entry's own bound `CurrentToken`; `do'i` → `Context` for the salient
  token/span — `Vague` only in the span's boundaries (pin P28).
- **L8.9** `la'e` on an utterance anaphor that demands assertion content uses
  `(RealizedContent u)` directly — its projective definedness requires one
  eligible performed, context-resolved host assertion occurrence (§7.4) — then
  applies the **host-sorted** crossing: `EventOfContent` for the
  state-of-affairs reading, `Reify` only where a proposition is demanded; no
  universal coercion (P13), and a non-assertion antecedent yields partiality
  where content is demanded (P21). Where the act package rather than performed
  content is requested, `RealizedAct<F>` remains the raw crossing.
- **L8.10** `doi X` → `(Perform AttachedAddress (Vocative X))` beside the host
  **plus** ⊳ binding of the active `do` (CLL 2.14 — `do` "now refers to" X):
  `do` and `ko` consult the active binding before falling back to the
  utterance's Audience, which itself is never mutated (each utterance's ctx
  carries its own audience as a fact about it; pin P27).
- **L8.11** *(reading)* `da'o` → ⊳ cancellation of **all** resolver
  assignments (KOhA, letteral, and pro-bridi stores);
- **L8.12** *(reading)* `ni'o` levels are segment-stack transitions with
  per-level cleared registers — the assignment-clearing level (`ni'o` spoken,
  `ni'o ni'o` written) clears assignments, the drastic level (one more `ni'o`)
  also resets tenses and indicators, and `no'i` resumes what its `ni'o`
  dropped along with the suspended frame — never a destructive `da'o` alias
  (CLL 7.13, 19.3).

**Abstractions** (L9; §9, P13, P14).

- **L9.1** The `ce'u`-capable abstractors of this baseline are exactly **`ka`
  and `du'u`**. The `du'u` case split:

  ```text
  du'u body, extracted row ⟨⟩    ↦ (Reify (CloseClause body-ClauseContent))
  du'u body, extracted row ρ ≠ ⟨⟩ ↦ the λ over ρ, exactly as ka
                                    (no DuhuRel, no se du'u — §9.2, §14)
  ```

  so `lo du'u ce'u klama` is the goer property, and the Rosta n-adic doctrine
  (n distinct extracted variables = n-adic; bare `du'u` the 0-adic case, whose
  extracted relation *is* the content, `PredTerm<⟨⟩>` ≅ `Content`, then
  reified) holds as a theorem of this mapping over `ka`/`du'u`.
- **L9.2** Elided places inside `du'u` close ordinarily (`zo'e` ≡ omission,
  P15); only explicit `ce'u` extracts.
- **L9.3** *(reading)* Arity counts **distinct extracted variables**: ⊳ `ce'u
  goi` aliasing identifies occurrences and `ce'u xi` indexing selects the
  extracting abstraction, both resolved at the text-to-reading layer.
- **L9.4** *(gap)* Explicit `ce'u` in the other abstractors is unmapped at
  baseline, and not by blanket referral to the reserved family: each would
  need a **result-specific typed analysis** — `lo ni ce'u clani` calls for an
  argument-indexed amount abstraction, and `jei`/`li'i`/the event abstractors
  likewise have their own codomains, none of them a reified `PredTerm<ρ>`
  (§14).
- **L9.5** *(note)* The Rosta all-`ce'u` reading of `si'o`, which genuinely
  nominalizes a predicate into a concept *object*, is the one reading that
  belongs to the reserved family (§9.1). Baseline `si'o` has no covert `ce'u`,
  closes its inner ClauseContent normally, and maps through `SihoRel` with the
  conceptualizing mind at x2 (CLL 11.9) — a stated divergence from the Rosta
  proposal's clause 7.
- **L9.6** `nu` + sorts → `Refer` directly over the ClauseContent event
  property (so eventless identity and mathematical bridi use their
  `StateClause` state);
- **L9.7** `ka` → `λ` (⊳ implicit `ce'u` at first unfilled place, counting
  converted places; P12, a rule of `ka` alone — the experimental lambda-prenex
  `ce'ai` names binder order explicitly where multiple readings arise);
- **L9.8** `ni`/`jei`/`li'i`/`si'o`/`su'u`/`pu'u`/`zu'o` → the abstraction
  relations with reference outside;
- **L9.9** `mo'e` → the `AmountValue` numeric crossing;
- **L9.10** the content parameter supplied to the other abstraction relations
  is `CloseClause` of the inner clause.
- **L9.11** `tu'a X` → constrained `Context` retrieval of the intended
  abstraction, constrained by shape + `srana`-aboutness, **sort selected by
  the host place** (an event place gets an event-sorted abstraction). At that
  event sort the shape condition is `∃p:Proposition. CoRef(v,
  EventOfContent(Holds p))`; quantification remains at the first-order
  Proposition sort and `EventOfContent`'s operand is inert — no
  object-language quantifier ranges over dynamic `Content`. The resolved
  reading declares which governors, if any, the site depends on; enclosing
  binders are not inherited automatically.
- **L9.12** `jai`+tag → explicit role promotion, old x1 to the fillable `fai`
  place (library expansion);
- **L9.13** bare `jai` → `JaiRaise` (§12): for resolved raised sort T and
  old-x1 sort A, retrieve the intended admissible role at `Fn<(Referents<T>,
  Referents<A>), Content>` through constrained `Context`, then conjoin that
  role between the new x1 and the old x1 at `fai`. The dependency profile
  follows §5.3, and a missing `fai` closes contextually like any other place
  (P14).
- **L9.14** `la'e`/`lu'e` → interpretation / sign-of crossings.

**Questions and answers** (L10; §8, P9).

- **L10.1** `xu` → `Polar`;
- **L10.2** `ma`/`mo`/`fi'a`/ `xo`/`ji`/`cu'e`/`pei` → `OpenQ` at their typed
  domains — ⊳ bare interrogatives take utterance-level scope even from
  embedded positions (CLL 11.8; §8.1);
- **L10.3** `kau` → `ContextualAnswer` with absent exhaustivity;
- **L10.4** `go'i` as answer → `Answer` with polar selection.

**Indicators and discourse** (L11; §7, P19).

- **L11.1** *(reading)* ⊳ UI target selection by grammatical attachment
  (FUhE/FUhO extend);
- **L11.2** UI → displayed-content relations per lexicon entries with
  host-force profiles;
- **L11.3** evidentials → the family force clause;
- **L11.4** `dai` → experiencer shift;
- **L11.5** `nai` → lexical pair;
- **L11.6** degree words → intensity regions.
- **L11.7** `.i` sequencing → `Do`;
- **L11.8** `ni'o`/`no'i` → `NewTopic`/`Resume`;
- **L11.9** discursives → library discourse relations;
- **L11.10** `po'o`, constituent `ji'a` → focus derivations;
- **L11.11** COI → performative expressive acts;
- **L11.12** `mi'e` → performative self-naming;
- **L11.13** `na'i` → the objection act (§7.3).
- **L11.14** `n mai`/`n mo'o` → `EnumerationOrdinal` display facts (§12) at
  the **attachment-selected** constituent (CLL 19.7 numbers sumti inside one
  bridi — not always the utterance), item and section level respectively;
  sequence key and resets Context-recovered; no temporal order implied.

**Quotation, signs, MEX** (L12; §7.5, §4.9).

- **L12.1** `lu…li'u` → `StructuredQuote`;
- **L12.2** `lo'u…le'u`/`zoi` → `OpaqueQuote`;
- **L12.3** `zo` → `WordSign`;
- **L12.4** letterals → `LetteralSign` (⊳ letteral anaphora keys bindings);
- **L12.5** `me'o` → mention of a math-expression sign;
- **L12.6** `li` → the value;
- **L12.7** `du` → `=` / `CoRef` (P23), then `StateClause` at the
  declarative-clause layer (so tense, CAhA, ROI, ZAhO, and `nu` all have a
  state parameter);
- **L12.8** operators → typed functions;
- **L12.9** `xi` subscripts → application.
- **L12.10** `me X [me'u]` → `(MePred X)` (§12);
- **L12.11** number + MOI → the MOI relation families (§12);
- **L12.12** `me … me'u MOI` composes them.
- **L12.13** MEX conversions `na'u`/`nu'a`/`ma'o`/ `ni'e` → the §12 partial
  interfaces (definedness projective; `ma'o`'s function recovery is `Context`,
  pin P36);
- **L12.14** `se` on operators → argument permutation.
- **L12.15** Numeral notation (`pi`, `fi'u`, `pi'e`, `ki'o`, `ra'e`, `ce'i`) →
  ⊳ numeral syntax producing `Number` constants (fractions, mixed radix with
  `pi'e`'s base data, grouping with `ki'o` zero-padding, repeating digits,
  percent);
- **L12.16** `xo'e` (experimental) → `Context` at `Number` (P15's analogue);
- **L12.17** `ji'i` → the §12 approximation schemas by position —
  prefix/medial approximate (`AdmissibleTolerance`), suffix rounds,
  directional under `ma'u`/`ni'u` (pin P37).
- **L12.18** `la'o` → the ordinary naming route at the opaque text payload
  (`(NameSign t)`/`Named` unchanged, §12);
- **L12.19** `zo'oi` (experimental) → the word-level opaque sign.

## 12. Library

Normative derived forms, **defined in the core language**; each
definition is its specification (Eberban's from-scratch discipline).
Metalanguage recursion (over `Natural`, over list structure) is permitted
in definitions; the term language itself has no recursion former (§4.4).
Schematic variables: `P, Q` properties; `r` plural references; `n`
naturals; `ρ` rows.

**Cardinal and logical quantifiers** (witness-set semantics, §4.10;
export status per §5.6). Types: restrictors `P : Fn<(T), Content>` are
pure member-level properties; the witness forms' nuclear scope `Q` is a
property **of the witness reference**, `EFn<(Referents<T>), Content>` —
neutral plural predication, per P4; `Every`'s nuclear scope is
member-level (`ro` is each — CLL ch. 16), as is `GlobalExactly`'s:

```text
(Exactly n P Q)  ≝ {Bind [$w :: Referents T] (SelectExactly n P) (Q $w)}
(AtLeast n P Q)  ≝ {Bind [$w :: Referents T] (SelectAtLeast n P) (Q $w)}
(Some P Q)       ≝ {Bind [$w :: Referents T] (SelectSome P)      (Q $w)}
(Every P Q)      ≝ {Bind [$w :: Referents T] (MaxRefer P)
                     (Distrib Q $w)}          ; the import is MaxRefer's
                                                ; own presupposition (below),
                                                ; emitted before any witness
                                                ; can fail; exports w
(No P Q)         ≝ (¬ (Some P Q))                          ; no export
(AtMost n P Q)   ≝ (¬ (AtLeast n+1 P Q))                   ; no export
(MoreThan n P Q) ≝ (AtLeast n+1 P Q)
(FewerThan n P Q)≝ (¬ (AtLeast n P Q))                     ; total at n = 0
(GlobalExactly n P Q) ≝ (= (Card (SetOf {λ [$x :: T] (∧ (P $x) (Q $x))})) n)
(Distrib Q r)    ≝ (∀ {λ [$x :: T] (→ (Among $x r) (Q $x))})
                   ; T the member type of r; $x lifts to a singleton
                   ; reference for Among — Distrib is unit distribution
```

**Zero and the selection floor.** The selections are formed only at
n ≥ 1: `SelectExactly 0` and `SelectAtLeast 0` are ill-formed — a
witness reference is nonempty by type (§3.2), so there is no
zero-strength witness to select. The boundary GQ cases are defined
directly, with no selection and no export:

```text
(AtLeast 0 P Q)  ≝ ⊤                ; trivially satisfied, exports nothing
(Exactly 0 P Q)  ≝ (No P Q)         ; the zero count is absence (P22)
```

The rest follow from the definitions: `MoreThan 0` = `AtLeast 1`;
`AtMost 0` = `No`; and `FewerThan 0` = `(¬ ⊤)` — never true, as
arithmetic demands.

`GlobalExactly` and `Most` place their operands inside `SetOf`, so
**both operands must be pure there**: the mapping hoists a nuclear
scope's `Context`/`Vague` sites out of the comprehension first (L0.1), and a
nuclear scope that would introduce a referent has no global reading unless
that reference is already bound outside the comprehension — introductions
are not hoisted.

`no prenu cu jmaji` is `(No prenu-property {λ [$w :: Referents Entity] (Close (jmaji $w))})` —
"no people-witness gathers", the reading a distributive quantifier
could not express at all (§4.10).

**The export contract.** The exporting forms are exactly the definitions
whose expansion is an outer `Bind` of a selection or maximal reference
(`Exactly`, `AtLeast`, `Some`, `MoreThan`, `Every`); that `Bind` may be
spelled at any width up to the enclosing `Do` — the accessibility table's
witness row licenses the widening, and the mapping spells the binder at
the width later anaphora requires (narrow when nothing refers back, over
the continuation when something does). The non-exporting forms (`No`,
`AtMost`, `FewerThan`, `GlobalExactly`) contain their selection under `¬`
or comprehension, where nothing escapes.

**Degree quantifiers** (§6.4; `θ` a `Vague` threshold, `σ` a `Context`
standard where marked). Admissibility predicates, declared here with
their VC1 nonemptiness axioms: `AdmissibleThreshold : ThresholdKind ×
Fn<(T),Content> × [Referents<Entity>] → Fn<(Natural), Content>` — with
`ThresholdKind` the closed enumeration `ManyK | FewK | TooManyK |
TooFewK | EnoughK` (an index type, nothing to do with the rejected
`Kind` sort of individuals, P3) — (for
every kind, restrictor, and standard, some threshold is admissible) and
`AdmissibleCutoff : Scale × Region<Scale> → Content` (every scale has an
admissible region — the gradable analogue, consumed by `Grade`'s
`Vague` region):

```text
(Many P Q)   ≝ {Bind [$θ :: Natural] (Vague (AdmissibleThreshold ManyK P))
                 (AtLeast $θ P Q)}
(Few P Q)    ≝ {Bind [$θ :: Natural] (Vague (AdmissibleThreshold FewK P))
                 (FewerThan $θ P Q)}
(Most P Q)   ≝ (> (Card (SetOf {λ [$x :: T] (∧ (P $x) (Q $x))}))
                  (Card (SetOf {λ [$x :: T] (∧ (P $x) (¬ (Q $x)))})))
(TooMany P Q)≝ {Bind [$σ :: Referents Entity] (Context)          ; purpose
                      [$θ :: Natural] (Vague (AdmissibleThreshold TooManyK P $σ))
                 (MoreThan $θ P Q)}
(TooFew P Q) ≝ {Bind [$σ :: Referents Entity] (Context)
                      [$θ :: Natural] (Vague (AdmissibleThreshold TooFewK P $σ))
                 (FewerThan $θ P Q)}
(Enough P Q) ≝ {Bind [$σ :: Referents Entity] (Context)
                      [$θ :: Natural] (Vague (AdmissibleThreshold EnoughK P $σ))
                 (AtLeast $θ P Q)}
```

Gradable predication: a `GradableRel<ρ,ℓ>` is a lexical relation whose
entry's **degree field** (§10) declares its graded place `ℓ : Label<ρ>`
and a degree projection

```text
deg_R    : Record ρ × Scale → Amount    (the degree may consult any
                                         place of the row, not only ℓ —
                                         comparison classes and standards
                                         live in the other places)
InRegion : Amount × Region<Scale> → Content
```

(`Region<Scale>` — poles, midpoints, intervals — declared here for the
whole document). Then

```text
(Grade R s reg) : PredTerm<ρ> ≝
  {λ [$rec :: Record ρ] (InRegion (deg_R $rec s) reg)}
```

— the relation holding of a row record exactly when its degree
on scale `s` lies in region `reg`.

**Complement selection** (`da'a`, CLL 18.8; default n = 1). A
**declared** primitive member of the §5.6 selection family (like its
siblings, its witness law is its axiom) — neutral witness sets,
ordinary export:

```text
(SelectAllBut n P) : RefComp<Referents<T>>   ; witness law:
   ; (∧ (CoveredBy P w)
   ;    (= (Card (SetOf {λ [$x :: T] (∧ (P $x) (¬ (Among $x w)))})) n))
   ; — the witness is P-covered without residue AND leaves exactly n
   ; P-individuals behind, spelled by comprehension: the plural kernel
   ; has no difference operator and needs none. Which individuals are
   ; left out is not a semantic parameter (neutral witness selection,
   ; P17); under distributive scope they may vary per instance (CLL's
   ; ro ratcu cu citka da'a re …). Nonemptiness of the witness follows
   ; from the reference type; model-side existence of a qualifying
   ; witness is the selection's success condition.
```

**Approximation** (`ji'i`, CLL 18.9; completes §6.4's classification).
`Precision` is the numeral's ⊳-supplied precision descriptor (which
digits/places are stated — an index sort of numeral syntax, never a
term-level computation). `AdmissibleTolerance` is the `Vague`
admissibility former for approximate number regions,
`AdmissibleThreshold`'s sibling:

```text
AdmissibleTolerance : Number × Precision → Fn<(Number), Content>
   ; admissible values: numbers within the tolerance region about the
   ; anchor at the given precision; the region's boundary is the Vague
   ; dimension; nonempty by VC1.
```

Position matters (CLL 18.9), and the numeral's value is what changes:
a prefix or medial `ji'i` numeral **denotes the computation**
`(Vague (AdmissibleTolerance n prec))` — a `Number`-valued
precisification family,
bound at its use site like any effectful operand (`prec` the
numeral's own precision descriptor); a suffix-`ji'i` numeral likewise
denotes a `Number`-valued precisification family over the **rounding preimage** —
`AdmissibleRounding : Number × Precision × Direction → Fn<(Number),
Content>` admits the numbers whose rounding at `prec` toward the
`ma'u`/`ni'u` direction (both sides unmarked; `Direction` the closed
Up | Down | Either) is the stated value — so the underlying quantity
is explicitly the bound `Number`, the stated digits exact by
construction of the region (nonempty by VC1; pin P37).

**Plurality and collections:** `UnitSet`/`CardBasis` (§4.8). The canonical
group constructions and collection crossings are:

```text
(CanonicalAggregateAt κ g C) ≝
  (∧ (Aggregate κ g) (CompleteGunmaAt κ g C))

(Massify κ C) : RefComp<Referents<Group<T>>> ≝
  (SelectExactly 1
    {λ [$g :: Group T] (CanonicalAggregateAt κ $g C)})

components_κ : Group<T> ⇀ Referents<T>
components_κ(g) = C exactly when CompleteGunmaAt κ g C
```

`components_κ` is partial where no complete cover exists and functional by
(F). `Massify` is definite by (E)+(A); it is a defined selection, not a
primitive term constructor. Repeated manufacture at one κ and `CoRef` cover
returns the same aggregate. An independently individuated organization with
that cover need not be the aggregate.

The LAhE collection crossings are type-directed:

- `lu'a r` on an ordinary plural reference marks member-wise use (`Distrib`
  at the consuming locus); on one `Set<T>` object it returns its nonempty
  member reference; on one `Group<T>` object it returns `components_κ(g)` at
  a constrained, dependency-declared basis and is projectively undefined
  without one. Several collection objects require an explicit flattening
  reading; no silent crossing is supplied.
- `lu'o X` retrieves an admissible group basis κ, resolves X's underlying
  nonempty reference (ordinary reference directly, set members, group
  components, or list elements), and returns `Massify κ C`. On an
  organization this canonicalizes its current cover; it is identity only
  when X already is that canonical aggregate at κ.
- `lu'i X` forms the exact `Set<T>` of the resolved covering units at a
  constrained unit basis. For a non-null operand an admissible basis cannot
  be unitless (§4.9's cover law); absent an admissible/recoverable basis the
  reading is undefined, not the empty set. Set input is identity.
- `vu'i X` forms a `List<T>` over those same units. If an order is intended,
  it is one constrained `Context` site and the returned list keeps that order
  for anaphora. A genuinely no-particular-order use is not defaulted to
  `Context`; it remains the §14 `SomeAdmissible` witness candidate pending
  evidence.

Empty set/list/member crossings and `nomei` remain governed by the nonempty
reference boundary and §14/#23.

`(Overlap a b)` ≝ `(∃ {λ [$c :: Referents T] (∧ (Among $c a) (Among $c b))})`;
`(Interval a b k₁ k₂)` ≝ `(SetOf {λ [$x :: T] (∧ (cmp₁ a $x) (cmp₂ $x b))})` with
`cmpᵢ` strict/nonstrict per the `ga'o`/`ke'i` endpoint kinds. The
reciprocal schema (consumed by `simxu`'s and `soi`'s lexicon rows):

```text
(Reciprocate r P) ≝
  (∀ {λ [$x $y :: T]
       (→ (∧ (Among $x r) (Among $y r) (¬ (= $x $y)))
           (P $x $y))})    ; member-wise, both ways: T is r's member
                            ; sort; the units singleton-lift at Among
                            ; and at P's places (§3.2). Vacuous on a
                            ; unitless (atomless) reference —
                            ; reciprocity of unstructured stuff needs
                            ; an explicit basis and is not claimed.
```

**Lists and `fa'u`** — the mandated full expansion. `ZipWith` is defined
by metalanguage recursion over list structure:

```text
(ZipWith f (List) (List))                 ≝ ⊤
(ZipWith f (List a as…) (List b bs…))     ≝ (∧ (f a b)
                                               (ZipWith f (List as…) (List bs…)))
```

so the `fa'u` specimen expands completely:

```lisp
; mi fa'u do tavla do fa'u mi
(ZipWith {λ [$s $l :: Referents Entity]
           (Close (tavla $s $l))}
  (List Speaker Audience)
  (List Audience Speaker))
; ≡ (∧ (Close (tavla Speaker Audience))
;      (Close (tavla Audience Speaker)))
```

**Reference utilities:**

```text
(CoRef x y)     ≝ (∧ (Among x y) (Among y x))    ; plural co-reference
(Named t x)     ≝ (Close (cmene (NameSign t) x)) ; bearer of name-sign t,
                                                 ; naming convention from
                                                 ; the lexicon's cmene row
(MaxRefer P)    : RefComp<Referents<T>> ≝
  (Presuppose (∃ P)                       ; defined only when P is
    (Refer {λ [$r :: Referents T]          ; inhabited
      (∧ (CoveredBy P $r)
          (∀ {λ [$x :: T] (→ (P $x) (Among $x $r))}))}))
                ; all P-satisfiers, only P-covered parts: every unit is P,
                ; every P-satisfier is Among it, and every subreference
                ; overlaps a P-unit (no atomless residue) — the maximal
                ; base (Every's export and explicit maximal uses). Models must supply
                ; this reference for each inhabited pure restrictor the
                ; mapping can form (a model condition: plural
                ; comprehension for P).
```

(`Holds`, `Reify`'s primitive inverse, is declared with it in §9.1.)

**Speaker description** (`le`; P10, L3.2). The description relation is
the lexical `skicu` (official x4 the description property); the defined
form fixes the describing event as this utterance's own locution:

```text
LocutionOf : Referents<UtteranceToken> × Referents<Locution> → Content
                ; the token's uttering event — token first, like §7.4's
                ; other entry predicates (SpeakerOf, AudienceOf, …)
(SpeakerDescribes r P) : Content
   ; r : Referents<T>, T ≤ Entity — the described reference (a member
   ; lifts to its singleton, §3.2); P : EFn<(Referents<T>), Content> —
   ; the description property, handed to skicu's x4 as a value, so the
   ; form is pure whatever P's arrow
(SpeakerDescribes r P) ≝
  (∃ {λ [$e :: Referents Locution]
    (∧ (LocutionOf CurrentToken $e)
       (skicu Speaker r Audience P :Eventuality $e))})
(SpeakerDescribesUnaddressed r P) : Content
   ; voi (L4.3): the same r and P, the audience place deleted
(SpeakerDescribesUnaddressed r P) ≝
  (∃ {λ [$e :: Referents Locution]
    (∧ (LocutionOf CurrentToken $e)
       ((DropPlace skicu 3) Speaker r P :Eventuality $e))})
```

Each form is the term: no other spelling abbreviates it (§2), which is why
the samples book displays them verbatim. `voi` (L4.3) goes through the
sibling form: deleting `skicu`'s audience place removes the addressee, not
the reason for the anchor — a `voi` description is likewise constituted by
this utterance's own locution (#49).

**Temporal incidence** (ROI's interface; P35). Declared:

```text
During : Referents<Eventuality> × Set<Time> → Content
   ; the eventuality's temporal extent lies within the interval —
   ; the same lexical facts the tense facets consult, packaged as a
   ; relation the counted schema can restrict by
```

The `n roi` schema, for a host `C : ClauseContent` whose surface arguments and
contextual effects have been bound so its event property is pure, and bound
interval `I`, is itself an outer holding-state clause:

```text
(RoiClause n C I) ≝
(StateClause
  (= (Card (SetOf {λ [$e :: Eventuality] (∧ (C $e) (During $e I))})) n))
```

This **replaces** `CloseClause C`: the counted component events remain the
members of the set, while the declarative clause eventuality is the state of
the count claim holding. `roi nai` negates the equation before `StateClause`;
subjective counts substitute the threshold-GQ condition for `=`.

**Events and tags.** `EventOfContent` is declared and constrained in §9.3.
The CAhA base is the primitive
`InnatelyCapable : ClauseContent → Content`: the clause event property is
realizable in worlds compatible with the relevant participants' innate
natures, with participant roles supplied by the lexical predication rather
than a hard-coded x1-only wrapper. Likewise the lexical projection
`MotionVector : Referents<Eventuality> × Referents<Entity> ×
Referents<Entity> → Content` (the `mo'i` heading: the event's `muvdu`
motion with `farna` direction). The CAhA clause formers are:

```text
(Realized C)           ≝ (∃ {λ [$e :: Referents Eventuality]
                              (∧ (C $e) (fasnu $e))})
(ActualClause C)       ≝ {λ [$e :: Referents Eventuality]
                            (∧ (C $e) (fasnu $e))}
(CapableClause C)      ≝ (StateClause (InnatelyCapable C))
(UnrealizedClause C)   ≝ (StateClause
                            (∧ (InnatelyCapable C) (¬ (Realized C))))
(DemonstratedClause C) ≝ (StateClause
                            (∧ (InnatelyCapable C) (Realized C)))
```

These are respectively `ca'a`, `ka'e`, `nu'o`, and `pu'i`. The last three
make the capability claim's holding-state their outer clause eventuality; the
possible/demonstrating C-events remain inside. Missing CAhA selects one of
these same modes upstream under P24, never an unstated fifth default.
For every lowering-produced direct or holding-state C, `ActualClause`'s
`fasnu` conjunct is extensionally redundant: the direct route has §5.1's
lexical occurrence law, and a satisfying `StateClause` candidate is already
actual. It remains overt because it records the selected CAhA mode uniformly.
The redundancy is not an axiom about arbitrary values inhabiting the
transparent `ClauseContent` function type; for example, a generic core
function `λe.⊤` supplies no occurrence claim until a caller adds one.

Tense helpers per the lexicon's tag-reduction rows. Tagged `jai`: for
a lexical row ρ with promoted role ℓ, writing ρ' for ρ with ℓ
relabelled `1` and `1` relabelled `fai`,

```text
(JaiPromote R ℓ) : PredTerm ρ' ≝
  {λ [$r :: Record ρ']
    (R ⟨the ρ-record with ℓ = $r.1 and 1 = $r.fai; rest unchanged⟩)}
```

— the promoted role becomes place 1 and the old place 1 becomes the labelled,
*fillable* `fai` place (closing contextually like any place when
unfilled — CLL 9.12).

**Bare `jai` role raising.** Let R have old place 1 type `Referents<A>`, and let
the resolved reading select raised-sumti sort T. The pure axiomatic
admissibility family

```text
JaiRoleAdmissible :
  PredTerm ρ × Fn ((Referents T) (Referents A)) Content → Content
```

holds of exactly the relations that interpret a T-sumti's admissible role in
an A-valued abstraction occupying R's old place 1. This is an interface constraint,
not reflection over an abstraction's syntax: ordinary place roles and exact
tag-reduction roles may satisfy it, while the baseline exposes no AST from
which to enumerate them. For a role K it defines the pure relation former

```text
(JaiRaise R K) : PredTerm ρ' ≝
  {λ [$r :: Record ρ']
    (∧ (R ⟨the ρ-record with 1 = $r.fai; rest unchanged⟩)
       (K $r.1 $r.fai))}
```

where ρ' replaces R's place 1 by `(1 (Referents T))` and adds the labelled,
fillable `fai:Referents<A>` place. Bare `jai` binds K visibly at the applied
predicate locus:

```text
((jai R) fills…) ↦
{Bind [$role :: Fn ((Referents T) (Referents A)) Content]
      (Context
        {λ [$k :: Fn ((Referents T) (Referents A)) Content]
          (JaiRoleAdmissible R $k)}
        deps…)
  ((JaiRaise R $role) fills…) }
```

T and A are indices of one resolved typed reading, not members of a union;
the profile must include every governor free in R or its constraint under
§5.3. CLL 9.12 supplies the x1/`fai` routing, while CLL 11.10 leaves which
underlying argument was raised unstated. Tagged `jai` remains `JaiPromote`.

**Acts and discourse:** discourse relations `Contrast`, `Addition`,
`Parallel`, `Elaboration` — lexical relations over two performed
`ActOccurrence` handles by default, displayed act-level per §7.6 (raw acts
remain explicit alternative targets); the `na'i` objection ≝

```lisp
(NahiObjection t) ≝
  {Bind [$d :: DefectKind] (Context)
    (Express (Close (MetalinguisticallyDefective t $d)))}
```

for a bound prior target `t` (`DefectKind` — wording, form, implication,
presupposition, register — is declared with the objection relation); COI
schemas ≝ performative `Express` of the COI lexical relation
(`coi-greeting`, `ki'e-thanks`, …), schematically `(COIExpress R
addr) ≝ (Express (Close (R Speaker addr)))` with the entry's
performative host-force profile; for `a : Act<F>`, `(GroundedBy b a)` ≝
`{Bind [$o :: ActOccurrence F] (Perform Host a)
   (Do (Perform AttachedDisplay
          (Express (Close (EvidentialBasis Speaker $o b)))))}` —
the act-level evidential spelling of §7.6 (named to
avoid the `Ground` sort, §5.1); focus for
a host content frame `H[·]` and focused sumti `f : Referents<T>`
(the alternatives `$y` singleton-lift into `CoRef` at `f`'s type):
`(Only f H) ≝ (Presuppose H[f] (¬ (∃ {λ [$y :: T] (∧ (¬ (CoRef $y f)) H[$y])})))`
(`po'o`), and `(Additive f H) ≝ (Presuppose (∃ {λ [$y :: T] (∧ (¬ (CoRef
$y f)) H[$y])}) H[f])` (constituent `ji'a`).

**Sumti-based selbri** (`me`, CLL 5.10): the Among-property —

```text
(MePred X) ≝ {λ [$w :: Referents T] (Among $w X)}   ; X's computation,
   ; if any, is bound before the pure property forms; T is X's sort.
   ; Singleton X: extensionally the P23 identity/co-reference.
```

The ratified gadri definitions expand `lo PA sumti` through `me`, so
this form retroactively grounds the P1 inner-PA machinery.

**MOI relation families** (CLL 18.11): five lexical relation families
indexed by the number `n`, catalogued with exact rows — not term
expansions (their content is lexical):

`Ordering T` is the pure comparison type `Fn (T T) Content`
(total and transitive as a definedness condition on its uses).
The rows, labelled and typed (P25's referential discipline; the
`Ordering` place is function-typed, the `InnatelyCapable` precedent):

```text
(MeiRel κ n) : PredTerm
  (Row (1 (Referents (Group T))) (2 (Referents (Set T)))
       (3 (Referents T)))
   ; κ : GroupBasis<T>, hoisted by the surface occurrence's constrained
   ; Context site before this pure row value is formed.
   ; lexical content: x1 is completely constituted, at the row's
   ; constrained GroupBasis<T>, by exactly x2's members, and
   ; (= (Card s) n) at the presupposed sole set member s of x2 (the
   ; §9.2 projective singular pattern); x3 among s's members.
   ; Objective-indefinite n extends the row with the comparison set
   ; x4:Referents<Set<T>>; subjective n extends it with the standard
   ; place (the degree quantifiers' σ, a Referents<Entity>).
(MoiRel n)  : PredTerm
  (Row (1 (Referents T)) (2 (Referents (Set T))) (3 (Ordering T)))
   ; x1 is the n-th member of x2 under x3; x3 Context-recovered when
   ; unstated; definedness: n within x2's cardinality.
(SiheRel n) : PredTerm
  (Row (1 (Referents Entity)) (2 (Referents Entity)))
   ; x1 is an n-fraction portion of the mass x2 (CLL: portion of
   ; mass); the fraction n a Number in (0, 1].
(CuhoRel n) : PredTerm
  (Row (1 (Referents Eventuality)) (2 (Referents Eventuality)))
   ; event x1 has probability n under conditions x2 — an opaque
   ; lexical relation; formation condition 0 ≤ n ≤ 1; the model
   ; supplies the measure. NO probability calculus enters the core
   ; (pin P29).
(VaheRel n) : PredTerm
  (Row (1 (Referents Entity)) (2 (Referents Scale)))
   ; x1's degree on x2 (through the gradable projection its lexical
   ; content names) lies in position n's region.
```

For positive `n`, the `MeiRel κ n` clause is stated by the pure maximal member
cover `m : Referents<T>` of the sole set `s` (the `MaxRefer` coverage pattern,
but no discourse introduction):

```text
MemberCover(s,m) ≝
  Distrib (λx.(x ∈ s)) m
  ∧ ∀x.(x ∈ s → Among(x,m))
  ∧ ∀r.(Among(r,m) → ∃x.(x ∈ s ∧ Overlap(x,r)))
```

After the mapping hoists the row's constrained κ site, its content includes
`MemberCover(s,m)`, `CompleteGunmaAt κ x1 m`, `Card(s)=n`, and
`Among(x3,m)`. Thus a threesome
cannot contain a fourth peer component. At `n=0` this expansion is unavailable:
`x3` and `Referents<T>` are nonempty, while the experimental dictionary entry
for `nomei` explicitly proposes an empty mass/0-tuple. Whether `Group<T>`
admits a null object and how a complete empty cover is represented without an
empty `Referents<T>` are gap-registered (§14; GitHub #23); the baseline neither
declares the form false nor inserts a covert empty plurality.

The `me X me'u MOI` composite (CLL Example 18.93) applies the family
the MOI cmavo selects at the number the `me`-complement supplies —
the complement's referent under the projective singular condition and
the `Number` sort (`li ny. su'i pa` supplies its sole numeric
member); never a property in the number index. The **non-numeric**
composite (CLL Example 18.94's `cu'o` snowball) is a **registered
divergence-gap**: its CLL reading would need value-indexed families
beyond the `Number` index, and no analysis is assigned (§14).

**Regions and intervals** (BIhI, CLL 14.16). `Metric<T>` is the pure
distance type `Fn<(T, T), Number>`, Context-recovered (spatial
distance, duration, …). Endpoint and center sumti are references;
each former below is defined — like the §9.2 numeric crossings — at
the reference type under the projective singular condition (the sole
member is what the definition consumes). `bi'o` takes the ordered
`Interval` (above) at ordered domains, endpoint kinds per GAhO;
`bi'i` at an ordered domain is its symmetrization (⊳ normalize
endpoint order together with their GAhO kinds), and at a metric
domain it is the betweenness span; `mi'i` is metric, never endpoint
arithmetic:

```text
(MetricBall c rad d k) ≝ (SetOf {λ [$x :: T] (cmpₖ (d c $x) rad)})
   ; cmpₖ = ≤ or < per the GAhO kind k; rad : Number — a measure
   ; sumti supplies it through AmountValue at its scale (§9.2)
(SpanRegion a b d k₁ k₂) ≝
   (SetOf {λ [$x :: T]
     (∧ (= (+ (d a $x) (d $x b)) (d a b))
        (endₖ₁ $x a) (endₖ₂ $x b))})
   ; metric betweenness; endₖ is ⊤ for ga'o and (¬ (= $x ·)) for
   ; ke'i — the endpoint kinds govern membership, as Interval's cmpᵢ do
(RegionComplement U A) ≝ (SetOf {λ [$x :: T] (∧ (∈ $x U) (¬ (∈ $x A)))})
   ; U the Context-recovered universe — the bi'o-nai reading
```

**MEX conversions** (CLL 18.18, 18.19, 18.21): **declared partial
crossings**, row-indexed, each with a projective definedness
condition (§5.5) — the core supplies no totality or unique-result
guarantees:

```text
RelToOp ρ : PredTerm ρ ⇀ Fn (Number …) Number           ; na'u
   ; defined only at rows whose x1 and operand places take
   ; Referents<Number> (each fill projectively singular): the
   ; operator maps the operands' sole members to the sole x1 member —
   ; definedness includes functionality of the relation in x1 there.
OpToRel : Fn (Number …) Number →
  PredTerm (Row (1 (Referents Number)) (2 (Referents Number)) …)
   ; nu'a — total: x1's sole member is the operator's result at the
   ; operands' sole members (P25's referential places; singular
   ; conditions formation-level).
OperandToOp : Number → RefComp (Fn (Number …) Number)   ; ma'o
   ; the intended function is a Context recovery — hence the
   ; computation type; the constant-function ambiguity CLL 18.21
   ; records is a recovery, not a default (pin P36).
AmountOperand ρ : PredTerm ρ ⇀ RefComp Number           ; ni'e
   ; its own crossing, NOT `NiRel` (which reifies an abstraction):
   ; defined where the row names a Number-sorted result place; the
   ; result is the computation that closes the remaining places per
   ; §4.6's discipline and selects the result place's sole member.
```

`se` on operators = argument permutation (a pure λ rewrite at the
known arity). Everything beyond these crossings — including `mo'e`'s
general sumti-to-operand cases past the §9.2 `AmountValue` route —
remains in the §14 MEX gap.

**Foreign names** (`la'o`; `zo'oi` experimental): parsing yields an
opaque text payload `t : Text`, and `la'o` is simply the §11 naming
route at that text — `(NameSign t)` and the `Named` relation apply
unchanged (no new former; the payload's being non-Lojban is a fact
about the text, not a type). `zo'oi` quotes one non-Lojban word as an
opaque word-level sign.

**Enumeration ordinals** (MAI, CLL 19.7): a non-at-issue metadata
relation — **declared**, not defined — displayed through the §7.6
machinery. `EnumerationLevel = Item | Section` is a closed index
type; `SequenceKey` is its own declared index sort (a sequence
identifier, Context-recovered with its reset behavior — distinct from
§5.3's retrieval-site keys); the target is the
⊳ attachment-selected constituent's bound value (a referent, sign, or
act — CLL 19.7 numbers sumti within one bridi, so the target is NOT
always the containing utterance):

```text
EnumerationOrdinal : Target × Number × SequenceKey × EnumerationLevel
                     → Content
   ; Target the union of the attachable values; `mai` = Item,
   ; `mo'o` = Section; NO temporal ordering of denoted events implied.
```

Display placement is §7.6's exactly: a constituent target takes one
`Supplement` anchored at the bound target with the ordinal fact as
side content; an act-level target takes an `Express` beside the
shared host act.

**Topic resolution** (`zo'u`, CLL 19.4). The comment frame is a
**mapping-level schematic** — the comment's open predication with its
row ρ, never a term-language object; `TopicResolution<ρ>` is the
closed union indexed by that row:

```text
TopicResolution<ρ,T> = PlaceFill(ℓ : CompatibleLabel<ρ,T>) | About
   ; CompatibleLabel<ρ,T> — the refinement of Label<ρ> to the places
   ; whose sort accepts Referents<T>, so the fill branch types
   ; statically
TopicAdmissible : Referents<T> × PredTerm<ρ>
                  → Fn<(TopicResolution<ρ,T>), Content>
   ; declared admissibility predicate (TanruAdmissible's sibling):
   ; PlaceFill(ℓ) is admissible for ℓ unfilled; About is admissible
   ; when srana-aboutness holds.
```

The lowering (pin P26), for topic `t` and open comment `R` with
unfilled row ρ:

```text
topic zo'u comment ↦
{Bind [$res :: TopicResolution<ρ,T>]
      (Context (TopicAdmissible t R) deps…)
  (∨ (∧ (= $res (PlaceFill ℓ₁)) (Close (At R ℓ₁ t)))
      …one disjunct per ℓ ∈ CompatibleLabel<ρ,T>…
      (∧ (= $res About)
         {Let [$p :: Proposition] (Reify (Close R))
           (∧ (Holds $p)
              (Close (srana t $p)))}))}
   ; the closed union eliminates by the finite equality-guarded
   ; disjunction (§3.5 — the §4.7 label-case precedent): one disjunct
   ; per compatible label (the topic fills ℓ; Close handles the rest)
   ; plus the About arm, whose single shared reification is the
   ; catalog 1.31 display — the comment holds AND the topic pertains
   ; to it.
```

CLL's fish (`le finpe zo'u citka`) is the `PlaceFill` choice — eater
or eaten as distinct admissible `Context` resolutions; `About` is the
available coarse intention. `deps…` is the occurrence's declared dependency profile. The
schema is defined only for one open-bridi comment. `tu'e…tu'u` may scope a
topic over a sequence, but cross-clausal place-linking within that sequence is
gap-registered (§14); explicit anaphora and coarse `About` remain available.

**Constitution-bearing `joi`.** The prior `AdmissibleMixture`/`Vague`
analysis is rejected: a positive use must not succeed through an unintended
connecting relation, and no hidden mixture-kind value is selected. After all
surface operands are computed once in source order and a homogeneous chain is
flattened, the applicable typed instance is one of these defined forms
(`Combine Xs` is the associative fold of the nonempty operand references):

```text
(JoiGroup κ X₁ … Xₙ) : RefComp<Referents<Group<T>>>  ≝
  (Massify κ (Combine X₁ … Xₙ))

(JoiEvent κ E₁ … Eₙ) : RefComp<Referents<Eventuality>>  ≝
  (SelectExactly 1 {λ [$j :: Eventuality]
    (CompleteGunmaAt κ $j (Combine E₁ … Eₙ))})

(JoiPred κ P₁ … Pₙ) : PredTerm<ρ>  ≝
  {λ [$a :: Record ρ]
    (MixAt κ (Family P₁ … Pₙ) $a)}
```

`SelectExactly 1` makes the returned reference one whole without claiming
that no co-descriptive whole exists outside the selected witness. This is the
`joi1` single-entity commitment; number-neutral group descriptors remain
separate. The mapping binds κ through
`(GroupBasisConstraint joi T)` or `(EventBasisConstraint joi)` after computing
the surface operands and before invoking these forms. `JoiGroup` is the
ordinary sumti result. `JoiEvent` is selected instead when
all operands are Eventuality references and the consuming place demands an
Eventuality; in an otherwise unconstrained `Entity` place the group reading
is the default. `JoiPred` requires pure, already-lowered operands of one exact
row and a declared `ContributionBasis<ρ>` instance. The mapping binds the one
intended κ first through a constrained `Context` site with the reading's
dependency profile; the transparent row-function result is then constructed
directly from `MixAt`, with `GunmaPredAt κ (JoiPred κ P₁ … Pₙ)
(Family P₁ … Pₙ)` following by definition. If no common row or declared
contribution basis exists, there is no baseline reading. The per-operand
`GunmaAt κ whole Xᵢ` facts are derivable from complete constitution plus the
operand-respecting admissibility law, so the definitions do not repeat them as
conjuncts.

At a shared-head tanru locus the head is not itself one of the mixed
properties. The exact schema is:

```text
((JoiTanru M₁ M₂ H) fills…) ≝
{Bind [$l1 :: PredTerm (RowOf H)]
        (Context {λ [$r :: PredTerm (RowOf H)]
          (TanruAdmissible M₁ H $r)} deps₁…)
      [$l2 :: PredTerm (RowOf H)]
        (Context {λ [$r :: PredTerm (RowOf H)]
          (TanruAdmissible M₂ H $r)} deps₂…)
      [$κ :: ContributionBasis (RowOf H)]
        (Context (ContributionBasisConstraint joi (RowOf H)) depsκ…)
  (∧ (H fills…) ((JoiPred $κ $l1 $l2) fills…)) }
```

Thus `blanu joi xunre bolci` asserts `bolci` once and mixes the two intended
head-relative color contributions. Distinct-head units use `JoiPred` over
their already-lowered whole common-row properties. All three `Context` sites
obey §5.3 independently; any free modifier/link dependencies appearing in
the basis constraint must be named in `depsκ…`. The homogeneous n-ary
generalization binds one intended link per modifier in source order, forms one
`Family⁺`, retrieves one κ, and asserts H once; it never nests a mixed
predicate as a new peer merely because the parser associated the chain.

The event-open clause form uses the same event instance without introducing
its local event witnesses into discourse:

```lisp
(JoiClause κ C D) ≝
  {λ [$j :: Referents Eventuality]
    (∃ {λ [$e1 :: Referents Eventuality]
      (∧ (C $e1)
          (∃ {λ [$e2 :: Referents Eventuality]
            (∧ (D $e2)
                (CompleteGunmaAt κ $j (Combine $e1 $e2))
                (fasnu $j))}))})}
```

The nested `∧` evaluates `C` then `D` exactly once. `CloseClause` retains `$j`
as the connected content's event; `$e1` and `$e2` remain local component
witnesses. Forethought `joi gi … gi …` uses the same form. This completes the
content/event contribution needed by `.i joi`; packaging it as one structured
performance, with component targeting and transcript spans, remains the
`ConnectionPlan` gap (§14). Exact tag/facet `joi` over an already shared event
continues to be ordinary `∧`, not `JoiClause`.

Because `Combine` is commutative and the property family is permutation-
invariant, `se joi` changes no denotation. Homogeneous chains flatten before
construction; mixed joik grouping remains syntactically significant. Repeated
co-referential sumti operands collapse at the plural `Combine` layer; the
language supplies no multiplicity reading for `joi`. `joi nai`, which CLL
15.7 calls scalar negation selecting some *other connection* rather than
negating an operand, and `pe'e joi` termsets remain gap-registered rather than
receiving a discrete-choice fallback. The natural future route for `joi nai`
is §6.3 contrast structure over a typed connective family, once its domain and
scope are actually defined.

**Tanru link connection** (jek at the tanru-unit locus; pin P33).
`TanruLinkConnect`: for a shared head, retrieve one intended admissible link
per conjunct through constrained `Context`, assert the head
predication once, and join the link applications with the connective —

```text
((TanruLinkConnect ⊙ M₁ M₂ H) fills…) ≝
{Bind [$l1 :: PredTerm ρ(H)]
        (Context {λ [$r :: PredTerm ρ(H)] (TanruAdmissible M₁ H $r)} deps₁…)
      [$l2 :: PredTerm ρ(H)]
        (Context {λ [$r :: PredTerm ρ(H)] (TanruAdmissible M₂ H $r)} deps₂…)
  (∧ (H fills…) (⊙ ($l1 fills…) ($l2 fills…)))}
```

with ⊙ the jek's operator and each dependency profile declared by the
resolved reading; links bind first so the connective ranges over fixed
intended values. NA/SE/NAI decorate ⊙ as at any locus.
Distinct-head units connect as whole predications —
`(⊙ ((Tanru M₁ H₁) fills…) ((Tanru M₂ H₂) fills…))`. Plain `joi` at a
shared-head locus uses `JoiTanru`; at a distinct-head locus it uses `JoiPred`
over the already-lowered whole common-row properties. Missing common rows or
declared contribution bases are gaps.
Other joiks dispatch by their own rows, and `nai` supplies no fallback
discrete-choice semantics.

**MEX:** by metalanguage recursion over `Natural` and lists:
`(te'a x 0) ≝ 1`, `(te'a x (n+1)) ≝ (× x (te'a x n))`;
`(gei x y) ≝ (× y (te'a 10 x))`; subscript
`(xi (List a as…) 1) ≝ a`, `(xi (List a as…) (n+1)) ≝ (xi (List as…)
n)` (undefined past the end — a projective definedness condition,
§4.9); operators are functions and `me'o` mentions their
expression signs (§7.5); `AmountValue` per §9.2.

**Tanru links:** named exact-link constants — `MannerLink`,
`MaterialLink`, `PurposeLink`, `SourceLink`, `InstrumentLink`,
`ResemblanceLink`, … — each a relation of the head row asserting the
modifier's specific bearing; usable wherever a resolved reading recovers
(§6.2), each satisfying `TanruAdmissible` by construction.

## 13. Pin annex

Numbered rulings resolving accidental underspecification; each cites its
evidence here, and the genuinely contested pins carry full arguments in
the rationale (§3) — the remainder rest on the evidence stated with
them. (Deliberate vagueness is never pinned; it is classified in §6.1.)

- **P1** No default quantifiers (xorlo). `lo P` = `Refer P`; inner PA
  counts the selected base's units; outer PA selects witness sets /
  subreferences; nonemptiness from the reference sort.
- **P2** `ro` over descriptions imports via `Presuppose`; bare `ro da` is
  mathematical `∀`.
- **P3** No automatic kind lift, no `Kind` sort; `Entity` open to
  kind-like referents where lexicon and model admit them.
- **P4** No distributivity default and **no covert cover parameter**;
  neutral plural predication is the resolved reading; marked readings are
  explicit; lexical plurality behavior lives in the lexicon.
- **P5** `loi`/`lo'i` denote group/set objects via `gunma`/`selcmi`,
  whose x2s (official components; xorxes' members) are read as plural
  references; inner PA = group/set size, outer PA counts groups/sets. Their
  lowering-internal base is ordinary non-maximal `Refer P`, like `lo P`,
  delimited by `Local` so it does not become a second surface antecedent;
  maximality is available only when explicitly marked or contextually
  resolved. General `gunma` is non-exhaustive `GunmaAt`, while group-forming
  `joi`, `loi`/`lei`/`lai`, and `MeiRel` use `CompleteGunmaAt`. `joi` forms a
  single selected constituted whole (`joi1`; no global uniqueness claim), not
  a `jo'u` plurality carrying a covert
  non-distributivity instruction (`joi2`); event and common-row property uses
  are the indexed instances of the same programme. No component-property
  inheritance follows. (`cmima` x2-as-set is the one defective gloss nearby;
  avoided.)
- **P6** Supported strong donkey/dependent-witness readings lower by reading
  selection to joint multi-parameter loci; this is not an
  equivalence-preserving normalization of the compositional selection
  computation. Dynamic accessibility includes restrictor introductions; CLL
  7.6 counting is the mapping discipline over accessible referents. The
  current cost is retroactive strengthening; plural-information states are the
  recorded model upgrade, and the weak selected-witness alternative is
  rejected absent a surface selector.
- **P7** `noi` is projective supplement, anchored; dependent supplements
  commit per instantiation inside their binder.
- **P8** A tenseless bridi is
  **reading-multiple**, per CLL 10.1's own enumeration (past, present,
  perfect, future, "I continually go…" — "context resolves which is
  correct"): an *episodic* reading carries a `Context`-anchored temporal
  facet (the contextually relevant occasion — the reading on which "I
  didn't turn off the stove" denies a particular failure, not all past
  ones); *habitual/gnomic* readings carry no temporal conjunct at all.
  The semantics never inserts a default; selecting the reading is
  upstream (§1.5), `ki` is text-to-reading stickiness, and **story time**
  (CLL 10.14) is one named text-to-reading resolver, never a semantic
  default.
- **P9** Bare `kau`: answerhood with exhaustivity **absent** — weakest
  truth conditions; strengthenings lexical, pragmatic, or separately stated.
  `MentionSome` is removed as inert and `Exhaustive` is gap-registered pending
  a pure answer function plus typed answer-domain membership/equivalence.
  (Absence, not `Vague`: Lojban has no grammatical precisification route.)
- **P10** `le` lowers through **`skicu`** — exact
  official fit, guskant-precedented — with the utterance-locution
  anchoring clause (§11 L3.2) answering act-vs-identification: the describing
  event is this very utterance, true by construction. Speaker-indexed,
  non-veridical, number-neutral; `voi` = `SpeakerDescribesUnaddressed`,
  the same anchored form with the audience place deleted (`(DropPlace
  skicu 3)` as its inner relation), restrictive (#49). No dictionary
  change (full argument: rationale §2.6).
- **P11** `lo'e`/`le'e` via the axiomatic `Generic` operator (mode +
  holder); no fixed prototype reference.
- **P12** Implicit `ce'u` — a rule of `ka` alone (§11 L9.7): exactly one,
  first unfilled place, counting
  converted places; multiple candidates are distinct readings.
- **P13** No implicit coercions among abstraction sorts; named explicit
  crossings; dictionary adjudicates sort drift.
- **P14** `tu'a X` retrieves the occurrence-specifically intended
  host-sorted abstraction through `Context`, constrained by abstraction shape
  and `srana`-aboutness to X. The speaker need not articulate it exactly; a
  cooperative hearer is expected to recover a discourse-sufficient value.
  Bare `jai` likewise retrieves the intended admissible raised-role relation
  at `Fn<(Referents<T>, Referents<A>), Content>`, where one resolved reading
  fixes the raised-sumti sort T and old-x1 sort A; tagged `jai` fixes the role
  exactly. Each site declares its governor dependencies;
  none are inherited automatically. `co'e`/`do'e` remain ordinary `Context`
  retrievals at their types.
- **P15** `zo'e` ≡ omission; distinct sites distinct; `zu'i` adds
  typicality as an **admissibility condition on the retrieval** (part
  of the site's key, §5.3): only the place's typical filler is an
  admissible recovery — the term is `Context`, the key differs.
- **P16** Anaphora resolution is text-to-reading; calculus sees bindings;
  `goi` discourse-scoped; unassigned KOhA = keyed `Context` (one value per
  key — `ko'a du ko'a` is reflexively true).
- **P17** Termsets: co-selected witness sets, full product, **no
  maximality** — CLL ch. 16 §7's own gloss of `ci gerku ce'e re nanmu cu
  batci` (Examples 16.41–16.45; the gloss is 16.45) is two picked groups
  with every dog biting each man, and says nothing stronger; the
  coordinate-closed profile is a named strengthening; referential members
  need no termset semantics at all (the citation edition's 16.7:
  unquantified descriptions are constants outside scope distinctions, and
  only explicit `ro…ro`, Example 16.46, spells the full product — wording
  this project authored under xorlo, fork commit `e21e63c7`, hence
  corroborative record rather than independent evidence; original 16.7
  instead gave an unquantified `le nanmu` an implicit `ro`, the pre-xorlo
  reading that xorlo's constant treatment of unquantified descriptions
  supersedes). The bare-PA half is a **documented
  divergence from CLL's letter**, in two respects: ch. 16 §6 glosses
  bare numeric quantification globally ("exactly two things, no more or
  less" — Example 16.34) *and* distributively (`PA broda` "is shorthand
  for `PA da poi broda`" — a singular variable), while this
  specification pins **neutral witness-set selection** instead (§4.10) —
  the xorlo-era reading that composes with witness export and termsets,
  and the only default under which collective predicates survive
  quantification (`su'o prenu cu jmaji`; P4) — with
  the CLL-literal global reading available as `GlobalExactly` and the
  each-reading as `Distrib`/`lu'a`.
- **P18** Connective scope from surface grammar; accessibility rows are
  meaning; `na` ≡ left-edge `naku` with ch. 16 flip rules.
- **P19** UI target = grammatically attached constituent (text-to-reading),
  a first-class value in the term; modifier composition in surface order.
- **P20** `da` ranges unrestricted; `poi` is the only domain restriction.
- **P21** Two truth values; partiality by projective definedness.
- **P22** Inner `no`: a description with inner `no` never lowers through
  `Refer` (plural references are nonempty by type); it is
  **special-cased at the mapping layer** to the zero-count schema —
  `lo no broda` in a bridi frame `R[·]` lowers to
  `(No {λ [$x :: Entity] (broda $x)} {λ [$w :: Referents Entity]
  R[$w]})`, guskant's unofficial
  `naku su'oi da poi ke'a broda` relativized to the frame ("gadri: an
  unofficial commentary from a logical point of view", the "Cannot say
  zero" section). This is what makes answer substitution work: `lo xo
  prenu cu jmaji …` answered by `no` is elliptical `lo no prenu cu
  jmaji …`, and `go'i`-inherited frames likewise. Anaphora to an
  inner-`no` description is inaccessible (`No` exports nothing) — there
  is nothing to refer to. `no lo broda` remains the fully explicit outer
  form.
- **P23** `ba'e` = sign-level focus; `du` = `=` between first-order
  individuals and `CoRef` between plural sumti (§4.5).
- **P24** Fresh clause eventuality per bridi unless shared explicitly; ZAhO pinned as
  boundary-relation shape, contours filled lexically. More exactly, every
  declarative lowering is `ClauseContent`: an unembedded direct lexical episode
  identifies its clause eventuality with the lexical event; eventless,
  negative, quantified/generic, and non-disjunctive compound claims take a
  holding State; disjunction is branch-relative. Missing CAhA is
  reading-multiple among `ca'a`/`ka'e`/`nu'o`/`pu'i` modes, with no default
  (CLL 10.19); explicit CAhA fixes the mode.
- **P25** Lexical argument rows take plural references, not sets. The
  set-typed alternative was examined in full: under the
  discipline of §4.8's representation note the two designs are
  intertranslatable, so the choice is architectural, and this
  specification chooses the design in which the discipline is
  type-theoretic — nonemptiness in the type, the member-wise/object-wise
  distinction as a sort split (`Referents<T>` vs `Set<T>`) rather than
  a per-place convention, and no atomistic basis imposed. Set objects
  keep their places where Lojban talks about collections as
  individuals (`lo'i`, `cmima`, `kampu`, `sisku` x3, the set
  operators); the "distributive" value of the lexicon's plurality
  field is defined by subreference monotonicity (§10). Reopens on the
  rationale's standing invitation: a construction where
  set-objecthood at a lexical place does work member-wise predication
  plus `SetOf` cannot.
- **P26** Prenex order is scope order (CLL 16.2; the P18 surface
  doctrine at the prenex); topic `zo'u` retrieves one intended
  `TopicResolution` through constrained `Context` — an admissible unfilled
  place of a single-bridi open comment frame, or coarse `srana`-aboutness to
  the closed comment. CLL 19.4 establishes that the surface does not choose
  the fish's place, not that one use asserts every admissible place. Compound
  cross-clausal place-linking is gap-registered; no segment-state effect.
- **P27** Imperative and address: `ko` = the active addressee with
  command force on the nearest **performed** clause — no force
  extrusion through `Reify` or quotation; `doi` performs `Vocative` at
  `AttachedAddress`
  and ⊳ binds the active `do` (CLL 2.14); the Audience projection is
  never mutated — each utterance's ctx carries its own audience.
- **P28** `do'i` is `Context` at the salient transcript token/span
  (`Vague` only in span boundaries); `la'e` over utterance anaphors
  that demand performed assertion content crosses host-sorted through
  partial `RealizedContent` (§7.4); act-demanding uses retain
  `RealizedAct<F>`, and raw package content for explicit re-resolution uses
  total `ActContent` only after that force check. No universal coercion (P13
  applied at the token sort).
- **P29** `cu'o` is an opaque lexical relation with a `Number` place
  in [0,1]; the model supplies the measure; **no probability
  calculus** enters the core. `JeiRel`'s epistemology-relative truth-value
  object is not a covert numeric probability (P38).
- **P30** `bu'a`-series = typed quantification at `PredTerm<ρ>` —
  variables, not objects; exact-row consistency across occurrences;
  non-`su'o` quantifiers prenex-only (CLL Example 16.107); only pure
  higher-order restrictions type. `cei`/`broda`-series bind bridi
  **templates** (fills, tense, negation; later fills override —
  CLL 7.5), not bare relation values.
- **P31** `ja'a`/`je'a` are transparent identities that ⊳ override
  inherited negation in pro-bridi expansions (`ja'a go'i` over a
  negative template removes the negation); no fourth `Scalar` kind.
- **P32** Sentence-level **logical** connection is **one performance of the
  connected ClauseContent, closed once for force** (forced by `.i ja`; stated
  for the content-taking forces, interrogative hosts querying the connected
  content). Constitution-bearing `.i joi` now has the indexed event/content
  form `JoiClause`; its structured compound performance is gap-registered
  pending `ConnectionPlan`. `.i TAG bo`
  exposes both event binders with the tag
  conjunct inside the performed content.
- **P33** Jek at the tanru-unit locus = `TanruLinkConnect`: shared
  head asserted once, one constrained-`Context` intended link per conjunct,
  connective over the link applications; distinct heads connect as whole
  predications. Constitution-bearing `joi` at this locus uses `JoiPred` over
  the already-lowered common-row properties, with `JoiTanru` asserting a
  shared head once and mixing only its head-relative links; a missing common
  row or contribution-basis instance is an explicit gap.
- **P34** `vu'o` distributes an incidental clause **once per
  immediate connectee** (never collectively over `Combine`, never
  member-distributed into a plural connectee); restrictives restrict
  each operand under the connective structure; group-forming joiks
  take the clause on the resultant object. CLL 8.8 attests the
  incidental case; the restrictive rule is this specification's
  extension.
- **P35** `n roi` **replaces** the single-event existential closure
  with `RoiClause`: Card over the distinct component eventualities in the
  interval, then `StateClause` for the count claim itself; the default interval is a
  Context-recovered anchor with `Vague` extent.
- **P36** `ma'o`'s operand-to-operator reading is a `Context`
  recovery of the intended function — never a constant-function
  default.
- **P37** `ji'i` is position-indexed, and both positions denote
  `Number`-valued `Vague` families: prefix/medial over the
  `AdmissibleTolerance` region, suffix over the `AdmissibleRounding`
  preimage (the stated digits exact by the region's construction),
  directionally under `ma'u`/`ni'u`; both regions VC1-nonempty.
- **P38** `jei` reifies an epistemology-relative `TruthValue` through
  `JeiRel`. The numeric [0,1] `TruthValueDegree` crossing is not baseline
  Lojban: CLL 11.6 records it as an unestablished proposal, preserved in the
  gap register for possible future adoption only through a new evidence-backed
  pin.
- **P39** `lo R` remains literally `(Refer R_p)`: description satisfaction
  is the ordinary resolved lexical property, never a second stronger
  description-only predicate. For each place and reference mode, the lexicon
  either declares a pure unit profile and fixes the plural extension by
  `R_p(r) ↔ CoveredBy(unit_Rℓ, r)`, or supplies the mode's exact direct
  plural condition (collective, kind-like, substance, or otherwise). The
  choice is lexical data, not a covert reading parameter. Selection witnesses
  use `CoveredBy`; `MaxRefer` adds only inhabitedness and the all-satisfiers
  conjunct. The rejected alternative strengthened `lo` alone; it duplicated
  lexical truth conditions, contradicted official/BPFK
  `lo broda = zo'e noi broda`, and mishandled collective heads. Reopens only
  on a supported case where the same resolved `R_p(r)` is true in nuclear
  predication but r must nevertheless be unavailable specifically to `lo R`.
- **P40** `mi'o` denotes exactly `Combine Speaker Audience`, the ordinary
  neutral plural reference corresponding to `mi jo'u do`. It is neither the
  logical connection `mi .e do` nor the canonical group `mi joi do`; P4
  leaves one predication's collective/distributive/reciprocal satisfaction to
  its lexical row. `mi'a`, `do'o`, and `ma'a` use the analogous §11 `Combine`
  lowerings with the token-relative `MiAOthers`, `DoOOthers`, and `MaAOthers`
  projections and §5.1's inclusion/exclusion constraints. One composite
  pro-sumti creates one argument and therefore one omitted-place site per
  unfilled host place, never a hidden member pairing. Original CLL §7.2's
  `mi'o = mi joi do` mass analysis is the coherent rejected alternative;
  current CLL's `mi jo'u do` wording is project-authored corroboration, not
  independent evidence. Positive `mi'o … mei` remains #24's separate carrier
  problem. Reopens only on ordinary unmarked uses that require a constituted
  group's own properties rather than neutral plural predication or #24's
  cardinality interface.
- **P41** In-situ scope. Descriptions and names (`lo`/`le`/`la`, with any
  nonzero inner PA) bind at clause level in source order (§4.1), outside every
  in-situ quantifier; quantified sumti — default witness-set PA, `ro`,
  inner `no`, thresholds, the marked global reading — scope in surface
  order over the clause body, the leftmost outermost (original CLL 16.7;
  P26 for prenexes), termsets keeping L5.3's joint scope; a description
  referent never co-varies with a quantifier witness unless the description
  sits syntactically inside the quantifier's restrictor or nuclear predicate
  (§11 L5.30). `ro gerku cu tavla lo mlatu` has one contextual cat
  plurality; `ro gerku cu tavla su'o mlatu` lets the cats vary. The
  pre-xorlo reading — `lo` as `su'o lo`, grouped left to right with every
  other sumti (original CLL 16.7) — is the coherent rejected alternative;
  under xorlo `lo` is not a quantifier and its referent is fixed at its own
  site (§5.3). Contemporary CLL 16.7's unquantified-description wording is
  project-authored corroboration (P17), not independent evidence. Reopens on
  speaker evidence that competent xorlo-era speakers default to the
  co-varying reading for `ro … lo …` (#62).

## 14. Gap register

Meanings this specification currently assigns no analysis, each with the
reason; a gap is an obligation on future revisions, never a license to
approximate:

- **No-particular-value discrete choice (`SomeAdmissible` candidate).** The
  analyzed baseline has no construction whose speaker both intends no
  particular discrete alternative and commits to existential success through
  any admissible one. Tanru, `tu'a`, bare `jai`, and topic links have intended
  values and use constrained `Context`; `na'e` denotes a direct coarse region;
  constitution-bearing `joi` uses the §4.9 indexed programme. Official `ju'e` (“vague
  non-logical connective”) is a real surface candidate, but CLL and the
  dictionary do not define whether its positive and negated uses have
  existential-choice, contextual, or other truth conditions; it remains
  unmapped pending its own source/usage adjudication. If that work or other
  speaker evidence establishes a genuine counterexample, the recorded
  candidate is a non-exporting
  `RefComp<T>` with one ordinary nondeterministic branch per admissible value
  (positive existential, negation denying all), never a `Vague`
  precisification family. Until such a witness and pin exist, `co'e`/`do'e` or
  any other form receives no exceptional weak reading.
  `vu'i` supplies a second bounded probe: CLL requires the resulting sequence
  to have an order while the dictionary leaves that order vague. An
  occurrence with an intended order uses `Context`; a genuinely
  no-particular-order use, if established, would need this exceptional
  analysis rather than a maximally tolerant `Context`. No baseline
  order-free reading is generated pending evidence.
- **Numeric `jei` crossing.** CLL 11.6 records the first-edition proposal that
  a `jei` truth value map to a number in [0,1], while also stating that its
  conventions were never worked out and the number-valued reading never
  became established. CLL 19.6 nevertheless says that the usual fuzzy-logic
  machinery in Lojban is `jei`; any revival must reconcile that confident
  cross-reference with 11.6's explicit historical disclaimer (and must also
  supply semantics for the likewise-unmapped subscripted-`ja'a` convention
  mentioned there). The recorded candidate is exactly
  `TruthValueDegree : Referents<TruthValue> ⇀ Number`, defined projectively
  only at a singleton truth-value reference. P38 keeps `JeiRel` in the
  baseline and withholds this crossing until corpus/speaker evidence supports
  a new prescriptive pin.
- **Exhaustive answer marker.** `MentionSome` is rejected as a semantically
  inert duplicate of unmarked answerhood. The recorded `Exhaustive` candidate
  would conjoin: every answer-domain value whose assigned content holds is in
  the selected answers. It is not a baseline `Selection` value because that
  clause is defined only when the query's answer-content function is pure and
  the answer domain supplies typed selection membership/equivalence; the
  general domains (plural references, heterogeneous tuples, labels, and
  predicate-valued answers) do not share such an interface. Lojban has no
  grammatical exponent that warrants adding it solely for this marker.
- **Residual `joi` and non-logical sentence connection.** Section 4.9 now
  defines the layered constitution interface and its group/event/property
  laws; §12 supplies `JoiGroup`, `JoiEvent`, `JoiPred`, `JoiTanru`, and
  `JoiClause`.
  Remaining gaps are bounded: (a) a tanru/property use with no common row or
  curated `ContributionBasis<ρ>` instance; (b) `pe'e joi` termsets, whose
  paired term-and-tag bundles cannot be reduced to either a plain group or a
  property family; (c) `joi nai`, whose CLL 15.7 scalar-negation reading has
  no selected contrast-domain member or scope law (the recorded candidate is
  §6.3 contrast machinery over the connective family); (d) the structured
  **performance** of `.i joi` and other non-logical ijoiks; and (e)
  joik-connected mekso operands such as `li pa joi re`, whose parser locus has
  no number/operator/collection denotation. `JoiClause`
  supplies (d)'s content and compound event but not its component roles,
  targeting, transcript spans, force, or accessibility plan. Any future
  `ConnectionPlan` constructor is constrained by §7.1: its one host `Perform`
  creates one `ActOccurrence` with one capture. Component transcript spans may
  realize component act packages for targeting, but do not become additional
  performed occurrences unless the semantics explicitly performs them; #6
  owns those laws. Exact tag/facet `joi` over an already shared event remains
  ordinary `∧`.
- **Zero-member `MeiRel` / `nomei`.** The positive-n `MeiRel κ n` definition
  uses a nonempty maximal member reference, as its x3 and the adopted
  `Referents<T>` component carrier require. The experimental dictionary entry
  for `nomei` instead proposes an empty mass/0-tuple. A treatment must decide
  whether `Group<T>` contains a null group and add a typed empty-cover case
  without weakening `Referents<T>` globally; until then `MeiRel κ 0` has no
  baseline row clause (GitHub #23). Ordinary claims that a set has cardinality zero remain
  available through `Card`.
- **Cross-clausal topic place-linking.** P26's `PlaceFill` arm is defined only
  for one open bridi. A topic scoped over a conditional or `tu'e…tu'u` sequence
  may bear different place relations to different clauses; no single residual
  row represents that. Coarse `About` and explicit internal anaphora are
  analyzed, while a typed comment-template treatment is the recorded future
  candidate.
- **`da'i` and counterfactual/hypothetical mood.** The discursive `da'i`
  marks content for evaluation under a hypothetical (possibly
  contrary-to-fact) scenario; CLL gives it no scope semantics, no
  persistence rule, and no scenario-identity criterion, and the core
  assigns its readings no analysis. The world-indexed model (§5.1) fixes
  the shape of any treatment — a shift of the evaluation world, a new
  member of the `Shift` operator family of which `InContext` is the
  utterance-context member (the two shift different indices and must not
  be conflated), never world variables in terms —
  and a treatment must define three things: (1) the **scope** of the
  shift (attached act only, persistence across `.i` until reset, reset at
  `ni'o`?); (2) **dynamic binding under the shift** — `da'i su'o gerku cu
  klama .i ri melbi` needs the hypothetical dog accessible to `ri`, i.e.
  the accessibility table commuting with the shift; (3) **scenario
  identity** across repeated `da'i` (`da'i mi ricfu .i da'i mi citka lo
  nobli` is one scenario), which is the dimension most likely to force
  new machinery — attempt a constraint form (same segment, no reset,
  compatible content) before conceding a visible scenario binder.
  Boundaries: `da'i` inside `Reify` needs nothing new (the reified
  intension is hypothetical); inside attitude complements it composes
  with the attitude's worlds; inside quotation it shifts nothing.
- **Generic anaphora** to `Generic` predications (§5.8).
- **`Generic`'s inference theory.** The operator is typed and its
  normality reading stated (§5.8), but no entailment axioms are yet
  fixed, so `Generic` currently licenses no inferences beyond typing;
  candidate axioms are under review, and until they land the operator
  is an interface with a stated intended reading, not a source of
  consequences.
- **ZAhO contours** pending their lexicon rows (P24); habituals (TAhE)
  likewise.
- **Dependency-preserving plural information states.** P6's supported strong
  joint-locus term is a selected construal, not the output of a
  semantics-preserving rewrite. It retroactively strengthens the antecedent
  when a later anaphor appears. The principled candidate stores each
  governor–witness dependency when the antecedent is evaluated and lets the
  anaphor consume that stored relation (van den Berg/Brasoveanu-style plural
  information states), so no retroactive reanalysis is needed. The weaker
  compositional alternative — continue through one selected witness branch —
  is a coherent comparison model but not an available baseline Lojban reading:
  no surface form selecting it has been identified.
- **Exotic donkey configurations**: anaphora out of disjunctive
  restrictors; stacked indefinites with split anaphora (§5.6).
- **Termset witness export** (joint anaphora to termset selections) and
  mixed-quantifier termsets where no coherent product reading exists
  (P17).
- **Reified predicates above row ⟨⟩** (§9.1's reservation): property
  and relation *objects* — referents for `lo ka` with
  discourse-referent behavior (`lo ka ce'u klama goi ko'a`, anaphora
  and quantification over property *objects* — distinct from the
  `bu'a`-series, which quantifies predicate-typed **variables** at
  `PredTerm<ρ>` with no objects involved, P30), the
  non-propositional readings
  of the experimental `me'ei`/`me'au` pair, the plural-reference
  `me'au` case (§9.1's singleton condition; the universal reading is
  the recorded candidate), `se du'u` under `ce'u` extraction (§9.2),
  the Rosta
  all-`ce'u` `si'o` (a genuine predicate nominalization into concept
  objects — the one explicit-`ce'u` reading outside `ka`/`du'u` that
  is reserved-family territory proper),
  and the open design points a
  family raises: row-isomorphism under `se`-relabeling, and typed
  cross-row operators (identity *within* a row is already fixed
  extensional over `PredTerm`, §9.1). The baseline lowers `lo ka`
  directly to the λ and defines reification at row ⟨⟩ only. The
  **adoption contract**: adding the family is additive — an indexed
  first-order sort family beside `Set<T>`/`Sign<K>` (§3.1's reserved
  opening) whose members are ordinary domains for `Refer`, anaphora,
  descriptions, and typed quantifiers; application-consuming lexical
  places stay `Fn`-typed and `lo ka` keeps its direct-λ lowering
  there, reified objects entering at referent positions with the
  row's crossing pair mediating (`me'ei P` ↦ the row's reification;
  `me'au` consumes through the row's `Holds`, plurality rule as at
  row ⟨⟩) — so adoption fills this declared hole without retyping
  any baseline place or reopening the bridge.
- **Explicit `ce'u` in the non-`ka`/`du'u` abstractors** (§11 L9.4): each
  needs a **result-specific typed analysis** — an argument-indexed
  amount abstraction for `ni`, and per-abstractor codomains for
  `jei`/`li'i`/the event abstractors likewise — none of them a
  reified `PredTerm<ρ>`, so this is its own gap, not part of the
  reservation above (whose one member from this territory is the
  all-`ce'u` `si'o` listed there).
- **The non-numeric `me … me'u MOI` composite** (CLL Example 18.94's
  `cu'o` snowball): its reading would need value-indexed MOI families
  beyond the `Number` index (§12); no analysis is assigned.
- **MEX beyond the library fragment**: non-decimal bases, arrays,
  indefinite operators.
- **Prosody and stress** as meaning carriers; conversational repair as
  reportable structure beyond quotation.

## 15. Adequacy

The coverage claim of this specification: every meaning expressible by a
Lojban utterance under a resolved reading either (a) denotes a core term
by the schemas of §11, (b) is a library form of §12, or (c) appears in
the gap register §14 with its reason. Clause (c) is an accounting of
honesty, not a denotation: a gap-registered meaning has no core term
yet, and the header's every-utterance-denotes claim holds exactly over
(a) and (b) — the analyzed coverage. The coverage matrix:

| Construct family | Schema | Library | Gap | Samples |
|---|---|---|---|---|
| predication, places, `zi'o`, conversion | §11 L1 | `ClauseContent`, `DirectClause`/`StateClause`/`CloseClause` | — | §1–§2 |
| tense/aspect/space, BAI, CAhA | §11 L6 | clause-event facets, `MotionVector`, CAhA clause formers | ZAhO contours, TAhE | §2 |
| gadri, descriptions, `lo'e`/`le'e` | §11 L3 | `Named`, `MaxRefer`, `Generic` at §5.8 | generic anaphora | §3 |
| relative clauses, `goi`, `voi` | §11 L4 | `SpeakerDescribesUnaddressed` (P10; #49) | — | §4 |
| quantifiers, termsets, negation scope | §11 L5 | GQ family, `GlobalExactly`, `Distrib` | mixed termsets, termset export | §5 |
| vague quantities, gradables | §6.4, §11 L5.28–L5.29 | degree GQs, `Grade` | — | §5, §8 |
| anaphora, KOhA, composite personal pro-sumti, `ra'o` | §11 L7–L8 | `Combine` plus the partial “others” context projections | exotic donkeys | §3–§5 |
| abstractions, `tu'a`, `jai`, `mo'e` | §11 L9 | `EventOfContent`, abstraction relations, `AmountValue`, `JaiPromote` | reified predicates; non-`ka`/`du'u` `ce'u` cases (§14) | §8–§10 |
| questions, answers, `kau` | §11 L10 | domain-enumeration schemas | — | §6 |
| indicators, evidentials, discursives, COI, `na'i` | §11 L11 | discourse relations, focus, objection, COI schemas | — | §7 |
| quotation, signs, letterals | §11 L12 | sign constructors | — | §10 |
| MEX | §11 L12 | `te'a`, `gei`, indexing, `Interval`, the conversion crossings, numeral schemas (`ji'i`, `da'a`, punctuation) | bases, arrays, indefinite operators, general `mo'e`, joik-connected mekso operands | §10 |
| plurality, masses, reciprocals | §4.8–4.9, §11 L3 | `CoveredBy`, `lu'a`, `Reciprocate` (`simxu`/`soi`), `GunmaAt`/`CompleteGunmaAt`, `JoiGroup`/`JoiEvent`/`JoiPred`/`JoiTanru`/`JoiClause` | `joi nai`, `pe'e joi`, missing contribution-basis and per-row unit-profile data, compound ijoik performance | §3, §5 |
| prenex, topic, imperative, vocative | §11 L2 | `Topic`/`TopicAdmissible`, `RealizedAct`/`ActContent`/`RealizedContent` and occurrence capture (§7.1–7.4) | cross-clausal topic place-linking | — |
| associators, `zi'e`, `vu'o`, `me`, MOI, group/set gadri | §11 L3–L4, L12 | `MePred`, the MOI families | — | — |
| utterance anaphora, `da'o`, NIhO depth, MAI | §11 L8, §7.2 | `EnumerationOrdinal` | — | — |
| relation variables, templates, connective residue, BIhI, ROI | §11 L5–L6 | `TanruLinkConnect`, `JoiPred`, `JoiTanru`, `JoiClause`, region formers, `SelectAllBut` | first-order restrictive clauses on `bu'a`; residual joik/ijoik performance; `ju'e`; `nomei`'s empty cover; the non-numeric MOI composite (§14) | — |
| hypothetical mood | — | — | `da'i` | §13 |
| repair, prosody | §11 *(reading)* rules / the resolved-reading datum (#9) | — | registered | — |

A claim of coverage that cannot cite a schema, a library definition, or a
gap entry is a defect in this document.

### Appendix: the kernel

The primitive inventory, for reference — audited so that nothing sits
here by historical accident; the criterion is that a primitive has no
term-language expansion, only its prose-and-axiom definition. The
primitives: the type formers of §3 (except `PredTerm`, a transparent
alias); the direct λ-binding form, function types, and application over
labelled records; `bind`, the computation carrier's sequencing operation
(the direct `Bind` form denotes it with a scoped continuation, §5.2); lexical
predication (dictionary relations as constants); `DropPlace`;
`¬ ∧ ∨ → ↔ ⊕ ∀ ∃ =`; `Combine`, `Among`; `SetOf`, `Card`, `∈`, the
arithmetic base; `Refer`, `Local`, `Context`, `Vague`, the `Select` family;
`Presuppose`, `Supplement` (display is its §7.6 spelling); `Generic`;
`Reify`/`Holds`; `TanruAdmissible` (the `Tanru` operator itself is
defined, §6.2), `JaiRoleAdmissible` (with `JaiRaise` defined in §12),
`Scalar`; the basis-indexed primitive interfaces `BasisUnitAt`, `PeerUnitAt`,
`MixAt`, and `ContributesAt`, plus the rigid group-basis classification
`Aggregate`;
`StateClause`, `CloseClause`, and the constrained
`EventOfContent` projection (§9.3); the
force constructors, `Perform`, `Do`, `NewTopic`, `Resume`; the linguistic
sign constructors (where quotation's opacity lives);
`InterpretContent`/`InterpretAct<F>`, the partial
`RealizedAct<F>`/`RealizedDiscourse`/`RealizedContent` projections with the
total `ActContent`, and the token/sign
fact relations; the declared MEX conversion crossings, `During`,
`EnumerationOrdinal`, and the
`SelectAllBut` member of the selection family (§12); `Deictic`, `ShiftedGround`, `InContext`, and the
context projections (including partial `MiAOthers`/`MaAOthers`/`DoOOthers`);
`Polar`, `OpenQ`, `QuestionOf`, `Answer` with the
answer-selection values; the abstraction relations (§9.2, minus the
derived `DuhuRel`), the crossing `AmountValue`,
`InnatelyCapable`, `MotionVector`; and the axiomatic
admissibility predicates (§12). **Defined forms** (term-language
expansions; everything else is library or lexicon): `DirectClause`, the six
clause-connective lifts, `Close`, `⊤` (the
empty conjunction, §2), `At` with all fill notation, `Let` as direct
value application, the
demonstratives, `Tanru` (§6.2), `TanruLinkConnect`, `JaiRaise`, `MePred`,
`GunmaAt`, `CompleteGunmaAt`, `ComponentAt`, `GunmaPredAt`, `JoiGroup`, `JoiEvent`, `JoiPred`, `JoiTanru`,
`JoiClause`, `CanonicalAggregateAt`, `Massify`, the partial `components_κ`
projection, and the LAhE collection crossings; the
region formers (`MetricBall`/`SpanRegion`/`RegionComplement`), the
`Topic` lowering,
`SelectSome`, the member-level `Refer` lift (§5.3), the `Utterance`/`Sign`
entry notations (§7.4),
`PredTerm`, `UnitSet`/`CardBasis`, `CoveredBy`, `DuhuRel`,
`ContextualAnswer`, `RoiClause`, the CAhA clause formers, and the library of §12. The
[catalog](catalog.md) carries one entry per name — prose, formal
definition where one exists, purpose, example, and links; each name's
content-word status is in §16.

## 16. The content-word program

The end state of §1.2's program: only content words serve as
object-language predicates. This chapter specifies what that means
operator by operator and keeps executing semantic operations distinct
from predicate vocabulary that merely describes their results.
**Status:** the chapter is the program's normative discipline plus its
initial audit; the full per-entry catalog accretes under §16.2's schema,
and its completion is a standing obligation of this specification (like
the gap register), not an achieved end state.

### 16.1 Three cash-out classes

"Placeholder for a content word" cashes out differently across the
inventory:

- **Class P — genuine predicates** (relations over individuals, acts,
  tokens, signs): the direct targets. Each is *exact-fit* (an existing
  word's official row serves, possibly through place baking, deletion,
  or `se` — the standard combinators), *near-fit* (an existing word
  would serve after a **proposed redefinition**: exact current wording,
  exact proposed wording, blast-radius assessment, committee-decided,
  never silently applied), or *no-fit* (a coinage is owed; until coined,
  the PascalCase placeholder carries the predicate-style definition).
- **Class O — operators over content, computations, or signs** (`Refer`,
  `Local`, `Context`, `Vague`, the `DirectClause`/`StateClause`/`CloseClause`/clause-
  connective family and `Close`, the force constructors, the
  `ActContent`/`RealizedContent` projections, the question formers,
  `Presuppose`/`Supplement`, `Tanru`/`Scalar`, the effectful/clausal
  `JoiGroup`/`JoiEvent`/`JoiTanru`/`JoiClause` forms,
  `DropPlace`, the selections — while defined machinery like `At`
  (record application) and library λs like `JaiPromote` are Class M
  under §16.2's machinery status): not predicates over
  individuals. An executing operator is not made into a predicate by
  assigning a content word to a relation that merely describes it.
  Where a natural *shadow relation* exists (a predicate that describes
  the operator's result — `xusra` for what `Assert` builds, `danfu` for
  answerhood, `smuni` for interpretation), the entry names it: the
  shadow is real vocabulary because acts, tokens, and signs are
  first-class objects the language can talk *about*, but it neither
  executes nor replaces the operator.
- **Class M — structural and metalanguage machinery**: the direct
  `λ`/`Let`/`Bind` forms, record filling, type formers, rows, typing and
  formation judgments, the computation carrier's `bind`, the evaluator,
  opaque `ActOccurrence` handle/capture infrastructure, the constitution-basis
  formers, `Family⁺`, and their primitive unit/mix/contribution interfaces,
  pure function-level `JoiPred`, and metalanguage recursion
  in library definitions. **No content word is
  owed**, and the committee should coin none merely to rename these forms:
  a sort *predicate* (`fasnu` for eventhood) is a content word; the sort
  *system* is not. A separately witnessed predicate that describes the
  result of a structural operation is Class P, not a conversion of the
  machinery into vocabulary.

### 16.2 Catalog entry schema

Each §16 entry carries: the core name and semantic class; its direct
semantic definition or expansion; **surface reachability**
(surface-reachable / lowering-only / generic infrastructure); and, where
a predicate or shadow relation is at issue, its x1…xn row, **status**
(exact-fit / near-fit / no-fit / machinery), and **see-also** entries —
nearby verified words and why each does or does not serve. A
**proposed redefinition** appears for near-fits only; the current example is the
`-nmo` indicator-emotion family, §16.5, whose rows need the intensity
place. The remaining candidates are recorded with the combinator route
their adoption would take, §16.5's audit note stating which routes still
owe their expansion equations. The formal fields the semantics needs are:
*semantic class* (content-producing,
value-producing, computation-producing, binder-producing, act-producing,
type/index — determining what a definition may claim), *effect profile
and sequencing law*, *binding arity and scope types* for direct binders,
*sign-operand policy* for actual linguistic-sign consumers
(**active** or **inert**), and *basis or derived* status with the
expansion equation. Derived entries terminate in basis vocabulary —
Brismu's dependency-order discipline. A predicate-style shadow never
stands in for an operator's effect, binding, or performance clause.

### 16.3 Operators, shadows, and linguistic signs

The baseline sign layer is linguistic (§7.5): raw text and opaque signs
remain quoted material, while sentence and act signs cross explicitly
through `InterpretContent` and `InterpretAct`. No baseline sign kind
contains executable core notation, and no surface cmavo implicitly
evaluates quoted material. An explicitly interpreted act may be passed to
`Perform`; the effects then come from performing the resulting act, not
from inspecting or splicing its sign.

This boundary is also the content-word programme's stopping rule. A core
operator produces, sequences, binds, questions, or performs meaning. A
shadow predicate describes an operator's result or an occurrence of its
use. Thus `xusra` can describe an assertion act without replacing
`Assert` or `Perform`; `smuni` can relate a sign to meaning without
being the interpretation crossing; and a relation describing a contextual
choice does not perform `Context` retrieval. Shadow vocabulary is
valuable precisely because the resulting acts, signs, tokens, and values
are first-class, but descriptive and executing roles never collapse.

A primitive operator may become a defined form only when an actual
term-language expansion is supplied. Every expansion must preserve:

- **typing and category** — no side condition or result type changes;
- **linearity** — each effectful operand is evaluated exactly once unless
  the source operator itself specifies otherwise;
- **site identity** — `Context` and `Vague` sites map one-to-one, with
  sharing expressed by a binder rather than textual duplication;
- **accessibility and projective policy** — the §5.4 row and handler
  placement are unchanged; and
- **acyclicity** — definitions terminate in the declared basis.

A proposed content word with only a predicate row is therefore an exact
fit for a predicate or shadow, never by itself for an executing operator.
Direct binders and other structural forms are classified by their semantic
role and surface reachability (§1.1); no sign-consuming `Make*` twin is
generated for them.

### 16.4 The structural floor

The reduction stops at semantic structure that no predicate extension can
perform:

| Floor item | Why it remains structural |
|---|---|
| scope and hygiene | direct `λ`/`Let`/`Bind` formation resolves binders and performs capture-avoiding substitution before denotation; an at-issue relation cannot establish lexical scope |
| lexical basis interpretation | definitions bottom out in model-given lexical relations or the dictionary is cyclic |
| effect sequencing | ordering introductions, contextual retrievals, and projective emissions is an operation on computations, not a truth condition |
| accessibility and effect-flow policy | whether an introduction escapes, a sign is inert, or an obligation projects is part of composition, not an extra claim |
| local introduction projection | `Local` preserves a computation's semantic filtering/value while hiding only its internal discourse slots; a predicate can describe neither that state projection nor which syntactic base is non-surface |
| force performance | describing or quoting an assertion must not assert it; only `Perform` executes an act package |
| typing and formation judgments | ill-formed combinations have no denotation; turning well-formedness into a predicate would make failure merely false |
| reading resolution | anaphora, erasure, template expansion, and dependency selection determine the resolved term upstream; predicates may describe their results but do not run the resolver |

Sort predicates remain content words where the lexicon supplies them
(`fasnu` for eventualities, `pruce` for processes, `namcu` for
numbers, `sinxa` for signs). The distinction is between predicating a
sort or semantic result and executing the structural operation that forms,
binds, or performs it.

### 16.5 The audit (initial population)

Summary of the initial audit (full entries accrete under §16.2's
schema; every official row cited here was verified against the
official dictionary or CLL). One orthogonality governs the reading:
**content-word status is independent of term-language status** — an
"exact fit through combinators" records a committee-pending *adoption
plan* (the lexicon program never applies proposals silently), so a
relation with such a fit remains a term-language primitive until
adoption turns it into a defined form over the adopted word; and a
term-defined form (`UnitSet`, `CardBasis`) may still *owe a name*, its
no-fit entry being about the missing content word, not about
definability:

- **Adopted now (exact-fit):** `skicu` for the `le` description (P10,
  with the §11 anchoring clause); `cmene` (`Named`); `gunma`, `selcmi`
  (P5); `purci`/`balvi`/`cabna` (tense facets); `srana` (`tu'a`
  aboutness); `fasnu` (actuality, realization); the BAI tag gismu that
  double as the named tanru-link relations (`tadji` manner, `mukti`
  purpose, `krasi` source, `marji` material, `pilno` instrument, `simsa`
  resemblance).
- **Candidate fits through combinators (adoption blocked on displayed
  equations):** `klani` for `NiRel`/`AmountValue` (bake the measured
  place; its scale place is the crossing's x2); `se lifri` for
  `LihiRel`; `sidbo` for `SihoRel`; `pruce` for `PuhuRel` (delete
  inputs/outputs); `mintu` for `CoRef` (delete the standard);
  `frica`/`simsa` for `Contrast`/`Parallel` (occurrence-handle relata by
  default, raw-act relata as the explicit alternative);
  `smuni` for the interpretation crossings; `sinxa`/`cusku`/`tavla`
  projections for the token-fact vocabulary. **Audit note:** for the
  content-parameterized relations (`NiRel`, `LihiRel`, `PuhuRel`,
  `SihoRel`) the official rows carry no place for the abstracted
  content `c`, so place surgery alone cannot derive `XRel(c)` — each
  candidate owes the displayed equation linking its row to `c` (e.g.
  through `EventOfContent` or an explicit realization conjunct)
  before it can be called exact; `smuni` and the token-fact
  projections likewise stand as shadows until their crossings are
  derived rather than described. Until those equations exist these
  are see-also candidates, not adopted fits.
- **Near-fit (proposed extension):** the **`-nmo` indicator-emotion
  family** for the indicator relations: community fu'ivla of the form
  *indicator* `zei cinmo` — `uinmo`
  ("feels happy about", glossed synonym of `gleki`), `u'inmo`,
  `le'onmo`, `fi'inmo`, `ue'inmo`, `uu'inmo`, `a'anmo`, … — one word
  per indicator by a mechanical derivation that extends to every UI
  and both `nai` poles, where the emotion gismu cover only a
  scattering. The generic `inmo` — "feels the emotions expressed by
  indicators x2 (text) about x3" — is the family's schema, and a
  dictionary-attested relation with a sign-typed place: exactly the
  shape §16.3 predicts. The near-fit delta, recorded per §16.2: the
  jbovlaste rows are
  unofficial and carry experiencer × target only, so this
  specification's intensity place is an extension to propose (the
  `le'onmo` entry's own `no'e`/`to'e` note shows the family already
  composes with the scalar operators); the emotion gismu (`gleki`,
  `badri`, `djica`, `ganse`, …) remain see-alsos.
- **No-fit (coinage owed; placeholder carries the definition):**
  `Among`, `Combine` (the plural algebra — `pagbu`/`cmima`/`gripau` all
  cross the plurality/object line and are rejected), `ZuhoRel`,
  `SuhuRel`, `JeiRel`, `Reify`/`Holds` (one coinage, two directions via
  `se`; see-also the experimental `me'ei`/`me'au` pair, the attested
  surface exponents of the two directions — §9.1), `UnitSet`/`CardBasis` (see-also `zilkancu`, which carries two
  competing community definitions and guskant's own vagueness warning —
  the unsettled record supports placeholder status), `InRegion`,
  `AdmissibleThreshold`, `Addition`, `MetalinguisticallyDefective`,
  `Realizes`/`TextOf`/`Quotes`, `Vocative`/`Mention` shadows.
- **Rejected fits (the method note):** `fadni` for `Generic` — its
  official row ("x1 [member] is ordinary/… typical/… in property x2 (ka)
  among members of x3 (set)") is verbatim the specimen theory the
  split-normality witness
  killed (the `Generic` ruling, P11): the audit's standing warning that
  surface resemblance must be checked against the semantics before
  adoption.
- **Class O shadows (vocabulary either way):** `tanru` — the
  modification operator's own name, and the sharpest shadow in the
  inventory: its official row "⟨1⟩ is a binary metaphor formed with ⟨2⟩
  modifying ⟨3⟩, giving meaning ⟨4⟩ in usage/instance ⟨5⟩" (operands
  "both text or both si'o concept") is the §6.2 semantics stated as a
  dictionary entry, place for place — x2/x3 are typed "both text or
  both si'o concept" (inert operands in §16.2's sense), x4 is the
  resolved
  reading `TanruAdmissible` admits, and x5 is the occasion that
  resolves it: the dictionary itself records an occasion-specific meaning,
  supporting §6.1's constrained-`Context` doctrine rather than a fixed lexical
  link or a no-fact-of-the-matter family.
  (`Tanru` the operator stays Class O — composition is an operator —
  but its shadow relation needs no coinage at all.) Further: `xusra`
  (assertion),
  `preti` (question text — its quoted-text x1 fits the sign machinery),
  `minde` (command), `cinmo` (display), `danfu`/`spuda` (answerhood /
  answering act), `drata` (the individual-level shadow of scalar
  otherness).

## References

Works cited across this document set (specification, primer, rationale,
samples). Inline citations name the work and, where applicable, the
chapter/section or dictionary entry. Living sources (wiki pages,
jbovlaste) were last verified 2026-08-25; the repository snapshots
used for source verification are noted per entry.

- **CLL** — Cowan, John Woldemar, *The Complete Lojban Language*,
  Logical Language Group, 1997. Chapter/section citations ("CLL 15.4" =
  chapter 15, section 4) and example numbers (chapter-sequential:
  "Example 16.34") follow the maintained **Contemporary Lojban
  Language** edition (<https://github.com/int19h/cll>), an up-to-date
  fork of the book; the in-text xorlo ratification cited in the header
  is its §6.2 ("The meaning of `lo` given here is the fruit of a reform
  the community calls 'xorlo', after the nickname of its principal
  author; it is now the ratified standard"). The original text is also
  served at <https://lojban.github.io/cll/>; its section and example
  numbering differ in places from the citation edition. (Snapshot:
  fork commit `82f72ae5e19bd4ea5cd9b800433e6a301e7aa0d4`, 2026-08-17.)
- **The official dictionary (jbovlaste)** —
  <https://jbovlaste.lojban.org/>. "Official" place structures and
  definitions are the entries credited to *officialdata*; entries are
  cited by word.
- **The baselined gismu list (1994)** — the official gismu wordlist
  with its original place-structure annotations,
  <https://lojban.org/publications/wordlists/gismu.txt>.
- **xorlo** — "How to use xorlo",
  <https://mw.lojban.org/papri/How_to_use_xorlo>.
- **guskant** — "gadri: an unofficial commentary from a logical point
  of view",
  <https://mw.lojban.org/papri/gadri:_an_unofficial_commentary_from_a_logical_point_of_view>
  (Lojban-only proof:
  <http://guskant.github.io/lojbo/jetnujarco.html>; wiki page id 14098,
  revision 122002, 2017-12-09). The section “Referent of a plural constant is
  not necessarily an individual or individuals” proves from Condition₁ that
  an indefinitely refinable plural constant is neither an individual nor
  individuals, then offers cut bread as the material-noun reading. This
  motivated §4.8's no-atoms boundary, the `CoveredBy` overlap conjunct, and
  cumulative/divisible mass unit profiles; it does not decide P39's placement
  between lexical and description semantics. The concrete dependent term is
  the Condition₁/`CoveredBy` specimen in `samples.md` §3.
- **BPFK Gadri** — "BPFK Section: gadri", Lojban Wiki,
  <https://mw.lojban.org/papri/BPFK_Section:_gadri> (page id 527; the table
  defines `lo [PA] broda` as `zo'e noi ke'a broda [gi'e zilkancu …]`). This
  supplies the description/predication identity used against P39's rejected
  description-only strengthening; it does not supply the `CoveredBy` formula.
- **Brismu** — *brismu: a relational interpretation of Lojban*,
  <https://brismu.systems/>; the chapter "Sets, not Masses" is at
  <https://brismu.systems/sets-not-masses.html>.
- **solpahi** — "A Simpler Quantifier Logic", 2016,
  <https://solpahi.wordpress.com/2016/09/25/a-simpler-quantifier-logic/>.
- **Eberban** — reference grammar,
  <https://eberban.github.io/eberban/> (source:
  <https://github.com/eberban/eberban>); chapters cited by title
  ("Logic framework", "Dictionary conventions", "Eberban from
  scratch"). (Snapshot: commit
  `65a4bc1d64bf7aaf2ed6b11d8758c10e301f605d`, 2026-08-15.)
- **Toaq / Kuna** — Toaq Delta reference grammar,
  <https://toaq.net/refgram/introduction/>; Kuna, its reference semantic
  implementation, <https://github.com/toaq/kuna> (the effect-constructor
  inventory cited in the charter is Kuna's semantics modules as of the
  Delta-era implementation, 2026; snapshot: commit
  `91b20daaac683f568557cc1badc085f8901d64f4`).
- **And Rosta et al.** — "ka, du'u, si'o, ce'u, zo'e", Lojban Wiki,
  <https://mw.lojban.org/papri/ka,_du%27u,_si%27o,_ce%27u,_zo%27e>
  (the n-adic abstraction doctrine discussed in rationale §2.10).
- **Chierchia & Turner** — Chierchia, Gennaro and Turner, Raymond,
  "Semantics and Property Theory", *Linguistics and Philosophy* 11(3),
  1988, pp. 261–302 (the nominalization/predicativization pair behind
  §9.1's reservation).
- **Fine** — Fine, Kit, "A Theory of Truthmaker Content I: Conjunction,
  Disjunction and Negation", *Journal of Philosophical Logic* 46(6), 2017,
  pp. 625–674, <https://doi.org/10.1007/s10992-016-9413-y> (comparative
  state-based composition for §9.3; evidence about the architecture, not
  authority for Lojban's pins).
- **BPFK Abstractors** — "BPFK Section: Abstractors", Lojban Wiki,
  <https://mw.lojban.org/papri/BPFK_Section:_Abstractors> (the
  proposed `ce'u` definition discussed in rationale §2.10 — a
  proposed, partial extension: `ce'u` "almost solely used in `ka`",
  with `si'o`/`du'u`/`su'u` noted as able to "make some sense").
- **BPFK Non-logical Connectives** — "BPFK Section: Non-logical
  Connectives", Lojban Wiki,
  <https://mw.lojban.org/papri/BPFK_Section:_Non-logical_Connectives>
  (proposed `joi` prose and the formal `X joi Y = lo gunma be X .e Y`
  equation; their `joi2`/`joi1` tension is discussed in rationale §1.7a).
- **`joi` working page** — "joi", Lojban Wiki,
  <https://mw.lojban.org/papri/joi> (2018 property/event extension proposals;
  architectural evidence, not a completed denotation).
- **Lojban discussion archive** — the Lojban IRC logs and mailing-list
  archive, cited from the project's verified local snapshot (`lojban-disc`;
  IRC citations give line numbers in its `irc/all_logs.txt`, mail citations
  give Message-IDs); rationale §1.7a cites the 2010 partial `se gunma` use at
  lines 408817–408825 and the 1995 component-inheritance critique preserved
  in the mailing-list archive. Rationale §1.7b cites Jorge Llambías,
  2014-02-07, `<CAO7tK2f+f5tebxR-eH5UAx8mkOJAaZnM3Es2syyOdcMHZpn0qw@mail.gmail.com>`
  (thread “Individuals and xorlo”), for the member-level reading of `lo`
  that the §5.3 lift makes exact — a source the lift generalizes, not one
  that states it.
- **Personal pro-sumti record** — sources for P40, with their evidential roles
  rather than authority: original CLL §7.2 at the baseline source commit
  `13ce309d` says the forms are masses and `mi'o = mi joi do` (the rejected
  alternative); the current `mi jo'u do`/neutral-plural wording was introduced
  by this project's CLL commit
  `224cb6312c6cd8c66a683e08f244f055abe2082b` and cannot self-ratify.
  Jorge Llambías, 2004-08-28,
  `<20040829024337.55170.qmail@web41906.mail.yahoo.com>`, says personal
  pronouns are unmarked for distributivity (independent post-xorlo support).
  Selpa'i, 2013-06-16, `<51BDBA1D.80602@gmx.de>`, explicitly proposes
  `mi'o = mi jo'u do`; Felipe Gonçalves Assis, 2013-06-16,
  `<CALMa68r4BqLh=eFcGPV1mA-fDkYpg3xR6d-Nu4RD8qVrueM4Gw@mail.gmail.com>`,
  favors `jo'u` as the simpler post-xorlo treatment; John E. Clifford,
  2013-06-16,
  `<1371405876.998.YahooMailNeo@web184401.mail.bf1.yahoo.com>`, describes the
  simplest forms as united pluralities whose predicate satisfaction remains
  open. The messages are in the local archive's
  `mail/lojban-list.maildir.zip`. Member-level corpus probes are
  `mi'o remna` by selckiku (IRC `all_logs.txt` line 477248, 2011-08-13) and
  `_mukti_` (line 1005240, 2015-11-01); they expose the no-inheritance cost of
  the rejected group carrier, while collective/reciprocal uses alone do not
  discriminate it.
- **Historical group/mass identity record** — messages in the same local
  archive, cited in rationale §1.7a with their role in the project's
  argument: Arthur W. Protin Jr., 1991-06-20,
  `<9106201157.aa26475@COR4.PICA.ARMY.MIL>` (simple aggregate versus
  organism/organization; inspiration, not adoption); Bob LeChevalier,
  1991-06-20, `<m0jqGpu-0002riC@snark.thyrsus.com>` (universal
  massifiability and the changing-body example; existence and persistence
  evidence, inheritance rejected); the 1994 sumti-paper draft circulated by
  Gerald Koenig, 1994-11-07, `<199411080334.AA18322@nfs2.digex.net>`
  (global extensional candidate, rejected); And Rosta, 1994-12-15,
  `<199412160019.AA21882@nfs1.digex.net>` (groups as singulars); Jorge
  Llambías, 1995-06-14, `<9506150238.aa20944@punt2.demon.co.uk>` (`re loi`
  counting problem and inheritance critique); John E. Clifford, 2002-07-06,
  `<1bb.2c60d43.2a586ccf@aol.com>` (intensional candidate and its costs), and
  2005-12-14, `<20051215003856.5328.qmail@web81308.mail.mud.yahoo.com>`
  (four incompatible mass doctrines); Martin Bays / Jorge Llambías,
  2011-08-12–15, `<20110812152917.GK10697@gonzales>`,
  `<CAO7tK2fvjYGpkpZKDzs6XvVc03xmBvLQEKK88aK5xb1CNYkzkQ@mail.gmail.com>`,
  `<CAO7tK2cCop=+UVuEbsW7_rZ=pdbbsDDyiYL-sW-QbY2RnG7LJg@mail.gmail.com>`
  (first-class groups and complete constituents); and Stela Selckiku,
  2011-07-17,
  `<CAJHgu=8Z8PcvteZkEoN4z0L+YNxwXG0savY4XNFdO=Sg6Q16NA@mail.gmail.com>`
  (arbitrary aggregate abstraction; responsibility/inheritance gloss not
  adopted).
- **Boolos** — Boolos, George, "To Be Is to Be a Value of a Variable
  (or to Be Some Values of Some Variables)", *The Journal of
  Philosophy* 81(8), 1984, pp. 430–449.
- **Oliver & Smiley** — Oliver, Alex and Smiley, Timothy, *Plural
  Logic*, 2nd edition, Oxford University Press, 2016.
- **McKay** — McKay, Thomas J., *Plural Predication*, Oxford University
  Press, 2006 (non-distributive predication with `among` as the plural
  primitive; the source of the xorlo page's “distributively” vocabulary;
  rationale §1.7b's plural-logic restrictor).
- **Wand** — Wand, Mitchell, "The Theory of Fexprs is Trivial",
  *Lisp and Symbolic Computation* 10(3), 1998, pp. 189–199 (the ground
  for the rejected unrestricted-operand-reflection alternative discussed
  in rationale §2.9).
- **Nanevski, Pfenning & Pientka** — "Contextual Modal Type Theory",
  *ACM Transactions on Computational Logic* 9(3), 2008 (prior art for
  the staged extension set aside in rationale §2.9).
- **Harper** — Harper, Robert, *Practical Foundations for Programming
  Languages*, 2nd edition, Cambridge University Press, 2016 (abstract
  binding trees and the direct binding discipline).
- **Taha & Sheard** — "MetaML and Multi-stage Programming with
  Explicit Annotations", *Theoretical Computer Science* 248, 2000
  (typed staging with open code).
- **Davies & Pfenning** — "A Modal Analysis of Staged Computation",
  *Journal of the ACM* 48(3), 2001 (staging as modal logic; retained as
  design-history background, not a baseline dependency).
- **Heim & Kratzer** — Heim, Irene and Kratzer, Angelika, *Semantics in
  Generative Grammar*, Blackwell, 1998.
- **Groenendijk & Stokhof** — Groenendijk, Jeroen and Stokhof, Martin,
  "Dynamic Predicate Logic", *Linguistics and Philosophy* 14(1), 1991,
  pp. 39–100.
- **Kamp** — Kamp, Hans, "A Theory of Truth and Semantic
  Representation", in *Formal Methods in the Study of Language*,
  Mathematisch Centrum, 1981 (Discourse Representation Theory).
- **van den Berg** — van den Berg, Martin H., *Some Aspects of the Internal
  Structure of Discourse: The Dynamics of Nominal Anaphora*, doctoral thesis,
  University of Amsterdam, 1996,
  <https://eprints.illc.uva.nl/id/eprint/1996/> (plural information states;
  recorded candidate for P6, not an adopted Lojban analysis).
- **Brasoveanu** — Brasoveanu, Adrian, "Donkey Pluralities: Plural
  Information States versus Non-Atomic Individuals", *Linguistics and
  Philosophy* 31(2), 2008, pp. 129–209,
  <https://doi.org/10.1007/s10988-008-9035-0> (comparison of dependency in
  plural information states and individual plurality; P6's model-level
  candidate).
- **Link** — Link, Godehard, "The Logical Analysis of Plurals and Mass
  Terms: A Lattice-theoretical Approach", in *Meaning, Use, and
  Interpretation of Language*, de Gruyter, 1983.
- **Hamblin** — Hamblin, Charles L., "Questions in Montague English",
  *Foundations of Language* 10(1), 1973, pp. 41–53.
- **Karttunen** — Karttunen, Lauri, "Syntax and Semantics of Questions",
  *Linguistics and Philosophy* 1(1), 1977, pp. 3–44.
- **Potts** — Potts, Christopher, *The Logic of Conventional
  Implicatures*, Oxford University Press, 2005 (published online
  December 2004).
- **Searle** — Searle, John R., *Speech Acts: An Essay in the Philosophy
  of Language*, Cambridge University Press, 1969.
