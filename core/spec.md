# The Lojban semantic core

*A definition of Lojban meaning in terms of a small typed semantic
language.*

This document defines a semantic core for Lojban: a typed language of
meanings such that every Lojban utterance, under a resolved reading,
denotes a term of the core. It is a **definition**, not a description: where
the Complete Lojban Language (CLL) is explicit that a meaning is vague, the
core represents that vagueness with typed machinery; where CLL is merely
underspecified — vague by accident rather than by design — this document
pins an interpretation and records the pin as a numbered ruling. The
baseline for gadri and quantification is xorlo
(<https://mw.lojban.org/papri/How_to_use_xorlo>); CLL's pre-xorlo gadri
semantics is superseded where they conflict.

The intended audience of this document is a reader comfortable with formal
semantics: typed lambda calculi, generalized quantifiers, dynamic semantics,
multidimensional/projective meaning, and speech-act theory. A companion
[primer](primer.md) presents the same content for fluent Lojbanists who are
not semanticians; a [rationale](rationale.md) argues, construct by
construct, why the core is shaped as it is and not otherwise; and
[samples](samples.md) gives worked specimens with their Lojban sources.

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

### 1.2 Resolved readings

The core denotes **resolved readings**. Processes that turn a text into a
reading — anaphora resolution (which antecedent `ri` takes), erasure
(`si`/`sa`/`su`), elliptical expansion (`go'i`, `no'a`), sticky-tense
propagation (`ki`), indicator target selection — are **text-to-reading
rules**. They are normative (the mapping annex states them; a conforming
reading of a Lojban text must obey them) but they contribute no term
constructors: the calculus sees their *results* — variable bindings, token
identities, expanded content — never the processes themselves. A
syntactically well-formed text whose resolution fails (an anaphor with no
accessible antecedent, an unassigned assignable with no discourse key) has
no resolved reading; that is a statement about the mapping, not an error
object in the semantics.

### 1.3 Three ways not to be specific

The single most load-bearing distinction in this document is between three
things a meaning can do short of full specificity. They are distinct term
formers with distinct semantics (§5.3), and confusing them is the
characteristic mistake this core is designed to prevent:

- **Reference** (`Refer`): introduce a discourse referent satisfying a
  descriptive condition. A referent is new, veridically described (for
  `lo`), and available to subsequent anaphora.
- **Contextual resolution** (`Context`): retrieve a contextually salient
  value. Nothing is asserted about it and no referent is introduced; the
  speaker expects a cooperative hearer to recover a *specific* value, and
  communication fails if they cannot. Omitted places, `zo'e`, `co'e`,
  `do'e`, deictic grounds, and salient scales are of this kind.
- **Deliberate vagueness** (`Vague`): a typed, constrained set of
  admissible precisifications with **no fact of the matter** as to which is
  meant. The term never chooses. The tanru modification link, `tu'a`'s
  withheld abstraction, and soritical thresholds are of this kind.

The operational test — the **recovery test** — is printed with the full
classification in §6.1.

A fourth possibility is **absence**: the meaning simply lacks a dimension.
An unmarked bridi makes no temporal claim; a bare `kau` answerhood makes no
exhaustivity claim; unmarked plural predication makes no distributivity
claim. Absence is represented by absence — no hole, no parameter, no
covert operator. Where a dimension is absent, the truth conditions are
those of the weakest reading, and strengthenings enter only lexically,
pragmatically, or by explicit marking. (Rulings P8, P9, P4.)

### 1.4 Ambiguity is upstream

Grammatical ambiguity — a text with several parses, or a parse with several
resolutions — yields several resolved readings, each a distinct core term.
The core never encodes disjunctions of readings; it is downstream of
disambiguation. In particular, a construct is never classified `Vague`
merely because a text is ambiguous: `Vague` is a property of one reading's
meaning, not of the reader's uncertainty between readings. (Where a
construction's readings genuinely differ — e.g. implicit `ce'u` with
several unfilled places — the mapping annex says "distinct readings," never
"contextual vagueness"; ruling P12.)

### 1.5 Well-formedness, not failure

The core is defined by formation rules and typing judgments. An ill-typed
combination is not a term; a construction whose side conditions fail (e.g.
closure over a non-defaultable place, §4.6) is undefined at that point.
This document has no failure codes, no diagnostics, and no processing
model. Meanings this core deliberately does not analyze are listed in the
gap register (§14) with the reason no analysis is assigned; a gap is a
statement about this specification, not a runtime event.

### 1.6 Two truth values

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

- `(operator operand …)` — application and operator forms; PascalCase
  names are core operators and library forms; lowercase names are lexical
  predicates (dictionary words: `klama`, `gerku`); Greek λ introduces
  functions; a small set of mathematical glyphs (`¬ ∧ ∨ → ↔ ⊕ ∀ ∃ = ∈ ⊆
  ∪ ∩ ≤ <`) name the logical and mathematical operators.
- `$name` — variables, always introduced by a binder with an explicit
  type: `(λ (($x Entity)) …)`, `(Let (($p T v)) …)`.
- `:label value` — a labelled place fill inside a predication (§4.2);
  `:2` names the second lexical place, `:Eventuality` the event place.
- `; text` — comments, to end of line; consumed as whitespace. By
  convention a specimen's first comment line is its Lojban source.

Notation conventions — elision of inferable types, the writing of `Close`
(§4.6), currying conventions, pretty-printing — are non-semantic: two
spellings that denote the same term per this document's rules are the same
meaning, and no unique canonical spelling is defined or required. This
chapter is the only place notation is normative, and only to the extent
that a reader must be able to parse the examples.

## 3. Types

### 3.1 Sorts of individuals

The domain of first-order individuals is sorted. `Entity` is the top
first-order sort. Beneath it:

```text
Entity
├─ Eventuality       events and states of affairs; subsorts:
│      Achievement, Process, Activity, State, Experience,
│      Locution (an uttering event)
├─ Location          ├─ Time
├─ Amount            (positions on scales)
├─ Scale             ├─ Epistemology
├─ TruthValue
├─ Concept           ├─ AbstractNature
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

Sorts on one line above are siblings, never subsorts of one another
(`Epistemology` is not a `Scale`, `AbstractNature` not a `Concept`).
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
description; see ruling P3.

### 3.2 Plural reference

`Referents<T>` is the type of **plural references**: nonempty,
number-neutral pluralities of `T`s. It is not `Set<T>` (a set is a single
first-order object with membership; a plurality is not an object over and
above its members), not a mereological sum, and not a group. Its algebra
(§4.8) has exactly a join (`Combine`) and the induced subreference order
(`Among`); no atomicity, no distributivity, and no covers are assumed.
`Referents<T>` is covariant in `T`, and a single `T` lifts implicitly to a
singleton `Referents<T>` at referential positions (a typing rule, not an
operator).

Nonemptiness is part of the type: there is no empty plural reference.
(Consequences for `lo no broda` are drawn in ruling P22.)

### 3.3 Relations, functions, and rows

A **place row** ρ is a finite sequence of labelled, typed places, e.g. for
`klama`:

```text
ρ(klama) = ⟨ x1:Referents<Entity>, x2:Referents<Entity>,
             x3:Referents<Entity>, x4:Referents<Entity>,
             x5:Referents<Entity> ; ev:Referents<Eventuality> ⟩
```

The event place `ev` is distinguished: it is present exactly on
event-licensed lexical entries (§10) and is filled with `:Eventuality`.

- `PredTerm<ρ>` — the type of relations over row ρ. It is a **transparent
  alias** for the row-function type `Record ρ → Content`: partial filling
  is abstraction over the residual row, place selection is record
  projection, and two relations equal on all row records are the same
  relation. The alias is retained pervasively in signatures because
  labelled places are the load-bearing Lojban-specific structure (free
  place order, `zi'o`, conversion, place questions all speak in labels).
- `Fn<(A …), B>` — ordinary functions with positional parameters, the type
  of λ-abstractions. Properties are `Fn<(T), Content>`; generalized
  quantifiers are `Fn<(Fn<(T), Content>), Content>`.
- `Label<ρ>` — the finite type of ρ's place labels; the domain of place
  questions (§8.3).

Purity is tracked in the function space: `Fn` is the **pure** arrow — a
function whose body, *when its result is evaluated*, performs no dynamic
effects (§5): no introductions, no contextual retrievals, no projective
emissions — and `EFn` the effectful arrow. Positions that demand purity
are exactly **set comprehension (§4.9), quantifier and `Generic`
restrictors (§4.10, §5.8), and selection restrictors (§5.6)**; a body with
unhoisted effects simply fails to have the pure type. Nuclear scopes,
`OpenQ` bodies, and `Generic`'s nuclear operand are `EFn` — they may
close places contextually and introduce referents, with the accessibility
table governing what escapes. This is the whole of the purity discipline:
a typing fact, not an algorithm. `PredTerm<ρ>`, `Fn`, and `EFn` are types
and appear freely in variable annotations, λ parameter lists, and
`Context`/`Vague` type arguments.

### 3.4 Control types

```text
Content            evaluable (dynamic) propositional content
RefComp<T>         reference/contextual computations returning T
Act<F>             speech acts of force F ∈ {Assertion, Question,
                   Directive, Expressive, Address}
Discourse          performed discourse (sequences of acts and transitions)
Query<A>           questions with answer domain A
```

`Content` is the type of what can be asserted, questioned, negated, and
embedded. Its denotation (§5.1) is a world-indexed context-change
potential; the world index never appears in the term language. `Act<F>`
values are first-class: constructing an act and performing it are
different things (§7.1), which is what keeps quotation and reported speech
from performing their contents.

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
; klama fe ti tu        — x2 = ti, x3 = tu, x1 unfilled
(klama :2 This Yonder)
```

The event place is filled as `:Eventuality e`. Unfilled places do not
default silently; they are closed by `Close` (§4.6) into explicit
contextual computations, or abstracted by λ, or genuinely absent only
under `DropPlace`.

### 4.2 Place conversion

`se`/`te`/`ve`/`xe` and FA tags are consumed by the mapping: a converted
predication is the base predication with fills routed to their base
places. A converted relation escaping into a function position is the
λ-abstraction over the permuted row:

```lisp
; se tavla, as a first-class binary relation
(λ (($new-x1 (Referents Entity)) ($new-x2 (Referents Entity)))
  (tavla $new-x2 $new-x1))
```

No `Se` operator exists in the core.

### 4.3 Place deletion

`(DropPlace R n) : PredTerm<ρ − n>` is the relation ρ with place `n`
removed — the meaning of `zi'o`. Deletion is semantic surgery on the
relation, not omission of a fill: `mi klama ti zi'o ti ti` predicates a
relation that *has no origin role*, which neither `zo'e` nor closure can
express. A lexical entry states which deletions are meaningful (§10).

### 4.4 Functions and binding

`(λ ((x T) …) body)` forms functions; application is juxtaposition.
`(Let ((x T v)) body)` is inert sharing — definable as immediate
application, retained for legibility and for expressing identity of one
value used twice (`goi` aliasing). `Let` bodies may not smuggle effects
into shared positions: an effectful computation is shared by `Bind`
(§5.2), never by `Let`. There is no recursion former in the term language;
recursive definitions occur only in the library's metalanguage (§12).

### 4.5 Connectives and quantifiers

The logical operators are `¬ ∧ ∨ → ↔ ⊕` over `Content` and the
quantifiers `∀ ∃` over typed λ-bodies, with (multi-parameter) joint loci:

```lisp
(∀ (λ (($x Entity) ($y Entity)) …))
```

Statically they have classical truth conditions. Dynamically each carries
an accessibility row (§5.4) that is part of its meaning; `↔` and `⊕` are
primitive precisely because their classical rewrites duplicate operands,
and duplication re-runs dynamic effects. Multi-parameter loci are the
normal form of donkey configurations (§5.6) and simultaneous termsets
(ruling P17).

Equality `=` is primitive at every first-order sort; `du` maps to it.

### 4.6 Closure

`Close` turns an open predication into `Content`: it existentially closes
the event place (when the row licenses one and no explicit event fill or
abstraction consumes it) and introduces one `Context` computation per
remaining defaultable place. It is a **normatively defined derived
operation** — schema, for a row with unfilled defaultable places p₁…pₖ and
an event place:

```lisp
(Close P)  ≝
(Bind (($v1 T1 (Context)) … ($vk Tk (Context)))
  (∃ (λ (($e (Referents Eventuality)))
    (P :p1 $v1 … :pk $vk :Eventuality $e))))
```

Each omitted place is a *distinct* contextual computation (ruling P15),
and the site/key identity rule of §5.3 applies: when a λ-abstracted
predication containing closure sites is applied more than once within one
performance, the closure sites keep their identity — `mi .e ti klama`
shares one contextual destination across both conjuncts unless the reading
expresses otherwise. `Close` is undefined at a row whose remaining places
are not defaultable; such content must fill or abstract them explicitly.
The surface convention that `Close` is implicit at force boundaries is
notation (§2), not semantics.

### 4.7 Place questions

`Label<ρ>` (§3.3) types questions over places. The defined form
`(At R $p v)`, for `R : PredTerm<ρ>` and `$p : Label<ρ>`, fills `R`'s
place denoted by `$p` with `v`; it abbreviates the finite case split over
ρ's labels

```lisp
(∨ (∧ (= $p ℓ₁) (R :ℓ₁ v …)) … (∧ (= $p ℓₙ) (R :ℓₙ v …)))
```

and is well-formed only when the candidate domains of distinct computed
fills in one predication are disjoint. `fi'a` maps to an open question
over `Label<ρ>` (§8.3); an open relation question (`mo`) binds a
`PredTerm`-typed variable directly and needs no special row machinery.

### 4.8 The plural algebra

`Combine : Referents<T> × Referents<T> → Referents<T>` is plural join
(associative, commutative, idempotent — `jo'u`), and
`Among : Referents<T> × Referents<T> → Content` is the subreference
order. Both are primitive at the plural type and axiomatized together
(`Among x y` holds exactly when `Combine x y` and `y` co-refer; typed
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

That is the whole plural kernel. No atoms are assumed (nothing requires
that references bottom out in singletons), no distributivity operator is
covert, and no cover parameter attaches to predication: a lexical
predicate applied to a plural reference holds or fails of that plurality,
and which configurations verify it is the predicate's lexical business
(the lexicon may declare per-place plurality behavior, §10). Marked
readings are explicit: the library's `Distrib` (from `∀`/`Among`) for
each-reading, group objects (§4.9) for collective packaging, `lu'a` and
cover vocabulary (§12) when a resolved reading commits to structure.
(Rulings P4; the design follows plural logic — Boolos, Oliver & Smiley —
rather than covert-operator theories.)

### 4.9 Collections and mathematics

Collection *objects* are first-order individuals distinct from plural
references:

- `(SetOf P) : Set<T>` for pure `P : Fn<(T), Content>` — extensional
  comprehension; `∈` is membership; `Card : Set<T> → Cardinal`.
- `Group<T>` objects are related to their components by the lexical
  relation `gunma` (x2 plural — ruling P5); `Set<T>` objects by `selcmi`.
  `loi`/`lo'i` descriptions refer to such objects (§11); neither unwraps
  implicitly to its members.
- `List<T>` objects carry order (`ce'o`); indexing and `ZipWith` (the
  `fa'u` analysis) are library forms over list recursion (§12).
- `Number` and its subsorts carry the arithmetic operators
  `+ − × ÷ < ≤`; partial operations (division, non-total roots) carry
  projective definedness conditions (§5.5). Intervals are comprehensions
  with endpoint conditions; further mathematics (exponentiation, bases,
  arrays) is library and gap-register material.

### 4.10 Cardinal quantification

Bare-PA terms denote **witness-set selection** (rulings P1, P17): `ci
gerku cu bajra` selects a three-membered witness set of dogs and says its
members ran —

```lisp
; ci gerku cu bajra — the default (witness-set) reading
(∃ (λ (($S (Set Entity)))
  (∧ (= (Card $S) 3)
     (∀ (λ (($x Entity)) (→ (∈ $x $S) (∧ (gerku $x) (bajra $x))))))))
```

— and this is what the library's `Exactly n` (§12) abbreviates. Exactness
attaches to the selected set; nothing is said about dogs outside it, so a
fourth runner does not falsify the sentence. The **global** exact reading
— "the dog-runners number exactly three, and no others" —

```lisp
; the marked global strengthening (not the bare-PA default)
(= (Card (SetOf (λ (($x Entity)) (∧ (gerku $x) (bajra $x))))) 3)
```

is a distinct, stronger meaning, named `GlobalExactly` in the library and
available where a reading commits to it. CLL ch. 16 §6's own gloss of bare
numeric quantification ("exactly two, no more or less") is this global
reading; pin P17 records, as a documented divergence with its argument,
that this specification takes witness-set selection as the default — the
reading dominant in xorlo-era usage and the one that composes with
witness export (§5.6) and termsets.

## 5. Dynamics

### 5.1 Model theory

A model supplies a set of worlds W, sorted domains, world-indexed lexical
interpretations, and **information states**: sets of world–assignment
pairs. The dynamic layer is one algebraic computation type. Its carrier:

```text
Comp<A>    =  InformationState → P( InformationState × A × Obligations )
Content    =  Comp<Unit>          RefComp<T> = Comp<T>
Act<F>, Discourse : Comp<Unit> at the performance level (their effect
                    vocabulary adds commitment/performance operations)
Bind       :  Comp<A> × (A → Comp<B>) → Comp<B>   (uniform; §5.2)
```

where `Obligations` collects the pending projective commitments
(presupposition conditions, supplement sides with their anchors and
handlers) accumulated but not yet discharged. A computation, run on a
state, yields the possible output states (nondeterminism carries plural
selection and `Vague` families), each with a returned value and its
obligations; lexical truth at a world filters states; assignment
extension is referent introduction; `Bind` sequences, threading state and
unioning obligations. Each named operation of this chapter (`Refer`,
`Context`, `Vague`, `Presuppose`, `Supplement`, the selections of §5.6,
the connectives' state-passing) is an operation of this algebra, and its
clause consists of two parts with two homes: **what escapes and what is
accessible is stated once, in the accessibility table (§5.4)** — nothing
elsewhere may restate it — while return values, truth filtering, and
obligation discharge are fixed by the carrier above and the operation's
own paragraph.

The world index supports the intensional facts of §5.7 (de re/de dicto,
opacity) and the subordinated contents of §7.6; **no world variable or
world type appears in the term language**. Counterfactual and hypothetical
mood (`da'i`) is a registered gap (§14) whose future treatment will live
in this index.

**The utterance context** is a typed record:

```text
ctx = ⟨ speaker  : Referents<Entity>,   audience : Referents<Entity>,
        time     : Time,                place    : Location,
        ground   : Ground ⟩

Speaker, Audience : ctx → Referents<Entity>
Now : ctx → Time            Here : ctx → Location
Proximity          = Proximal | Medial | Distal   (a closed type)
GroundDescription  : the sort of ground specifications (an orientation
                     center with its perspective facts; `Ground` values
                     are constructed from them)
Deictic       : Proximity × Ground → Referents<Entity>
ShiftedGround : GroundDescription → Ground        (constructs — §6.1)
InContext     : Content × Ground → Content
```

Demonstratives (`This`/`That`/`Yonder`, i.e. `ti`/`ta`/`tu`) are
`Deictic` at the three proximities against the context's ground.
`ShiftedGround` **constructs** a ground (never a contextual resolution),
and `InContext` evaluates content with deictic projections taken from the
given ground — the explicit form of context shift (`ra'o`; §11).
`InContext` shifts the *utterance* context only; shifting the *evaluation
world* (hypothetical mood) is a different member of the same `Shift`
operator family and awaits the `da'i` gap entry (§14).

### 5.2 Effectful binding

`(Bind ((x T comp)) body)` runs the computation `comp : RefComp<T>` and
binds its result for `body`, sequencing effects left to right. `Bind` is
the eliminator for `RefComp` and cannot be β-reduced away: the computation
may introduce referents, consult context, or project obligations. `Let`
(§4.4) is its pure degenerate case.

`Bind` is **uniform across the result categories**: `Act<F>` and
`Discourse` denote computations in the same carrier as `Content` (§5.1 —
their effects include performance and commitment), so `body` may be
`Content`, an act, or a discourse, and the binding scopes the referent
over the whole body either way. This is what lets a description or
selection introduced before an act sequence remain bound across it
(`(Bind ((x (Refer P))) (Do a₁ a₂))` — the ordinary spelling of
cross-sentence reference).

### 5.3 The specificity triad

Three primitive computations answer §1.3:

- `(Refer P) : RefComp<Referents<T>>`, for `P` a property of references —
  introduces a **new discourse referent**: a nonempty, number-neutral
  plurality satisfying `P` veridically, fixed for its force segment, and
  accessible to later anaphora per §5.4. This is the xorlo semantics of
  descriptions (ruling P1): no implicit outer quantifier, no uniqueness,
  no default cardinality.
- `(Context deps…) : RefComp<T>` — retrieves a contextually salient value
  of type `T`, constrained by an optional property and by its declared
  dependencies (binders the choice may covary with). It asserts nothing
  and introduces nothing. **Site/key identity:** each syntactic occurrence
  is one site; a site retrieves once per performance, so re-applications
  of a shared λ reuse the site's value; keyed uses (unassigned KOhA,
  ruling P16) retrieve once per key per discourse segment, every
  occurrence of the key consuming the same value.
- `(Vague P) : RefComp<T>` — denotes the nonempty set of **admissible
  precisifications** of type `T` satisfying the constraint `P`, with no
  fact of the matter selecting one. Composition law: precisification sets
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
| `∧`, `Do` | Left to right; each operand sees all preceding successful introductions; introductions of both survive. Facet conjunctions over a shared event (tense/modal joining, §11) are ordinary `∧`. |
| `∨` | Operands each see the incoming state; branch-local introductions do not escape the disjunction. |
| `¬` | Operand sees the incoming state; nothing escapes. |
| `→` | Antecedent sees the incoming state; consequent sees the antecedent's successful introductions; nothing escapes the conditional. Donkey normalization (§5.6) applies when a consequent anaphor binds an antecedent introduction. |
| `↔`, `⊕` | Each operand evaluated exactly once against the incoming state; nothing escapes. (Hence primitive: rewrites would duplicate evaluation.) |
| `∃`, `∀`, GQs | The restrictor is pure (`Fn`); body introductions are local to each instantiation. **Witness export:** a successful evaluation of an exporting quantifier introduces its witness referent(s) — see §5.6, including the dependent case. |
| `Refer` | Introduces its referent into the current force segment; fixed there (no re-selection under `¬` or across facets). |
| `Presuppose` | See §5.5: the condition projects to the nearest legal commitment boundary; the at-issue operand sees the incoming state. |
| `Supplement` | See §5.5: side content is committed once at its handler, projectively; the at-issue operand's value passes through. |
| Force constructors, `Perform` | Act boundaries close force segments: referents introduced inside a constructed-but-unperformed act are not accessible outside it; performed acts in `Do` chain normally. |
| Quotation, `Reify` | Opaque: nothing crosses a sign boundary; reified content's internal introductions are not discourse-accessible. |

### 5.5 Projective content

`(Presuppose π body)` imposes `π` as a projective condition: it must hold
at the nearest boundary that can commit it (accommodating contexts may add
it), and it survives `¬`, `∨`, `→`, and question force. It is the
mechanism of quantifier import (ruling P2), definedness of partial
operations (§1.6), and lexically triggered presuppositions.

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
SelectSome      P : RefComp<Referents<T>>   ; ≥ 1 (su'o)
```

(restrictor `P` pure). A selection introduces its witness reference —
explicitly bound by `Bind`, like every computation — and the nuclear
content then predicates of it:

```lisp
; ci gerku cu bajra .i ri tatpi
(Do
  (Bind (($dogs (Referents Entity)
          (SelectExactly 3 (λ (($x Entity)) (gerku $x)))))
    (Do (Assert (Distrib bajra $dogs))
        (Assert (Close (tatpi $dogs))))))
```

The library's GQ forms (`Exactly`, `AtLeast`, `Some`, … — §12) are
defined over selections; forms whose success is grounded in absence or an
upper bound (`No`, `AtMost`, `FewerThan`) select nothing and export
nothing. `Every` exports the full restrictor reference. Binding a witness
never re-evaluates a selection; witnesses of distinct selections are
distinct; and a witness is accessible exactly where the accessibility
table lets its `Bind` scope reach (so nothing here is a free-variable
convention — the binder is visible in the term).

**Dependent witnesses.** A selection in the scope of a quantifier is a
*dependent* selection — one witness per value of each governing binder.
An anaphor binding a dependent witness from outside the governing scope
triggers joint-locus normalization (the donkey rule below, one level up):
the selection raises into a joint locus with its governor, both
restrictions form the antecedent (with the description quantifier's
import preserved — the `Presuppose` wrapper carries over), and the
anaphor's content joins the consequent. Fixture: `ro prenu cu ponse ci
gerku .i ri tatpi` normalizes to

```lisp
(Presuppose (∃ (λ (($x Entity)) (prenu $x)))
  (∀ (λ (($p Entity) ($d (Referents Entity)))
    (→ (∧ (prenu $p)
          (= (CardBasis $d (λ (($x Entity)) (gerku $x))) 3)
          (Close (ponse $p $d)))
       (Close (tatpi $d))))))
```

— each person's dogs are tired; no single plural of all dogs is asserted,
and the summation reading is expressible only by explicit collection,
never automatic. Two boundary notes: an embedded xorlo *description*
(`ro prenu cu bevri lo pipno`) is a referential constant shared across the
governor's values, not a dependent witness — only genuinely
quantificational selections depend; and anaphora to a witness that does
not escape its governor is simply inaccessible — a reading the table
correctly refuses.

**Donkey normalization** (ruling P6). When an anaphor binds an
introduction made inside a restrictor (`ro prenu poi ponse su'o xasli cu
darxi ri`), the reading normalizes to the governing quantifier's joint
multi-parameter locus, with the description's import preserved and the
indefinite's variable at the plural type (its witness is a plural
reference; the atomic-pair spelling is the distributive strengthening):

```lisp
(Presuppose (∃ (λ (($x Entity)) (∧ (prenu $x)
              (∃ (λ (($y Entity)) (∧ (xasli $y) (Close (ponse $x $y)))))))
  (∀ (λ (($p Entity) ($d (Referents Entity)))
    (→ (∧ (prenu $p) (xasli $d) (Close (ponse $p $d)))
       (Close (darxi $p $d))))))
```

The restrictor's relational conjunct ties the parameters; no E-type
description or choice function is invoked. Bare mathematical `ro da`
normalizes without the `Presuppose` — the import belongs to description
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

### 5.8 Genericity

`(Generic mode holder? restrictor nuclear) : Content`, with
`mode ∈ {Typical, Stereotypical}` and `holder` present exactly for the
stereotype reading (`le'e`: the Speaker, grammatically fixed), is the
axiomatic generic quantifier: it relates a pure restrictor and nuclear
scope through a normality ordering **that may depend on the nuclear
predicate**. It is not `∀`, not `∃`, and yields no referent: `lo'e cinfo
cu se kerfa lo clani` and `lo'e cinfo cu jbena lo cinfo` are supported by
different normality classes (adult males; adult females), which is why no
fixed "typical lion" reference exists to verify both. Generic anaphora
(`lo'e mlatu … .i ri …`) is gap-registered. The operator is frankly
axiomatic — its normality structure is constrained, not defined; the
rationale records why this honesty beats both a fixed-prototype reference
and a silent lexical relation.

## 6. Explicit vagueness

### 6.1 The recovery test and the classification

The decision rule for §5.3's triad, applied to every underspecified
construct in Lojban:

> **The recovery test.** If a cooperative hearer is expected to arrive at
> a *specific* value — and communication fails when they cannot — the
> construct is `Context`. If the speaker waives specificity, so that
> recovery yields at most an admissible family with no fact of the matter
> selecting a member, it is `Vague`. If the meaning simply lacks the
> dimension, it is **absence** (§1.3) and gets no machinery at all.

The normative classification:

| Construct | Class | Notes |
|---|---|---|
| omitted places, `zo'e` | `Context` | one distinct site per omission (P15) |
| `co'e` (elliptical selbri), `do'e` (elliptical tag) | `Context` | the ellipsis family expects recovery; a deliberately waiving use is written with explicit `Vague` |
| `zu'i` | `Context` | with a typicality constraint |
| deictic grounds; demonstrative grounds | `Context` | `ShiftedGround` values are constructed, never resolved |
| scale **dimension** of gradable/scalar predication | `Context` | which scale (beauty, price, speed) is recoverable |
| soritical **cutoffs/regions** on a scale | `Vague` | includes `no'e`'s neutral-region width, riding a `Context` scale |
| tanru modification link | `Vague` | CLL ch. 5's constitutive vagueness; the library's named link values (manner, material, purpose, …) are precisification constants a resolved reading may commit to |
| `tu'a` | `Vague` | admissible values are abstractions of some content (`∃c,k. a = the abstraction of c under k`) bearing `srana`-aboutness to the operand; the abstraction-shape conjunct is required — aboutness alone is too weak |
| `joi`'s connecting relation; mixture kind | `Vague` | the exact non-logical connectives (`jo'u`, `ce`, `ce'o`, `fa'u`, `ku'a`, `jo'e`, `pi'u`) are exact |
| vague-quantity thresholds (`so'i`, `so'e`, …; `ji'i` tolerance) | `Vague` | sorites: no fact fixes the boundary |
| `du'e` / `mo'a` / `rau` | `Vague` threshold **constrained by** a `Context` standard/purpose | two parameters; the purpose is recoverable, the boundary is not |
| `na'i`'s defect dimension | `Context` | the hearer is expected to see what is defective |
| bare `jai` (no FAI tag) | `Vague` | an unspecified involvement of the promoted argument in the host relation's event — the `tu'a` pattern at relation level (CLL 9.12); tagged `jai` promotes an explicit role and is exact (library expansion) |
| tenselessness; bare-`kau` exhaustivity; unmarked distributivity | **absence** | no hole, no parameter (P8, P9, P4) |

### 6.2 Tanru

`(Tanru M H) : PredTerm<ρ(H)>` — modification of head `H` by modifier `M`.
The result's row is the head's row (CLL ch. 5: the tanru's places are the
tertau's). Its semantics: the head predication holds, and an admissible
modification link relates `M` to that predication —

```lisp
((Tanru M H) fills…) ≝
(Bind (($link (PredTerm ρ(H))
        (Vague (λ (($r (PredTerm ρ(H)))) (TanruAdmissible M H $r)))))
  (∧ (H fills…) ($link fills…)))
```

`TanruAdmissible` is part of tanru's meaning, not a lookup: it requires
that the link make `M` modify *something* in the head predication (the
event's manner, a participant, a purpose, a source, …) and nothing
stronger — no x1-sharing, no intersectivity. The library's named links are
the common precisifications; a lujvo is a lexicalized precisification.

### 6.3 Scalar operators

`(Scalar k P)`, `k ∈ {OtherThan, Opposite, Neutral}`, is the `na'e`/
`to'e`/`no'e` family: an operation on `P` relative to a scale or
admissible-alternative set. The scale dimension is `Context` (lexically
fixed when the dictionary provides one); soritical region boundaries are
`Vague` per §6.1. Each operator **denies `P`'s stated region and
positively asserts an alternative** — CLL 15.4: a selbri negation
"asserts that a relationship exists other than that stated", and "the
result of `na'e` negation remains an assertion of some specific truth" —
so all three entail `¬P` at the stated region, differing in the region
asserted: `OtherThan` some admissible alternative (chosen `Vague`-ly
within the scale/set), `Opposite` the antipodal region, `Neutral` the
midpoint region (excluding both extremes). Scalar negation is therefore
*stronger* than `¬`, not weaker: `ta na'e melbi` denies beauty and
asserts a contextually admissible alternative aesthetic standing. The
same former serves as the documented *fallback* for indicator polarity
where the lexicon lists no `nai`-pair (§7.6).

### 6.4 Gradable predication and vague quantities

Gradable predication exposes its two parameters through the library's
`Grade` schema:

```text
Grade : GradableRel<ρ,ℓ> × Scale × Region<Scale> → PredTerm<ρ>
```

with the scale obtained by `Context` when not lexical (which dimension —
size, price, beauty — is recoverable) and the region boundary by `Vague`
(no fact fixes the cutoff). `ta barda` is `Grade(barda, Context-scale,
Vague-region)` applied; the `na'e` family (§6.3) operates on the same
scale value.

The degree quantifiers (`Many`, `Few`, `TooMany`, `TooFew`, `Enough`,
`Most`; §12) are cardinal comparisons against thresholds whose
admissibility predicate `AdmissibleThreshold(kind, restrictor, standard)`
is declared with them: the threshold is `Vague`, and for the
purpose-relative kinds (`du'e`/`mo'a`/`rau`) it is constrained by a
`Context`-recovered standard/purpose. `ji'i n` is `Vague` tolerance about
a stated `n` — a different shape from `so'i`'s vague threshold. None of
these rounds to an exact number, and none fails: `so'i prenu cu klama`
has exactly the truth conditions its vagueness permits — the family of
readings over admissible thresholds (§5.3, §6.5).

### 6.5 The composition law for `Vague`

Normative, and complete — no operator interacts with precisification sets
in any way not stated here:

- **VC1 (Denotation).** A `Vague` computation denotes the nonempty set of
  its admissible precisifications and no choice among them; a reading
  containing a `Vague` parameter denotes the family of precisified
  readings. Nonemptiness is a **static proof obligation of the formation
  judgment**: `(Vague P)` is well-formed at `A` only under a discharged
  judgment `⊢ ∃a:A. P(a)` — supplied by the construct's definition (the
  library's admissibility predicates are defined nonempty) or by the
  mapping when it introduces the parameter; an empty admissibility set is
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
  `Context` and never coerced inside the core. A reading that commits to
  a precisification says so explicitly, with a library precisification
  constant or an exact value — and the commitment must itself pass the
  recovery test. Absence of commitment is `Vague`; absence of the
  dimension is nothing at all (§1.3); the two are never conflated.

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
Perform : Act<F> → Discourse
Do      : Discourse × Discourse × … → Discourse   (flattening, associative)
```

A document denotes one `Discourse`, whose top-level `Do` sequence is
called the **spine**; an `Act` written directly in a `Do` operand is
notation for its `Perform` (the coercion is notational, §2, never
semantic). `Do` sequences with the `∧`-row's accessibility. `Discourse`
never embeds where `Content` is required — in particular never under
`Reify`. Reported speech mentions constructed acts (`mi cusku lu ko klama
li'u` describes a directive without issuing it); only `Perform` executes.

### 7.2 Discourse structure

`(NewTopic d)` and `(Resume d)` are the `ni'o`/`no'i` transitions —
discourse-structural meaning with no truth conditions. Discourse
*relations* (contrast `ku'i`, addition `ji'a`, parallel `si'a`,
elaboration `no'u`, …) are library relations over acts; the prior act is
an ordinary `Let`-bound value in `Do` (no prior/following-discourse
constants exist). Constituent-level additive/exclusive focus (`ji'a` on a
sumti, `po'o`) derives via `Presuppose` over alternatives (§12).

### 7.3 Metalinguistic rejection

`na'i` is a derived discourse act: an objection targeting a prior
utterance or act, predicating a defect whose dimension is a `Context`
parameter (§6.1), with the objected content not performed. It is neither
`¬` (no truth-conditional negation occurs) nor `Scalar` (no scale is
invoked); the three-way `na`/`na'e`/`na'i` contrast is thereby three
different operators.

### 7.4 Utterance tokens

`(Utterance ((u UtteranceToken)) fact…)` binds a fresh utterance token
with its facts — ordinary predicates, assertable and embeddable:
`SpeakerOf`, `AudienceOf`, `LocutionOf`, `DeicticTimeOf`,
`DeicticPlaceOf`, `TextOf`, `Realizes` (token realizes act), `Utters`
(agent utters token). Token binding is reference introduction at the token
sort — the binder form exists for legibility, not as a new kind of
binding. Transcript entries (quoted utterances, §7.5) carry unperformed
acts.

### 7.5 Signs and quotation

`Sign<K>` classifies signs by kind `K` (Name, Sentence, Word, Letteral,
Quotation, MathExpression, Structured, Opaque, Text, Connective).
Constructors: `(OpaqueQuote text)` (`lo'u…le'u`, `zoi`),
`(StructuredQuote entry)` (`lu…li'u` — a transcript entry, unperformed),
`(NameSign text)`, `(SentenceSign content)`, `(LetteralSign text)`,
`(WordSign text)`. `(Sign ((s (SignToken K))) fact…)` binds sign tokens
with facts (`TextOf`, `Quotes`, `Denotes`). Interpretation is explicit and
typed: `(InterpretContent sign) : Content` and
`(InterpretAct sign) : Act<F>` (force-indexed; a sign does not carry its
force) — the `la'e` crossings; `lu'e` is the inverse sign-of crossing.
Quotation boundaries are opaque to dynamics (§5.4).

### 7.6 Indicators: attitudes, evidentials, discursives

Indicators (UI) are **lexical relations in the displayed-content family**,
not generated wrappers. Display has two spellings, by the level of its
target — no dedicated operator is needed:

- **Act-level** (the target is a performed act — the top-level case): the
  display is an `Express` act beside the host on the discourse spine,
  its content the indicator relation applied to the bound host act:
  `(Do (Perform $a) (Express (Close (i-rel Speaker $a degree))))`.
  Expressive force is itself non-at-issue commitment, and the family
  **force clause** holds: an evidential displayed this way *grounds* the
  host act — a mode of commitment, not a second claim — and a host-force
  profile (below) may subordinate the host instead of performing it.
- **Content-level** (the target is embedded content, a referent, or a
  sign): the display is a `Supplement` whose anchor is the target's
  first-order object — for content, its reification — and whose side is
  the indicator predication of that object. The content occurs **once**,
  under a pure `Reify` shared by `Let`, and is evaluated through the
  library's `Holds` (the model-theoretic inverse of `Reify`):

  ```lisp
  (Let (($p Proposition (Reify c)))
    (Supplement $p (Close (i-rel Speaker $p degree)) (Holds $p)))
  ```

  so anchor, side, and evaluated body all speak of the same content with
  the same contextual sites; the side projects per §5.5.

Targets are always bound terms or pure object-formers — never free
names. Each indicator's lexicon entry (§10) provides:

- its relation with typed roles — for attitudes: experiencer, first-class
  **target** (content, act, referent, or sign, resolved by the mapping),
  and a **degree** place on the library's intensity scale (`cai`/`sai`/
  bare/`ru'e`/`cu'i` select regions);
- its **`nai`-pair**: `nai` selects the lexically paired polar indicator
  (`.uinai` is unhappiness, a named emotion — not "other than happy"), and
  all other modifiers compose over the *pair* in surface order — `.uinai
  cai` is intense unhappiness (degree selects the pair's scale region),
  `dai` shifts the pair's experiencer, `cu'i` selects the neutral region
  of whatever relation it reaches. Where no pair is listed, the documented
  fallback composes `Scalar OtherThan` over the relation — weaker
  semantics (other-than-this-stance, naming no polar stance), so lexicon
  review prefers declaring pairs. Every grammatical `nai` attachment thus
  has a denotation, by pairing or fallback, exhaustively and exclusively.
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
  `ju'a`): the relation experiencer × target × basis-kind, with the family
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

## 8. Questions and answers

### 8.1 Query formation

`(Polar c) : Query<Bool>` (`Bool` the two-element answer type, §3.1);
`(OpenQ f) : Query<A>` for `f : EFn<(A…), Content>` — typed answer
domains, including tuples (`ma klama ma`), relation variables (`mo` — the
one-place row shown in samples is the common case; the general domain
quantifies over rows accepting the fill), place labels (`fi'a`, §4.7),
connectives and operators by domain enumeration, tags (`cu'e`), and
attitudes/bases (`pei`, `ju'apei`). `(Ask q)` makes the question act;
`(QuestionOf q) : Question` reifies a query as an embeddable object.
(Embedded question objects in Lojban conventionally carry `kau` — `lo
du'u ma kau cortu`; a bare-`ma` `du'u` is the question object without
answerhood, a deliberate extension noted here.)

### 8.2 Answers

`Answer : Query<A> × Selection<A> → Content` pairs a query with a
selection from its typed answer domain. The `Selection<A>` family:
`(PolarAnswer Yes|No) : Selection<Bool>` and
`(TupleAnswer tuple [Exhaustive|MentionSome]) : Selection<A>` are the
base forms; `ContextualAnswer` — the semantics of bare `kau` — is the
defined form making its contextual retrieval explicit:

```text
(Answer q ContextualAnswer) ≝
  (Bind ((a A (Context))) (Answer q (TupleAnswer a)))
```

(no exhaustivity marker: absence, per P9). `Answer` yields `Content` and
so embeds under `Reify` as any content does. **The exhaustivity operand is optional and its
absence is meaningful** (ruling P9): unmarked answerhood carries no
exhaustivity conjunct — truth-conditionally the weakest (mention-some-
compatible) reading — and strengthenings enter only by explicit marker or
lexically (an embedding predicate such as `djuno` may contribute its own
completeness presupposition through §5.5; it never rewrites the answer).
Lojban has no grammatical means to mark `kau` exhaustivity, so no `Vague`
parameter is posited: a decision point the language cannot express is
silence, not vagueness.

### 8.3 Place and relation questions

`fi'a` asks over `Label<ρ>` (§4.7); `mo` binds a `PredTerm`-typed
variable; both are ordinary `OpenQ` at their domains. No dedicated
question machinery exists beyond typed domains.

## 9. Abstractions

### 9.1 One primitive bridge

`(Reify c) : Proposition` is the single primitive content-to-object
crossing — `du'u`. A proposition is a first-order object standing in a
representation relation to the content's intension; it is what `djuno`,
`krici`, `cusku` embed, quantify over, and identify.

### 9.2 The abstraction relations

Every other abstractor is a **named abstraction relation with a labelled
row**, parameterized by the abstracted content — CLL's own shape: CLL
assigns these abstractors place structures (CLL ch. 11 §3 for the event
types, §5 for `ni`, §6 for `jei`, §9 for `li'i`/`si'o`/`su'u`):

```text
(NiRel c)   : PredTerm⟨ x1:Referents<Amount>,        x2:Referents<Scale> ⟩
(JeiRel c)  : PredTerm⟨ x1:Referents<TruthValue>,    x2:Referents<Epistemology> ⟩
(LihiRel c) : PredTerm⟨ x1:Referents<Experience>,    x2:Referents<Entity> ⟩  ; experiencer
(SihoRel c) : PredTerm⟨ x1:Referents<Concept>,       x2:Referents<Entity> ⟩  ; mind
(SuhuRel c) : PredTerm⟨ x1:Referents<AbstractNature>, x2:Referents<Entity> ⟩ ; category
(PuhuRel c) : PredTerm⟨ x1:Referents<Process>,   x2:Referents<Eventuality> ⟩ ; stages
(ZuhoRel c) : PredTerm⟨ x1:Referents<Activity>,  x2:Referents<Eventuality> ⟩ ; repeated actions
(DuhuRel c) : PredTerm⟨ x1:Referents<Proposition>, x2:Referents<Sign<Sentence>> ⟩
```

`DuhuRel` is derived (its x1 relates to `Reify c`, its x2 to a sentence
sign expressing `c` — CLL 11.7's x2 and `se du'u`); the others are the
family proper. Reference applies **outside** the relation, exactly as for
any selbri: `lo ni mi klama` is `Refer` over `λ($a : Referents<Amount>).
Close((NiRel …) $a)` — so the `lo`/`le` contrast, outer quantification,
and relative clauses all work on abstractions for free, and an omitted x2
is ordinary closure into `Context` (the `su'u` categorizer's contextual
default — CLL 11.9's "type x2" — is this general rule, not a special
one). Event abstraction (`nu` and its one-place sort refinements
`mu'e`/`za'i`) is `Refer` over a property of eventualities satisfying the
clause; `pu'u`/`zu'o`, having real x2s, live in the relation family
above, and `li'i` is its own abstractor (`LihiRel`), not an event
refinement. `ka` is not in this family: property abstraction is `λ`
(implicit `ce'u` pinned in P12). Sort discipline and no-coercion (P13)
are unchanged; adjacent-sort recastings are explicit named operators in
the library — including the **numeric crossings**

```text
AmountValue     : Referents<Amount> × Referents<Scale> → Number
TruthValueDegree: Referents<TruthValue> → Number      ; fuzzy jei ∈ [0,1]
```

(defined at the reference types `lo ni`/`lo jei` actually yield, with the
singular-reading condition their lexicon rows state; CLL 11.5: a `ni`
sumti is semantically a number, and `mo'e` maps to `AmountValue`, so
`li pa vu'u mo'e le ni …` type-checks; CLL 11.6 for fuzzy `jei`).

## 10. The lexicon interface

The core is parameterized over an external, curated lexicon. This chapter
fixes only the **schema** of lexical knowledge — what a dictionary entry
must provide for the core to interpret predications over it:

| Field | Content |
|---|---|
| row | the labelled, typed place row (§3.3), with the distinguished event place where licensed |
| defaultability | per place: whether closure (§4.6) may introduce a `Context` there; non-defaultable places must be filled or abstracted |
| scope policy | per place: extensional / intensional / opaque (§5.7) |
| plurality behavior | optional, per place: how the relation composes with plural arguments (distributive-capable, collective-leaning, neutral) — lexical knowledge, never a covert operator (§4.8) |
| deletions | which `DropPlace` deletions are meaningful, with the deleted role's semantic characterization (§4.3) |
| degree | optional: for gradable entries, the graded place label ℓ and degree projection `deg_R` consumed by `Grade` (§6.4) |
| kind admission | whether a place admits kind-like referents (ruling P3) |
| abstraction sorts | for places selecting abstractions: which sorts (§9), with drift cases adjudicated in the dictionary, not coerced |
| tag reductions | for tense/modal cmavo: the event-predicate expansion (`pu` → `purci(e, anchor)`, BAI → their gismu relations with the licensed host-event link), consumed by the mapping annex |
| indicator entries | for UI: relation, roles, degree place, `nai`-pair (with `Scalar OtherThan` fallback where unpaired), host-force profile, evidential basis-kind where applicable (§7.6) |

Two legislated entries (rulings carried into the lexicon): `gunma` and
`selcmi` take **plural x2** (components/members as a plural reference —
repairing CLL's self-referential `selcmi` gloss); the `le`-description
relation is a dedicated entry `DescribedBy⟨describer, described, audience,
property⟩`. (Official `skicu` x4 is itself a description property, so a
`skicu`-based lowering is expressively adequate; the dedicated entry is
chosen because `skicu` denotes a describing *event* — a `skicu`-based
`le` would need performative anchoring to the current utterance — and to
keep a closed-class meaning independent of an open-class dictionary
entry. See the rationale; the alternative is flagged at P10.) `voi`
uses the audience-deleted variant `(DropPlace DescribedBy 3) :
⟨describer, described, property⟩` restrictively — the deletion is
semantic (no audience role exists in a `voi` description), per pin P10.

## 11. Mapping annex: Lojban constructs to core terms

Normative lowering schemas, one line each; the cited pins carry the
arguments. Text-to-reading rules (marked ⊳) resolve before the calculus
and contribute no term constructors.

**Predication and places.** Bridi → lexical predication + `Close` at the
force boundary. FA/conversion → labelled fills / row routing (§4.2).
`zi'o` → `DropPlace`. `zo'e`/omission → per-site `Context` (P15). `fi'a` →
`OpenQ` over `Label<ρ>`. `co'e`/`do'e` → `Context` at relation/tag type.
⊳ `si`/`sa`/`su` erase before reading; quoted text preserves them.

**Descriptions** (P1, P10, P11). `lo P` → `(Refer P)`, veridical,
number-neutral. `le P` → `Refer` via `DescribedBy(Speaker, ·, Audience,
P)`, non-veridical, speaker-identifying. `la N` → `Refer` via naming
(`Named`/`NameSign`). `lo'e P`/`le'e P` → `Generic(Typical|Stereotypical,
[Speaker], P, ·)` at their predication (§5.8). `loi`/`lo'i` → `Refer` to
group/set objects via `gunma`/`selcmi` (P5), the base being the **maximal
plurality of the description** (`lo'i gerku` is the set of the dogs, not
of some dogs — the library's maximal-base form supplies it). Inner PA →
unit count of the selected base (`CardBasis`); outer PA → witness-set
selection / subreference selection (P1, §4.10). Inner `no` → the
zero-count schema, never `Refer` (special case, P22).

**Relative clauses.** `poi` → conjunct in the reference property; `noi` →
`Supplement` anchored at the referent (P7); `voi` → `DescribedBy`
restrictively; `goi` → discourse-scoped binding; `ke'a` → the property's
parameter. Outer `poi` after `ku` → restriction on the outer selection;
maximal-subreference readings are explicit library content, not defaults.

**Quantification and connectives** (P2, P17, P18). `ro` over descriptions
→ importing `Every` (`Presuppose` nonemptiness + `∀`); bare `ro da` → `∀`.
PA-quantifiers → library cardinal GQs over a counting basis. Termsets
(`ce'e`, `nu'i`) → co-selected witness sets at one joint locus with the
full product; no coordinate maximality (the coordinate-closed profile is a
named strengthening). Logical connectives → `¬ ∧ ∨ → ↔ ⊕` with surface
grammar fixing structure; `na` ≡ left-edge `naku`; `naku` movement flips
quantifiers per CLL ch. 16. Non-logical: `jo'u` → `Combine`; `ce` → set;
`ce'o` → list; `fa'u` → `ZipWith`; `joi` **by syntactic position** —
sumti `joi` → group formation with `Vague` mixture kind; tag/facet
joining → `∧`; discourse joining → `Do`; residual genuinely-unspecified
connection → `Vague` over the connecting relation; `ku'a`/`jo'e`/`pi'u`
→ `∩`/`∪`/`×`.

**Events, tense, modals** (P8, P24). Each bridi introduces its event
existentially unless shared explicitly. Tense/aspect/spatial cmavo and BAI
→ event-predicate conjuncts per the lexicon's tag reductions, joined by
`∧` at the tag locus; tense chains (`pu pu`) compose as anchor paths.
Tenseless bridi → no temporal conjunct. ⊳ `ki` stickiness propagates
resolved tense by source order. CAhA: `ka'e` → the library's capability
schema; `ca'a` → `fasnu` actuality conjunct. ZAhO → boundary relations per
lexicon rows (gap-registered until filled). `fi'o P` → `P` as tag with the
lexicon's host-event link.

**Anaphora** (P16). ⊳ `ri`/`ra`/`ru` by CLL ch. 7 counting over accessible
referents (§5.6); `vo'a`-series → bridi-place bindings; KOhA assigned →
bound variable; unassigned → keyed `Context`; ⊳ `go'i`-family → expansion
with the antecedent's resolved context; `ra'o` → re-resolution under
`InContext`/`ShiftedGround` (§5.1).

**Abstractions** (§9, P13, P14). `du'u` → `Reify`; `nu` + sorts → `Refer`
over event properties; `ka` → `λ` (⊳ implicit `ce'u` at first unfilled
place, counting converted places; P12); `ni`/`jei`/`li'i`/`si'o`/`su'u`/`pu'u`/`zu'o` →
the abstraction relations with reference outside; `mo'e` → the
`AmountValue` numeric crossing; `tu'a X` → `Vague` abstraction
constrained by shape + `srana`-aboutness, **sort selected by the host
place** (an event place gets an event-sorted abstraction); tagged `jai` →
explicit role promotion (library expansion over the host row); bare
`jai` → `Vague` involvement (§6.1); `la'e`/`lu'e` → interpretation /
sign-of crossings.

**Questions and answers** (§8, P9). `xu` → `Polar`; `ma`/`mo`/`fi'a`/
`xo`/`ji`/`cu'e`/`pei` → `OpenQ` at their typed domains; `kau` →
`ContextualAnswer` with absent exhaustivity; `go'i` as answer → `Answer`
with polar selection.

**Indicators and discourse** (§7, P19). ⊳ UI target selection by
grammatical attachment (FUhE/FUhO extend); UI → displayed-content
relations per lexicon entries with host-force profiles; evidentials →
the family force clause; `dai` → experiencer shift; `nai` → lexical pair;
degree words → intensity regions. `.i` sequencing → `Do`; `ni'o`/`no'i` →
`NewTopic`/`Resume`; discursives → library discourse relations; `po'o`,
constituent `ji'a` → focus derivations; COI → performative expressive
acts; `mi'e` → performative self-naming; `na'i` → the objection act
(§7.3).

**Quotation, signs, MEX** (§7.5, §4.9). `lu…li'u` → `StructuredQuote`;
`lo'u…le'u`/`zoi` → `OpaqueQuote`; `zo` → `WordSign`; letterals →
`LetteralSign` (⊳ letteral anaphora keys bindings); `me'o` → mention of a
math-expression sign; `li` → the value; `du` → `=`; operators → typed
functions; `xi` subscripts → application.

## 12. Library

Normative derived forms, **defined in the core language**; each
definition is its specification (Eberban's from-scratch discipline).
Metalanguage recursion (over `Natural`, over list structure) is permitted
in definitions; the term language itself has no recursion former (§4.4).
Schematic variables: `P, Q` properties; `r` plural references; `n`
naturals; `ρ` rows.

**Cardinal and logical quantifiers** (witness-set semantics, §4.10;
export status per §5.6):

```text
(Exactly n P Q)  ≝ (Bind ((w (SelectExactly n P))) (Distrib Q w))
(AtLeast n P Q)  ≝ (Bind ((w (SelectAtLeast n P))) (Distrib Q w))
(Some P Q)       ≝ (Bind ((w (SelectSome P)))      (Distrib Q w))
(Every P Q)      ≝ (Presuppose (∃ P)            ; import emitted FIRST —
                     (Bind ((w (MaxRefer P)))    ; else an empty restrictor
                       (Distrib Q w)))          ; would fail the selection
                                                ; instead of failing the
                                                ; presupposition; exports w
(No P Q)         ≝ (¬ (Some P Q))                          ; no export
(AtMost n P Q)   ≝ (¬ (AtLeast n+1 P Q))                   ; no export
(MoreThan n P Q) ≝ (AtLeast n+1 P Q)
(FewerThan n P Q)≝ (AtMost n−1 P Q)
(GlobalExactly n P Q) ≝ (= (Card (SetOf (λ x. (∧ (P x) (Q x))))) n)
(Distrib Q r)    ≝ (∀ (λ x. (→ (Among x r) (Q x))))
```

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
standard where marked):

```text
(Many P Q)   ≝ (Bind ((θ Natural (Vague (AdmissibleThreshold Many P))))
                 (AtLeast θ P Q))
(Few P Q)    ≝ (Bind ((θ Natural (Vague (AdmissibleThreshold Few P))))
                 (FewerThan θ P Q))
(Most P Q)   ≝ (> (Card (SetOf (λ x. (∧ (P x) (Q x)))))
                  (Card (SetOf (λ x. (∧ (P x) (¬ (Q x)))))))
(TooMany P Q)≝ (Bind ((σ (Referents Entity) (Context))          ; purpose
                      (θ Natural (Vague (AdmissibleThreshold TooMany P σ))))
                 (MoreThan θ P Q))
(TooFew P Q) ≝ (Bind ((σ (Referents Entity) (Context))
                      (θ Natural (Vague (AdmissibleThreshold TooFew P σ))))
                 (FewerThan θ P Q))
(Enough P Q) ≝ (Bind ((σ (Referents Entity) (Context))
                      (θ Natural (Vague (AdmissibleThreshold Enough P σ))))
                 (AtLeast θ P Q))
```

Gradable predication: a `GradableRel<ρ,ℓ>` is a lexical relation whose
entry's **degree field** (§10) declares its graded place `ℓ : Label<ρ>`
and a degree projection

```text
deg_R    : Referents<T_ℓ> × Scale → Amount     (T_ℓ the type at place ℓ)
InRegion : Amount × Region<Scale> → Content
```

(`Region<Scale>` — poles, midpoints, intervals — declared here for the
whole document). Then

```text
(Grade R s reg) : PredTerm<ρ> ≝
  (λ (r : Record ρ). (InRegion (deg_R r.ℓ s) reg))
```

— the relation holding of a row record exactly when its ℓ-field's degree
on scale `s` lies in region `reg`. No `…` remains in this chapter.

**Plurality and collections:** `UnitSet`/`CardBasis` (§4.8); `lu'a r` ≝
distribution over members (`Distrib` at the use site); maximal base
`(MaxRefer P)` ≝ the reference of *all* P-satisfiers (the `lo'i`/`loi`
base: `Refer` constrained so every P-satisfier is `Among` it);
`(Interval a b k₁ k₂)` ≝ `(SetOf (λ x. (∧ (cmp₁ a x) (cmp₂ x b))))` with
`cmpᵢ` strict/nonstrict per the `ga'o`/`ke'i` endpoint kinds. Reciprocals:

```text
(simxu r P) ≝ (∀ (λ (x y). (→ (∧ (Among x r) (Among y r) (¬ co-ref(x,y)))
                              (P x y))))       ; soi likewise, pairwise
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
(ZipWith (λ (($s (Referents Entity)) ($l (Referents Entity)))
           (Close (tavla $s $l)))
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
  (Refer (λ (r. (∧ (Distrib P r)
                   (∀ (λ x. (→ (P x) (Among x r))))))))
                ; the P-satisfying reference every P-satisfier is Among —
                ; the maximal base (lo'i/loi, Every's export)
(Holds p)       : Content — the content the proposition object p
                  represents (the model-theoretic inverse of Reify;
                  evaluating Holds(Reify c) is evaluating c)
```

**Events and tags:** the adjacent-sort crossings of P13 —
`EventOfContent : Content → Referents<Eventuality>` (the eventuality of a
clause, used by `tu'a`'s shape conjunct and `nu`-recasting) and its named
kin; tense helpers per the lexicon's tag-reduction rows;
`(MotionVector e mover dir)` ≝ the heading-reduced `muvdu` projection
with `farna` direction; the capability schema `(InnatelyCapable b P)` ≝
`jinzi`-grounded possibility of `P`-events with bearer `b` (evaluated at
capability worlds, §5.1); `(nu'o b P)` ≝ `(∧ (InnatelyCapable b P)
(¬ (Realized b P)))` and `(pu'i b P)` ≝ `(∧ (InnatelyCapable b P)
(Realized b P))`, where `(Realized b P)` ≝ an actual `P`-event of `b`
(`∃e. ∧ (P-event b e) (fasnu e)`). Tagged `jai`: for a lexical row ρ with
event place and promoted role ℓ,

```text
(JaiPromote R ℓ) : PredTerm<ρ[ℓ→x1]> ≝
  (λ (x, remaining-fills…).
    (∃ (λ e. (R remaining-fills… :ℓ x :Eventuality e))))
```

per the lexicon's promotion row; bare `jai` per §6.1.

**Acts and discourse:** discourse relations `Contrast`, `Addition`,
`Parallel`, `Elaboration` — lexical relations over two act values,
displayed act-level per §7.6; the `na'i` objection ≝

```lisp
(NahiObjection t) ≝
  (Bind ((d DefectKind (Context)))
    (Express (Close (MetalinguisticallyDefective t d))))
```

for a bound prior target `t` (`DefectKind` — wording, form, implication,
presupposition, register — is declared with the objection relation); COI
schemas ≝ performative `Express` of the COI lexical relation
(`coi-greeting`, `ki'e-thanks`, …); `(Ground b a)` ≝ the act-level
evidential spelling of §7.6 applied to act `a` with basis `b`; focus for
a host `H[·]` with focused constituent `f`:
`(Only f H) ≝ (Presuppose H[f] (¬ (∃ (λ y. (∧ (¬ (CoRef y f)) H[y])))))`
(`po'o`), and `(Additive f H) ≝ (Presuppose (∃ (λ y. (∧ (¬ (CoRef y f))
H[y]))) H[f])` (constituent `ji'a`).

**MEX:** `te'a` (integer exponentiation) and `gei` (`gei x y` ≝
`y × 10^x`) by metalanguage recursion over `Natural`; subscript `xi` ≝
list/sequence indexing; operators are functions and `me'o` mentions their
expression signs (§7.5); `AmountValue` per §9.2.

**Tanru links:** named precisification constants — `MannerLink`,
`MaterialLink`, `PurposeLink`, `SourceLink`, `InstrumentLink`,
`ResemblanceLink`, … — each a relation of the head row asserting the
modifier's specific bearing; usable wherever a resolved reading commits
(§6.2), each satisfying `TanruAdmissible` by construction.

## 13. Pin annex

Numbered rulings resolving accidental underspecification; each cites its
evidence, its cost, and its full argument in the rationale. (Deliberate
vagueness is never pinned; it is classified in §6.1.)

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
- **P5** `loi`/`lo'i` denote group/set objects via `gunma`/`selcmi` with
  plural x2 (legislated); inner PA = group/set size, outer PA counts
  groups/sets.
- **P6** Donkey configurations normalize to joint multi-parameter loci;
  dynamic accessibility includes restrictor introductions; CLL 7.6
  counting is the mapping discipline over accessible referents.
- **P7** `noi` is projective supplement, anchored; dependent supplements
  commit per instantiation inside their binder.
- **P8** Tenseless bridi carry no temporal predication; `ki` is
  text-to-reading stickiness.
- **P9** Bare `kau`: answerhood with exhaustivity **absent** — weakest
  truth conditions; strengthenings lexical/pragmatic/explicit. (Absence,
  not `Vague`: Lojban has no grammatical precisification route.)
- **P10** `le` via the dedicated `DescribedBy` relation — speaker-indexed,
  non-veridical, number-neutral; `voi` restrictive variant. *(Flagged
  for review: the once-claimed `skicu` x4 place-misuse was false —
  official x4 is a description property — so the dedicated relation
  stands only on act-vs-identification and definitional-ownership
  grounds, and a performatively anchored `skicu`-based analysis is a
  live alternative; §10, rationale §2.6.)*
- **P11** `lo'e`/`le'e` via the axiomatic `Generic` operator (mode +
  holder); no fixed prototype reference.
- **P12** Implicit `ce'u`: exactly one, first unfilled place, counting
  converted places; multiple candidates are distinct readings.
- **P13** No implicit coercions among abstraction sorts; named explicit
  crossings; dictionary adjudicates sort drift.
- **P14** `tu'a` = `Vague` abstraction (shape conjunct + `srana`
  aboutness, host-place sort); `co'e`/`do'e` = `Context` at their types.
- **P15** `zo'e` ≡ omission; distinct sites distinct; `zu'i` adds
  typicality.
- **P16** Anaphora resolution is text-to-reading; calculus sees bindings;
  `goi` discourse-scoped; unassigned KOhA = keyed `Context` (one value per
  key — `ko'a du ko'a` is reflexively true).
- **P17** Termsets: co-selected witness sets, full product, **no
  maximality** — CLL ch. 16 §7's own gloss of `ci gerku ce'e re nanmu cu
  batci` (its examples 16.42–16.45, print numbering) is two picked groups
  with every dog biting each man, and says nothing stronger; the
  coordinate-closed profile is a named strengthening; referential members
  need no termset semantics at all. The bare-PA half is a **documented
  divergence from CLL's letter**: ch. 16 §6 glosses bare numeric
  quantification globally ("exactly two, no more or less"), and this
  specification pins witness-set exactness instead (§4.10) — the
  xorlo-era reading that composes with witness export and termsets — with
  the CLL-literal reading available as `GlobalExactly`.
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
  `(No (λx. broda x) (λx. R[x]))`, guskant's unofficial
  `naku su'oi da poi ke'a broda` relativized to the frame ("gadri: an
  unofficial commentary from a logical point of view", the "Cannot say
  zero" section). This is what makes answer substitution work: `lo xo
  prenu cu jmaji …` answered by `no` is elliptical `lo no prenu cu
  jmaji …`, and `go'i`-inherited frames likewise. Anaphora to an
  inner-`no` description is inaccessible (`No` exports nothing) — there
  is nothing to refer to. `no lo broda` remains the fully explicit outer
  form. *(Amended after review on the owner-raised guskant argument;
  the earlier ruling made the form defective outright.)*
- **P23** `ba'e` = sign-level focus; `du` = `=`.
- **P24** Fresh event per bridi unless shared explicitly; ZAhO pinned as
  boundary-relation shape, contours filled lexically.

## 14. Gap register

Meanings this specification currently assigns no analysis, each with the
reason; a gap is an obligation on future revisions, never a license to
approximate:

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
- **ZAhO contours** pending their lexicon rows (P24); habituals (TAhE)
  likewise.
- **Exotic donkey configurations**: anaphora out of disjunctive
  restrictors; stacked indefinites with split anaphora (§5.6).
- **Termset witness export** (joint anaphora to termset selections) and
  mixed-quantifier termsets where no coherent product reading exists
  (P17).
- **MEX beyond the library fragment**: non-decimal bases, arrays,
  indefinite operators.
- **Prosody and stress** as meaning carriers; conversational repair as
  reportable structure beyond quotation.

## 15. Adequacy

The coverage claim of this specification: every meaning expressible by a
Lojban utterance under a resolved reading either (a) denotes a core term
by the schemas of §11, (b) is a library form of §12, or (c) appears in
the gap register §14 with its reason. The coverage matrix:

| Construct family | Schema | Library | Gap | Samples |
|---|---|---|---|---|
| predication, places, `zi'o`, conversion | §11 ¶1 | — | — | §1 |
| tense/aspect/space, BAI, CAhA | §11 ¶4 | tag helpers, `MotionVector`, capability, `nu'o`/`pu'i` | ZAhO contours, TAhE | §2 |
| gadri, descriptions, `lo'e`/`le'e` | §11 ¶2 | `Named`, `MaxRefer`, `Generic` at §5.8 | generic anaphora | §3 |
| relative clauses, `goi`, `voi` | §11 ¶3 | `DescribedBy` variants | — | §4 |
| quantifiers, termsets, negation scope | §11 ¶4 | GQ family, `GlobalExactly`, `Distrib` | mixed termsets, termset export | §5 |
| vague quantities, gradables | §6.4 | degree GQs, `Grade` | — | §5, §8 |
| anaphora, KOhA, `ra'o` | §11 ¶5 | — | exotic donkeys | §4, §5 |
| abstractions, `tu'a`, `jai`, `mo'e` | §11 ¶6 | abstraction relations, `AmountValue`, `JaiPromote` | — | §8, §9 |
| questions, answers, `kau` | §11 ¶7 | domain-enumeration schemas | — | §6 |
| indicators, evidentials, discursives, COI, `na'i` | §11 ¶8 | discourse relations, focus, objection, COI schemas | — | §7 |
| quotation, signs, letterals | §11 ¶9 | sign constructors | — | §10 |
| MEX | §11 ¶9 | `te'a`, `gei`, indexing, `Interval` | bases, arrays, indefinite operators | §10 |
| plurality, masses, reciprocals | §4.8, §11 ¶2 | `lu'a`, covers, `simxu`/`soi` | — | §3, §5 |
| hypothetical mood | — | — | `da'i` | §12 |
| repair, prosody | §11 ⊳ | — | registered | §12 |

A claim of coverage that cannot cite a schema, a library definition, or a
gap entry is a defect in this document.

### Appendix: the kernel

The primitive inventory, for reference (everything else is library or
lexicon): the type formers of §3; `λ`, application, `Let`, `Bind`;
lexical predication with labelled fills; `DropPlace`; `¬ ∧ ∨ → ↔ ⊕ ∀ ∃
=`; `Combine`, `Among`, `SetOf`, `Card`, `∈`, the arithmetic base;
`Refer`, `Context`, `Vague`, the `Select` family; `Presuppose`,
`Supplement` (display is its §7.6 spelling); `Generic`; `Reify`;
`Tanru`, `Scalar`; the
force constructors, `Perform`, `Do`, `NewTopic`, `Resume`; token and
sign binders with the fact vocabulary, the sign constructors,
`InterpretContent`/`InterpretAct`; the deictic projections, `Deictic`,
`ShiftedGround`, `InContext`; `Polar`, `OpenQ`, `Answer` with its
selection values; `Close` and `At` are normatively defined forms (§4.6,
§4.7) and the library defines the rest.
