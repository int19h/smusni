# Catalog of the core forms

One entry per named identifier of [the specification](spec.md), in two
sections. **Primitives** are the names with no term-language expansion:
their entire definition is the prose and axioms the spec gives them,
restated here. **Defined forms** are everything else — each expands, by
its `≝`, into primitives and other defined forms, and the expansion is
its specification. Every entry gives the informal definition first
(even where a formal one exists), then the formal definition if there
is one, then what the form is for with an example of use, then where
the details live ([spec](spec.md) by section, [primer](primer.md) by
chapter, [rationale](rationale.md) where the shape is argued).

Tightly coupled families (the force constructors, the sign
constructors, the abstraction relations, the cardinal quantifiers)
share one subsection with per-name coverage inside it, so that their
common story is told once.

Section numbers 1.47–1.49 and 2.28 are retired. They belonged to the
withdrawn staged-reflection design; later numbers are deliberately left
unchanged so existing cross-references remain stable. The design history
is recorded in rationale §2.9 and the review archive.

The scope is the **term language**: model-theory symbols
(`Comp`, `InformationState`, `Obligations`, `Unit`, the `ctx` record,
the world set W) are not forms and live in the short appendix at the
end. Two notational facts are catalogued here once rather than per
entry:
multi-place fill notation (positional fills, `:n` labels, FA routing,
`se`-conversion) desugars to nested single-place `At` (spec §4.1); and
a specimen displayed as a bare act denotes the one-act discourse
performing it (spec §7.1).

## 1. Primitives

### 1.1 The sort hierarchy

**Informally.** First-order individuals are sorted: `Entity` at the
top; beneath it `Eventuality` (with subsorts `Achievement`, `Process`,
`Activity`, `State`, `Experience`, and `Locution`, an uttering event),
`Location`, `Time`, `Amount`, `Scale`, `Epistemology`, `TruthValue`,
`Concept`, `AbstractNature`, `Proposition`, `Question`, `Number` (with
`Natural` and `Cardinal` beneath it), `Text`, the collection and sign
sorts of the entries below, `UtteranceToken`, and `Ground`. Subsorting
is subset inclusion; a subsort term stands wherever the supersort is
required, never conversely; there are no implicit crossings between
sorts (pin P13).
**For.** Lexical selection — `fasnu` selects an `Eventuality` where
`barda` selects an `Amount`-bearer — and the no-coercion discipline:
swapping a `du'u` for a `ni` is ill-typed, not false.
**See.** [Spec §3.1](spec.md); [primer ch. 8](primer.md).

### 1.2 `Referents<T>` — the plural reference type

**Informally.** Nonempty, number-neutral pluralities of `T`s: one or
more things *referred to together*, which are not a set-object, not a
mereological sum, and not a group — no object exists over and above
the things. There is no empty plural reference; a single `T` lifts to
a singleton reference at referential positions. Covariant in `T`.
**For.** The type of every ordinary lexical argument place. `mi jo'u
do bevri lo pipno` — a plurality carries; no set carries anything.
**See.** [Spec §3.2, §4.8](spec.md); [primer ch. 3](primer.md);
[rationale §1.7, §2.8](rationale.md).

### 1.3 `Set<T>`, `Group<T>`, `List<T>` — collection object types

**Informally.** First-order *objects* that package other things: a set
(extensional, with membership and cardinality and possibly empty), a
group (a concrete collective with its own properties — a crowd can
surround a building), a list (order-bearing). Distinct from plural
reference: none unwraps implicitly to its members.
**For.** `lo'i gerku` denotes a `Set<Entity>`; `loi prenu` a group via
`gunma`; `ce'o` builds lists. The two-sort split (reference vs object)
is what makes `lo selcmi cu simxu` unambiguous.
**See.** [Spec §4.9](spec.md); [primer ch. 3](primer.md) ("Not the
same as!"); [rationale §2.8](rationale.md).

### 1.4 `Fn` and `EFn` — the function types

**Informally.** `Fn<(A…), B>` is the pure function type: a body that
performs no dynamic effects when its result is evaluated — no
introductions, no contextual retrievals, no projective emissions.
`EFn` is the effectful arrow. Purity is demanded exactly at set
comprehension, quantifier and `Generic` restrictors, and selection
restrictors; nuclear scopes are `EFn`.
**For.** Properties are `Fn<(T), Content>`; `ka` abstractions are λs
at these types. A restrictor that smuggles a `Refer` simply fails to
have the pure type — the purity discipline is a typing fact, not an
algorithm.
**See.** [Spec §3.3](spec.md); [rationale §1.14](rationale.md) (the
pure/effectful seam).

### 1.5 `Record ρ` and `Label<ρ>` — rows

**Informally.** A place row ρ is a finite sequence of labelled, typed
places; `Record ρ` is the type of complete fills for it; `Label<ρ>` is
the finite type of its place labels. Labels are semantically real:
Lojban reorders, deletes, and *asks about* places by label.
**For.** `klama fi'a ti` is a question over the compatible-label
refinement of `Label<ρ(klama)>` (spec §4.7 — sort-incompatible places
and the event place contribute no branch); the
fill notation computes labels (spec §4.1). `PredTerm<ρ>` (defined
section) is the row-function alias over these. (`Record` and `Label`
are type constructors of the record theory, not first-order sorts —
they do not appear in §3.1's hierarchy.)
**See.** [Spec §3.3, §4.7](spec.md); [rationale §1.1](rationale.md).

### 1.6 `Content` — dynamic propositional content

**Informally.** The type of what can be asserted, questioned, negated,
and embedded. Its denotation is a world-indexed context-change
potential: run against an information state, it filters and extends
that state and accumulates projective obligations. No world variable
ever appears in a term.
**For.** Every bridi's meaning lands here before force applies.
**See.** [Spec §3.4, §5.1](spec.md); [primer ch. 1, ch. 4](primer.md).

### 1.7 `RefComp<T>` — reference computations

**Informally.** Computations that return a `T` while possibly
performing dynamic effects: introducing referents (`Refer`,
selections), consulting context (`Context`), or denoting
precisification families (`Vague`). Consumed by `Bind`.
**For.** The type of every description and selection before its
witness is bound.
**See.** [Spec §3.4, §5.2–5.3](spec.md).

### 1.8 `Act<F>` and `Discourse` — speech-act types

**Informally.** An `Act<F>` value is a force-tagged content package —
force `F` (Assertion, Question, Directive, Expressive, Address) plus
the content computation — built inertly: constructing an act runs
nothing. An act is a pure value, not a computation — only `Perform`
(§1.36) injects it into the dynamic carrier. `Discourse` is performed
discourse: sequences of performed
acts and transitions. A document denotes one `Discourse`.
**For.** Quotation and report: `mi cusku lu ko klama li'u` mentions a
directive without issuing it, because only `Perform` executes.
**See.** [Spec §3.4, §7.1](spec.md); [primer ch. 6](primer.md);
[rationale §1.11](rationale.md).

### 1.9 `Query<A>`, `Selection<A>`, `Bool` — question types

**Informally.** A `Query<A>` is a question with typed answer domain
`A`, denoting its answer-content function; a `Selection<A>` picks from
that domain; `Bool` is the two-element polar answer type (distinct
from the epistemology-relative `TruthValue` sort).
**For.** `xu`, `ma`, `mo`, `fi'a`, `pei` all land in `Query` at
different domains; `kau` supplies the contextual answer selection
inside `Answer` (a `Proposition` results), while `QuestionOf` reifies
a query as a `Question` object for question-object-selecting places.
**See.** [Spec §8](spec.md); [primer ch. 6](primer.md).

### 1.10 `Sign<K>`, `SignToken<K>`, `UtteranceToken` — sign types

**Informally.** Signs are quoted or mentioned linguistic material,
classified by kind `K` (Name, Sentence, Word, Letteral, Quotation,
MathExpression, Structured, Opaque, Text, and Connective);
sign tokens and utterance tokens are the concrete occurrences facts
attach to. Sign boundaries are opaque: no referent, presupposition, or
introduction crosses them.
**For.** Use/mention discipline — the reason Lojban can talk about
Lojban without paradox.
**See.** [Spec §7.4–7.5](spec.md); [primer ch. 10](primer.md).

### 1.11 `Ground`, `GroundDescription`, `Proximity` — deictic ground types

**Informally.** A ground is an orientation center with its perspective
facts — what demonstratives point against; `Proximity` is the closed
three-value type `Proximal | Medial | Distal`; ground descriptions are
the specifications grounds are constructed from.
**For.** `ti`/`ta`/`tu` and `ra'o`-style re-orientation.
**See.** [Spec §5.1](spec.md).

### 1.12 `Region<Scale>` — scale regions

**Informally.** Regions of a scale — poles, midpoints, intervals — the
values gradable cutoffs and scalar operators work over.
**For.** `Grade`'s vague cutoff and the `na'e`/`to'e`/`no'e` regions.
**See.** [Spec §6.3–6.4, §12](spec.md).

### 1.13 The pure function substrate

**Informally.** Typed functions over labelled-record-aware parameters,
with juxtaposition as application — the pure functional substrate:
function types, application, and the laws (β-reduction, substitution,
α-conversion are unconditionally meaning-preserving here, which is
exactly what the effectful fragment must not silently inherit — see
`bind`). `λ` is the direct binding form: its telescope introduces
typed parameters and its brace-delimited body fixes their scope. The
braces are punctuation, not quoted signs.
**Content-word status.** Class M structural machinery: no Lojban word is
owed merely to rename function formation.
**For.** Properties (`ka` with `ce'u` = λ, pin P12), quantifier
bodies, everything higher-order.
**Example.** `lo ka se klama` →
`(λ {$x :: Referents Entity} {(Close (klama :2 $x))})`.
**See.** [Spec §4.4](spec.md); [primer ch. 8](primer.md).

### 1.14 `bind` (and the `Bind` word)

**Informally.** The computation carrier's sequencing operation
`bind : Comp<A> × (A → Comp<B>) → Comp<B>`: run the computation once,
sequencing its effects before the continuation, and pass its *result*
— never the computation. It is function application under mandatory
call-by-value at computation types, made visible: the pure λ-fragment
keeps unconditional β-equality, and every effect-sequencing point is a
`bind` node the accessibility table can name. Uniform across the
computation categories: the continuation may yield content, a
reference computation, or a discourse (a bare act body stands for its
performing one-act discourse — spec §7.1's display coercion), so a
referent introduced before an act sequence stays bound across it. The
surface form `(Bind {$x :: T} comp {body})` is a direct effectful binder;
its denotation applies carrier `bind` to `comp` and the scoped body
continuation.
**Content-word status.** Both carrier `bind` and the direct `Bind` form
are Class M structural machinery. A predicate may describe a binding or
its result, but does not sequence the computation.
**For.** Cross-sentence reference: `(Bind {$cat :: Referents Entity}
(Refer mlatu-prop) {(Do (Assert …) (Assert …))})` — the
introduction runs once, the witness is reused in both acts.
Multi-binding `Bind` is left-to-right nesting (spec §5.2).
**See.** [Spec §5.2](spec.md); [primer ch. 4](primer.md);
[rationale §1.14, §2.4](rationale.md) (why not λ; why not CPS; the
statics/dynamics seam).

### 1.15 Lexical predication

**Informally.** Dictionary words (`klama`, `gerku`, …) are relation
constants over their labelled rows, with the row, defaultability,
scope policy, plurality behavior, meaningful deletions, and the rest
supplied by the lexicon interface. The core is parameterized over the
lexicon; a predication applied to fills for its row is `Content`.
**For.** Every bridi. `(Close (klama Speaker This))` — the remaining
places handled explicitly by `Close`'s contextual slots (or by λ or
`DropPlace`), never silently.
**See.** [Spec §4.1, §10](spec.md); [primer ch. 1](primer.md);
[rationale §2.6](rationale.md).

### 1.16 `DropPlace`

**Informally.** `(DropPlace R n)` is the relation with place `n`
*removed* — semantic surgery, not omission: the resulting relation has
no such role at all. Which deletions are meaningful, and what the
deleted role's absence means, is stated per entry in the lexicon.
**For.** `zi'o`. `mi klama ti zi'o` predicates a four-place going with
no origin role — something neither `zo'e` nor closure can say. Also
`voi` = `(DropPlace skicu 3)` (no audience role).
**See.** [Spec §4.3](spec.md); [primer ch. 1](primer.md) ("Not the
same as!"); [rationale §1.8](rationale.md).

### 1.17 `¬`, `∧`, `∨`, `→` — the dynamic connectives

**Informally.** Classical truth conditions plus a normative
accessibility row each: `∧` passes introductions left to right and
lets both survive; `∨` keeps them branch-local; `¬` lets nothing
escape; `→` feeds the antecedent's introductions to the consequent and
exports nothing. The rows are part of the meaning. (`⊤` — the
trivially true content, `∧`'s unit, spec §2 — is the defined empty
conjunction, not a further primitive.)
**For.** `ganai da mlatu gi da ciska` (donkey feeding), `.ija`
(branch-local), `naku` (blocking) — three policies no truth table
derives.
**See.** [Spec §4.5, §5.4](spec.md); [primer ch. 4](primer.md);
[rationale §1.5](rationale.md).

### 1.18 `↔`, `⊕` — biconditional and exclusive-or

**Informally.** Once-per-operand evaluation of two truth-functional
shapes, with nothing escaping. Primitive precisely because their
classical rewrites duplicate operand text — two `Context` sites,
doubled supplement handlers, reshaped accessibility — and no sharing
route exists in a calculus that (deliberately) lacks truth-capture
reflection.
**See.** [Spec §4.5, §5.4](spec.md); [rationale §1.5](rationale.md).

### 1.19 `∀`, `∃` — the logical quantifiers

**Informally.** Classical quantifiers over typed λ-bodies with
(multi-parameter) joint loci; restrictorless, domain-unrestricted
(`da` — pin P20). The restrictor position of derived quantifiers is
pure; body introductions are local per instantiation; exporting
quantifiers are built from selections, not from bare `∃`.
**For.** `ro da zo'u …` and the joint loci of donkey normalization.
**See.** [Spec §4.5, §5.6](spec.md); [primer ch. 4–5](primer.md).

### 1.20 `=` — typed equality

**Informally.** Primitive identity at every first-order sort and at the
discrete index types (`Bool`, place labels, the closed
enumerations); never at the plural reference type, where co-reference
(`CoRef`, mutual `Among`) does the work; plural-sumti `du` lowers to
`CoRef` (P23).
**For.** `li re su'i re du li vo`; `ko'a du ko'a` reflexively true
under keyed retrieval (pin P16) — at `CoRef` when the referents are
plural.
**See.** [Spec §4.5, §4.8](spec.md).

### 1.21 `Combine`

**Informally.** Plural join: the reference to these-and-those
together. Associative, commutative, idempotent. With `Among` it is the
whole plural algebra: no atomicity, no covers, no distributivity
assumptions.
**For.** `jo'u`. `mi jo'u do` = `(Combine Speaker Audience)`.
**See.** [Spec §4.8](spec.md); [primer ch. 3](primer.md);
[rationale §1.7](rationale.md).

### 1.22 `Among`

**Informally.** The subreference order: these are some of those.
Axiomatized with `Combine` (`Among x y` iff `Combine x y` and `y`
co-refer). Singulars lift to singleton references, so `Among x r` with
`x` a unit reads "x is one of r".
**For.** `me`-style membership talk, `Distrib`, subreference selection
(`re lo mu plise`), and the subreference-monotonicity criterion of the
lexicon's plurality field.
**See.** [Spec §4.8, §10](spec.md); [rationale §1.7, §2.8](rationale.md).

### 1.23 `SetOf`, `Card`, `∈`, and the arithmetic base

**Informally.** Extensional set comprehension over a *pure* property;
membership; cardinality (`Card : Set<T> → Cardinal`); and the number
operators `+ − × ÷ < ≤` (with `>`/`≥` defined), partial operations
carrying projective definedness conditions.
**For.** Mathematics (`li`, `mekso`), the global readings
(`GlobalExactly`, `Most`), and `UnitSet`-based counting.
**See.** [Spec §4.9](spec.md); [primer ch. 5](primer.md).

### 1.24 `Refer`

**Informally.** Introduce a **new discourse referent**: a nonempty
plurality satisfying the given property veridically, fixed for its
force segment, accessible to later anaphora per the table. No implicit
quantifier, no uniqueness, no default cardinality (xorlo, pin P1).
Embedded under a quantifier it stays a referential constant — it does
not covary (that is the selections' job).
**For.** `lo`/`le`/`la` descriptions. `lo mlatu cu blabi .i ri jbena` —
the cat outlives its sentence and survives negation.
**See.** [Spec §5.3](spec.md); [primer ch. 3](primer.md);
[rationale §1.3](rationale.md).

### 1.25 `Context`

**Informally.** Retrieve a contextually salient value of the declared
type: nothing asserted, nothing introduced, recovery *expected* — if
the hearer cannot find the value, communication failed. Site/key
identity: one retrieval per syntactic site per performance; keyed uses
(unassigned KOhA) retrieve once per key.
**For.** Omitted places, `zo'e`, `co'e`, `do'e`, `zu'i`, salient
scales, episodic tenseless time (pin P8).
**Example.** `mi klama` — the destination is a `Context` slot; `mi na
klama` denies going *there*, not existence of a destination.
**See.** [Spec §5.3](spec.md); [primer ch. 1, ch. 9](primer.md);
[rationale §1.3](rationale.md).

### 1.26 `Vague`

**Informally.** Denote the nonempty family of admissible
precisifications, with *no fact of the matter* selecting one — the
speaker waives specificity. Composition is by the VC law: pointwise
lifting, one precisification per parameter per binding site, truth
simpliciter as supertruth. Never resolved by context, never coerced.
**For.** The tanru link, `tu'a`, soritical thresholds (`so'i`), `joi`'s
mixture kind, bare `jai`'s role.
**See.** [Spec §5.3, §6](spec.md); [primer ch. 9](primer.md);
[rationale §1.3](rationale.md).

### 1.27 `SelectExactly`, `SelectAtLeast`, `SelectAllBut` — the primitive selections

**Informally.** The quantifier-strength members of the `Refer`
family: introduce a witness reference of the stated cardinal strength,
with the restrictor pure and the strength n ≥ 1 (the zero floor, spec
§12: a witness reference is nonempty by type, so no zero-strength
selection forms). The witness laws: `(Distrib P w)` holds, and
`(CardBasis w P)` is `= n` (`SelectExactly`) or `≥ n`
(`SelectAtLeast`). Unlike `Refer`, a selection under a governing
quantifier is *dependent* — one witness per value of the governor (the
dependence law) — which is what dependent anaphora normalizes over,
and why no `Refer`-plus-cardinality spelling can replace them (a
`Refer` is a governor-invariant constant). Binding a witness never
re-evaluates a selection; distinct selections introduce distinct
discourse referents (introduction identity — the witness values may
still co-refer). `SelectSome` is **defined** (§2.22).
**For.** Bare-PA terms: `ci gerku cu bajra` selects a three-dog
witness and predicates running of it, neutrally.
`SelectAllBut n P` (`da'a`; default n = 1) is the complement-count
member: its witness satisfies P member-wise (`Distrib P w`) and
leaves exactly n P-individuals behind, spelled by `SetOf`
comprehension (spec §12); the omitted individuals are not a
parameter.
**See.** [Spec §5.6, §4.10](spec.md); [primer ch. 5](primer.md);
[rationale §1.6](rationale.md).

### 1.28 `Presuppose`

**Informally.** Impose a projective condition: it must hold at the
nearest boundary that can commit it (or be accommodated there), and it
survives negation, disjunction, conditionals, and question force.
Introductions inside the condition stay local to it. Polymorphic over
the computation categories —
`Presuppose : Content × Comp<A> → Comp<A>` (the §2.10 `MaxRefer` use).
**For.** `ro`-import (pin P2), definedness of partial operations,
lexical presuppositions. `naku ro gerku cu blabi` still grants dogs.
**See.** [Spec §5.5](spec.md); [primer ch. 5](primer.md);
[rationale §1.4](rationale.md).

### 1.29 `Supplement`

**Informally.** Commit a side content about an anchor while the
at-issue value passes through: new information, speaker-committed,
projecting past negation and question force. Dependent sides commit
per instantiation inside their binder. Not interchangeable with
presupposition: supplements always commit anew.
**For.** `noi`, `sei`, `to…toi`, content-level indicator display.
`xu lo gerku noi blabi cu melbi` questions beauty, never whiteness.
**See.** [Spec §5.5, §7.6](spec.md); [primer ch. 11](primer.md);
[rationale §1.4](rationale.md).

### 1.30 `Generic`

**Informally.** The axiomatic generic quantifier: relate a pure
restrictor and nuclear scope through a normality ordering that may
depend on the nuclear predicate; mode Typical or Stereotypical (the
latter with the Speaker as holder). Not `∀`, not `∃`, no referent
introduced; its normality structure is constrained, not defined —
frankly axiomatic (and currently inference-free beyond typing — the
spec §14 gap entry). Restrictor and nuclear scope are member-level:
`Fn<(T), Content>` and `EFn<(T), Content>` (spec §5.8).
**For.** `lo'e`/`le'e`. The split-normality witness (maned male lions,
birthing female lions) kills every fixed-specimen theory.
**See.** [Spec §5.8](spec.md); [primer ch. 3](primer.md);
[rationale §1.9](rationale.md).

### 1.31 `Reify` and `Holds`

**Informally.** The one bridge between content and object: `Reify`
turns content into a `Proposition` (a first-order object representing
the content's intension); `Holds` is its primitive inverse, with the
axiom pair: evaluating `(Holds (Reify c))` is evaluating `c`, and
`(= (Reify (Holds p)) p)` for every proposition — so every
proposition, however introduced, represents exactly the content
`Holds` returns for it. The pair is the sole Proposition↔Content
bridge (the sign and event crossings target other sorts).
Construction is inert — nothing runs at `Reify` — while `(Holds p)`
runs the represented content at its own occurrence, escapes governed
by the surrounding operators (spec §5.4, §9.1).
**For.** `du'u`; attitude objects; single-evaluation display
(`Let`-shared `Reify` with `Holds` as the evaluated body). The shape
generalizes row by row to reified predicates — a §9.1 reservation
(registered gap), with the experimental `me'ei`/`me'au` pair as the
attested surface exponents; at the propositional case `me'au` is
`Holds` in selbri position under §9.1's singleton condition
(the `Meau0` schema — singularity projective; no plural baseline
reading).
**See.** [Spec §9.1, §7.6, §14](spec.md); [primer ch. 8](primer.md);
[rationale §1.10, §2.10](rationale.md).

### 1.32 `TanruAdmissible`

**Informally.** The axiomatized admissibility constraint behind tanru
modification: a relation of the head's row is admissible as the
modification link exactly when it makes the modifier bear on
*something* in the head predication (the event's manner, a
participant, a purpose, …) and nothing stronger — no x1-sharing, no
intersectivity. Nonempty by axiom: some link always exists,
discharging the `Vague` formation obligation. The `Tanru` operator
that consumes it is **defined** (§2.6).
**For.** Constraining `sutra klama`'s open modification relation
(CLL ch. 5).
**See.** [Spec §6.2](spec.md); [primer ch. 9](primer.md);
[rationale §1.8](rationale.md).

### 1.33 `Scalar`

**Informally.** `(Scalar k P)`, `k ∈ ⟨OtherThan, Opposite, Neutral⟩`:
deny `P`'s stated region on a contextually recovered scale *and*
positively assert an alternative region — some admissible other
(`na'e`), the antipode (`to'e`), the midpoint (`no'e`). Stronger than
`¬`, never weaker.
**For.** `ta na'e melbi` denies beauty and asserts an alternative
aesthetic standing. Also the `nai`-fallback for unpaired indicators
(`Opposite`).
**See.** [Spec §6.3, §7.6](spec.md); [primer ch. 7](primer.md);
[rationale §1.8](rationale.md).

### 1.34 `AdmissibleThreshold`, `AdmissibleTolerance`, `AdmissibleMixture`, `AdmissibleCutoff`, `InRegion`, `deg_R`

**Informally.** The gradable/vague-quantity interface: the axiomatic
admissibility predicates. `AdmissibleTolerance : Number × Precision →
Fn<(Number), Content>` and its rounding sibling `AdmissibleRounding`
serve `ji'i` (the tolerance/rounding-preimage regions about an anchor
at the numeral's precision, nonempty by VC1 — spec §12, pin P37;
`Direction` — the closed `Up | Down | Either` — is declared with the
rounding former);
`AdmissibleMixture` serves sumti-`joi` (the composition relations
refining `gunma` — nonempty by construction, `gunma` the trivial
refinement; spec §12);
the threshold predicates serve the degree quantifiers (indexed by
the closed `ThresholdKind` enumeration — `ManyK | FewK | TooManyK |
TooFewK | EnoughK`, an index type unrelated to the rejected `Kind`
sort) and gradable
scale regions (each nonempty by axiom, discharging the `Vague`
formation obligation), the region-membership relation
`InRegion : Amount × Region<Scale> → Content`, and the per-relation
degree projection `deg_R : Record ρ × Scale → Amount` declared by a
gradable entry's lexicon row (`GradableRel<ρ,ℓ>` classifies such
entries by their graded place ℓ).
**For.** `so'i`, `du'e`/`mo'a`/`rau`, `ta barda` via `Grade`.
**See.** [Spec §6.4, §10, §12](spec.md); [primer ch. 9](primer.md).

### 1.35 `Assert`, `Ask`, `Command`, `Express`, `Vocative`, `Mention` — the force constructors

**Informally.** Turn content (or a query, or an addressee, or any
value) into a first-class act of the corresponding force: assertion,
question, directive, expressive display, address, and use/mention
display of a value. Constructing performs nothing.
**For.** One content under four forces: `do klama` / `xu do klama` /
`ko klama` / displayed. `Mention` covers bare-sumti display and
specimen fragments.
**See.** [Spec §7.1](spec.md); [primer ch. 6](primer.md);
[rationale §1.11](rationale.md).

### 1.36 `Perform` and `Do`

**Informally.** `Perform` injects an act into the performance level —
the content's computation runs with the force's commitment effects;
`Do` sequences performed discourse (flattening, associative, with
`∧`'s accessibility row). Act boundaries close force segments:
introductions inside an unperformed act do not escape.
**For.** The discourse spine; `.i` sequencing.
**See.** [Spec §7.1, §5.4](spec.md); [primer ch. 6](primer.md).

### 1.37 `NewTopic` and `Resume`

**Informally.** The `ni'o`/`no'i` transitions,
`Discourse → Discourse`: discourse-structural operations with no
truth conditions but with stated effects on the information state's
segment structure — `NewTopic` suspends the current discourse segment
onto the suspended-topic stack and opens a fresh one (keyed `Context`
retrievals are per-segment, so keys re-retrieve; segment-bounded
text-to-reading rules like `ki` stickiness and `go'i` reach reset);
`Resume` pops the most recently suspended segment and reopens it.
**See.** [Spec §7.2, §5.1, §5.3](spec.md).

### 1.38 The sign constructors

**Informally.** `(OpaqueQuote text)` — unparsed quoted text
(`lo'u…le'u`, `zoi`); `(StructuredQuote entry)` — a transcript entry
carrying an unperformed act (`lu…li'u`; the entry operand is a pure
token-description property, §2.27, and the constructor supplies the
opaque boundary); `(NameSign text)`,
`(WordSign text)` (`zo`), `(LetteralSign text)`,
`(SentenceSign content)`. All build `Sign<K>` values; all boundaries
are opaque to dynamics.
**For.** Quotation, names (`Named` goes through `NameSign`), letteral
signs, `me'o` expression mention.
**See.** [Spec §7.5](spec.md); [primer ch. 10](primer.md).

### 1.39 `InterpretContent` and `InterpretAct`

**Informally.** The explicit, typed interpretation crossings from
signs (`la'e`; `lu'e` is the inverse sign-of): a sign to the content
or the act it expresses. `InterpretAct<F>` is a force-indexed
*partial* family — defined exactly when the sign's realized (or
intended) act has force `F`, since a sign does not carry its force. On
transcript entries, `InterpretAct` yields the realized act;
`InterpretContent` is defined exactly when that act is an
assertion (the content projection); a question, directive, or
expressive entry has no content projection and interprets only as an
act.
**For.** `la'e lu mi klama li'u` — the content, not the sentence.
**See.** [Spec §7.5, §16.3](spec.md); [primer ch. 10](primer.md).

### 1.40 The token and sign fact relations

**Informally.** The vocabulary for talking about utterances and signs
as objects — ordinary assertable relations, placeholder content words
under the §16 program. Signatures (u an `UtteranceToken`, s a
`SignToken<K>`, each relation `Content`-valued): `SpeakerOf u
speaker`, `AudienceOf u audience` (both at `Referents<Entity>`);
`LocutionOf locution u` (the locution first, at
`Referents<Locution>` — the order the §11 anchoring clause writes);
`DeicticTimeOf u t`
(`Time`); `DeicticPlaceOf u l` (`Location`); `TextOf u|s text`
(`Text`); `Realizes u a` (`a` an act value of whatever force — the
force index is existential); `Utters agent u`; `Quotes s x` (`x` the
quoted material: a sign or `Text`); `Denotes s x` (`x` a value of any
sort — denotation is sort-polymorphic).
**For.** Transcript entries, reported speech, the `le`-anchoring
clause (the describing event is this utterance's locution).
**See.** [Spec §7.4–7.5, §10–11](spec.md).

### 1.41 `Deictic`, `ShiftedGround`, `InContext`, and the context projections

**Informally.** The utterance context is a typed record (speaker,
audience, time, place, ground) with projections `Speaker`, `Audience`,
`Now`, `Here`. `Deictic` picks referents at a proximity against a
ground; `ShiftedGround` *constructs* a ground from a description
(never a contextual resolution); `InContext` evaluates content with
deictic projections from a given ground — the explicit context shift
(`ra'o`), currently the sole member of the index-shift family.
**For.** `mi`/`do`, `ti`/`ta`/`tu` (via the defined demonstratives),
narrative perspective shifts.
**See.** [Spec §5.1](spec.md); [rationale §2.3](rationale.md).

### 1.42 `Polar`, `OpenQ`, `QuestionOf`, `Answer`, and the answer selections

**Informally.** `(Polar c)` is the two-valued query (`Yes ↦ c`,
`No ↦ ¬c`); `(OpenQ f)` the open query whose answer-content function
sends each domain tuple `a` to `f a…`; `QuestionOf` reifies a query as
an embeddable `Question` object. `Answer` applies a query's
answer-content function to a selection: `(PolarAnswer Yes|No)`,
`(TupleAnswer a [Exhaustive|MentionSome])` — `Exhaustive` conjoining
the completeness claim, `MentionSome` overtly marking the weakest
reading, and absence of the marker meaning absence (pin P9).
**For.** `xu`/`ma`/`mo`/`fi'a`/`pei` questions; `kau` answerhood via
the defined `ContextualAnswer`.
**See.** [Spec §8](spec.md); [primer ch. 6](primer.md).

### 1.43 The abstraction relations

**Informally.** CLL's non-event abstractors are named relations with
labelled rows, parameterized by the abstracted content; reference
applies *outside*, so gadri, quantifiers, and relative clauses work on
abstractions for free. The rows (each `(XRel c) : PredTerm⟨…⟩`, every
place at `Referents<·>`): `NiRel` ⟨x1: Amount, x2: Scale⟩ (`ni`);
`JeiRel` ⟨x1: TruthValue, x2: Epistemology⟩ (`jei`); `LihiRel`
⟨x1: Experience, x2: Entity — experiencer⟩ (`li'i`); `SihoRel`
⟨x1: Concept, x2: Entity — mind⟩ (`si'o`); `SuhuRel`
⟨x1: AbstractNature, x2: Entity — category⟩ (`su'u`); `PuhuRel`
⟨x1: Process, x2: Eventuality — stages⟩ (`pu'u`); `ZuhoRel`
⟨x1: Activity, x2: Eventuality — repeated actions⟩ (`zu'o`). Event
abstraction (`nu` and its sort refinements) is plain `Refer` at the
event sort; `ka` is λ; `du'u` is `Reify`; `DuhuRel` is derived
(defined section). Where the §16.5 audit records a combinator fit
(`klani` for `NiRel`, `se lifri` for `LihiRel`, …), that is a
committee-pending adoption plan: upon adoption the relation becomes a
defined form over the adopted word; until then it stands primitive —
content-word status and term-language status are independent axes.
**For.** `lo ni mi klama cu barda` — an amount, referred to like
anything else, its scale a contextual slot.
**See.** [Spec §9.2](spec.md); [primer ch. 8](primer.md);
[rationale §1.10](rationale.md).

### 1.44 `AmountValue`, `TruthValueDegree`, `EventOfContent`

**Informally.** The named adjacent-sort crossings (pin P13 allows no
implicit ones): `AmountValue : Referents<Amount> × Referents<Scale> →
Number` — an amount's numeric value on its scale (`mo'e`; CLL 11.5);
`TruthValueDegree : Referents<TruthValue> → Number` — a truth value's
fuzzy degree in [0,1] (CLL 11.6); and `EventOfContent : Content →
Referents<Eventuality>` — the eventuality of a clause's content (used
by `tu'a`'s shape conjunct and `nu` recasting).
**See.** [Spec §9.2, §12](spec.md).

### 1.45 `MetalinguisticallyDefective` and the named value enumerations

**Informally.** The objection relation behind `na'i` (a prior
utterance or act is defective in a contextually recovered dimension),
with `DefectKind` (wording, form, implication, presupposition,
register) declared beside it; the evidential `BasisKind` enumeration
(`Observation`, `Hearsay`, `CulturalKnowledge`, `InternalExperience`,
`Expectation`, `Opinion`, `BareAssertion`); and the intensity-scale
regions (`Intense`/`cai`, `Strong`/`sai`, `Moderate`/unmarked,
`Weak`/`ru'e`, `Neutral`/`cu'i`).
**See.** [Spec §7.3, §7.6](spec.md); [primer ch. 7](primer.md).

### 1.46 The placeholder lexical relations

**Informally.** Relations the core uses that await their Lojban
content words under the §16 program. The indicator relations —
`Happiness`, `Unhappiness`, `Desire` : experiencer × `Target` ×
intensity region → `Content`, and
`EvidentialBasis` : experiencer × `Target` × `BasisKind` → `Content`
(`Target` the closed union of §7.6: a `Proposition` — content targets
go through `Reify` — an act value, a plural reference, or a sign) —
with the §16.5 audit mapping them to the `-nmo` indicator-emotion
family (*indicator* `zei cinmo`: `uinmo`, `u'inmo`, `le'onmo`, …, the
generic `inmo`; one word per indicator, mechanically extensible to
every UI and both `nai` poles) as its sole near-fit — the unofficial
rows carry experiencer × target, and the intensity place is the
proposed extension; the emotion gismu (`gleki`, `badri`, `djica`, …)
are see-alsos. The discourse
relations — `Contrast`, `Addition`, `Parallel`, `Elaboration` : two
act values → `Content` (audit: `frica`/`simsa` for contrast and
parallel). The named tanru-link precisification constants —
`MannerLink`, `MaterialLink`, `PurposeLink`, `SourceLink`,
`InstrumentLink`, `ResemblanceLink` — each a relation of its head row
satisfying `TanruAdmissible` by construction, shadowed by the BAI
gismu (`tadji`, `marji`, `mukti`, `krasi`, `pilno`, `simsa`); an open
family — a resolved reading may name links beyond these six.
PascalCase marks exactly this placeholder status; as with §1.43, a
recorded fit becomes a definition only when the committee adopts it.
**See.** [Spec §7.6, §7.2, §12, §16.5](spec.md);
[primer ch. 0, ch. 7](primer.md); the indicator instances appear in
[samples §7, §11](samples.md).


### 1.50 `InnatelyCapable` and `MotionVector`

**Informally.** Two lexically grounded primitives declared with the
§12 helpers they serve. `InnatelyCapable : Referents<Entity> ×
Fn<(Referents<Entity>, Referents<Eventuality>), Content> → Content` —
`jinzi`-grounded innate possibility of P-events with the bearer,
evaluated at capability worlds (the CAhA base). `MotionVector :
Referents<Eventuality> × Referents<Entity> × Referents<Entity> →
Content` — the `mo'i` heading: the event carries the mover's `muvdu`
motion in the `farna` direction.
**For.** `ka'e` (via the capability forms, §2.21) and the `mo'i`
motion tags.
**See.** [Spec §12, §11](spec.md).

### 1.51 `TopicAdmissible` and `TopicResolution`

**Informally.** The typed interface for `zo'u` topic-comment (P26):
`TopicResolution<ρ,T>` is the closed union indexed by the comment's
row and the topic's sort — fill an unfilled compatible place
(`PlaceFill ℓ`, ℓ : `CompatibleLabel<ρ,T>` — the refinement that
makes the fill branch type statically), or
bear `srana`-aboutness to the closed comment (`About`) — and
`TopicAdmissible` is the axiomatic admissibility predicate over
resolutions, `TanruAdmissible`'s sibling. The `Topic` schema binds a
`Vague` resolution: CLL 19.4's fish is exactly the place choice
(eater or eaten), typed.
**For.** `le finpe zo'u citka`.
**See.** [Spec §12, §11](spec.md), pin P26.

### 1.52 The MOI relation families

**Informally.** Five lexical relation families indexed by a number
(CLL 18.11), catalogued with exact rows: `MeiRel n` (group formed
from an n-membered set, members among it; comparison set for
objective-indefinite n; by-standard for subjective), `MoiRel n`
(n-th under a pure `Ordering<T>`, Context-recovered), `SiheRel n`
(typed portion), `CuhoRel n` (opaque probability, 0 ≤ n ≤ 1, the
model's measure — P29: no probability calculus), `VaheRel n` (scale
position via the degree projection). Lexical families, not term
expansions.
**For.** `lei mi ratcu cu cimei`; `ti pamoi le'i mi ratcu`.
**See.** [Spec §12, §11](spec.md), pin P29.

### 1.53 The declared partial projections and crossings

**Informally.** Declared, definedness projective (§5.5):
`RealizedAct<F>` / `RealizedDiscourse` (the act or act-sequence a
transcript token/span realizes — utterance anaphora's crossing, P28)
with the total `ActContent` (an assertion's packaged content);
`During` (an eventuality's temporal extent within an interval — the
ROI count schema's restriction, P35); and
the MEX conversions `RelToOp<ρ>` (`na'u`, at Number-rowed relations,
functional in x1), `OpToRel` (`nu'a`, total), `OperandToOp` (`ma'o`,
computation-typed: the function is a `Context` recovery — P36),
`AmountOperand<ρ>` (`ni'e`,
the Number-result computation at a Number-rowed relation). `se` on
operators is pure argument permutation.
**See.** [Spec §7.4, §12, §11](spec.md), pins P28, P36.

### 1.54 `EnumerationOrdinal`

**Informally.** MAI's declared display relation: the
attachment-selected constituent bears ordinal n in a
`SequenceKey`-identified enumeration at the closed
`EnumerationLevel` (`Item` for `mai`, `Section` for `mo'o`);
non-at-issue — placed by §7.6's machinery (`Supplement` at a
constituent target, `Express` beside an act-level target); no
temporal ordering of denoted events implied (CLL 19.7 numbers sumti
inside one bridi).
**For.** `mi klama pamai le zarci .e remai le zdani`.
**See.** [Spec §12, §11](spec.md).

## 2. Defined forms

Everything below expands into the primitives (and other defined forms,
acyclically). The expansion *is* the specification; the prose says the
same thing a first time.

### 2.1 `PredTerm<ρ>`

**Informally.** The type of relations over row ρ — a transparent alias,
not a new type: relations are row-functions, partial filling is
abstraction over the residual row, and a relation over the exhausted
row is its content.
**Formally.** `PredTerm<ρ> ≝ Record ρ → Content`, with
`PredTerm<⟨⟩>` applied at the empty record ≡ `Content`.
**For.** Keeping labels load-bearing (FA, `zi'o`, `fi'a` all speak in
labels) with the ontology of functions.
**See.** [Spec §3.3](spec.md); [rationale §1.1](rationale.md).

### 2.2 `At` and the fill notation

**Informally.** The single-place fill: fill place ℓ of relation `R`
with value `v`, yielding the relation over the residual row. All
multi-fill notation — positional fills, `:n` labels, the
continue-after-`n` rule, FA routing, `se`-conversion — desugars to
nested single fills. Distinct-label fills commute (fills are values),
which is why Lojban's free surface order is pure notation. With a
*computed* label (`fi'a`), `At` abbreviates the finite case split over
literal fills.
**Formally.** `(At R ℓ v) ≝ (λ {$rest :: Record ρ−ℓ} {(R ⟨$rest
extended with ℓ = v⟩)})`;
`(klama :2 This Yonder) ≝ (At (At klama x2 This) x3 Yonder)`.
**For.** `klama fe ti tu`; `klama fi'a ti` at the computed-label case.
**See.** [Spec §4.1, §4.7](spec.md); [primer ch. 1](primer.md).

### 2.3 `Let`

**Informally.** Pure sharing: bind a value for a body — definable as
immediate application, retained for legibility and for identity of one
value used twice (`goi` aliasing, act targets). May not bind an
effectful computation; that is `Bind`'s job, by type.
**Formally.** `(Let {$x :: T} v {body}) ≝ ((λ {$x :: T} {body}) v)`.
**Content-word status.** Class M structural machinery: no content word is
owed for this sharing syntax.
**For.** `(Let {$a :: Act Assertion} (Assert …) {(Do (Perform $a)
(Express (… $a …)))})` — the display targets *that* act.
**See.** [Spec §4.4](spec.md); [primer ch. 7](primer.md).

### 2.4 `Close`

**Informally.** Complete an open predication into content: close the
event place existentially (where the row licenses one) and give each
remaining defaultable place its own contextual slot — one distinct
site per omission, staying put under negation.
**Formally.** `(Close P) ≝ (Bind {$v1 :: T1} (Context) … {$vk :: Tk}
(Context) {(∃ (λ {$e :: Referents Eventuality} {(P :p1 $v1 … :pk $vk
:Eventuality $e)}))})`.
**For.** Every unmarked bridi: `mi klama` commits to a contextually
recoverable destination — not "some destination", not nothing.
**See.** [Spec §4.6](spec.md); [primer ch. 1](primer.md);
[rationale §1.2](rationale.md).

### 2.5 `This`, `That`, `Yonder`

**Informally.** The demonstratives, as deictic picks at the three
proximities against the context's ground.
**Formally.** `This ≝ (Deictic Proximal g)`, `That ≝ (Deictic Medial
g)`, `Yonder ≝ (Deictic Distal g)`, where `g` is the enclosing
utterance context's ground (the `ctx` record's ground projection,
spec §5.1).
**For.** `ti`/`ta`/`tu`.
**See.** [Spec §5.1](spec.md).

### 2.6 `Tanru`

**Informally.** Modification of a head by a modifier: the head's row,
the head's predication, plus an admissible modification link — a
`Vague` parameter ranging over the relations `TanruAdmissible`
(§1.32) admits, with no fact of the matter selecting one.
**Formally.** `((Tanru M H) fills…) ≝ (Bind {$link :: PredTerm ρ(H)}
(Vague (λ {$r :: PredTerm ρ(H)} {(TanruAdmissible M H $r)}))
{(∧ (H fills…) ($link fills…))})`.
**For.** `sutra klama` — a goer, with `sutra` bearing on the going
*somehow*; the library's named links are the common precisifications,
a lujvo a lexicalized one.
**See.** [Spec §6.2](spec.md); [primer ch. 9](primer.md);
[rationale §1.8](rationale.md).

### 2.7 `UnitSet` and `CardBasis`

**Informally.** Basis extraction: the set of P-satisfying units among
a reference, and counting as counting units *under a description*
within a reference — how inner cardinality works, with no canonical
atomic basis assumed.
**Formally.** `(UnitSet P r) ≝ (SetOf (λ {$x :: T} {(∧ (P $x) (Among $x r))}))`;
`(CardBasis r P) ≝ (Card (UnitSet P r))`.
**For.** `lo ci gerku` — counted as dogs, three; the same plurality
may count differently under another basis (three dogs, one pack).
**See.** [Spec §4.8](spec.md); [primer ch. 3, ch. 11](primer.md).

### 2.8 `CoRef` and `Overlap`

**Informally.** Plural co-reference (mutual subreference — the
equivalence the plural type uses instead of `=`) and plural overlap
(some common subreference).
**Formally.** `(CoRef x y) ≝ (∧ (Among x y) (Among y x))`;
`(Overlap a b) ≝ (∃ (λ {$c :: Referents T} {(∧ (Among $c a) (Among $c b))}))`.
**See.** [Spec §4.8, §12](spec.md).

### 2.9 `Distrib` and `lu'a`

**Informally.** The marked each-reading: the property holds of every
unit among the reference. `lu'a` is this distribution applied at its
use site. Never a default — unmarked plural predication is neutral
(pin P4).
**Formally.** `(Distrib Q r) ≝ (∀ (λ {$x :: T} {(→ (Among $x r)
(Q $x))}))`, `T` the member type.
**For.** "each of them", `ro`'s nuclear scope, forced distributive
readings.
**See.** [Spec §12, §4.8](spec.md); [primer ch. 3](primer.md);
[rationale §2.5](rationale.md).

### 2.10 `MaxRefer`

**Informally.** The maximal base: the reference to *all* the
P-satisfiers and nothing else — every unit is P, every P-satisfier is
among it, every part overlaps a P-unit. Defined only for inhabited P
(a presupposition), with the model required to supply the reference
(plural comprehension).
**Formally.**

```text
(MaxRefer P) ≝
  (Presuppose (∃ P)
    (Refer (λ {$r :: Referents T}
      {(∧ (Distrib P $r)
         (∀ (λ {$x :: T} {(→ (P $x) (Among $x $r))}))
         (∀ (λ {$r' :: Referents T}
              {(→ (Among $r' $r)
                 (∃ (λ {$x :: T} {(∧ (P $x) (Overlap $x $r'))})))})))})))
```

Models must supply this reference for each inhabited pure restrictor
the mapping can form (plural comprehension — a model condition).
**For.** The `lo'i`/`loi` base ("the set of *the* dogs") and `Every`'s
witness export.
**See.** [Spec §12, §11](spec.md).

### 2.11 `Reciprocate`

**Informally.** The reciprocal schema: every two distinct members of
the witness stand in the relation, both ways (member-wise; vacuous on
a unitless reference — mass reciprocity needs an explicit basis).
Consumed by `simxu`'s and `soi`'s lexicon rows.
**Formally.** `(Reciprocate r P) ≝ (∀ (λ {$x $y :: T} {(→ (∧ (Among $x r) (Among $y r) (¬ (= $x $y)))
(P $x $y))}))` — `T` the member sort; the units singleton-lift at
`Among` and at `P`'s places.
**For.** `ci jbopre cu simxu lo ka tavla` — pairwise mutual talk.
**See.** [Spec §12](spec.md); [samples §5](samples.md).

### 2.12 The cardinal quantifiers

**Informally.** The witness-set family: select a witness of the stated
strength and predicate the nuclear scope of it **neutrally** — the
each-reading comes from the lexicon or `Distrib`, never from the
quantifier (pin P17, pin P4). `Every` is the importing universal:
presuppose the restrictor inhabited, export the maximal base,
distribute (`ro` is each). The negative/bounded forms contain their
selection under `¬` and export nothing.
**Formally.**
`(Exactly n P Q) ≝ (Bind {$w :: Referents T} (SelectExactly n P)
{(Q $w)})`;
`(AtLeast n P Q)` / `(Some P Q)` likewise over their selections;
`(Every P Q) ≝ (Bind {$w :: Referents T} (MaxRefer P) {(Distrib Q
$w)})` — the import is `MaxRefer`'s own presupposition; `(No P Q) ≝ (¬ (Some P Q))`; `(AtMost n P Q) ≝ (¬ (AtLeast n+1
P Q))`; `(MoreThan n P Q) ≝ (AtLeast n+1 P Q)`; `(FewerThan n P Q) ≝
(¬ (AtLeast n P Q))`; `(GlobalExactly n P Q) ≝ (= (Card (SetOf (λ {$x :: T} {(∧ (P $x) (Q $x))}))) n)` (pure operands; the marked global reading).
Zero floor (spec §12): the selections form only at n ≥ 1;
`(AtLeast 0 P Q) ≝ ⊤` and `(Exactly 0 P Q) ≝ (No P Q)`, with the
bounded forms following from the definitions.
**For.** `ci gerku cu bajra .i ri tatpi` (witness export); `no prenu
cu jmaji` (the collective reading a distributive default cannot say).
**See.** [Spec §12, §4.10, §5.6](spec.md); [primer ch. 5](primer.md);
[rationale §3 (P17)](rationale.md).

### 2.13 The degree quantifiers

**Informally.** Cardinal comparisons against thresholds that are
`Vague` (and, for the purpose-relative kinds, constrained by a
`Context`-recovered standard): many, few, most, too many, too few,
enough.
**Formally.** (`θ` a `Vague` threshold; `σ` a `Context` standard;
kinds from `ThresholdKind`, §1.34; `P`, `Q` pure for `Most`.)

```text
(Many P Q)    ≝ (Bind {$θ :: Natural} (Vague (AdmissibleThreshold ManyK P))
                  {(AtLeast $θ P Q)})
(Few P Q)     ≝ (Bind {$θ :: Natural} (Vague (AdmissibleThreshold FewK P))
                  {(FewerThan $θ P Q)})
(TooMany P Q) ≝ (Bind {$σ :: Referents Entity} (Context)
                       {$θ :: Natural} (Vague (AdmissibleThreshold TooManyK P $σ))
                  {(MoreThan $θ P Q)})
(TooFew P Q)  ≝ (Bind {$σ :: Referents Entity} (Context)
                       {$θ :: Natural} (Vague (AdmissibleThreshold TooFewK P $σ))
                  {(FewerThan $θ P Q)})
(Enough P Q)  ≝ (Bind {$σ :: Referents Entity} (Context)
                       {$θ :: Natural} (Vague (AdmissibleThreshold EnoughK P $σ))
                  {(AtLeast $θ P Q)})
(Most P Q)    ≝ (> (Card (SetOf (λ {$x :: T} {(∧ (P $x) (Q $x))})))
                   (Card (SetOf (λ {$x :: T} {(∧ (P $x) (¬ (Q $x)))}))))
```
**For.** `so'i prenu cu klama` — the family over admissible
thresholds; no exact count hides anywhere.
**See.** [Spec §6.4, §12](spec.md); [primer ch. 5, ch. 9](primer.md).

### 2.14 `Grade`

**Informally.** Gradable predication with its two parameters exposed:
the relation holds of a row record when its degree on the given scale
falls in the given region — scale recoverable (`Context`), region
boundary `Vague`.
**Formally.** `(Grade R s reg) ≝ (λ {$rec :: Record ρ} {(InRegion
(deg_R $rec s) reg)})`.
**For.** `ta barda` — big along which dimension is recovered; where
"big" starts has no fact of the matter.
**See.** [Spec §6.4, §12](spec.md); [primer ch. 9](primer.md).

### 2.15 `Interval`

**Informally.** The set of values between two endpoints, each endpoint
strict or non-strict (`ga'o`/`ke'i`).
**Formally.** `(Interval a b k₁ k₂) ≝ (SetOf (λ {$x :: T} {(∧ (cmp₁ a $x) (cmp₂ $x b))}))`.
**See.** [Spec §12](spec.md).

### 2.16 `ZipWith`

**Informally.** Respective pairing over two lists, by metalanguage
recursion — the `fa'u` analysis, expanding completely into a
conjunction.
**Formally.** `(ZipWith f (List) (List)) ≝ ⊤`; `(ZipWith f (List a
as…) (List b bs…)) ≝ (∧ (f a b) (ZipWith f (List as…) (List bs…)))`.
**For.** `mi fa'u do tavla do fa'u mi` ≡ I talk to you ∧ you talk to
me.
**See.** [Spec §12](spec.md); [samples §5](samples.md).

### 2.17 `Named`

**Informally.** Bearing a name-sign, through the lexicon's `cmene`
row: the referent is what the name names, the namer contextual.
**Formally.** `(Named t x) ≝ (Close (cmene (NameSign t) x))`.
**For.** `la .alis.` — `Refer` over `(Named "alis" ·)`.
**See.** [Spec §12, §11](spec.md); [primer ch. 3](primer.md).

### 2.18 `DuhuRel`

**Informally.** The derived `du'u` relation: its x1 is the reified
content, its x2 a sentence sign expressing it (CLL 11.7's x2, `se
du'u`). Derived because `Reify` already carries the crossing.
**Formally.** `((DuhuRel c) x1 x2) ≝ (∧ (CoRef x1 (Reify c))
(Distrib (λ {$s :: Sign Sentence} {(CoRef (Reify (InterpretContent
$s)) (Reify c))}) x2))` — x2's signs are those whose interpretation
reifies the same content.
**For.** `lo se du'u mi klama` — the sentence, not the proposition.
**See.** [Spec §9.2](spec.md); [samples §9](samples.md).

### 2.19 `ContextualAnswer`

**Informally.** Bare `kau`'s answerhood: the answer tuple is retrieved
from context, with the exhaustivity slot absent (pin P9) — the weakest
reading, strengthened only lexically or by explicit marker.
**Formally.** `(Answer q ContextualAnswer) ≝ (Bind {$a :: A} (Context)
{(Answer q (TupleAnswer $a))})` at open domains; at `Query<Bool>` the
retrieval is at `Bool` and the selection is `(PolarAnswer $a)` — the
`xu kau` case (spec §8.2).
**For.** `mi djuno lo du'u ma kau klama`.
**See.** [Spec §8.2](spec.md); [primer ch. 6](primer.md).

### 2.20 `JaiPromote`

**Informally.** Tagged `jai`: promote the tagged role to x1 and move
the old x1 to the labelled, fillable `fai` place (closing contextually
when unfilled — CLL 9.12). Bare `jai` is the mapping's
`Vague`-role raising instead.
**Formally.** Writing ρ' for ρ with ℓ relabelled x1 and x1 relabelled
`fai`: `(JaiPromote R ℓ) ≝ (λ {$r :: Record ρ'} {(R ⟨ℓ = $r.x1,
x1 = $r.fai, rest unchanged⟩)})`.
**For.** `mi jai gau rinka` patterns; `fai` fills.
**See.** [Spec §12, §6.1, §11](spec.md).

### 2.21 `Realized`, `nu'o`, `pu'i` — the capability forms

**Informally.** Over the primitive `InnatelyCapable` (§1.50):
`Realized` — an actual P-event of the bearer occurred; `nu'o` =
capable and never realized; `pu'i` = capable and demonstrated. `P` is
an event property of the bearer,
`Fn<(Referents<Entity>, Referents<Eventuality>), Content>`.
**Formally.**

```text
(Realized b P) ≝ (∃ (λ {$e :: Referents Eventuality}
                    {(∧ (P b $e) (fasnu $e))}))
(nu'o b P)     ≝ (∧ (InnatelyCapable b P) (¬ (Realized b P)))
(pu'i b P)     ≝ (∧ (InnatelyCapable b P) (Realized b P))
```
**See.** [Spec §12, §11](spec.md).

### 2.22 `SelectSome`

**Informally.** The `su'o`-strength selection — at least one unit —
as the weakest member of the selection family.
**Formally.** `(SelectSome P) ≝ (SelectAtLeast 1 P)`.
**For.** `su'o gerku cu bajra` — some dogs (one or more) ran.
**See.** [Spec §5.6](spec.md); §1.27 above.

### 2.23 `NahiObjection`

**Informally.** The `na'i` act: express, of a bound prior target, that
it is metalinguistically defective in a contextually recovered
dimension — performing nothing, negating nothing.
**Formally.** `(NahiObjection t) ≝ (Bind {$d :: DefectKind} (Context)
{(Express (Close (MetalinguisticallyDefective t $d)))})`.
**See.** [Spec §12, §7.3](spec.md); [primer ch. 7](primer.md).

### 2.24 `GroundedBy`

**Informally.** The act-level evidential spelling: display, beside a
performed act, the speaker's basis for it — a mode of commitment, not
a second claim.
**Formally.** `(GroundedBy b a) ≝ (Do (Perform a) (Express (Close
(EvidentialBasis Speaker a b))))`.
**For.** `za'a do cadzu` — the assertion grounded in observation;
negation touches the walking, never the basis.
**See.** [Spec §12, §7.6](spec.md); [primer ch. 7](primer.md).

### 2.25 `Only` and `Additive`

**Informally.** Constituent focus: `po'o` presupposes the host holds
of the focus and denies it of every non-co-referent alternative;
constituent `ji'a` presupposes an alternative and asserts the host of
the focus.
**Formally.** `(Only f H) ≝ (Presuppose H[f] (¬ (∃ (λ {$y :: T} {(∧ (¬
(CoRef $y f)) H[$y])}))))`; `(Additive f H) ≝ (Presuppose (∃ (λ {$y :: T}
{(∧ (¬ (CoRef $y f)) H[$y])})) H[f])`.
**See.** [Spec §12, §7.2](spec.md).

### 2.26 The COI schemas

**Informally.** Performative expressives: a COI greeting/thanks/… is
constituted by its performance — `Express` of the COI lexical relation
with the performative host-force profile.
**Formally.** `(COIExpress R addr) ≝ (Express (Close (R Speaker
addr)))`, `R` the COI entry's lexical relation (`coi-greeting`,
`ki'e-thanks`, …), performed with its performative profile.
**For.** `coi do` — the greeting is the act.
**See.** [Spec §12, §7.6, §11](spec.md).

### 2.27 The `Utterance` and `Sign` entry notations

**Informally.** A token variable with facts about it — the transcript
entry `StructuredQuote` consumes, and the same notation at the
sign-token sort. Defined: the λ suspends the facts by nature (nothing
performed, nothing introduced — quoted material introduces no
discourse referents), yielding a *pure token-description property*;
the opacity belongs to the consuming sign constructor, not to this
notation. Performed-level token talk needs no special form — it is
ordinary `Refer` at the token sort.
**Formally.** `(Utterance {$u :: UtteranceToken} {fact…}) ≝ (λ {$u :: Referents UtteranceToken} {(∧ fact…)})`; the `Sign` notation likewise
at `SignToken<K>`.
**For.** `lu mi klama li'u` → `(StructuredQuote (Utterance {$u :: UtteranceToken} {(Realizes $u (Assert (Close (klama Speaker))))}))`.
**See.** [Spec §7.4–7.5](spec.md); [primer ch. 10](primer.md);
[samples §6, §10](samples.md).


### 2.29 `te'a`, `gei`, and `xi` indexing

**Informally.** MEX helpers by metalanguage recursion: integer
exponentiation, order-of-magnitude, and subscripting as list
indexing (undefined past the end — a projective definedness
condition).
**Formally.**

```text
(te'a x 0)              ≝ 1
(te'a x (n+1))          ≝ (× x (te'a x n))
(gei x y)               ≝ (× y (te'a 10 x))
(xi (List a as…) 1)     ≝ a
(xi (List a as…) (n+1)) ≝ (xi (List as…) n)
```
**For.** `li re te'a ci du li bi`.
**See.** [Spec §12](spec.md); [samples §10](samples.md).

### 2.30 `MePred`

**Informally.** `me` as a defined form: the Among-property of a
sumti's referents — `(MePred X) ≝ (λ {$w :: Referents T} {(Among $w
X)})`, X's computation bound before the pure property forms. The
ratified gadri definitions expand `lo PA sumti` through `me`.
**For.** `la .baltazar. cu me le ci nolraitru`.
**See.** [Spec §12, §11](spec.md).

### 2.31 `TanruLinkConnect`

**Informally.** Jek at the tanru-unit locus (P33): for a shared head,
bind one `Vague` link per conjunct and join the link applications
with the connective — the head asserted once
(`blabi ja cmalu zdani`: a house, whose modification link is
white-flavored or small-flavored). Distinct-head units connect as
whole predications; joiks route to the mixture semantics.
**For.** `ta blabi je cmalu zdani`.
**See.** [Spec §12, §6.2, §11](spec.md), pin P33.

### 2.32 The region formers

**Informally.** The BIhI region formers beyond ordered `Interval`,
all defined by `SetOf` comprehension over a Context-recovered
`Metric<T>` (spec §12): `MetricBall` (`mi'i` — center, radius,
GAhO boundary kind; no endpoint arithmetic), `SpanRegion` (`bi'i` at
metric domains — metric betweenness), `RegionComplement` (`bi'o nai`
— complement in a Context universe). `bi'i` at ordered domains is ⊳
symmetrization of the ordered `Interval` (endpoint order normalized
together with the GAhO kinds). Endpoint/center references take the
projective singular condition (the §9.2 pattern).
**For.** `la .uacintyn. mi'i lo minli be li muno`.
**See.** [Spec §12, §11](spec.md).

## Appendix: model-theory symbols

Not term-language forms — the denotational metalanguage of
[spec §5.1](spec.md), listed so no named symbol goes unaccounted:
`Comp<A> = InformationState → P(InformationState × A × Obligations)`
is the computation carrier (`Content = Comp<Unit>`,
`RefComp<T> = Comp<T>`; discourse denotes at the same carrier with
its commitment effects, while an act value is the pure force-tagged
package only `Perform` injects — spec §5.1, §7.1); an `InformationState` is a set of
world–assignment pairs over the model's world set W; `Obligations`
collects pending projective commitments; `Unit` is the one-value
return type of contentful computations; and `ctx` is the utterance
context record (speaker, audience, time, place, ground) whose
projections §5.1 names. These symbols may change with the model (the
`da'i` gap entry anticipates a world-shift operation) without any term
changing — which is the point of keeping them out of the term
language (rationale §1.14).
