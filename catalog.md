# Catalog of the core forms

This catalog indexes named forms in [the specification](spec.md), which
remains normative. Primitives have no term-language expansion; their meanings
are fixed by the specification's declarations and laws. Defined forms expand
into primitives and other definitions. Reserved names are labelled separately
and do not count as completed definitions or surface mappings.

Entries give a prose description, a formal definition where available,
uses, and references to the specification, [primer](primer.md), and
[rationale](rationale.md). Related forms share entries where they have common
rules. [The decision ledger](decisions.md) records current coverage limits.

Section numbers 1.47–1.49 and 2.28 are retired. They belonged to the
withdrawn staged-reflection design; later numbers are deliberately left
unchanged so existing cross-references remain stable. Rationale §2.9 explains
the direct-binder choice; the detailed design history remains in the review archive.

The scope is the term language: model-theory symbols
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

First-order individuals are sorted: `Entity` at the
top; beneath it `Eventuality` (with subsorts `Achievement`, `Process`,
`Activity`, `State`, `Experience`, and `Locution`, an uttering event),
`Location`, `Time`, `Amount`, `Scale`, `Epistemology`, `TruthValue`,
`Concept`, `AbstractNature`, `Proposition`, `Question`, `Number` (with
`Natural` and `Cardinal` beneath it), `Text`, the collection and sign
sorts of the entries below, `UtteranceToken`, and `Ground`. Subsorting
is subset inclusion; a subsort term stands wherever the supersort is
required, never conversely. Apart from stated subsorting and reference lifts,
crossings require explicit operations. P13 records the abstraction-sort case.

Use: Lexical type selection and the no-coercion rule. A Proposition
cannot replace an Amount in a resolved Amount-selecting row without an
explicit crossing. This does not determine every possible lexical reading.

References: [Spec §3.1](spec.md); [primer ch. 8](primer.md).

### 1.2 `Referents<T>` — the plural reference type

Nonempty, number-neutral pluralities of `T`s: one or
more things *referred to together*, which are not a set-object, not a
mereological sum, and not a group — no object exists over and above
the things. There is no empty plural reference; a single `T` lifts to
a singleton reference at referential positions. That lift need not be an
Among-atom; first-order identity, lift injectivity and minimality are distinct.
Covariant in `T`.

Use: The type of every ordinary lexical argument place. `mi jo'u
do bevri lo pipno` — a plurality carries; no set carries anything.

References: [Spec §3.2, §4.8](spec.md); [primer ch. 3](primer.md);
[rationale §1.7, §2.8](rationale.md).

### 1.3 `Set<T>`, `Group<T>`, `List<T>` — collection object types

First-order *objects* that package other things: a set
(extensional, with membership and cardinality and possibly empty), a
group (a concrete collective with its own properties — a crowd can
surround a building), a list (order-bearing). Distinct from plural
reference: none unwraps implicitly to its members.

Use: `lo'i gerku` denotes a `Set<Entity>`; `loi prenu` a group via
complete `GunmaAt`; free `gunma` stays non-exhaustive; `ce'o` builds lists.
The two-sort split (reference vs object)
is what makes `lo selcmi cu simxu` unambiguous.

References: [Spec §4.9](spec.md); [primer ch. 3](primer.md);
[rationale §2.8](rationale.md).

### 1.4 `Fn` and `EFn` — the function types

`Fn<(A…), B>` is the pure function type: a body that
performs no dynamic effects when its result is evaluated — no
introductions, no contextual retrievals, no projective emissions, subject
to P45's explicit negation-local reference qualification: references consumed
wholly inside the negative Content test do not count against purity. Other
effects and every obligation record remain; `Local` and other connective
rules are unchanged.
`EFn` is the effectful arrow. Pure positions include set comprehensions,
quantifier and Generic restrictors, selection restrictors, and the member-level
Refer lift. GlobalExactly and Most also require pure nuclear properties.
Other nuclear scopes may use EFn; the complete conditions are in the spec.

Use: Pure properties have type `Fn<(T), Content>`; effectful property
bodies use `EFn`. A `ka` abstraction's type follows its body and consumer.
A restrictor exposing an unclosed `Refer` introduction does not satisfy a
pure-position requirement. P45 supplies the specific negation-local exception.

References: [Spec §3.3, P45](spec.md); [rationale §1.14, §2.11](rationale.md) (the
pure/effectful seam).

### 1.5 `Record ρ` and `Label<ρ>` — rows

A place row ρ is a finite sequence of labelled, typed
places; `Record ρ` is the type of complete fills for it; `Label<ρ>` is
the finite type of its place labels. Labels are semantically real:
Lojban reorders, deletes, and *asks about* places by label.

Use: `klama fi'a ti` is a question over the compatible-label
refinement of `Label<ρ(klama)>` (spec §4.7 — sort-incompatible places
and the event place contribute no branch); the
fill notation computes labels (spec §4.1). `PredTerm<ρ>` (defined
section) is the row-function alias over these. (`Record` and `Label`
are type constructors of the record theory, not first-order sorts —
they do not appear in §3.1's hierarchy.)

References: [Spec §3.3, §4.7](spec.md); [rationale §1.1](rationale.md).

### 1.6 `Content` and `ClauseContent`

The type of what can be asserted, questioned, negated,
and embedded. Its denotation is a world-indexed context-change
potential: run against an information state, it filters and extends
that state and accumulates projective obligations. No world variable
ever appears in a term. Its structured denotation also carries the §9.3
clause-event intension projected by `EventOfContent`. `ClauseContent` is the transparent alias
`EFn<(Referents<Eventuality>), Content>`: one distinguished clause
eventuality remains open for tense, tags, CAhA, ROI, and `nu`, then
`CloseClause` supplies ordinary Content and records its locally selected
argument as that Content's clause-event intension. `ClauseContent` is a
function type, not a first-order event or proposition sort. Where ROI needs a pure comprehension,
the mapping binds effects before using the ordinary `Fn` refinement.

Use: `mi pu klama` exposes its going event; `ta pu du lo mi zdani`
exposes a holding State while `du` remains binary identity.

References: [Spec §3.4, §4.6, §5.1](spec.md); [primer ch. 1–2](primer.md).

### 1.7 `RefComp<T>` — reference computations

Computations that return a `T` while possibly
performing dynamic effects: introducing referents (`Refer`,
selections), consulting context (`Context`), or denoting
precisification families (`Vague`). Consumed by `Bind`.

Use: The type of every description and selection before its
witness is bound.

References: [Spec §3.4, §5.2–5.3](spec.md).

### 1.8 `Act<F>`, `PerfComp<T>`, and `Discourse` — speech-act types

An `Act<F>` value is a force-tagged content package —
force `F` (Assertion, Question, Directive, Expressive, Address) plus
the content computation — built inertly: constructing an act runs
nothing. An act is a pure value, not a computation — the `Perform` boundary
(§1.36) injects it into the dynamic carrier. `Discourse` is performed
discourse: sequences of performed
acts and transitions. A document denotes one `Discourse`. The package stays
raw and reusable: performance-specific contextual capture belongs to the
`ActOccurrence` handle returned by `Perform`, never to `Act<F>` or
`ActContent`. `PerfComp<T>` is the performance computation category and
`Discourse = PerfComp<Unit>`.

Use: Quotation and report: `mi cusku lu ko klama li'u` mentions a
directive without issuing it, because only performance executes. The
source-preparing `PerformSource` boundary is catalogued at §1.36a.

References: [Spec §3.4, §7.1](spec.md); [primer ch. 6](primer.md);
[rationale §1.11](rationale.md).

### 1.8a `ActOccurrence<F>` — opaque performance handle

One execution of one reusable act package, associated with
the current transcript token/span and the extensional semantic capture of
that performance's utterance context and `Context` resolver. Re-performing
one act creates another occurrence and may realize different content without
mutating the package.

Semantic class: Class M model infrastructure.
The captured resolver is its original partial function over every declared
dependency tuple at the package's sites, not a visited-tuple cache; newly
reached tuples use that function or project its undefinedness.

Surface reachability: lowering-only generic infrastructure — `Perform`
returns the handle and act-level UI lowerings `Bind` it, but there is no
direct Lojban sumti spelling, pure constructor, or state inspector. Its factorization witness is the
`ActContent`/`RealizedContent` distinction and occurrence-relative indicator
grounding.
`OccurrenceRole` is the closed `Host | AttachedDisplay | AttachedAddress`
index supplied explicitly to `Perform`; unary `Perform a` is Host shorthand.
A standalone display/COI/vocative is Host; the attached roles occur only
beside a distinct Host.

Use: Cross-performance default `go'i` and `la'e di'u` preserve the antecedent occurrence's
resolved context; `ra'o` selectively rebuilds its marked pro-assign sites from
the raw package while retaining other captured sites.

References: [Spec §5.1, §7.1–7.4](spec.md); [rationale §1.11](rationale.md).

### 1.9 `Query<A>`, `Selection<A>`, `Bool` — question types

A `Query<A>` is a question with typed answer domain
`A`, denoting its answer-content function; a `Selection<A>` picks from
that domain; `Bool` is the two-element polar answer type (distinct
from the epistemology-relative `TruthValue` sort).

Use: `xu`, `ma`, `mo`, `fi'a`, `pei` all land in `Query` at
different domains; implicit-answer `kau` supplies the contextual answer selection
to `Answer`, which returns Content. In `lo du'u … kau …`, `Reify` represents
that Content as a Proposition. `QuestionOf` instead represents the query as a
Question object.

References: [Spec §8](spec.md); [primer ch. 6](primer.md).

### 1.10 `Sign<K>`, `SignToken<K>`, `UtteranceToken` — sign types

Signs are quoted or mentioned linguistic material,
classified by kind `K` (Name, Sentence, Word, Letteral, Quotation,
MathExpression, Structured, Opaque, Text, and Connective);
sign tokens and utterance tokens are the concrete occurrences facts
attach to. Constructing a sign does not evaluate its represented content or
emit that content's references and projective obligations. Explicit
interpretation and represented-source anaphora have separate rules.

Use: The distinction between using an expression and mentioning it.

References: [Spec §7.4–7.5](spec.md); [primer ch. 10](primer.md).

### 1.11 `Ground`, `GroundDescription`, `Proximity` — deictic ground types

A ground is an orientation center with its perspective
facts — what demonstratives point against; `Proximity` is the closed
three-value type `Proximal | Medial | Distal`; ground descriptions are
the specifications grounds are constructed from.

Use: `ti`/`ta`/`tu` and `ra'o`-style re-orientation.

References: [Spec §5.1](spec.md).

### 1.12 `Region<Scale>` — scale regions

Regions of a scale — poles, midpoints, intervals — the
values gradable cutoffs work over. Scalar contrast uses the distinct
`ContrastDomain<ρ>` / `ContrastRegion<ρ>` interface.

Use: `Grade`'s vague cutoff.

References: [Spec §6.4, §12](spec.md).

### 1.13 The pure function substrate

Typed functions over labelled-record-aware parameters, with juxtaposition
as application. Bound variables obey ordinary α-renaming and capture-avoiding
substitution. Application to value arguments satisfies β: if its result is a
computation, substitution constructs that computation without running it.
That rule does not remove the sequencing supplied by `Bind`.
`λ` is the direct binding form: its telescope introduces
typed parameters and its brace-delimited body fixes their scope. The
braces are punctuation, not quoted signs.

Content-word status: Class M structural machinery: no Lojban word is
owed merely to rename function formation.

Use: Properties (`ka` with `ce'u` = λ, pin P12), quantifier
bodies, everything higher-order.

Example: `lo ka se klama` →
`(λ {$x :: Referents Entity} (Close (klama :2 $x)))`.

References: [Spec §4.4](spec.md); [primer ch. 8](primer.md).

### 1.14 `bind` (and the `Bind` word)

The computation carrier's sequencing operation
`bind : Comp<A> × (A → Comp<B>) → Comp<B>`: run the computation once,
sequencing its effects before the continuation, and pass its result.
This differs from sharing a computation value. The pure fragment retains
β-equality; explicit bind nodes expose sequencing and scope. Uniform across the
computation categories at one carrier, with an explicit effect join:
`RefComp` may sequence into content, reference, or performance; a
`PerfComp` operand keeps the result performance-level and cannot disappear
inside Content. A bare act body stands for its performing one-act discourse
(§7.1's display coercion), so a
referent introduced before an act sequence stays bound across it. The
surface form `(Bind {$x :: T} comp body)` is a direct effectful binder;
its denotation applies carrier `bind` to `comp` and the scoped body
continuation, of model-level shape `λx. body`. An existing suitable function
can be used through `(k $x)` as the body. Naming is ordinary binding;
sequencing additionally carries each returned value's state and obligations.
Forming the term does not run it. The model equation is not a new core
operator or term-language desugaring; spec §5.2 labels its alternative
`Run`/suspension illustration explicitly as hypothetical.

Content-word status: Both carrier `bind` and the direct `Bind` form
are Class M structural machinery. A predicate may describe a binding or
its result, but does not sequence the computation.

Use: Cross-sentence reference: `(Bind {$cat :: Referents Entity}
(Refer mlatu-prop) (Do (Assert …) (Assert …)))` — the
introduction runs once, the witness is reused in both acts.
Multi-binding `Bind` is left-to-right nesting (spec §5.2).

References: [Spec §5.2](spec.md); [primer ch. 4](primer.md);
[rationale §1.14, §2.4](rationale.md) (sequencing, lambda continuations,
and state-based alternatives).

### 1.15 Lexical predication

Dictionary words (`klama`, `gerku`, …) are relation
constants over their labelled rows, with the row, defaultability,
scope policy, plurality and constitution behavior (including admissible
basis/`ContributionBasis` clauses), meaningful deletions, and the rest
supplied by the lexicon interface. The core is parameterized over the
lexicon; a predication applied to fills for its row is `Content`.

Use: Every bridi. `(Close (klama Speaker This))` — the remaining
places handled explicitly by `Close`'s contextual slots (or by λ or
`DropPlace`), never silently.

References: [Spec §4.1, §10](spec.md); [primer ch. 1](primer.md);
[rationale §2.6](rationale.md).

### 1.16 `DropPlace`

`(DropPlace R n)` is the relation with place `n`
*removed* — semantic surgery, not omission: the resulting relation has
no such role at all. Which deletions are meaningful, and what the
deleted role's absence means, is stated per entry in the lexicon.

Use: `zi'o`. `mi klama ti zi'o` predicates a four-place going with
no origin role — something neither `zo'e` nor closure can say. Also
`voi` = `(DropPlace skicu 3)` (no audience role).

References: [Spec §4.3](spec.md); [primer ch. 1](primer.md), on omission,
deletion, and quantification; [rationale §1.8](rationale.md).

### 1.17 `¬`, `∧`, `∨`, `→` — the dynamic connectives

Classical truth conditions plus a normative
accessibility row each: `∧` passes introductions left to right and
lets both survive; `∨` keeps them branch-local; `¬` lets nothing
escape; `→` feeds the antecedent's introductions to the consequent and
exports nothing. The rows are part of the meaning. (`⊤` — the
trivially true content, `∧`'s unit, spec §2 — is the defined empty
conjunction, not a further primitive.)

Use: `ganai da mlatu gi da ciska` (conditional anaphora), `.ija`
(branch-local), `naku` (blocking) — three policies no truth table
derives.

References: [Spec §4.5, §5.4](spec.md); [primer ch. 4](primer.md);
[rationale §1.5](rationale.md).

### 1.18 `↔`, `⊕` — biconditional and exclusive-or

Once-per-operand evaluation of biconditional and exclusive-or,
with internal introductions kept local. Direct classical expansions duplicate
evaluation and may change site or handler structure. Sharing inert content
preserves that value but not the result of its evaluation; Content returns
Unit, not a reusable Boolean. No equivalent expansion using the existing
forms is established. The core retains these restricted operators rather
than adding general truth-capture reflection solely to define them.

References: [Spec §4.5, §5.4](spec.md); [rationale §1.5](rationale.md).

### 1.19 `∀`, `∃` — the logical quantifiers

Classical quantifiers over typed λ-bodies with
(multi-parameter) joint loci; restrictorless, domain-unrestricted
(`da` — pin P20). The restrictor position of derived quantifiers is
pure; body introductions are local per instantiation; exporting
quantifiers are built from selections, not from bare `∃`.

Use: `ro da zo'u …` and the joint loci selected by strong donkey readings.

References: [Spec §4.5, §5.6](spec.md); [primer ch. 4–5](primer.md).

### 1.20 `=` — typed equality

Primitive identity at every first-order sort and at the
discrete index types (`Bool`, place labels, the closed
enumerations); never at the plural reference type, where co-reference
(`CoRef`, mutual `Among`) does the work; plural-sumti `du` lowers to
`CoRef` (P23).

Use: `li re su'i re du li vo`; `ko'a du ko'a` reflexively true
under keyed retrieval (pin P16) — at `CoRef` when the referents are
plural.

References: [Spec §4.5, §4.8](spec.md).

### 1.21 `Combine`

Plural join: the reference to these-and-those
together. Associative, commutative, idempotent. With `Among` it is the
whole plural algebra: no atomicity, no covers, no distributivity
assumptions.

Use: `jo'u`. `mi jo'u do` = `(Combine Speaker Audience)`.

References: [Spec §4.8](spec.md); [primer ch. 3](primer.md);
[rationale §1.7](rationale.md).

### 1.22 `Among`

The subreference order: these are some of those.
Axiomatized with `Combine` (`Among x y` iff `Combine x y` and `y`
co-refer). Singulars lift to singleton references, so `Among x r` with
`x` a unit reads "x is one of r".

Use: `me`-style membership talk (`ko'a me ko'e`), `Distrib`, L3.9's
outer-count individual membership lift, and the subreference-monotonicity criterion of the
lexicon's plurality field.

References: [Spec §4.8, §10](spec.md); [rationale §1.7, §2.8](rationale.md).

### 1.23 `SetOf`, `Card`, `∈`, and the arithmetic base

Extensional set comprehension over a *pure* property;
membership; finite-set cardinality (`Card : Set<T> ⇀ Cardinal`); and the number
operators `+ − × ÷ < ≤` (with `>`/`≥` defined), partial operations
carrying projective definedness conditions.

Use: Mathematics (`li`, `mekso`), the global readings
(`GlobalExactly`, `Most`), and `UnitSet`-based counting.

References: [Spec §4.9](spec.md); [primer ch. 5](primer.md).

### 1.24 `Refer`

Introduce a new discourse referent: a nonempty
plurality satisfying the given property veridically, fixed for its
force segment, accessible to later anaphora per the table. No implicit
quantifier, no uniqueness, no default cardinality (xorlo, pin P1).
It may have declared Skolem-like dependencies on bound values (P41). A binding
stays fixed in its continuation; a dependent binding must be inside its required
governors. Fixed reference does not mean universal governor invariance.

Use: `lo`/`le`/`la` descriptions. `lo mlatu cu blabi .i ri jbena` —
the cat outlives its sentence and survives negation.

References: [Spec §5.3](spec.md); [primer ch. 3](primer.md);
[rationale §1.3](rationale.md).

### 1.24a `Local`

Run one `RefComp<A>` normally and return the same branch
value, truth filtering, contextual choices, and projective obligations, while
projecting away only discourse-reference slots freshly introduced inside it.
The value remains available to an enclosing `Bind`; later anaphora cannot see
the hidden introduction. It cannot take `PerfComp`, hide an act, or make an
effectful computation pure. Generic lowering infrastructure, not surface-
reachable.

Use: The internal base of every group/set descriptor:
`(Local (Refer P))`. CLL 6.52's `ri` then sees `lo'i ratcu`'s set, not an
invisible second rat reference.

Status: Class O; lowering-only.

References: [Spec §5.2, §5.4, §11](spec.md); [rationale §1.7](rationale.md);
[samples §3](samples.md).

### 1.25 `Context`

Retrieve a contextually salient value of the declared
type: nothing asserted, nothing introduced. The occurrence has one intended
value; a listener is expected to recover a value equivalent enough for the
discourse purpose, not an identical private articulation. A site may carry a
pure admissibility constraint and an explicit dependency profile; it covaries
only with the listed binders and never all enclosing governors by default.
Every externally bound variable free in the constraint must be listed; an
omission is ill-formed, while extra dependencies may express covariation not
mentioned by the constraint.
Site/key identity gives one retrieval per site/dependency tuple per
performance; keyed uses retrieve once per key. A failed exact guess may be
repairable, while failure to recover any discourse-sufficient value leaves no
resolved reading.

Use: Omitted places, `zo'e`, `co'e`, `do'e`, `zu'i`, tanru links,
`tu'a`, bare `jai`, topics, contrast domains, salient scales, and episodic
tenseless time (pin P8/P14/P26).

Example: `mi klama` — the destination is a `Context` slot; `mi na
klama` denies going *there*, not existence of a destination.

References: [Spec §5.3](spec.md); [primer ch. 1, ch. 9](primer.md);
[rationale §1.3](rationale.md).

### 1.26 `Vague`

Denote the nonempty family of admissible
sharpenings of one soritical concept or boundary, with *no fact of the matter*
fixing one cutoff. Arbitrary discrete alternatives do not form a `Vague`
domain. Composition is by the VC law: pointwise
lifting, one precisification per parameter per binding site, truth
simpliciter as supertruth. Never resolved by context, never coerced.

Use: Soritical thresholds (`so'i`), gradable cutoffs, `ji'i`
tolerance/rounding boundaries and loose temporal/spatial extents. A neutral
region may instead be exact; ji'i equality/cardinality and profile completion
remain explicit adequacy obligations.

References: [Spec §5.3, §6](spec.md); [primer ch. 9](primer.md);
[rationale §1.3](rationale.md).

### 1.27 `SelectExactly`, `SelectAtLeast`, `SelectAllBut` — the primitive selections

The quantifier-strength members of the `Refer`
family: introduce a witness reference of the stated cardinal strength,
with the restrictor pure and the declared strength floor n ≥ 1 (spec §12).
Reference nonemptiness alone does not imply positive counted units.
The witness laws: `(CoveredBy P w)` holds, and
`(CardBasis w P)` is `= n` (`SelectExactly`) or `≥ n`
(`SelectAtLeast`). A selection under a governing
quantifier is *dependent* — one witness per value of the governor (the
dependence law). A supported strong dependent-anaphora reading selects and
lowers to a joint locus over that dependency; this is not an equivalent
rewrite of the selection computation. Reference may also depend on governors; any claimed replacement must preserve
the actual witness, scope and export laws, not invoke a false invariant-Refer
premise. Binding a witness never
re-evaluates a selection; distinct selections introduce distinct
discourse referents (introduction identity — the witness values may
still co-refer). `SelectSome` is defined (§2.22).

Use: Explicit plural/core-helper comparisons select a three-dog witness
and predicate running of it neutrally; they are not the standard mapping of
`ci gerku cu bajra`. Standard finite numerals count individual qualifiers
globally. P43 retires P42's automatic outward numerical-group export;
explicit bindings retain their actual scope and correlation.
`SelectAllBut n P` is the library complement-selection member, not the
standard `da'a n` lowering. Its witness satisfies `CoveredBy P w` and
leaves exactly n P-individuals behind, spelled by `SetOf`
comprehension (spec §12); the omitted individuals are not a
parameter. Standard finite pure `da'a n` instead counts exactly n P-members
that fail Q (`GlobalExactly n P (λx.¬Qx)`, spec L5.4; default n = 1),
without introducing a selected remainder group.

References: [Spec §5.6, §4.10](spec.md); [primer ch. 5](primer.md);
[rationale §1.6](rationale.md).

### 1.28 `Presuppose`

Impose a projective condition: it must hold at the
nearest boundary that can commit it (or be accommodated there), and it
survives negation, disjunction, conditionals, and question force.
Introductions inside the condition stay local to it. Polymorphic over
the computation categories —
`Presuppose : Content × Comp<A> → Comp<A>`; see catalog §2.10 for MaxRefer.

Use: Explicit `MaxRefer` import, definedness of partial operations and
lexical presuppositions. Bare `ro` does not import under P2; do not use its
external negation as a presupposition example.

References: [Spec §5.5](spec.md); [primer ch. 5](primer.md);
[rationale §1.4](rationale.md).

### 1.29 `Supplement`

Commit a side content about an anchor while the
at-issue value passes through: new information, speaker-committed,
projecting past negation and question force. Dependent sides commit
per instantiation inside their binder. Not interchangeable with
presupposition: supplements always commit anew.

Signature: The permitted inert-anchor/computation-category family is
`Supplement<B,A> : B × Content × Comp<A> → Comp<A>`, with structured Content
preserved when that is the body. Anchor and side must be in scope at the handler.

Use: `noi` and content-level indicator display; general SEI/TO/ti'o dispatch
is still a separate gap, not arbitrary text cast to one Content.
`xu lo gerku noi blabi cu melbi` questions beauty, never whiteness.

References: [Spec §5.5, §7.6](spec.md); [primer ch. 11](primer.md);
[rationale §1.4](rationale.md).

### 1.30 `Generic`

The axiomatic generic quantifier: relate a pure
restrictor and nuclear scope through a normality ordering that may
depend on the nuclear predicate; mode Typical or Stereotypical (the
latter with the Speaker as holder). Not `∀`, not `∃`, no referent
introduced. Its normality structure is axiomatic; further generic inference
remains in spec §14. Restrictor and nuclear scope are member-level:
`Fn<(T), Content>` and `EFn<(T), Content>` (spec §5.8).

Use: `lo'e`/`le'e`. The maned-lion and birthing-lion generalizations can
use different normality classes rather than one fixed specimen.

References: [Spec §5.8](spec.md); [primer ch. 3](primer.md);
[rationale §1.9](rationale.md).

### 1.31 `Reify` and `Holds`

The one bridge between content and object: `Reify`
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

Use: `du'u`; attitude objects; single-evaluation display
(`Let`-shared `Reify` with `Holds` as the evaluated body). The shape
generalizes row by row to reified predicates — a §9.1 reservation
(registered gap), with the experimental `me'ei`/`me'au` pair as the
attested surface exponents; at the propositional case `me'au` is
`Holds` in selbri position under §9.1's singleton condition
(the `Meau0` schema — singularity projective; no plural baseline
reading).

References: [Spec §9.1, §7.6, §14](spec.md); [primer ch. 8](primer.md);
[rationale §1.10, §2.10](rationale.md).

### 1.32 `TanruAdmissible`

The axiomatized admissibility constraint behind tanru
modification: a relation of the head's row is admissible as the
modification link exactly when it makes the modifier bear on
*something* in the head predication (the event's manner, a
participant, a purpose, …) and nothing stronger — no x1-sharing, no
intersectivity. Context uses this constraint to recover an intended link.
This entry adds no universal nonemptiness or successful-recovery axiom.
The Tanru operator that consumes it is defined in §2.6.

Use: Constraining `sutra klama`'s open modification relation
(CLL ch. 5).

References: [Spec §6.2](spec.md); [primer ch. 9](primer.md);
[rationale §1.8](rationale.md).

### 1.33 `Scalar`

`(Scalar k D P)`, with `D : ContrastDomain<ρ>` and
`k ∈ ⟨OtherThan, Opposite, Neutral⟩`:
deny `P`'s stated region in a contextually recovered `ContrastDomain` *and*
positively assert a directly denoted region — the domain complement
(`na'e`), antipode (`to'e`), or between-region (`no'e`). No fine
alternative is selected; opposite/neutral are projectively partial when the
domain lacks their required structure. Stronger than `¬`, never weaker.
The Lojban mapping binds a lexically fixed or constrained-`Context` D before
applying the pure relation former.

Use: `ta na'e melbi` denies beauty and
asserts membership in the coarse other-than-beautiful region. Also the
`nai`-fallback for unpaired indicators
(`Opposite`).

References: [Spec §6.3, §7.6](spec.md); [primer ch. 7](primer.md);
[rationale §1.8](rationale.md).

### 1.34 `AdmissibleThreshold`, `AdmissibleTolerance`, `AdmissibleCutoff`, `InRegion`, `deg_R`

The gradable/vague-quantity interface. AdmissibleTolerance
and AdmissibleRounding name the unfinished ji'i tolerance/rounding interfaces;
their old Number-valued point-family signatures are superseded, not operative
axioms. P37 instead constrains exact values inside a pure claim at each vague
tolerance profile; equality remains exact and an actual count is tested against
the constraint. The typed profile/composition/retention realization remains work.
The threshold predicates serve the library degree helpers (indexed by
the closed `ThresholdKind` enumeration — `ManyK | FewK | TooManyK |
TooFewK | EnoughK`, an index type unrelated to the rejected `Kind`
sort) and gradable
scale regions (each nonempty by axiom, discharging the `Vague`
formation obligation), the region-membership relation
`InRegion : Amount × Region<Scale> → Content`, and the per-relation
degree projection `deg_R : Record ρ × Scale → Amount` declared by a
gradable entry's lexicon row (`GradableRel<ρ,ℓ>` classifies such
entries by their graded place ℓ).

Use: `so'i`, `du'e`/`mo'a`/`rau`, `ta barda` via `Grade`.

References: [Spec §6.4, §10, §12](spec.md); [primer ch. 9](primer.md).

### 1.35 `Assert`, `Ask`, `Command`, `Express`, `Vocative`, `Mention` — the force constructors

Turn content (or a query, or an addressee, or any
value) into a first-class act of the corresponding force: assertion,
question, directive, expressive display, address, and use/mention
display of a value. Constructing performs nothing.

Use: One content under four forces: `do klama` / `xu do klama` /
`ko klama` / displayed. `Mention` is a genuine display act. A fragment value and an illustrative
Mention wrapper are distinct; bare sumti do not acquire this force automatically.

References: [Spec §7.1](spec.md); [primer ch. 6](primer.md);
[rationale §1.11](rationale.md).

### 1.36 `Perform` and `Do`

`Perform` injects an act into the performance level —
at explicit `OccurrenceRole` (unary `Perform a` = `Perform Host a`), first
creating a fresh `ActOccurrence` under `CurrentToken`, then running the
force payload under that occurrence's capture, handling projectives, and
applying the force's commitment effects; its `PerfComp` result is the opaque
occurrence handle, which `Bind` may name. At a `Discourse` position the handle
is discarded through carrier `bind` and empty `Do`;
`Do` sequences performed discourse (flattening, associative, with
its own accessibility row; zero operands is the empty-discourse unit). Act boundaries close force segments:
introductions inside an unperformed act do not escape. Re-performing an act
creates another occurrence; it never changes the package.
In spec §7.1.1's ordinary-assertion fragment, terminal T/F/U payloads all
return the occurrence and reached scope-eligible state; the original status
remains recorded. Local scope projection and cumulative acceptance are
separate: later truth does not erase earlier falsity. The other-force,
guard/accommodation and full-model exclusions remain explicit.

Use: The discourse spine; `.i` sequencing.

References: [Spec §7.1, §5.4](spec.md); [primer ch. 6](primer.md).

### 1.36a `PerformSource` — source-preserving assertion binder

Class and scope: Lowering-only direct primitive; no ordinary term-language
expansion is claimed. Its necessity is the combination of strict `Bind`, a
possibly valueless source and a later actual assertion that still occurs.
No new source-result/null-reference or world/lineage type is introduced.

Formation: `PerformSource Host [x::R] S (Assert C1)
[read::RefComp R] [o::ActOccurrence Assertion] D`, for R = Referents<T>:
S is RefComp<R>; only C1 sees x; only D sees read/o. Host omission is
shorthand. S is independent of all three binders.

Meaning: Prepare one permitted description source and perform one Host.
One internal read preserves the original source result: the first payload is
F on an empty source and U on an unresolved one; on an obtained reference it
runs the original assertion frame. The later read returns that same reference
or U if absent.
Each read preserves its caller's state and repeats no source effects. One
shared Act and captured Content have interpretation-dependent denotations,
not independently reselected references or separately selected projections.
The ordinary assertion-return law retains eligible prefixes and reached
legal sides even after F/U; full-model embedding remains owed.

Scope: One exportable description; supplied pure restriction and finite
source alternatives with established scope/side premises. Not general
multi-source failure, stronger whole-source intension, other forces or a
completed Comp/quotient model. A no-return Bind's event is partial, not an
invented holding state. PR91 encodes formation and typing, not general
source-family execution or the full semantic model; see decisions.md.

References: [Spec §7.1.1, L8.13, §14](spec.md), [rationale §1.14a](rationale.md),
[samples §12.1](samples.md), [primer ch. 6](primer.md).

### 1.37 `NewTopic` and `Resume`

The `ni'o`/`no'i` transitions,
`Discourse → Discourse`: discourse-structural operations with no
truth conditions but with stated effects on the information state's
segment structure — `NewTopic` suspends the current discourse segment
onto the suspended-topic stack and opens a fresh one (keyed `Context`
retrievals are per-segment, so keys re-retrieve; segment-bounded
text-to-reading rules like `ki` stickiness and `go'i` reach reset);
`Resume` pops the most recently suspended segment and reopens it.

References: [Spec §7.2, §5.1, §5.3](spec.md).

### 1.38 The sign constructors

`(OpaqueQuote text)` — unparsed quoted text
(`lo'u…le'u`, `zoi`); `(StructuredQuote entry)` — a transcript entry
carrying an unperformed act (`lu…li'u`; the entry operand is a pure
token-description property, §2.27, and the constructor supplies the
opaque boundary); `(NameSign text)`,
`(WordSign text)` (`zo`), `(LetteralSign text)`,
`(SentenceSign content)`. All build `Sign<K>` values; all boundaries
are opaque to dynamics.

Use: Quotation, names (`Named` goes through `NameSign`), letteral
signs, `me'o` expression mention.

References: [Spec §7.5](spec.md); [primer ch. 10](primer.md).

### 1.39 `InterpretContent` and `InterpretAct`

The explicit, typed interpretation crossings from
signs (`la'e`; `lu'e` is the inverse sign-of): a sign to the content
or the act it expresses. `InterpretAct<F>` is a force-indexed
*partial* family — defined exactly when the sign's realized (or
intended) act has force `F`, since a sign does not carry its force. On
transcript entries, `InterpretAct` yields the realized act;
`InterpretContent` is defined exactly when that act is an
assertion (the raw `ActContent` projection — a quotation's `Realizes` fact is
not a performance occurrence and does not invoke `RealizedContent`; the sign's
own intended utterance context still governs its interpretation, not the later
caller's); a question, directive, or
expressive entry has no content projection and interprets only as an
act. `InterpretContent(SentenceSign(c)) = c` at the constructor-defined
Sentence kind; this is not a Structured-to-Sentence coercion.

Use: `la'e lu mi klama li'u` — the content, not the sentence.

References: [Spec §7.5, §16.3](spec.md); [primer ch. 10](primer.md).

### 1.40 The token and sign fact relations

The vocabulary for talking about utterances and signs
as objects — ordinary assertable relations, placeholder content words
under the §16 program. Signatures (u an `UtteranceToken`, s a
`SignToken<K>`, each relation `Content`-valued): `SpeakerOf u
speaker`, `AudienceOf u audience` (both at `Referents<Entity>`);
`LocutionOf u locution` (token first, with locution at
`Referents<Locution>` — the §12 anchoring clause's order);
`DeicticTimeOf u t`
(`Time`); `DeicticPlaceOf u l` (`Location`); `TextOf u|s text`
(`Text`); `Realizes u a` (`a` an act value of whatever force — the
force index is existential; this fact alone does not say the act was
performed); `Utters agent u`; `Quotes s x` (`x` the
quoted material: a sign or `Text`); `Denotes s x` (`x` a value of any
sort — denotation is sort-polymorphic).

Use: Transcript entries, reported speech, the `le`-anchoring
clause (the describing event is this utterance's locution). Performed
association lives in the model's `ActOccurrence` transcript; this separation
is why quoted entries can carry `Realizes` without acquiring
`RealizedContent`. Each `Perform a` entails `Realizes(CurrentToken,a)`, but
not conversely.

References: [Spec §7.4–7.5, §10–11](spec.md).

### 1.41 `Deictic`, `ShiftedGround`, `InContext`, and the context projections

The utterance context is a typed record (speaker,
audience, time, place, ground, current token/span) with projections `Speaker`, `Audience`,
`Now`, `Here`, and `CurrentToken`. `Deictic` picks referents at a proximity against a
ground; `ShiftedGround` *constructs* a ground from a description
(never a contextual resolution); `InContext` evaluates content with
deictic projections from a given ground — the explicit context shift
(`ra'o`), currently the sole member of the index-shift family.
`CurrentToken` associates each `Perform` with its occurrence and is the model
value surface `dei` binds; it is not a global last-utterance constant.
Its `SpeakerOf`/`AudienceOf`/deictic time/place facts cohere with the matching
context projections.

Use: `mi`/`do`, `ti`/`ta`/`tu` (via the defined demonstratives),
narrative perspective shifts.

References: [Spec §5.1](spec.md); [rationale §2.3](rationale.md).

### 1.42 `Polar`, `OpenQ`, `QuestionOf`, `Answer`, and the answer selections

`(Polar c)` is the two-valued query (`Yes ↦ c`,
`No ↦ ¬c`); `(OpenQ f)` the open query whose answer-content function
sends each domain tuple `a` to `f a…`; `QuestionOf` reifies a query as
an embeddable `Question` object. `Answer` applies a query's
answer-content function to a selection: `(PolarAnswer Yes|No)`,
or `(TupleAnswer a)`. Baseline answerhood adds no completeness marker
(pin P9): `MentionSome` is removed as an inert duplicate, and `Exhaustive` is
gap-registered until a pure answer function and typed answer-domain
membership/equivalence make its proposed completeness clause meaningful.

Use: `xu`/`ma`/`mo`/`fi'a`/`pei` questions; `kau` answerhood via
the defined `ContextualAnswer`.

Status: Rationale §1.11a explains the shared interface and the remaining
necessity/reduction comparison for its individual primitive constructors.
Their current status is retained, not proved irreducible by this entry.

References: [Spec §8](spec.md); [primer ch. 6](primer.md).

### 1.43 The abstraction relations

CLL's non-event abstractors are named relations with
labelled rows, parameterized by the abstracted content; reference
applies *outside*, so gadri, quantifiers, and relative clauses work on
abstractions through the ordinary rules. The rows (each `(XRel c) : PredTerm⟨…⟩`, every
place at `Referents<·>`): `NiRel` ⟨x1: Amount, x2: Scale⟩ (`ni`);
`JeiRel` ⟨x1: TruthValue, x2: Epistemology⟩ (`jei`); `LihiRel`
⟨x1: Experience, x2: Entity — experiencer⟩ (`li'i`); `SihoRel`
⟨x1: Concept, x2: Entity — mind⟩ (`si'o`); `SuhuRel`
⟨x1: AbstractNature, x2: Entity — category⟩ (`su'u`); `PuhuRel`
⟨x1: Process, x2: Eventuality — stages⟩ (`pu'u`); `ZuhoRel`
⟨x1: Activity, x2: Eventuality — repeated actions⟩ (`zu'o`). Event
abstraction (`nu` and its sort refinements) is `Refer` over the inner
`ClauseContent`, whose effects retain their written sites; `ka` is λ;
`du'u` is `Reify`; `DuhuRel` is derived
(defined section). Where the §16.5 audit records a combinator fit
(`klani` for `NiRel`, `se lifri` for `LihiRel`, …), that is a
committee-pending adoption plan: upon adoption the relation becomes a
defined form over the adopted word; until then it stands primitive —
content-word status and term-language status are independent axes.

Use: `lo ni mi klama cu barda` — an amount, referred to like
anything else, its scale a contextual slot.

References: [Spec §9.2](spec.md); [primer ch. 8](primer.md);
[rationale §1.10](rationale.md).

### 1.44 `AmountValue` and `EventOfContent`

The named adjacent-sort crossings (pin P13 allows no
implicit ones): `AmountValue : Referents<Amount> × Referents<Scale> ⇀
Number` — an amount's numeric value on its scale (`mo'e`; CLL 11.5),
defined projectively at singleton amount and scale references;
and `EventOfContent : Content →
Referents<Eventuality>` — the inert projection of a clause's event
intension. Direct closure projects its selected lexical witness. Content
conjunction projects the joint of the operand events; ClauseAnd uses the
separate holding-state route. Disjunction is branch-relative, and negation
projects a negative holding State. Projection does not evaluate its operand.
No-return Bind coordinates have a partial event intension; reconciling this
with the declared term signature remains a spec §14 obligation.
P38 removes the unestablished numeric `jei` crossing from the baseline and
records its exact `TruthValueDegree` proposal in the gap register.

References: [Spec §9.2–9.3, §13–14](spec.md); [rationale §1.10, §1.15](rationale.md).

### 1.45 `MetalinguisticallyDefective` and the named value enumerations

The objection relation behind `na'i` (a prior
utterance or act is defective in a contextually recovered dimension),
with `DefectKind` (wording, form, implication, presupposition,
register) declared beside it; the evidential `BasisKind` enumeration
(`Observation`, `Hearsay`, `CulturalKnowledge`, `InternalExperience`,
`Expectation`, `Opinion`, `BareAssertion`); and the intensity-scale
regions (`Intense`/`cai`, `Strong`/`sai`, `Moderate`/unmarked,
`Weak`/`ru'e`, `Neutral`/`cu'i`).

References: [Spec §7.3, §7.6](spec.md); [primer ch. 7](primer.md).

### 1.46 The placeholder lexical relations

Relations the core uses that await their Lojban
content words under the §16 program. The indicator relations —
`Happiness`, `Unhappiness`, `Desire` : experiencer × `Target` ×
intensity region → `Content`, and
`EvidentialBasis` : experiencer × `Target` × `BasisKind` → `Content`
(`Target` the closed union of §7.6: a `Proposition` — content targets
go through `Reify` — an act value, an opaque `ActOccurrence` handle, a plural
reference, or a sign) —
with the §16.5 audit mapping them to the `-nmo` indicator-emotion
family (*indicator* `zei cinmo`: `uinmo`, `u'inmo`, `le'onmo`, …, the
generic `inmo`; one word per indicator, mechanically extensible to
every UI and both `nai` poles) as its sole near-fit — the unofficial
rows carry experiencer × target, and the intensity place is the
proposed extension; the emotion gismu (`gleki`, `badri`, `djica`, …)
are see-alsos. The discourse
relations — `Contrast`, `Addition`, `Parallel`, `Elaboration` : two
performed `ActOccurrence` handles → `Content` by default, with raw act
values available as explicit metalinguistic alternatives (audit: `frica`/`simsa` for contrast and
parallel). The named tanru-link precisification constants —
`MannerLink`, `MaterialLink`, `PurposeLink`, `SourceLink`,
`InstrumentLink`, `ResemblanceLink` — each a relation of its head row
satisfying `TanruAdmissible` by construction, shadowed by the BAI
gismu (`tadji`, `marji`, `mukti`, `krasi`, `pilno`, `simsa`); an open
family — a resolved reading may name links beyond these six.
PascalCase marks exactly this placeholder status; as with §1.43, a
recorded fit becomes a definition only when the committee adopts it.

References: [Spec §7.6, §7.2, §12, §16.5](spec.md);
[primer: feelings and evidence](primer.md#7-feelings-and-evidence); the indicator instances appear in
[samples §7, §11](samples.md).

### 1.50 `InnatelyCapable` and `MotionVector`

Two lexically grounded primitives declared with the
§12 helpers they serve. `InnatelyCapable : ClauseContent → Content` —
the clause event property is realizable in worlds compatible with the
relevant participants' innate natures, with roles supplied by its lexical
predication (the CAhA base). `MotionVector :
Referents<Eventuality> × Referents<Entity> × Referents<Entity> →
Content` — the `mo'i` heading: the event carries the mover's `muvdu`
motion in the `farna` direction.

Use: `ka'e` (via the capability forms, §2.21) and the `mo'i`
motion tags.

References: [Spec §12, §11](spec.md).

### 1.51 `TopicAdmissible` and `TopicResolution`

The typed interface for `zo'u` topic-comment (P26):
`TopicResolution<ρ,T>` is the closed union indexed by the comment's
row and the topic's sort — fill an unfilled compatible place
(`PlaceFill ℓ`, ℓ : `CompatibleLabel<ρ,T>` — the refinement that
makes the fill branch type statically), or
bear `srana`-aboutness to the closed comment (`About`) — and
`TopicAdmissible` is the axiomatic admissibility predicate over
resolutions, `TanruAdmissible`'s sibling. The `Topic` schema retrieves one
intended resolution through constrained `Context`: CLL 19.4's fish has
distinct eater/eaten `Context` resolutions, while `About` is the available
coarse intention. Place filling is defined only for a single open bridi;
cross-clausal place-linking is a gap.

Use: `le finpe zo'u citka`.

References: [Spec §12, §11](spec.md), pin P26.

### 1.52 The MOI relation families

The existing displayed numerical rows (CLL 18.11):
`MeiRel κ n` (κ hoisted from a
constrained `Context`; group completely
constituted through `CompleteGunmaAt` from an n-membered set, members among
it; comparison set for
objective-indefinite n; by-standard for subjective), `MoiRel n`
(n-th under a pure `Ordering<T>`, Context-recovered), `SiheRel n`
(typed portion), `CuhoRel n` (opaque probability, 0 ≤ n ≤ 1, the
model's measure — P29: no probability calculus), `VaheRel n` (scale
position via the degree projection). Lexical families, not term
expansions.

Use: `lei mi ratcu cu cimei`; `ti pamoi le'i mi ratcu`.
That Group instance is not all adopted mei coverage: direct-reference positive
mei and a separate exact set-count x2-only row for every Natural n are selected
contracts awaiting construction. A supplied sole empty Set is countable at zero;
this neither repairs a false full-member-cover row nor invents empty Referents.
Nonnumeric moi uses the selected typed correspondence direction, with actual
rows still owed (spec §14/Q15.g).

References: [Spec §12, §11](spec.md), pin P29.

### 1.53 The declared partial projections and crossings

Declared, definedness projective (§5.5):
`RealizedAct<F>` / `RealizedDiscourse` (the act or act-sequence a
transcript token/span realizes — utterance anaphora's crossing, P28)
with the total, inert `ActContent` (an assertion package's raw content),
and partial, inert `RealizedContent` (the structured Content captured by the
one eligible performed, context-resolved host assertion occurrence
selected by transcript attachment/role; associated displays do not compete).
`RealizedContent` is surface-reachable through default pro-bridi
reuse and assertion-content `la'e` over utterance anaphors; `ActContent` is
the raw route used by quotation interpretation and as the source template for
selective `ra'o` re-resolution. Both are Class O content projections;
the opaque `ActOccurrence` handle/capture interface is separately Class M,
lowering-only generic infrastructure;
`During` (an eventuality's temporal extent within an interval — the
ROI count schema's restriction, P35); and
the MEX conversions `RelToOp<ρ>` (`na'u`, at Number-rowed relations,
functional in x1), `OpToRel` (`nu'a`, total), `OperandToOp` (`ma'o`,
computation-typed: the function is a `Context` recovery — P36),
`AmountOperand<ρ>` (`ni'e`,
the Number-result computation at a Number-rowed relation). `se` on
operators is pure argument permutation.

References: [Spec §7.4, §12, §11](spec.md), pins P28, P36.

### 1.54 `EnumerationOrdinal`

MAI's declared display relation: the
attachment-selected constituent bears ordinal n in a
`SequenceKey`-identified enumeration at the closed
`EnumerationLevel` (`Item` for `mai`, `Section` for `mo'o`);
non-at-issue — placed by §7.6's machinery (`Supplement` at a
constituent target, `Express` beside an act-level target); no
temporal ordering of denoted events implied (CLL 19.7 numbers sumti
inside one bridi).

Use: `mi klama pamai le zarci .e remai le zdani`.

References: [Spec §12, §11](spec.md).

### 1.55 `ContrastDomain<ρ>`, `ContrastRegion<ρ>`

The typed domain interface against which a row-ρ predicate
occupies an associated `ContrastRegion<ρ>` for scalar contrast. Neither type
is a first-order set or a group of predicate terms. A domain interpretation
supplies its relevant universe, the cell occupied by a predicate, region
membership, and relative complement; it may add polarity and betweenness
structure for `Opposite`/`Neutral`. Cell membership agrees with the predicate
inside the domain universe, and complement is exact relative complement, so
`OtherThan` requires no partition into fine alternatives. On a declared polar
pair, opposite is extensionally involutive; the between-region is symmetric
between the poles and disjoint from the opposite pole. These are membership
laws, not an undeclared equality on region values. The applicable
domain is lexically fixed or retrieved through constrained `Context`, and
soritical boundaries inside its regions may remain `Vague`.

Use: `na'e melbi` uses the complement of beauty's region in the intended
aesthetic domain; `to'e` and `no'e` additionally require an antipode or
between-region.

References: [Spec §3.5, §6.3](spec.md); [rationale §1.8](rationale.md).

### 1.56 `JaiRoleAdmissible`

The pure axiomatic constraint behind bare-`jai` raising. For
a host R whose old x1 has sort `Referents<A>` and a resolved raised-sumti sort
T, it admits role relations of type
`Fn<(Referents<T>, Referents<A>), Content>` that relate the promoted
participant to the abstraction moved to `fai`. Ordinary inner-place roles and
exact tag-reduction roles may be admissible; the constraint does not inspect
an abstraction AST. The type is indexed by T and A rather than hard-coded to
Entity/Eventuality, preserving the no-implicit-crossing rule.

Use: Bare `jai rinka`: recover the intended role (commonly agent) between
the raised participant and the hidden cause event.

References: [Spec §6.1, §12](spec.md), pin P14; [rationale §3](rationale.md).

### 1.57 `StateClause`

The primitive holding-state route
`StateClause : Content → ClauseContent`. When applied it evaluates the
at-issue facts relative to its State while running contextual/dynamic effects
exactly once, and makes that State the clause parameter. It returns no truth
value and exposes no syntax. Identity,
mathematics, negation, quantified/generic claims, and non-disjunctive compound
claims need this route; direct lexical episodes use the defined
`DirectClause` instead. Its State may be temporally/spatially unbounded, and
values scoped inside are evaluated relative to it (outside bindings stay de
re).

Use: `ta pu du lo mi zdani`; the negative state of `mi na klama`.

References: [Spec §4.6, §9.3](spec.md); [rationale §1.15](rationale.md).

### 1.58 Constitution bases and their primitive relations

`DecompositionBasis<W,C>` supplies a non-atomic peer-unit
cover for C-components of W-wholes. Primitive `BasisUnitAt` exposes the
cover's units and primitive `PeerUnitAt` the whole's total peer field.
`ContributionBasis<ρ>` is the function-typed sibling: it states per row how a
nonempty `Family⁺<PredTerm<ρ>>` jointly realizes a mixed predicate through
primitive `MixAt`; the basis axioms require `ContributesAt` for every member
and no additional peer contribution. These are typed semantic
interfaces, not first-order sets or inspectable records.

Definition: See spec §4.9 for the unit/cover laws, event trace/participant/
cause obligations, and `GunmaPredAt`'s pointwise `MixAt` condition. Group and
event component arguments remain `Referents<·>`; only predicate components
need `Family⁺`. A basis used by a `joi` construction must preserve every
operand-cover unit in the combined cover; merging granularities are
inadmissible for that operand partition.

Use: The defined constitution relations below; conjunction's canonical
`joint_M` basis.

Status: `BasisUnitAt`, `PeerUnitAt`, `MixAt`, and `ContributesAt`, the
basis formers, event instance, and `Family⁺` are generic infrastructure with
the factorization argument in rationale §1.7a; Class M, so no content word is
owed.

References: [Spec §3.5, §4.9, §10](spec.md); [rationale §1.7a](rationale.md).

## 2. Defined forms

Entries below with an actual expansion are defined acyclically in the core.
Explicitly reserved names such as Additive are not completed definitions;
graph-only interfaces are declared separately.

### 2.1 `PredTerm<ρ>`

The type of relations over row ρ — a transparent alias,
not a new type: relations are row-functions, partial filling is
abstraction over the residual row, and a relation over the exhausted
row is its content.

Definition: `PredTerm<ρ> ≝ Record ρ → Content`, with
`PredTerm<⟨⟩>` applied at the empty record ≡ `Content`.

Use: Keeping labels load-bearing (FA, `zi'o`, `fi'a` all speak in
labels) with the ontology of functions.

References: [Spec §3.3](spec.md); [rationale §1.1](rationale.md).

### 2.2 `At` and the fill notation

The single-place fill: fill place ℓ of relation `R`
with value `v`, yielding the relation over the residual row. All
multi-fill notation — positional fills, `:n` labels, the
continue-after-`n` rule, FA routing, `se`-conversion — desugars to
nested single fills. Distinct-label fills commute (fills are values),
which is why Lojban's free surface order is pure notation. With a
*computed* label (`fi'a`), `At` abbreviates the finite case split over
literal fills.

Definition: `(At R ℓ v) ≝ (λ {$rest :: Record ρ−ℓ} (R ⟨$rest
extended with ℓ = v⟩))`;
`(klama :2 This Yonder) ≝ (At (At klama 2 This) 3 Yonder)`.

Use: `klama fe ti tu`; `klama fi'a ti` at the computed-label case.

References: [Spec §4.1, §4.7](spec.md); [primer ch. 1](primer.md).

### 2.3 `Let`

Pure sharing: bind a value for a body — definable as
immediate application, retained for legibility and for identity of one
value used twice (`goi` aliasing, act targets). Let binds an inert value,
including a supplied computation value. It does not run that computation
or bind its returned result; Bind performs that sequencing. The complete
admission rule for newly written computation expressions in value positions
remains a formation obligation (spec §14), not a reason to infer execution
from a derived checker's static effect record.

Definition: `(Let {$x :: T} v body) ≝ ((λ {$x :: T} body) v)`.

Content-word status: Class M structural machinery: no content word is
owed for this sharing syntax.

Use: `(Let {$a :: Act Assertion} (Assert …)
(Bind {$o :: ActOccurrence Assertion} (Perform Host $a)
(Do (Perform AttachedDisplay (Express (… $o …))))))` — `Let` shares the raw act, while `Bind` names
the one performance occurrence the display targets.

References: [Spec §4.4](spec.md); [primer ch. 7](primer.md).

### 2.4 `DirectClause`, `CloseClause`, `Close`, and clause connectives

`DirectClause` turns an event-licensed row into
`ClauseContent`, contextually filling ordinary omitted places while leaving
the lexical event open. `CloseClause` has the run of existentially closing
that common event interface and additionally retains the local witness as the
closed Content's event. `Close` is the type-directed actual-mode predication
abbreviation; eventless
rows go through primitive `StateClause`. The six `Clause*` connective lifts
preserve the event discipline: conjunction joint state, disjunction branch
event, negation negative state, other Boolean compounds holding states.

Definition:

```text
(DirectClause P) ≝ λe. Bind ordinary omitted places, then P(…, e)
CloseClause : ClauseContent → Content
run(CloseClause(C)) = run(∃e. C(e)); event(CloseClause(C)) = e per branch
(Close P)        ≝ CloseClause(ActualClause(DirectClause P))
(Close (P :Eventuality e)) ≝
  CloseClause(λe'.(CoRef(e', e) ∧ ActualClause(DirectClause P)(e)))
(Close P_eventless) ≝ bind ordinary omissions, then
                       CloseClause(ActualClause(StateClause(P_filled)))

ClauseNot C   ≝ StateClause(¬ CloseClause(C))
ClauseAnd C D ≝ StateClause(CloseClause(C) ∧ CloseClause(D))
ClauseOr C D  ≝ λe.(C(e) ∨ D(e))
ClauseImp / ClauseIff / ClauseXor
              ≝ StateClause of the corresponding closed Content operation
```

Use: `mi klama`; `ta pu du lo mi zdani`; `.i ja` over two clauses.
`Close` is not a surface default: the other resolved CAhA modes use their
own §2.21 formers.

References: [Spec §4.6, §9.3](spec.md); [primer ch. 1–2](primer.md);
[rationale §1.2, §1.15](rationale.md).

### 2.5 `This`, `That`, `Yonder`

The demonstratives, as deictic picks at the three
proximities against the context's ground.

Definition: `This ≝ (Deictic Proximal g)`, `That ≝ (Deictic Medial
g)`, `Yonder ≝ (Deictic Distal g)`, where `g` is the enclosing
utterance context's ground (the `ctx` record's ground projection,
spec §5.1).

Use: `ti`/`ta`/`tu`.

Scope: These fixed-ground abbreviations do not supply the complete
occurrence-sensitive lowering for repeated demonstratives; see decisions Q12.

References: [Spec §5.1](spec.md).

### 2.6 `Tanru`

Modification of a head by a modifier: the head's row,
the head's predication, plus the occurrence's intended admissible
modification link, retrieved by constrained `Context` from the relations
`TanruAdmissible` (§1.32) admits. Convention changes resolver priors; it does
not lexicalize the bare tanru or create a family of truth conditions.

Definition: `((Tanru M H) fills…) ≝ (Bind {$link :: PredTerm ρ(H)}
(Context (λ {$r :: PredTerm ρ(H)} (TanruAdmissible M H $r)) deps…)
(∧ (H fills…) ($link fills…)))`.

Use: `sutra klama` — a goer, with `sutra` bearing on the going
in the way intended here; the library's named links are common exact
recoveries, and a lujvo lexicalizes one.

References: [Spec §6.2](spec.md); [primer ch. 9](primer.md);
[rationale §1.8](rationale.md).

### 2.7 `UnitSet` and `CardBasis`

Basis extraction: the set of P-satisfying units among
a reference, and counting as counting units *under a description*
within a reference — how inner cardinality works, with no canonical
atomic basis assumed.

Definition: `(UnitSet P r) ≝ (SetOf (λ {$x :: T} (∧ (P $x) (Among $x r))))`;
`(CardBasis r P) ≝ (Card (UnitSet P r))`.

Use: `lo ci gerku` — counted as dogs, three; the same plurality
may count differently under another basis (three dogs, one pack).

References: [Spec §4.8](spec.md); [primer ch. 3, ch. 11](primer.md).

### 2.8 `CoRef` and `Overlap`

Plural co-reference (mutual subreference — the
equivalence the plural type uses instead of `=`) and plural overlap
(some common subreference).

Definition: `(CoRef x y) ≝ (∧ (Among x y) (Among y x))`;
`(Overlap a b) ≝ (∃ (λ {$c :: Referents T} (∧ (Among $c a) (Among $c b))))`.

References: [Spec §4.8, §12](spec.md).

### 2.9 `Distrib` and `lu'a`

The marked each-reading: the property holds of every
unit among the reference. `lu'a` is this distribution applied at its
use site. Never a default — unmarked plural predication is neutral
(pin P4).

Definition: `(Distrib Q r) ≝ (∀ (λ {$x :: T} (→ (Among $x r)
(Q $x))))`, `T` the member type.

Use: "each of them", `ro`'s nuclear scope, forced distributive
readings.

References: [Spec §12, §4.8](spec.md); [primer ch. 3](primer.md);
[rationale §2.5](rationale.md).

### 2.10 `MaxRefer`

The maximal base: the reference to *all* the
P-satisfiers and nothing else — every unit is P, every P-satisfier is
among it, every part overlaps a P-unit. Defined only for inhabited P
(a presupposition), with the model required to supply the reference
(plural comprehension).

Definition:

```text
(MaxRefer P) ≝
  (Presuppose (∃ P)
    (Refer (λ {$r :: Referents T}
      (∧ (Distrib P $r)
         (∀ (λ {$x :: T} (→ (P $x) (Among $x $r))))
         (∀ (λ {$r' :: Referents T}
              (→ (Among $r' $r)
                 (∃ (λ {$x :: T} (∧ (P $x) (Overlap $x $r')))))))))))
```

Models must supply this reference for each inhabited pure restrictor
the mapping can form (plural comprehension — a model condition).
Uniqueness up to CoRef is not proved from ACI alone. The selected model contract
uses local least covered upper bounds on admitted extensions; existence and
joint realization remain owed. Model-wide separation is a stronger alternative,
not silently adopted (spec §12/§14).

Use: The witness within the importing library Every's explicit Bind scope,
and explicitly/contextually maximal bases; no automatic baseline ro-group export.
Bare `loi`/`lo'i` use ordinary `(Local (Refer P))` instead (P5).

References: [Spec §12, §11](spec.md).

### 2.11 `Reciprocate`

The reciprocal schema: every two distinct members of
the witness stand in the relation, both ways (member-wise; vacuous on
a unitless reference — mass reciprocity needs an explicit basis).
Consumed by `simxu`'s and `soi`'s lexicon rows.

Definition: `(Reciprocate r P) ≝ (∀ (λ {$x $y :: T} (→ (∧ (Among $x r) (Among $y r) (¬ (= $x $y)))
(P $x $y))))` — `T` the member sort; the units singleton-lift at
`Among` and at `P`'s places.

Use: Pairwise mutual talk of an explicitly bound plural reference. The
three-person selection in samples §5 is a plural/core comparison, not the
standard outer-quantified `ci jbopre` lowering.

References: [Spec §12](spec.md); [samples §5](samples.md).

### 2.12 The cardinal quantifiers

The witness-set family: select a witness of the stated
strength and predicate the nuclear scope of it neutrally — the
each-reading comes from the lexicon or `Distrib`, never from the
quantifier in these reference-level helpers (P4). `Every` is an explicit
importing library universal, not the standard bare-ro mapping:
presuppose the restrictor inhabited and bind the maximal base within its explicit scope,
distribute (`ro` is each). The negative/bounded forms contain their
selection under `¬` and export nothing.

Definition:
`(Exactly n P Q) ≝ (Bind {$w :: Referents T} (SelectExactly n P)
(Q $w))`;
`(AtLeast n P Q)` / `(Some P Q)` likewise over their selections;
`(Every P Q) ≝ (Bind {$w :: Referents T} (MaxRefer P) (Distrib Q
$w))` — the import is `MaxRefer`'s own presupposition; `(No P Q) ≝ (¬ (Some P Q))`; `(AtMost n P Q) ≝ (¬ (AtLeast n+1
P Q))`; `(MoreThan n P Q) ≝ (AtLeast n+1 P Q)`; `(FewerThan n P Q) ≝
(¬ (AtLeast n P Q))`; `(GlobalExactly n P Q) ≝ (= (Card (SetOf (λ {$x :: T} (∧ (P $x) (Q $x))))) n)` (pure operands; standard finite exact count).
Zero floor (spec §12): the selections form only at n ≥ 1;
`(AtLeast 0 P Q) ≝ ⊤` and `(Exactly 0 P Q) ≝ (No P Q)`, with the
bounded forms following from the definitions.

Status: Helper meanings are unchanged. Standard finite exact counts use
`GlobalExactly`, not neutral plural `Exactly`; ordinary su'o/no use
IndividualSome/IndividualNo. Counted No is distinct from P22's uncounted
PluralNo. Core Bind scope does not license implicit baseline group export:
P43 supersedes that P42 policy. General permitted source/force continuity,
experimental mappings and model obligations remain explicit gaps.

Use: Pure standard exact counts; separately marked plural/core comparisons
of selection and same-reference continuation.

References: [Spec §12, §4.10, §5.6](spec.md); [primer ch. 5](primer.md);
[rationale §3 (P17)](rationale.md).

### 2.13 The degree quantifiers

Cardinal comparisons against thresholds that are
`Vague` (and, for the purpose-relative kinds, constrained by a
`Context`-recovered standard): many, few, most, too many, too few,
enough.

Definition: (`θ` a `Vague` threshold; `σ` a `Context` standard;
kinds from `ThresholdKind`, §1.34; `P`, `Q` pure for `Most`.)

```text
(Many P Q)    ≝ (Bind {$θ :: Natural} (Vague (AdmissibleThreshold ManyK P))
                  (AtLeast $θ P Q))
(Few P Q)     ≝ (Bind {$θ :: Natural} (Vague (AdmissibleThreshold FewK P))
                  (FewerThan $θ P Q))
(TooMany P Q) ≝ (Bind {$σ :: Referents Entity} (Context)
                       {$θ :: Natural} (Vague (AdmissibleThreshold TooManyK P $σ))
                  (MoreThan $θ P Q))
(TooFew P Q)  ≝ (Bind {$σ :: Referents Entity} (Context)
                       {$θ :: Natural} (Vague (AdmissibleThreshold TooFewK P $σ))
                  (FewerThan $θ P Q))
(Enough P Q)  ≝ (Bind {$σ :: Referents Entity} (Context)
                       {$θ :: Natural} (Vague (AdmissibleThreshold EnoughK P $σ))
                  (AtLeast $θ P Q))
(Most P Q)    ≝ (> (Card (SetOf (λ {$x :: T} (∧ (P $x) (Q $x)))))
                   (Card (SetOf (λ {$x :: T} (∧ (P $x) (¬ (Q $x)))))))
```

Status: These are reference-level library comparisons. Their standard
individual-count surface adaptation remains the explicit L5.28 gap; a
neutral plural nuclear predicate is not silently substituted for an
individual predicate. Helper binding scope is not baseline outward export.

Export: Few/TooFew export nothing; positive forms export only at profiles
where the inner selection does. Enough at threshold0 is top and exports nothing.
Zero admissibility is per kind/standard, not a blanket ≥2 rule.

Use: The threshold-family comparison underlying vague count talk such
as `so'i prenu cu klama`, subject to that mapping gap.

References: [Spec §6.4, §12](spec.md); [primer ch. 5, ch. 9](primer.md).

### 2.14 `Grade`

Gradable predication with its two parameters exposed:
the relation holds of a row record when its degree on the given scale
falls in the given region — scale recoverable (`Context`), region
boundary `Vague`.

Definition: `(Grade R s reg) ≝ (λ {$rec :: Record ρ} (InRegion
(deg_R $rec s) reg))`.

Use: `ta barda` — big along which dimension is recovered; where
"big" starts has no fact of the matter.

References: [Spec §6.4, §12](spec.md); [primer ch. 9](primer.md).

### 2.15 `Interval`

The set of values between two endpoints, each endpoint
strict or non-strict (`ga'o`/`ke'i`).

Definition: `(Interval a b k₁ k₂) ≝ (SetOf (λ {$x :: T} (∧ (cmp₁ a $x) (cmp₂ $x b))))`.

References: [Spec §12](spec.md).

### 2.16 `ZipWith`

Respective pairing over two lists, by metalanguage
recursion — the `fa'u` analysis, expanding completely into a
conjunction.

Definition: `(ZipWith f (List) (List)) ≝ ⊤`; `(ZipWith f (List a
as…) (List b bs…)) ≝ (∧ (f a b) (ZipWith f (List as…) (List bs…)))`.

Use: `mi fa'u do tavla do fa'u mi` ≡ I talk to you ∧ you talk to
me.

References: [Spec §12](spec.md); [samples §5](samples.md).

### 2.17 `Named`

Bearing a name-sign, through the lexicon's `cmene`
row: the referent is what the name names, the namer contextual.

Definition: `(Named t x) ≝ (Close (cmene (NameSign t) x))`.

Use: `la .alis.` — `Refer` over `(Named "alis" ·)`.

References: [Spec §12, §11](spec.md); [primer ch. 3](primer.md).

### 2.18 `DuhuRel`

The derived `du'u` relation: its x1 is the reified
content, its x2 a sentence sign expressing it (CLL 11.7's x2, `se
du'u`). Derived because `Reify` already carries the crossing.

Definition: `((DuhuRel c) x1 x2) ≝ (∧ (CoRef x1 (Reify c))
(Distrib (λ {$s :: Sign Sentence} (CoRef (Reify (InterpretContent
$s)) (Reify c))) x2))` — x2's signs are those whose interpretation
reifies the same content.

Use: `lo se du'u mi klama` — the sentence, not the proposition.

References: [Spec §9.2](spec.md); [samples §9](samples.md).

### 2.19 `ContextualAnswer`

Bare `kau`'s answerhood: the answer tuple is retrieved
from context, with the exhaustivity slot absent (pin P9) — the weakest
reading, strengthened only lexically or by explicit marker.

Definition: `(Answer q ContextualAnswer) ≝ (Bind {$a :: A} (Context)
(Answer q (TupleAnswer $a)))` at open domains; at `Query<Bool>` the
retrieval is at `Bool` and the selection is `(PolarAnswer $a)` — the
`xu kau` case (spec §8.2).
Explicit-value kau is a distinct selected mapping: consume the supplied value
once and form its typed selection, not a new ContextualAnswer. General
source/effect and query-aware consumer handling remains spec L10.3/§14 work.

Use: `mi djuno lo du'u ma kau klama`.

References: [Spec §8.2](spec.md); [primer ch. 6](primer.md).

### 2.20 `JaiPromote` and `JaiRaise`

Tagged `jai`: promote the tagged role to x1 and move
the old x1 to the labelled, fillable `fai` place (closing contextually
when unfilled — CLL 9.12). Bare `jai` instead fixes raised sort T and old-x1
sort A in the resolved reading, retrieves one intended
`Fn<(Referents<T>, Referents<A>), Content>` role through constrained
`Context`, and uses `JaiRaise` to conjoin that role between the new x1 and the
old x1 at `fai`.

Definition: Writing ρ' for ρ with ℓ relabelled x1 and x1 relabelled
`fai`: `(JaiPromote R ℓ) ≝ (λ {$r :: Record ρ'} (R ⟨ℓ = $r.x1,
x1 = $r.fai, rest unchanged⟩))`. For bare `jai`, ρ' instead replaces x1
by `Referents<T>` and adds `fai:Referents<A>`:
`(JaiRaise R K) ≝ (λ {$r :: Record ρ'} (∧ (R ⟨x1 = $r.fai,
rest unchanged⟩) (K $r.x1 $r.fai)))`; the mapping binds K from
`Context (JaiRoleAdmissible R)` before applying it.

Use: `mi jai gau rinka` patterns; `fai` fills.

References: [Spec §12, §6.1, §11](spec.md).

### 2.21 The CAhA clause formers

Over `C : ClauseContent`, `ca'a` keeps C's event and demands
its world-relative actuality; `ka'e`, `nu'o`, and `pu'i` make the capability
claim's holding State the outer clause event. `Realized` tests whether an
actual C-event exists. Missing CAhA is reading-multiple among these four modes
with no default (P24; CLL 10.19).

Definition:

```text
(Realized C)           ≝ ∃e.(C(e) ∧ fasnu(e))
(ActualClause C)       ≝ λe.(C(e) ∧ fasnu(e))
(CapableClause C)      ≝ StateClause(InnatelyCapable(C))
(UnrealizedClause C)   ≝ StateClause(InnatelyCapable(C) ∧ ¬Realized(C))
(DemonstratedClause C) ≝ StateClause(InnatelyCapable(C) ∧ Realized(C))
```

Use: `mi ca'a citka`; `ro datka ka'e flulimna`.

References: [Spec §5.1, §12, §11](spec.md), pin P24.

### 2.22 `SelectSome` and the individual/plural closure forms

`SelectSome P ≝ SelectAtLeast 1 P` is a counted plural helper, not ordinary
surface su'o and not unrestricted plural existence. `IndividualSome P Q`
expands to ∃x:T.(P x ∧ Q x), and `IndividualNo` negates it.
`IndividualEvery P Q ≝ ∀x:T.(P x → Q x)` names the non-importing closure
shared by bare/restricted ro and their specimens. It is defined, not a new
primitive or an outward witness source. Bare me'i defaults to ro and negates IndividualEvery
on resolved pure individual P/Q (P44), without a finite-cardinality premise.
Explicit me'i pa remains zero; neither truth equation supplies a later RI source.
`PluralSome`
uses r:Referents<T> instead, with no counted-unit floor; `PluralNo` negates
that condition and supplies P22's negative plural frame. These closure forms are
non-exporting truth-condition forms. P43 retains ordinary existential continuity
and independently bound sources without synthesizing numerical/universal groups
or governor-external families. The general Q01 source/force interface remains
unfinished; supported in-scope P6 is retained. P42's old selected-S default
is retired, not a residual fallback.

References: [Spec §4.10, §12, §14](spec.md); [decisions Q01](decisions.md).

### 2.23 `NahiObjection`

The `na'i` act: express, of a bound prior target (normally the
performed occurrence or utterance token; a raw act only when explicitly
intended), that it is metalinguistically defective in a contextually recovered
dimension. Performing the objection does not perform or negate the
objected-to content.

Definition: `(NahiObjection t) ≝ (Bind {$d :: DefectKind} (Context)
(Express (Close (MetalinguisticallyDefective t $d))))`.

References: [Spec §12, §7.3](spec.md); [primer ch. 7](primer.md).

### 2.24 `GroundedBy`

The act-level evidential spelling: bind one performed act's
occurrence handle and display the speaker's basis for that occurrence — a mode of commitment, not
a second claim.

Definition: for `a : Act<F>`, `(GroundedBy b a) ≝
(Bind {$o :: ActOccurrence F} (Perform Host a)
(Do (Perform AttachedDisplay
  (Express (Close (EvidentialBasis Speaker $o b))))))`.

Use: `za'a do cadzu` — the assertion grounded in observation;
negation touches the walking, never the basis.

References: [Spec §12, §7.6](spec.md); [primer ch. 7](primer.md).

### 2.25 `Only` and `Additive` — pure focus and unfinished display adaptation

For pure H and independently resolved relevant alternatives A, both at
`Fn<(Referents<T>), Content>`, and f at that reference type:
`Only A H f ≝ H(f) ∧ ∀y.((A(y) ∧ H(y)) → Among(y,f))`.
Host and exclusion are both at issue; no Presuppose wrapper. Own subparts
are exempt, but overlapping outsiders can compete. The rejected not-Overlap
policy would exempt them; the old not-CoRef formula wrongly excluded own members.
Effectful shared-frame lifting must still avoid duplicate performances and
uncontrolled side effects. Additive remains reserved for ji'a's unfinished
target/lexical adaptation: it separately displays addition without strict novelty.

References: [Spec §12/§14](spec.md); [decisions Q10/Q11](decisions.md).

### 2.26 The COI schemas

Performative expressives: a COI greeting/thanks/… is
constituted by its performance — `Express` of the COI lexical relation
with the performative host-force profile.

Definition: `(COIExpress R addr) ≝ (Express (Close (R Speaker
addr)))`, `R` the COI entry's lexical relation (`coi-greeting`,
`ki'e-thanks`, …), performed with its performative profile.

Use: `coi do` — the greeting is the act.

References: [Spec §12, §7.6, §11](spec.md).

### 2.27 The `Utterance` and `Sign` entry notations

A token variable with facts about it — the transcript
entry `StructuredQuote` consumes, and the same notation at the
sign-token sort. Defined: the λ suspends the facts by nature (nothing
performed, nothing introduced — quoted material introduces no
discourse referents), yielding a *pure token-description property*;
the opacity belongs to the consuming sign constructor, not to this
notation. Performed-level token talk needs no special form — it is
ordinary `Refer` at the token sort.

Definition: `(Utterance {$u :: UtteranceToken} {fact…}) ≝ (λ {$u :: Referents UtteranceToken} (∧ fact…))`; the `Sign` notation likewise
at `SignToken<K>`.

Use: `lu mi klama li'u` → `(StructuredQuote (Utterance {$u :: UtteranceToken} {(Realizes $u (Assert (Close (klama Speaker))))}))`.

References: [Spec §7.4–7.5](spec.md); [primer ch. 10](primer.md);
[samples §6, §10](samples.md).

### 2.29 `te'a`, `gei`, and `xi` indexing

MEX helpers by metalanguage recursion: integer
exponentiation, order-of-magnitude, and subscripting as list
indexing (undefined past the end — a projective definedness
condition).

Definition:

```text
(te'a x 0)              ≝ 1
(te'a x (n+1))          ≝ (× x (te'a x n))
(gei x y)               ≝ (× y (te'a 10 x))
(xi (List a as…) 1)     ≝ a
(xi (List a as…) (n+1)) ≝ (xi (List as…) n)
```

Use: `li re te'a ci du li bi`.

References: [Spec §12](spec.md); [samples §10](samples.md).

### 2.30 `MePred`

`me` as a defined form: the Among-property of a
sumti's referents — `(MePred X) ≝ (λ {$w :: Referents T} (Among $w
X))`, X's computation bound before the pure property forms. The
ratified gadri definitions expand `lo PA sumti` through `me`.

Use: `la .baltazar. cu me le ci nolraitru`.

References: [Spec §12, §11](spec.md).

### 2.31 `TanruLinkConnect`

Jek at the tanru-unit locus (P33): for a shared head,
retrieve one intended admissible link per conjunct through constrained
`Context` and join the link applications
with the connective — the head asserted once
(`blabi ja cmalu zdani`: a house, whose modification link is
white-flavored or small-flavored). Distinct-head units connect as
whole predications. Constitution-bearing `joi` instead uses `JoiTanru` at a
shared head (head once, mixed head-relative links) and `JoiPred` on
already-lowered distinct-head common-row properties; only
missing-row/missing-basis cases remain gaps.

Use: `ta blabi je cmalu zdani`.

References: [Spec §12, §6.2, §11](spec.md), pin P33.

### 2.32 The region formers

The BIhI region formers beyond ordered `Interval`,
all defined by `SetOf` comprehension over a Context-recovered
`Metric<T>` (spec §12): `MetricBall` (`mi'i` — center, radius,
GAhO boundary kind; no endpoint arithmetic), `SpanRegion` (`bi'i` at
metric domains — metric betweenness), `RegionComplement` (`bi'o nai`
— complement in a Context universe). `bi'i` at ordered domains is ⊳
symmetrization of the ordered `Interval` (endpoint order normalized
together with the GAhO kinds). Endpoint/center references take the
projective singular condition (the §9.2 pattern).

Use: `la .uacintyn. mi'i lo minli be li muno`.

References: [Spec §12, §11](spec.md).

### 2.33 `RoiClause`

Count the host ClauseContent's component eventualities in a
reference interval, replacing ordinary clause closure; then make the count
claim's holding State the outer clause eventuality. This keeps “the two
goings” distinct from “the state of there being two goings.”

Definition: `(RoiClause n C I) ≝ (StateClause (= (Card (SetOf
(λ {$e :: Eventuality} (∧ (C $e) (During $e I))))) n))`, after all
surface arguments and contextual effects are bound so the comprehension is
pure.

Scope: State episodes and non-cardinal ROI still need their interfaces;
counting first-order presentations of one state is not counting occasions.

Use: `mi re roi klama`; `roi nai` negates the count before state lift.

References: [Spec §12, §11](spec.md), pin P35.

### 2.34 `GunmaAt`, `CompleteGunmaAt`, `GunmaPredAt`, and the `Joi*` forms

`GunmaAt` matches the supplied basis cover to some of a
whole's peer units. `CompleteGunmaAt` strengthens it by
requiring the supplied cover to contain every peer component at κ.
`ComponentAt` is only its singular non-exhaustive display abbreviation.
`JoiGroup` and `JoiEvent` introduce a complete whole from all flattened
operands; `JoiPred` constructs the intended common-row mixed predicate under a
declared contribution basis; `JoiTanru` asserts a shared head once and mixes
only its intended head-relative links; `JoiClause` evaluates two component clauses once
and exposes their complete joint event as its clause parameter.

Definition:

```text
(GunmaAt κ w Cs) ≝
  ∀u.(BasisUnitAt κ u Cs →
        ∃v.(PeerUnitAt κ v w ∧ CoRef u v))
CompleteGunmaAt κ w Cs ≝ GunmaAt κ w Cs
  ∧ ∀v.(PeerUnitAt κ v w →
          ∃u.(BasisUnitAt κ u Cs ∧ CoRef u v))
ComponentAt κ x w ≝ GunmaAt κ w x       ; x singleton-lifts
GunmaPredAt κ R F ≝ ∀a : Record ρ.(R(a) ↔ MixAt κ F a)
```

`ComponentAt` is formed only for a non-null x; a basis-declared null remains
absorbable rather than becoming an ordinary component of every whole.

The five `Joi*` expansions are displayed in spec §12. Homogeneous chains
flatten; `se joi` is symmetric; no property inheritance follows.

Use: `mi joi do bevri lo pipno`; event-sumti `joi`; `blanu joi xunre
bolci`; the compound event inside `.i joi`.

Status: Defined `GunmaAt` is surface-reachable through `gunma`;
`JoiGroup`, `JoiEvent`, `JoiPred`, and `JoiTanru` are lowering-only;
`JoiClause` is the semantic ingredient for a surface construction whose full
performance remains gap-registered in #6. `GunmaAt` is Class P through the
adopted lexical row; `JoiGroup`/`JoiEvent`/`JoiTanru`/`JoiClause` are Class O,
while pure `JoiPred` and generic `GunmaPredAt` are Class M infrastructure.

References: [Spec §4.9, §11–§14](spec.md); [samples §2–§3](samples.md);
[rationale §1.7a](rationale.md).

## Appendix: model-theory symbols

Not term-language forms — the denotational metalanguage of
[spec §5.1](spec.md), listed so no named symbol goes unaccounted:
The displayed `Comp<A> = InformationState → P(InformationState × A × Obligations)`
is the successful-output carrier interface, not the full failure-aware model.
Spec §7.1.1 adds bounded assertion observation/return laws and leaves their
joint carrier/quotient embedding explicit. (`ContentRun = Comp<Unit>`;
`ClauseEventIntension` is the defined world/assignment/precisification/branch-indexed event
projection; `Content` pairs those two,
`RefComp<T> = Comp<T>`; `PerfComp<T>` is that carrier at the performance
effect vocabulary and `Discourse = PerfComp<Unit>`, while an act value is the pure force-tagged
package the performance boundary injects; every such injection creates a model-level
`ActOccurrence<F>` pairing that package with `CurrentToken` and an extensional
capture of the performance context/resolver; `RealizedContent` projects the
assertion member's captured Content without running it — spec §5.1,
§7.1–7.4); an `InformationState` is a set of
world–assignment pairs over the model's world set W; `Obligations`
collects pending projective commitments; `hold_M` is `StateClause`'s model-
level holding-state operation, while `joint_M` is §4.9's event-level complete
joint at `κ∧`. Event composition uses the operand events; the selected holding-
fusion contract uses the operand holding states and still owes its State-closure/
inheritance/model construction (§9.3/§14). These are two composition laws,
not a requirement for two different joint operators or universally unequal results;
`s ⊩_w c` is the at-issue
verification relation for a State's partial situation; `Unit` is the one-value
return type of contentful computations; and `ctx` is the utterance
context record (speaker, audience, time, place, ground, current token/span) whose
projections §5.1 names. These symbols may change with the model (the
`da'i` gap entry anticipates a world-shift operation) without any term
changing — which is the point of keeping them out of the term
language (rationale §1.14).

## Post-full-pass inventory completions

- **CoveredBy** (defined, §4.8): Distrib P r plus every subreference of r
  overlapping a P-unit. No atom/minimal-lift premise; selection witnesses need
  the full condition, not just Distrib.
- **Massify / CanonicalAggregateAt** (defined, §12): the local reference-level
  restriction returns a reference co-referring with the canonical Group object's
  lift. CardBasis=1 alone did not establish that contract. Construction scope
  preserves dependence; number-neutral group descriptions are not rewritten.
- **components_κ / InRegion** (declared primitive interfaces): model graphs do
  not count as core-term expansions. Group components remain partial without a
  complete cover; the term-defined versus denotational distinction is explicit.
- **Target injections**: PropositionTarget, ActTarget, OccurrenceTarget,
  ReferenceTarget and SignTarget are §3.5's finite tagged-union injections.
  Eliminate tags, with payload/index bound only in its matching arm; no blanket
  payload equality is added.
- **Discursive lexical candidates**: mintu/drata for mi'u/nai, simsa for si'a,
  frica/jmina adaptations for ku'i/ji'a. These do not force a new Case object,
  a smuni-only route or a fixed intrinsic count. The default recovered
  criterion, comparison-chain sharing, and same-standard nai are adopted;
  precise lexical rows, typed targets, and effectful composition remain work
  (spec's discursive audit; rationale §1.12a).
- **Deictic**: the old fixed-ground This/That/Yonder abbreviations cover a
  resolved fixed-ground fragment, not two independent pointing occurrences.
  Occurrence anchoring and introduction/ri eligibility remain Q12 work.
