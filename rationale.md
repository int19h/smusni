# Rationale for the Lojban semantic core

Why each piece of [the specification](spec.md) exists, why it is shaped as
it is, and what was tried and rejected. The [samples](samples.md) supply
the worked specimens cited here. Sources — CLL (and the edition whose
section numbering is used), the official dictionary, the baselined gismu
list, the xorlo page, guskant's commentary, Brismu, solpahi's articles,
the Eberban and Toaq reference materials, and the plural-logic
literature — are cited inline by name and section; full citations with
URLs are collected in the specification's References section.

## 0. Method

A construct earns a place in the kernel only by a **necessity witness**: a
Lojban meaning that the rest of the core cannot express. A construct that
merely *helps* is defined in the library, where its definition is its
specification. Each entry below follows one template:

1. **Job** — the contrast the construct represents.
2. **Witness** — the shortest Lojban that requires it.
3. **Why not …?** — the plausible reductions, each with the exact
   sentence that kills it.
4. **Shape** — why this signature rather than the neighbors.
5. **Cost** — what the choice makes awkward, honestly.

Pins (rulings on accidental underspecification) follow a different
standard — CLL/xorlo evidence rather than necessity — and are argued in
§3. The global design essays (§2) cover the choices that cut across
constructs.

## 1. The constructs

### 1.1 Labelled place rows

**Job.** Lojban predicates have named, reorderable, deletable places;
functions have positions. **Witness.** `klama fe ti tu` (out-of-order
fill), `mi klama ti zi'o` (place deletion), `klama fi'a ti` (a question
*about places*). **Why not plain curried functions?** Position-only
application cannot state "x2, whichever argument position that ends up
being" — FA reordering, `zi'o`, and `fi'a` all speak in labels, so labels
must exist semantically. **Why not a primitive relation type distinct
from functions?** No witness separates two extensionally equal
row-functions, so `PredTerm<ρ>` is a *transparent alias* for
`Record ρ → Content`: the name and machinery of labels with the ontology
of functions. **Shape of filling.** One former: the single-place `At`
(itself record partial application), with all multi-fill notation
desugaring to nested single fills (spec §4.1). Fills are values, so
distinct-label fills commute — which is the semantic fact that makes
FA reordering and `se`-conversion pure notation: the order of fills
never was part of the meaning. **Cost.** The type theory needs
labelled records — which it needs for `fi'a` anyway.

### 1.2 Clause formation and `Close`

**Job.** An unmarked bridi with omitted places still makes a complete claim,
while tense and abstraction must see the clause eventuality before it closes.
**Witnesses.** `mi klama` needs a contextually recoverable destination and a
going event; `ta pu du lo mi zdani` needs a past state although `du` has no
lexical event place. **Why not existential closure of omitted ordinary
places?** Negation: `mi na klama` does not mean “there is no destination I go
to”; the contextual destination stays fixed under negation. **Why not add an
event/situation place to every row?** That is a coherent alternative, not a
category error. It loses the factorization test here: binary `=` is also used
in case splits, label guards, definitions, and proofs, and `+` is a
value-producing function rather than a clause. Those ordinary signatures
must remain, so event-indexing their declarative uses would add lifted twins
rather than eliminate machinery; those twins do exactly the job
`StateClause` factors once. It would also duplicate lexical events on ordinary
brivla unless it retained the same direct-vs-holding distinction. The type
`ClauseContent = EFn<(Referents<Eventuality>), Content>` instead leaves one
event open:
`DirectClause` uses the lexical event, `StateClause` supplies a holding state
only when no single lexical event survives, and `CloseClause` closes the
common interface with the same run as existential closure while retaining the
selected witness as the structured Content's event. `Close` is the convenient
actual-CAhA composition of these steps; it is a core form for that reading,
not a claim that surface omission defaults to actual. **Why are
`StateClause` and `CloseClause` primitive?** No existing operation constructs
a state of arbitrary complete content holding, so `StateClause` is primitive.
Plain ∃ reproduces `CloseClause`'s run but loses which local witness is the
closed Content's event. Making every application at the transparent
`ClauseContent` function alias overwrite the result's event would instead
break ordinary β-equality: `((λ e. ⊤) x)` must equal `⊤`, not acquire x as
extra structured identity. `CloseClause` is the one semantically meaningful
constructor that records the closure witness. **Cost.** Logical and quantified
composition must say whether it preserves, joins, branches, or replaces
component events; §9.3 states that ledger rather than hiding it.
This argument assumes neither that every `du` claim is true nor that every
mathematical sentence is necessary. The ordinary equality/arithmetic axioms
decide each claim; a true mathematical holding State may be unbounded, and a
false one remains described but nonactual.
Reopen this factorization if a uniform situation-argument calculus can derive
ordinary binary equality/value functions and every clause-event law from one
signature family without duplicating the non-clausal operations.

### 1.3 The specificity triad: `Refer`, `Context`, `Vague`

The single most consequential design decision. Three constructs, because
Lojban distinguishes three ways of not spelling something out, and
collapsing any two produces wrong meanings:

- **`Refer`** — *introduce*. Witness: `lo mlatu cu blabi .i ri jbena` —
  the cat outlives its sentence. Why not `∃`? An existential's witness is
  inaccessible after its scope closes and re-quantifies under negation
  (`lo mlatu na jbena` keeps *the* cat; `∃` would not). Why not ι (the
  definite)? xorlo `lo` claims no uniqueness. This is the dynamic
  indefinite of DRT/DPL, plural from birth.
- **`Context`** — *intend and recover*. Witness: `mi klama`
  (destination), `co'e` (the relation meant here), `zu'i` (the usual
  value), `sutra klama` (the occurrence's intended modification link), and
  `tu'a lo cukta` (the book-related abstraction meant but not spelled out).
  Why not `Refer`? Nothing is introduced or described — `mi na dunda`
  denies the giving of the contextual thing, not the existence of a
  describable gift. Why not a free variable? Free variables have no
  discipline: `Context` declares its type, admissibility constraint,
  dependency profile, and site/key identity. Why not require exact recovery?
  A speaker may be unable or unwilling to articulate the intended relation
  more finely; successful communication requires only a recovered value whose
  differences are irrelevant to the discourse. The resolved term still uses
  one exact value, so this pragmatic tolerance adds no semantic branching.
- **`Vague`** — *leave a soritical boundary unfixed*. Witness: `so'i`
  (no fact fixes where "many" starts), a gradable cutoff, or `ji'i`'s
  tolerance edge. Why not `Context`? There is no intended cutoff to recover,
  even approximately. Why not use the same device for discrete tanru/topic
  alternatives? Supertruth would require the fish to eat and be eaten and a
  tanru to satisfy every admissible link. Existential choice fares no better
  at intended-value constructs: an unintended link can make the positive true,
  while negation denies all links. The composition law (spec §6.5) therefore
  applies only to sharpenings of one soritical concept: pointwise lifting,
  consistent precisification per site, and supertruth where invoked.

The classification of each Lojban construct into this triad (or into
**absence** — no machinery at all) is itself normative (spec §6.1), with
the recovery test printed as the decision rule. The disputed entries settle
coherently: `co'e`/`do'e`, tanru, `tu'a`, bare `jai`, and topic links all
convey occurrence-specific intended values through constrained `Context`;
conventionality changes resolver priors, not semantic type. Gradable
predication splits — *which scale/domain* is `Context` (say the wrong one and
you have misunderstood), *where a soritical cutoff sits* is `Vague`; scalar
`OtherThan` directly denotes the complement region, not a hidden finer choice;
and unmarked distributivity is **absence**, not a parameter (see §2.5).
No analyzed construction requires the possible `SomeAdmissible` existential
choice former. Official `ju'e`, explicitly glossed as a vague non-logical
connective but left without compositional truth conditions, is the concrete
gap-level candidate; its source and usage adjudication must establish whether
it has genuinely no particular intended connection before that former can
enter the baseline.

### 1.4 Projective content: `Presuppose` and `Supplement`

**Job.** Some commitments escape the operators wrapped around them.
**Witnesses.** `naku ro gerku cu blabi` still grants dogs (`Presuppose` —
import survives negation); `xu lo gerku noi blabi cu melbi` questions
beauty, never whiteness (`Supplement`). **Why not conjunction?** `∧` puts
both conjuncts under the negation/question — flatly wrong truth
conditions in both witnesses. **Why two constructs and not one?**
Presuppositions can be *satisfied* by prior context (no new commitment);
supplements always commit anew. Conflating them loses accommodation.
**Shape.** `Supplement` carries an explicit anchor, and a side that
depends on a quantified variable commits per instantiation inside the
binder — `ro gerku noi ke'a se cmene cu bajra`-type dependencies would
otherwise have no coherent projection site. **Cost.** A handler
discipline in the dynamics; the accessibility table carries it.

### 1.5 The accessibility table

**Job.** State, once, what each operator lets subsequent discourse see.
**Witness.** The `ganai da mlatu gi da ciska` conditional (antecedent
feeds consequent) versus `.ija` (branch-local) versus `naku` (nothing
escapes) — three connectives, three policies, none derivable from truth
tables. **Why a table rather than derived behavior?** Because the
policies *are* the connectives' dynamic meanings; deriving them from an
effect algebra is possible (and the model theory does — spec §5.1), but
the table is the single normative statement, so surface and model can
never drift apart. **Why are `↔`/`⊕` primitive?** Their classical
rewrites evaluate operands twice; under effects, twice-evaluated
introductions and supplements are real differences, not stylistic ones.
**Why not share the operands instead of duplicating them?** No sharing
route exists. The classical rewrite `(A → B) ∧ (B → A)` *textually
copies* each operand: two syntactic occurrences are two `Context` sites
(site identity is per occurrence, spec §5.3), two supplement handlers
committing the side twice (handler placement is a fact about term
structure — VC4), and a reshaped accessibility structure (in the
rewrite, the second conjunct sees the first's introductions through
`∧`, which the original `↔` never granted). `Let` cannot rescue it:
`Let` is the *pure* sharing form — spec §4.4 forbids binding an
effectful computation with it, precisely so that sharing a term never
silently shares an evaluation. `Bind` shares an evaluation but shares
its *returned value*, and `Content` returns unit — the meaning is the
state transformation, and no boolean comes back to reuse. The derivation
could be forced through by minting a truth-capture operator
(`TruthOf : Content → RefComp<Bool>` — run once, reify the truth
outcome), but that is not a reduction: it is a general
**dynamic-to-static reflection**, strictly more powerful than the two
connectives it would replace, usable anywhere as an escape hatch
(testing content in a restrictor without its effects), and needed by no
Lojban construct. `↔` and `⊕` are that same once-per-operand evaluation
confined to two closed truth-functional shapes with stated accessibility
rows — capabilities minimized, not operator names. In a pure,
effect-free logic both would be derivable; they are primitive *given*
effects and given the deliberate absence of any reflection operator to
route the sharing through.

### 1.6 Witness export without run objects

**Job.** `ci gerku cu bajra .i ri tatpi` — quantifier picks stay
referable. **Why not a term-level "retrieve the witnesses of run R"
operator?** Because the object needed is just the referent: an
accessibility rule ("a successful exporting evaluation introduces its
witness referent") supplies it with no run identities, no retrieval
operator, and no bookkeeping — and every construction expressible with a
retrieval operator is expressible by binding the referent. The dependent
case (`ro prenu cu ponse ci gerku .i ri tatpi`) does not compositionally export
the witness beyond its governor. Its supported strong reading is selected
upstream and lowers one scope level up to a joint locus, rather than adding an
object-language retrieval operator. **Cost.** This is not an equivalent
rewrite of the original selection computation and retroactively strengthens
the antecedent when the later anaphor appears. The plural-information-state
upgrade in §14 is the principled repair; exotic configurations stay gaps.

### 1.7 The plural algebra, without covers

**Job.** Number-neutral reference with subreference and join. **Witness.**
`mi jo'u do bevri lo pipno` (a plurality acts; no set object exists to
act), `re lo mu plise` (subreference selection). **Why not sets?** In
the nonempty, atomistic, member-wise fragment the two designs are
intertranslatable — the honest answer is an equivalence-plus-choice,
argued in full in §2.8. The short form: sets used the way a set-typed
lexicon actually uses them (nonempty, predication reading the members,
never the set-object) are a plurality wearing set-notation clothing, and the
clothing costs more than it carries — the plural axioms return as
side conditions, the member-wise/object-wise distinction moves from
the type system into per-place convention, and coverage is lost where
Lojban is deliberately non-atomistic — a boundary motivated in part by
guskant's Condition₁ not-individuals proof and cut-bread interpretation (see
References). (The familiar objection — "the
crowd can be large while the set is abstract" — attacks set-*object*
predication, which no serious set-typed design proposes; this document
does not lean on it.) **Why no distributivity/cover
parameter?** See §2.5 — the strongest single "less is more" decision in
the core. **Cost.** Marked readings need marks (`lu'a`, `Distrib`,
group gadri) — which Lojban has.

Collection gadri do not silently maximize their base. Bare `loi P`/`lo'i P`
first use the same ordinary non-maximal `Refer P` as `lo P`, under `Local`,
then refer to the group/set object constituted from that base. `Local` is
needed, not decorative: without projection of the hidden introduction,
CLL Example 6.52's `lo'i ratcu … .i ku'i lu'a ri …` would leave both the rats and the
set in the discourse store, while the text has introduced only the set sumti.
It retains the selected base as a lexical `Bind` value and all truth/
projective effects, hiding only its anaphoric slot. This matches CLL's
contextual `lo'i ratcu` discussion and preserves P1's selection while making
the surface boundary honest. The outer restriction is singular-object-valued:
bare outer reference remains number-neutral, but each selected group/set must
individually have the complete base. The all-P base remains available through
explicit `ro`/`MaxRefer` or a context that genuinely selects it; the cost is
only that mathematical users must state maximality when the context does not
already make it clear.

### 1.7a Constitution: why `joi` is not another plural join

**Decision.** `joi` forms a constituted whole (`joi1`); `jo'u` remains the
plain plural join. The official dictionary calls `joi` “mixed together,
forming a mass” and `gunma` a whole composed of x2, while current CLL 14.14
contrasts a group that acts as one object with `jo'u`'s still-plural result.
The BPFK record is internally revealing: its English proposal describes
unchanged referents plus non-distributivity (`joi2`), but its formal equation
is `X joi Y = lo gunma be X .e Y` (`joi1`). The latter wins because the former
adds no semantic content this core permits: `Combine` plus P4 already leaves
collective/distributive behavior to the lexical predicate. A covert
“do not distribute” flag would make `joi` a redundant `jo'u` plus the very
reading parameter P4 rejects. Contrast `mi joi do bevri lo pipno` (a group
whole carries) with `mi jo'u do bevri lo pipno` (the plural argument is
neutral; `bevri` decides what configurations satisfy it).

One universal mass constructor would be smaller on paper and wrong in type:
a group of cats is not a cat, while a mass of events must remain an
Eventuality and a mixed property must remain a common-row predicate. The
indexed programme therefore has a `Group<T>` result, an Eventuality result,
and a `PredTerm<ρ>` result. The predicate family cannot be packaged as
`Group<PredTerm<ρ>>`: `Group<T>` is first-order while `PredTerm` is a function
type, and reifying it would make ordinary `joi` depend on §9.1's reserved
predicate-object family. `Family⁺` is admitted only at `GunmaPredAt`; that is
the concrete factorization argument for this otherwise surface-unspellable
carrier. At a shared-head tanru locus `JoiTanru` keeps the head outside that
family and asserts it once; mixing two already-head-conjoined predicates would
wrongly make the head itself a duplicated contribution.

**Why the layers.** Official `gunma` now glosses itself as partially
specified, the community `mulgunma` entry explicitly supplies the complete
contrast, and actual IRC usage has `mi se gunma le mi lanzu` when the speaker
is merely one family member (2010-08-14, `lojban-disc/irc/all_logs.txt`
408817–408825). Making general x2 exhaustive would falsify that ordinary
converted use. Thus `GunmaAt` is non-exhaustive, `CompleteGunmaAt` is its
defined “no other peer at this basis” strengthening, and singular
`ComponentAt` is only the ordinary singleton/argument-swapped abbreviation—
never special `se` semantics. `joi`, group descriptors, and `MeiRel` use the
complete layer because allowing an extra peer would make “X mixed with Y” or
“the group of P” silently include Z. Free `gunma` remains partial-friendly.

**Why a basis.** Components are not atoms. People may be team members;
eventualities may have phases; a hybrid's lion/tiger contribution is by
origin, not lion-only and tiger-only body parts; desire and fear can blend as
aspects without pure subevents. `DecompositionBasis` therefore supplies
non-atomic covers and peer units, while `ContributionBasis<ρ>` supplies a
curated realization clause per common row. Every declared event basis must
also state trace, role-participant, and causal aggregation; every property
basis must make all operands contribute and jointly suffice. This moves the
hard semantics to a typed, auditable interface rather than renaming it “the
model's mixture”. A basis used by `joi` must also preserve each surface
operand's units in the combined cover; a granularity that merges away the
speaker's operand boundary is inadmissible for that occurrence, not a reason
for the term to become false. No component property inherits automatically: the 1995
mailing-list critique's reductio (`lei mlatu` would be a tail, or have been in
the sun, because some material part was) is decisive.

**Cross-locus payoff.** The same event instance gives `.i joi` its compound
event and gives ordinary conjunction its model-level `joint_M`. The canonical
conjunction basis is associative, transparent to its own nested wholes, and
treats `hold_M(⊤)` as null, so the old event interface and the new connective
do not proliferate rival “joint” objects. `JoiClause` supplies content but
does not settle performance roles, UI targeting, or transcript spans; those
remain #6. Property rows with no declared contribution basis, `pe'e joi`, and
`joi nai` likewise remain honest bounded gaps.

**Canonical aggregate identity versus organizations.** Explicit `joi` and
`lu'o` must succeed for arbitrary nonempty components and must not select one
of several rival “bare aggregates” accidentally supplied by a model. The
adopted answer is a primitive, rigid `Aggregate κ g` classification plus
one-way rigidity (R), existence (E), within-class uniqueness (A), and local
complete-cover functionality (F). `Massify` is the defined unique selection
from that class. Descriptors remain descriptions: `loi`/`lei`/`lai` may refer
to the canonical aggregate or to an independently individuated team, family,
body, committee, or other organization whose complete current cover happens
to be the same.

Two countermodels fix the boundary. First, budget and ethics committees may
have the same three members at one time and later diverge. Unrestricted
same-cover uniqueness would identify them rigidly at the first time; after
divergence one object would have two non-`CoRef` complete covers, contradicting
(F). Second, an organization whose roster never changes can still differ from
the bare aggregate of that roster (and from another same-roster organization)
by charter, task, history, or legal identity. Defining “aggregate” as merely
“has one cover at every observed situation” would collapse those objects and
would make classification unstable when a model gains a new future or
counterfactual situation. Hence the classification is primitive and the
rigidity implication is one-way.

This preserves both ordinary readings of “the same people on two committees”:
one roster object may bear two committee roles, or two organizations may share
a roster. `du` decides a model/context fact; membership coincidence alone does
not. `lu'o` applied to an organization instead returns the canonical aggregate
of its resolved current components and is not identity in general. Cross-basis
identity likewise remains model-given.

The historical record genuinely splits. Protin's 1991 aggregate/organism
distinction inspired the organization boundary; LeChevalier's same-day
universal-massifiability argument motivates (E), while his `lai lojbab.` body
example supports persistent **described** wholes rather than mutable bare
constructor outputs. The 1994 sumti-paper draft states the extensional
candidate; Clifford's 2002 “intensional, with all the horrors” response exposes
its identity/anaphora costs. Llambías' 1995 `re loi broda` puzzle exposes the
counting problem, and Selckiku's 2011 pinkie-and-bug example supports arbitrary
explicit aggregation without its proposed inheritance gloss. Bays and
Llambías' 2011 exchange supplies both the complete-constituents reading and
the need for first-order group objects when groups are quantified over. These
sources motivate and test the project law; none independently ratifies it.

Rejected alternatives are therefore: global or situation-local uniqueness
over **all** groups (organization collapse); fully model-given manufacture
(no success or identity guarantee for `joi`/`lu'o`); no group objects (loses
outer counting, equality, anaphora, and nested partitions); distinct group
sorts for aggregates and organizations (makes their possible identity
ill-typed); and the rigid-cover biconditional (collapses permanent
organizations). The cost of the adopted primitive classification is explicit
model structure, but it is exactly the distinction the surface constructors
need and is factored by both `joi` and `lu'o`.

**Costs and source limits.** Contemporary CLL's clean group prose is partly
this project's own amendment and cannot ratify the choice by itself. Original
CLL supplies the blue/red and joint-cause phenomena but not a coherent
polymorphic model; the 2018 wiki proposals likewise assume the hard event/
property realization step. The indexed interfaces are therefore a
prescriptive construction justified by coverage and type discipline, not a
claim that the sources already contained it. Complete constitution is exact
relative to the selected base; P39 now makes the base's own no-residue
behavior part of its resolved lexical extension, without imposing a count
profile on mass terms.

### 1.7b Count and mass coverage: lexical extension, not descriptor repair

The original defect was real: if `gerku(r)` at plural type were left wholly
unconstrained, a model could make it true of three dogs plus a cat, while
`CardBasis r gerku = 3` simply ignored the residue. `CoveredBy` closes that
hole and remains meaningful without atoms: every subreference must overlap a
P-unit, but a P-unit may itself be indefinitely divisible. Guskant's
Condition₁ proof and cut-bread interpretation are the motivating witness for
that second conjunct, not a proof of the project's lexical placement.

Two placements were coherent. The rejected descriptor-specific repair made
`lo R` select only `R(r) ∧ CoveredBy(unit_Rℓ,r)` while leaving nuclear
`R(r)` weaker. The adopted lexical-extension repair makes the resolved `R_p`
itself obey that equation wherever its lexicon place/reference mode declares
a unit profile; `lo R` stays literally `Refer R_p`. The official dictionary
and the BPFK gadri table both say `lo broda = zo'e noi broda`, so the
descriptor-only alternative creates an unsupported asymmetry. It also buys
nothing for collective heads: `lo bevri be lo pipno` may denote a team that
carries the piano even when no member does, so such rows need their own direct
plural condition under either design. Adding a descriptor layer on top merely
duplicates the per-row distinction.

The same point blocks a lexeme-wide count/mass Boolean. Official `nanba`
means a quantity of **or container of** bread; substance portions can be
cumulative and divisible, while container and kind modes have different
units or direct plural conditions. The schema is therefore per place and
resolved reference mode. Count profiles, cumulative substance profiles,
singleton-container profiles, and direct collective/kind conditions are
lexical alternatives, never a covert choice at application time. Actual row
values remain #12 work.

The factorization dividends are exact rather than rhetorical. All exporting
cardinal selections use `CoveredBy` plus `CardBasis`, so dog-plus-cat and
dog-plus-pack witnesses fail without forcing their nuclear predicate to be
distributive. `MaxRefer` is inhabitedness plus `CoveredBy` plus the
all-satisfiers conjunct. A collective nuclear scope remains neutral under P4.
Kuna's plural-determiner architecture is comparative evidence that the
ordinary plural predicate can serve as the restrictor; it does not decide
Lojban.

The cost is lexicon work and an explicit commitment: under a count profile,
P-external residue makes both `ko'a R` and `lo R` fail. The rejected
description-only placement reopens only if speakers accept the same resolved
`R_p(r)` as nuclear predication while forbidding r specifically as a `lo R`
referent. No such witness survived the design audit.

### 1.7c Composite personal pro-sumti are plural, not constituted groups

**Decision.** `mi'o` is `Combine Speaker Audience`: the same neutral plural
argument as `mi jo'u do`. The sibling forms use the same construction with
their token-relative “others” projections; the context constraints spell out
the inclusion and exclusion facts instead of relying on English “we”. P4 then
lets one lexical predication determine how that plurality satisfies it.

The three nearby constructions are observably different. `mi .e do jmaji`
connects two clauses and therefore says separately that the speaker gathers
and the audience gathers; `mi'o jmaji` makes one collective predication of
their combined plurality. `mi joi do` manufactures a first-order group. Under
P5 no component property inherits to that group, so bare attested `mi'o
remna` is the decisive carrier probe: the speaker and audience can be humans
without the group object itself being human. Collective `casnu`/`jmaji` and
reciprocal `simxu` examples do not discriminate the carriers, and the two
`se cmene` examples are likewise compromised by collective naming and overt
`ro`; the rationale does not overclaim them.

The evidence is genuinely layered. Original CLL §7.2 explicitly says the
forms are masses and equates `mi'o` with `mi joi do`; that is the coherent
rejected alternative and the principal compatibility cost. Current CLL §7.2
says `mi jo'u do`, but that sentence is this project's July 2026 amendment
and cannot ratify the project. The official dictionary fixes speaker,
listener, and others but no carrier ontology. Independent post-xorlo support
comes from Llambías' 2004 “not marked either way for distributivity” remark
and the 2013 Selpa'i/Assis/Clifford thread: `mi'o = mi jo'u do`, preference
for `jo'u`, and united pluralities whose satisfaction mode remains open. The
References entry gives exact Message-IDs and roles. The IRC `mi'o remna`
tokens supply compatibility evidence, not a universal usage theorem.

One composite pro-sumti remains one argument. Thus `mi'o klama` has one
omitted destination retrieval, possibly returning a plural place value; it
does not distribute the clause into speaker/listener journeys or pair each
member with a separately recovered destination. That contrast belongs to the
surface structure, not pragmatic pairing.

**Cost and reopening.** This diverges from original CLL and requires three
explicit “others” context projections. It does not solve positive `mi'o …
mei`: #24 must add or reject a plural carrier instance without changing the
pronoun. Reopen P40 only for ordinary unmarked uses that require properties of
a constituted group which its members lack; collective or reciprocal plural
predication and cardinality alone do not qualify.

### 1.8 `DropPlace`, `Tanru`, `Scalar`

Three relation formers, three witnesses: `mi klama ti zi'o` (a relation
with the role *gone* — neither `zo'e` nor closure can remove a role);
`sutra klama` (an intended but underspecified modification link — §1.3);
`ta na'e
melbi` (scalar otherness is not `¬` — it is *stronger*: CLL 15.4, a
selbri negation "asserts that a relationship exists other than that
stated" and "remains an assertion of some specific truth", so `na'e P`
denies P's stated region *and* positively asserts the complementary coarse
region of the recovered `ContrastDomain`; `to'e` asserts the antipode,
`no'e` the midpoint. No hidden fine alternative is selected. An earlier
analysis had `na'e` weaker than
`¬`; the primary text overruled it, and the King-of-France passage of
CLL 15.4 — selbri negations "still make affirmative claims" — is the
decisive witness). Why not lexicalize scalar forms per predicate? The
operators are productive across the whole lexicon; three formers beat
thousands of entries.

The `Tanru` analysis has independent lexical corroboration: the gismu
`tanru`'s official row gives the compound its "meaning ⟨4⟩ in
usage/instance ⟨5⟩" — occasion-specific intended resolution as a dictionary
fact, adopted as the operator's shadow relation in spec §16.5. CLL 5.2's
warning that a speaker risks being misunderstood likewise presupposes a
speaker-side intention and fallible recovery; it does not make every listed
link true at once.

### 1.9 `Generic`

**Job.** `lo'e`/`le'e` talk about typicality without a specimen.
**Witness (against every specimen theory).** `lo'e cinfo cu se kerfa lo
clani` (maned — normal *males*) with `lo'e cinfo cu se jbena lo cinfo`
(bears young — normal *females*): no single typical lion verifies both,
so a fixed "typical-lion reference" gives wrong conjunctions under
referential transparency. **Why not `∀`/`∃`/`Refer`?** Generics tolerate
exceptions (`∀` fails), claim more than instances (`∃` fails), and
introduce nothing anaphorically stable (`Refer` fails — generic anaphora
is honestly gap-registered instead). **Shape.** One operator, mode
Typical/Stereotypical, holder fixed to Speaker for `le'e` (a grammatical
fact, so it lives in the operator, not the lexicon). **Cost.** The
normality ordering is constrained, not defined — the operator is
*frankly axiomatic*, because genericity is an open problem in semantics
at large and pretending otherwise would be false precision.

### 1.10 `Reify` and the abstraction relations

**Job.** Lojban predicates select different abstraction sorts. **Witness.**
`lo du'u mi klama cu se djuno do` (knowledge takes propositions) against
`lo ni mi klama cu barda` (bigness takes amounts): swap them and both are
gibberish — the sorts are real. **Why is the `Reify`/`Holds` pair primitive?**
Because `du'u` is the one genuine Proposition↔Content crossing —
`Reify` inward, its axiomatized inverse `Holds` outward — while the
others — `ni`, `jei`, `li'i`, `si'o`, `su'u`, `pu'u`, `zu'o` — are
abstractors to which CLL itself assigns place structures (CLL 11.3, 11.5,
11.6, 11.9: "x1 is the amount of … on scale x2"), so the core renders
them as named abstraction relations and
lets reference apply outside: `lo ni …` and `le ni …` then differ exactly
as `lo` and `le` always differ, outer quantifiers and relative clauses
work unchanged, and the omitted x2 (`su'u`'s "type", `ni`'s scale) is
ordinary contextual closure. A family of primitive
`Content × operand → sort` constructors was rejected because it would
re-derive all of that machinery, worse, per sort. **Cost.** Terms are a
little longer; uniformity pays for it.

`jei` stops at its epistemology-relative `TruthValue` object. CLL 11.6's
numeric [0,1] treatment is explicitly a proposal whose conventions were never
worked out and whose number-valued reading never became established. P38
therefore removes `TruthValueDegree` from the normative crossing inventory and
keeps its exact signature only as a gap proposal. This is prescriptive rather
than optional-per-reading: a future evidence-backed pin may add the crossing;
the current surface never chooses between two hidden type-changing readings.

### 1.11 Acts, performance, tokens, signs

**Job.** Force, quotation, and reported speech. **Witnesses.** One content
under four forces (`do klama` / `xu` / `ko` / displayed); `mi cusku lu ko
klama li'u` (a directive described, not issued — construction ≠
performance); `lo'u mi do du le'u` (quoting the unparseable — signs carry
text, not meaning); `la'e lu mi klama li'u` (a sign and what it expresses
are different things, and Lojban crosses between them explicitly).
**Why opaque quotation boundaries?** Anaphora and presupposition must not
leak out of mentioned material, or quotation collapses into use.
**Why three performance layers?** A reusable act package cannot contain one
performance's resolved speaker, deixis, or omitted-place values: the same
`Act` may be quoted without performance and may be performed twice in two
contexts. `ActContent` must therefore remain the raw package projection.
Conversely, cross-performance default `go'i` and assertion-content `la'e di'u` must not run that
raw package against the later caller's context; they need the content as
resolved at the selected utterance. `RealizedContent` supplies that partial
token-to-content crossing, while the `ActOccurrence` record/opaque handle is the semantic
join point between one `Perform`, its token/span, its extensional context
capture, and occurrence-relative grounding. `Perform` returns only an opaque
handle to this record, so a UI can target one of two performances of the same
act without inspecting the capture. Putting the capture inside the
act would make repeat performance impossible; relying only on a
hoist-before-construction convention would leave arbitrary deictic or
`Context`-bearing packages undefined. The occurrence layer factors both
problems once. **Why not target only the utterance token?** One token/span may
realize a host plus displays/vocatives, or future compound components; the
token does not identify which act was performed. The occurrence handle pairs
token, act, and capture, while transcript attachment supplies its role,
without identifying any two of them. **Why not
target only the raw act?** Re-performing one package would make the two
targets identical. It freezes contextual interpretation, not dynamic truth,
reference outcomes, projective discharge, or a `Vague` sharpening.
The resolver capture is likewise extensional rather than historical: at each
captured site it retains the original partial function on the entire declared
dependency domain. A later override that reaches a tuple not traversed in the
antecedent therefore uses the original captured answer when defined and is
projectively undefined otherwise; fresh caller-context resolution would break
the very capture default this layer exists to state.
CLL 7.6 independently supplies the key minimal pair: ordinary GOhA keeps the
antecedent pro-sumti meanings, whereas `ra'o` reinterprets them in the new
context. That source does **not** license reopening every omitted place or
tanru link. The mapping therefore merges the raw template with the occurrence
capture: only the marked pro-assign sites are rebuilt, while unrelated
`Context` values remain captured. A wholesale raw `ActContent` replay was
considered and rejected as an overgeneralization of `ra'o`.
**Cost.** Tokens and signs enlarge the ontology; the model also carries
performance occurrences and semantic closures. None exposes resolver state
to terms, and every element is independently witnessed.

### 1.12 Indicators: displayed content with lexicon discipline

**Job.** `.ui nai cai`, evidentials, discursives — meaning that is shown.
**Witnesses**, one per design decision: `.au mi sipna` (host
*subordinated* — no sleeping asserted: host-force profiles are real and
lexical); `.uinai cai` (intense *unhappiness* — `nai` selects the paired
emotion, then degree applies: pairing must precede degree, so pairing is
lexical, with `Scalar Opposite` only as documented fallback — CLL 15.7's
opposite-end rule); `mi jinvi
lo du'u ti'e do klama` (hearsay marked on *embedded* content — so
evidentials cannot be an operand on assertion force; they are targeted
display whose force-grounding effect fires when the target is the
enclosing act's content); `pei` (attitudes are questionable — so they are
first-class relations, not wrappers). **Why not a closed generated
inventory?** The UI lexicon is open; the core supplies the *shape*
(relation, target, degree, pair, profile) and the dictionary supplies the
instances. **Cost.** The lexicon carries real semantic load — by design
(§2.6).

### 1.13 Why facet joining is plain conjunction

**Why not a dedicated operator.** A dedicated non-logical joining
operator for tense/modal facets sharing an event might look necessary
— surely "same locus" needs a connector — but no witness separates it
from dynamic `∧`: the shared event is an explicit variable, so locus
identity is carried by binding, not by a connector; and the
tag-negation paradigm *derives* from `∧`-placement what a dedicated
operator would have to stipulate — `mi klama ti
sepi'onai ti` negates just the instrument conjunct (`klama ∧ ¬pilno`)
while bridi `na` negates the whole (`¬(klama ∧ pilno)`), and tense
chains (`pu pu`) need precisely `∧`'s left-to-right accessibility for
their anchor anaphora. The one settled job in this neighborhood is exact
facet conjunction. Constitution-bearing sumti/property/event `joi` instead
uses the indexed §4.9 programme; no generic `Vague` connector fills its
remaining per-row/performance gaps (spec §6.1, §14). **Cost.** A use needs a
declared result kind and basis, and unmapped loci stay gaps rather than
borrowing facet conjunction.

### 1.14 `Bind`

**Job.** Run an effectful computation once and use its result under a
binder — the seam between the pure λ-fragment and the dynamics.
**Witness.** `lo mlatu cu blabi .i ri jbena`: the introduction must run
*once*, with its witness reused across two performed acts —
`(Bind {$cat :: Referents Entity} (Refer P) {(Do a₁ a₂)})`. **Why not
ordinary λ-application?** In the calculus as typed, application simply
*cannot* consume a computation where a value is demanded — `Bind` is the
value-returning computation eliminator (`RefComp` and `PerfComp`), and that
type mismatch is the primary
necessity witness. The effect join is load-bearing: a performance operand
keeps the result in `PerfComp`, so binding its occurrence handle cannot smuggle
a performed act into `Content`. The live alternative is a different calculus: a
direct-style call-by-value core where application itself sequences
effectful arguments. There the two would coincide — the honest gloss
is that `Bind` *is* application under mandatory call-by-value at
computation types, made visible — but the direct-style calculus pays
with a value-restricted β-law: substitution copies the argument's
*text*, so β-equality would hold only for value arguments, with every
effectful application node an unmarked sequencing point. The core
prefers the discipline visible: β holds unconditionally in the pure
fragment, and every sequencing point is a `Bind` node the
accessibility table can name (witness-export width is stated in terms
of it). **Why not the CPS/state encoding?** `Bind` is famously
λ-definable if `RefComp<T>` is spelled as its *transparent*
state-threading function type — but then information states and
continuations become first-class term values, and the term language
acquires meanings no Lojban sentence has: state inspection, double-shot
continuations (backtracking), and truth-capture-without-effects — the
reflection operator §1.5 deliberately refuses — all free of charge and
all requiring ban-conditions to re-exclude. (An *abstract* or
linearity-disciplined encoding avoids the junk exactly by reimposing
the monadic interface — which concedes the point.) The transparent
encoding also freezes §5.1's carrier into the definition (any carrier
refinement — the `da'i` gap entry already commits to extending it
with a world-shift operation — would rewrite the type of every term
ever written) and turns the definition
from an interface with many models into a description of one machine.
**Comparative note.** Kuna — the loglang implementation nearest this
territory — makes the same choice: its expression language is a typed
λ-calculus plus named effect constructors and named combinators
(`and_then` — monadic bind — among its built-in constants), not a CPS
expansion; exactly one of its effects (`Cont`, scope-taking) is
deliberately continuation-typed. Eberban has no `Bind` because it has
no distinct computation type to eliminate — see §2.4. **Cost.** Two binder forms
(`Let`/`Bind`) where one calculus habit expects one; the distinction
is load-bearing and must be taught.

### 1.15 `ClauseContent`, `StateClause`, and `EventOfContent`

**Job.** Give every declarative clause one available eventuality without
pretending every predicate lexically has an event argument. **Coverage
witnesses.** `ta pu du lo mi zdani`, `lo nu ta du lo mi zdani`, and `li re
su'i re ca'a du li vo` are grammatical: tense, event abstraction, and CAhA
all apply to equality, whose core meaning is plain `=`. The former model could
not lower any of them. **Why not wrap every eventive clause in a state of its
event occurring?** That double-indexes `mi klama`: tense and BAI should target
the going itself, not a second state. `DirectClause` therefore preserves the
lexical event; only eventless or scope-composed content uses `StateClause`.
**Why not leave compounds untyped?** Quantifiers cannot share one event among
all instantiations, conjunction needs both components, disjunction may be true
through either, and negation has no positive component event. The clause
forms make those decisions explicit: quantified and conjunctive claims take
holding/joint states, disjunction is branch-relative, and negation takes a
negative state.

**Why this model interface?** `StateClause` is a content-to-event-open
constructor, `CloseClause` binds that interface while retaining the branch
witness, and `EventOfContent` is the inert object projection; none is a
truth-capture operator. `CloseClause` has the run of ordinary existential
closure but is not reducible to it because Content identity also contains the
event intension. The operand runs only when the clause is evaluated, no
`Bool` is returned, and no syntax is exposed. `Reify` already
provides the only route from content to a first-order proposition and `Holds`
the route back, so the event projection adds no hidden evaluation power.
Fine's truthmaker semantics is a useful comparative model here: conjunctive
verification fuses component states, disjunctive verification takes an
alternative, and negation requires an explicit policy. It does not decide
Lojban. This project chooses negative holding states because the
human-adopted coverage includes negative clauses, and §4.9 identifies
conjunctive joint
states with the canonical complete event `GunmaAt` constitution rather than
proliferating notions of “joint.”

**Actuality cost and repair.** The domain contains described nonactual
eventualities; `fasnu` says which occur at a world. A direct episode is actual
at its evaluation world, while `ka'e` evaluates its event property in
capability worlds. Missing CAhA cannot simply mean actual: CLL 10.19 explicitly
uses bare `ro datka cu flulimna` and `ta jelca` for capability and says context
disambiguates an omitted CAhA. P24 therefore makes omission reading-multiple
among the four overt CAhA modes, with no default. Explicit `ca'a` fixes the
actual reading and is overtly contrastive even where its `fasnu` conjunct is
extensionally redundant. A holding State need not be bounded: a mathematical
truth may occupy an all-time/all-space state, after which `purci`/`cabna` have
their ordinary relation-specific results rather than failing to type.

**State-relative values.** Keeping binary identity does not force every
quantity to be rigid. “The fine-structure parameter's value is X now and may
differ later” either uses an explicit value-of relation, or forms the
state-sensitive value description/projection *inside* each `StateClause`.
Binding the quantity/value outside gives the de re reading; binding/evaluating
it inside gives the state-relative reading. Arithmetic constants and `+`
remain rigid, while the physical value interface may vary by time, location,
world, or scale. **Cost.** Content denotations carry an event
intension in addition to their dynamic run, and model construction must honor
that congruence; issue #10 must include it in the term-model exercise.

## 2. Design essays

### 2.1 Why not plain predicate logic

FOL loses, in order: cross-sentence anaphora (no discourse referents —
spec §5.6), donkey readings (no compositional dynamic binding — the
truth conditions are classically statable, the anaphoric route to them
is not; §5.6), projective
content (one dimension of meaning — §5.5), force (assertion only —
§7.1), plurals (singular terms — §3.2/§4.8), vagueness-as-meaning
(bivalent atoms only — §6), and use/mention (no signs — §7.5).
Each loss above is a witnessed Lojban phenomenon. The core is exactly
FOL's spine — typed λ, connectives, quantifiers — plus the
disciplined extensions those witnesses force.

### 2.2 Why two truth values (against Eberban's three)

Eberban builds true/false/unknown into its logic. The phenomena "unknown"
covers split, in Lojban, into things the core keeps apart: contextually
unresolved values (`Context`), unasserted content (force), presupposition
failure (projective definedness), and unanswered questions (`Query`
values). Bundling them into a truth value forfeits those distinctions —
e.g. negation treats presupposition failure and plain falsity
differently, which strong-Kleene tables cannot see. Two values plus
projection recovers every honest use of "unknown" with none of the
collateral.

### 2.3 Why explicit context (against the threaded context argument)

Eberban threads a hidden context parameter through every predicate —
elegant, and it makes tense and deixis nearly free. The core declines it:
a definition optimizes for *auditability*, and a hidden argument on every
relation is the single largest source of "where did that reading come
from?". Instead the utterance context is one explicit record, deictics
are its projections, `Context` computations consult it per site, and
`InContext`/`ShiftedGround` shift it visibly — so `ra'o`-style shifts,
which the threaded design gets for free, cost one visible operator here,
and everything else stays inspectable. The trade is verbosity for
transparency, which is this project's trade everywhere.

### 2.4 Why worlds live only in the model (and effects only in the model)

De re/de dicto and opacity are real (`mi djica lo nu mi pilno lo karce`
has two readings), so the model theory is world-indexed. But no Lojban
sentence *binds* a world: the candidates were hunted down (attitudes, CAhA, `da'i`,
property-internal descriptions — `lo ka viska lo pavyseljirna` included)
and every candidate resolves by binder placement plus lexical
intensional-place marking, evaluated in the world-indexed model. So terms
stay world-free; `da'i` waits in the gap register for the treatment its
three open dimensions deserve. The same restraint governs effects: the
dynamics *is* one algebraic computation type in the model, but the
normative surface is the named operations and the accessibility table —
Kuna demonstrates the algebraic surface working for Toaq, and also
demonstrates its cost (a composition search and ten wrapper types between
the reader and the meaning). One content, two presentations; the
definition shows the readable one and states the equivalence.

Worth stating once, because it locates this whole design: **dynamic
semantics is static semantics at a higher type**, twice over. A
supported at-issue declarative discourse — once its readings,
contextual parameters, and precisifications are fixed — has
classically statable truth conditions: the
selected strong donkey reading's joint-locus lowering *is* a classical
formula; it is a reading-specific mapping, not an equivalence theorem for the
underlying selection computation. (Questions, directives,
displays, and the projective dimension carry more than truth
conditions; for them the desugaring target is the model's
state-transformer objects, the second sense below.) And sentence meanings are
statable statically too, at the state-transformer type — §5.1's
carrier is a plain set-theoretic function space. What cannot be
recovered by any desugaring is *compositional locality*: no assignment
of ordinary truth-condition-type meanings to sentences makes `.i`
conjunction and lets `su'o gerku cu klama .i ri melbi` come out right,
because the witness closes inside sentence one before sentence two
exists. A semantics of Lojban discourse must either raise the sentence
type (the transformer model) or globalize the translation (per-
configuration reading selection and lowering); this core does the second in the mapping
for the selected supported fragment and tests those rules against the
first in the model — with `Bind` as the visible seam (§1.14).

The comparison with Eberban sharpens here. Eberban is a *sentence*
logic with a threaded context parameter: its binding particles desugar,
in its own refgram's equations, to conjunction, ∃-closure, and argument
routing in static HOL, and its `ze` family gives latest-instance
cross-sentence anaphora that reaches even a preceding existential's
witness (the refgram equates the follow-up sentence with the first
sentence's witness, and marks the multiply-evaluated/donkey cases as
an open TODO). Its conversation context is genuinely carried
between sentences and updated by dedicated predicates (the refgram's
`an` family), so what it lacks is neither conversational state nor
simple witness anaphora but the general case: a *distinct computation
type* with compositional witness export — covariant (donkey)
dependence across binders — and a formal projective-commitment layer
(at-issue vs aside). Nothing propositional is thereby inexpressible
(HOL states any classical truth condition, given restructuring into
one sentence with shared variables); the anaphoric route is what is
absent. Lojban's grammar makes exactly that route
core (`ri`, `go'i`, witness export, `noi`), so its definition cannot
decline the discourse level; a language that adds covariant
cross-sentence binding faces the same fork, and the fork is a fact
about the phenomena, not a house style.

### 2.5 Why there is no distributivity parameter

The tempting design: unmarked plural predication carries a covert cover
variable (context supplies it, or it's vague). Rejected on three grounds.
First, xorlo says unmarked gadri are *unspecified* for distributivity —
and a parameter is not unspecification, it is a question the sentence
now silently asks. Second, plural logic's lesson ("the rocks rained
down" hides no quantifier over ways-of-raining) — the predicate holds of
the plurality, and *how* it holds is the predicate's lexical business, which
the lexicon interface records per place. Third, the cover readings fail
the vagueness test from the other side: each-carried and
together-carried are things speakers separately *mean* and hearers
recover — reading-level choices, which live upstream in
disambiguation — while the unmarked sentence's configurations (the
piano carried, however the three shared the load) verify it without any
cover fact existing at all. A covert parameter would turn every
unmarked plural sentence into that upstream question, silently asked.
So: neutral predication is
the reading; `lu'a`, `Distrib`, and the group gadri are the marked forms.
Absence means absence.

### 2.6 Why the lexicon is a first-class interface

Many disputes that look semantic are lexical: which places are
intensional, which deletions are meaningful, what `djuno` demands of its
answer, which emotion `.uinai` names, how `bevri` composes with plural
carriers. A definition that inlined all of this would be a dictionary; one
that ignored it would be unusable. The core's answer is a typed interface
(spec §10): the *schema* of lexical knowledge is normative, its *content*
is curated data. The constitution field follows the same discipline: a
`gunma`/event row declares admissible decomposition bases and every supported
property-`joi` row supplies a concrete `MixAt`/`ContributesAt` instance;
absence is a coverage gap, not permission for a model to improvise. No
collection **place-structure replacement** was needed —
source verification showed
official `gunma` x2 is already the components and `selcmi` (a xorxes
lujvo, now also glossed and used by the Contemporary CLL edition's
set-descriptor expansion) already takes its members as x2; both are
adopted with plural-reference x2. The defective gloss in this area is
official `cmima`'s x2-as-set, which the library simply avoids.
The `le`-description analysis deserves its history spelled out, since
it was contested during drafting. `skicu`'s official definition — "x1 tells
about/describes x2 (object/event/state) to audience x3 with description
x4 (property)" —
makes its x4 a property, so a `skicu`-based `le` (the property applied
to x2 by `skicu`'s own definition) is expressively adequate. The
question closed when guskant's own `le` expansion surfaced —
`zo'e noi mi ke'a do skicu lo ka ce'u broda` (the commentary's gadri
definitions) — showing the community's
formal analysis was the `skicu` analysis all along, and the one
surviving concern (that `skicu` names a describing *event*) is
answered by the anchoring clause: the describing event is this
utterance's own locution, true by construction, with the token
machinery already there to say it. So `le` lowers through `skicu`,
exact official fit, no dictionary change. (Why not a dedicated
`DescribedBy` relation: it might look cleaner than reusing a
dictionary word, but both of its would-be supports fail — reading
`skicu`'s x4 as a "medium of expression" misreads the official row,
and requiring core relations to be definable independently of the
dictionary imposes a constraint nothing needs, since the lexicon
program defines gismu semantics.)

### 2.7 Alternatives shaped like implementations

A recurring failure mode in formalizing a language: machinery that mirrors
how a *processor* would work — run identities for quantifier retrieval,
error taxonomies as meanings, canonical spellings as semantics, registry
lookups as analyses, "unresolved" as a semantic value. This project's
history included several such shapes, and each died the same death: ask
for the *meaning* the machinery denotes and there is none — only a
process state. The tests that killed them are usable on any future
proposal: Does it survive alpha-conversion and re-serialization? Does a
sentence witness it? Does it still make sense on paper, with no program
running? Nothing in the core fails those tests; §14's gap register exists
so that honesty about coverage never again requires inventing semantic
objects for process states.

### 2.8 Why lexical arguments are plural references, not sets

The most serious alternative to §1.7's plural algebra is a set-typed
lexicon: every argument place currently typed `Referents<T>` becomes a
nonempty `Set<T>`, as Eberban's dictionary does throughout (its `tce`
type is a *non-empty* set; a `*` marks places whose satisfaction
survives passing a subset — refgram, "Dictionary conventions") and as
Brismu's foundations choose ("sets are free over a universe of
individuals … an inevitable structure" — Brismu, "Sets, not Masses").
The pre-xorlo dictionary ran a partial version of the same experiment:
in the baselined gismu list (1994), roughly thirty places carry
set-typed annotations — the word "set" in the place gloss, usually with
a completeness side condition; the literal "(set)" marker on about a
dozen entries (`sisku` x3 "complete specification of set"; `kampu`,
`simxu` x1, `cuxna` x3, the `-mei`/`cmima` cluster).
This section records what a full examination established, so the
choice is never again defended with less than its real argument.

**First, the concession.** Under the discipline a working set-typed
lexicon actually imposes — call it **D**: sets nonempty; members drawn
from the individuals (atomistic generation); predication at lexical
places reading the *members*, never the set-object; extensional
identity, with discourse-introduction identity carried separately;
representation sets kept distinct from first-order set objects — the
two designs are intertranslatable. `Combine` is union, `Among` is
subset, the singleton lift sends each individual to the set
containing exactly it, and
`Referents<T>/CoRef ≅ NonEmptySet<T>` is a theorem. Inside D nothing
expressible distinguishes the designs; "the crowd is large while the
set is abstract" is no objection there, because under D largeness is
never predicated of the set-object at all. Eberban's own gloss of
eating shows the discipline at work: the set is a delivery mechanism
for the members, and the word's definition says how the members
satisfy it (refgram, "Dictionary conventions": the `bure` example).

**Second, the choice, and its grounds.**

1. *The isomorphism is conditional, and the core sits outside its
   conditions on purpose.* D's atomicity clause is a strict
   strengthening of the plural algebra: §4.8 assumes no atoms
   ("nothing requires that references bottom out in singletons"), and
   counting is `CardBasis` — units under a description — rather than
   cardinality of a canonical member basis. That is deliberate
   plural-logic territory (guskant's indefinitely divisible bread;
   mass-like reference generally). A set-typed lexicon either loses
   that coverage or re-legislates it.

2. *Inside D the re-spec is relabeling plus obligations.* The plural
   axioms do not disappear; they return as side conditions —
   nonemptiness at every place (Eberban's `tce` states it in the
   argument's type just as our reference type does), ur-element
   legislation, the member-wise reading imposed per place, and
   provenance labels re-creating the co-reference/introduction
   distinction that extensional sets collapse. Meanwhile lists, groups,
   and genuine set objects survive untouched, so "one collection
   machinery" is not delivered by any actual set-based design: Eberban
   itself needs a wrapped/unwrapped split ("mostly use these 'wrapped
   versions' unless … speaking about nested sets" — refgram, "Eberban
   from scratch", the sets chapter) — which is the
   `Referents<T>`/`Set<T>` distinction with the names filed off,
   enforced by convention where this core enforces it by type.

3. *The two-sort split structurally excludes a real ambiguity.* With
   plural references and set objects as different sorts, `lo selcmi cu
   simxu lo ka tavla` has one analysis (set objects don't talk; the
   members-reading goes through membership machinery). With one
   set-type everywhere it is genuinely ambiguous — several sets
   reciprocally related, or one set's members — which is solpahi's
   argument ("A Simpler Quantifier Logic") that a place cannot accept
   both readings without "a true ambiguity", and is where the
   pre-xorlo set places actually hurt.
   Under a uniform set re-spec the exception class that must be carved
   out — `cmima`, `selcmi`, `kampu`, `sisku` x3, the set operators —
   is exactly the current `Set<T>` vocabulary. The core is not
   set-averse; it is place-precise, and the re-spec's own exceptions
   recover its shape.

4. *The dictionary record.* The set annotations of the baselined
   gismu list were inconsistently applied (the paradigm collective
   predicate `sruri` carries none), dragged completeness side
   conditions that plural reference does not need, and were re-read as
   plural by xorlo-era practice without the text ever changing — the
   official jbovlaste entry for `simxu` still says "(set)" as of this
   writing, while the community's formal treatments (guskant's
   commentary; solpahi's articles) reconstructed the plural reading
   externally. Plural
   reference is what the set annotations were reaching for; the core
   says it directly. The per-place audit itself is owed under both
   designs (spec §10's plurality-behavior field is the same docket as
   Eberban's stars); what differs is the failure mode — under the
   re-spec a misassigned member-wise/object-wise call silently moves
   truth conditions, while an unpopulated lexical field leaves
   vagueness, not error.

5. *Brismu's second-order objection does not weigh here.* "Plural
   logic is equiconsistent with monadic second-order logic, given a
   predicate for masses" ("Sets, not Masses" — an assertion the chapter
   supplies without proof) is, even granted, idle: equiconsistency is far
   weaker than equivalence of designs, the hedge concedes that plural
   quantification is present either way, and second-orderness is no
   incremental cost in a core that is already a typed λ-calculus with
   comprehension. The metatheory may freely use sets to model plural
   extensions — §4.10's witness sets already do — without lexical
   places denoting set objects.

**Third, what was adopted from the set side.** The sharpest thing in
Eberban's conventions is the star's definition, and the lexicon
interface now uses it: the plurality-behavior field's
subreference-monotonicity value means *satisfaction preserved under
subreference* (`Among`) — a checkable lexical criterion — with
collective capability recorded as an independent fact (a satisfying
plurality need not satisfy in its parts, which is an absent guarantee,
not a counter-entailment); per P4, never a reading parameter. Not imported: the cumulative default
Eberban writes into definitions like its eating verb (everyone eats at
least one; every apple is eaten) — that is a resolved cover reading,
which P4 declines as a default and Lojban marks when it means.

Solpahi's "A Simpler Quantifier Logic" stands in the record as
independent convergence: plural constants demand plural variables (the
2004 Clifford–xorxes exchange, quoted there), and bare PA as
plural-existential
witness-sets is P17 arrived at from the other direction — including
the scope-commutativity bonus. His hybrid-era gap (`no prenu cu
jmaji` inexpressible) was the price of xorlo's no-rewrite move, and
this core pays the other half of that bill with plural selections and
joint loci — a repair orthogonal to sets.

### 2.9 Why the reflection layer was tried and withdrawn

An earlier design made every binder a function over quoted core syntax.
The attraction was real: atoms, quotation, and application would have
given the notation one uniform grammar; binders and control operators
could have been named like other vocabulary; and a stage-indexed tower
might eventually have let Lojban describe the semantics of the stage
below it. R's uniform call syntax and typed multi-stage calculi were useful
inspirations rather than commitments (Nanevski, Pfenning & Pientka; Taha
& Sheard; Davies & Pfenning).

The proposal did not earn its cost. No current Lojban construction
requires executable quotation of core notation. To make binder operands
safe, the design added `Expression<Γ,A,ε>`, telescope signs,
elaboration environments, capture rules, site-preservation laws, a
partial staged `Interpret` family, `MakeLambda`, and facades for the
remaining operators. The displayed type still omitted the very stage
index on which the safety argument depended, while captured outer values
already constituted cross-stage flow. Most importantly, a
predicate-style row for a binder or force constructor could only
*describe* the resulting function or act; it could not perform binding or
force. The programme had conflated executing operators with their useful
shadow predicates.

Unrestricted fexpr-style access to operand syntax was never acceptable:
Wand's collapse result remains a warning that observation of arbitrary
caller syntax destroys useful contextual equivalence. The attempted layer
avoided the full fexpr problem, but doing so required almost all of the
machinery just listed. With no Lojban necessity witness, that was
complexity in service of the notation rather than the semantics.

The baseline therefore uses direct `λ`, `Let`, and `Bind` formation.
Scope, α-equivalence, capture-avoiding substitution, and inert binder
positions are structural judgments (§4.4/§5.2), as they are in ordinary
typed calculi and proof assistants (Harper). Braces remain visible scope
punctuation; they are not term-valued quotation. The carrier-level
`bind` operation remains indispensable — this decision removes only its
reflective facade, not effect sequencing.

Nothing needed for linguistic use/mention is lost. Lojban quotations,
signs, utterance tokens, `InterpretContent`/`InterpretAct`, and explicit
`Perform` remain. Shadow relations such as `xusra`, `danfu`, and
`smuni` remain valuable vocabulary for talking about acts and meanings,
but they do not execute the operators they describe. The refusal of a
general `TruthOf` dynamic-to-static crossing likewise remains (§1.5).

A future core-self-description extension is not forbidden. Reconsider it
only if an independently witnessed meaning requires executable core code,
and then require an explicit stage index, a complete hygiene/capture
theory, a nontrivial equational theory, and a proof that ordinary terms
cannot be reified or inspected implicitly. Such an extension would be an
additive proposal, outside the normative baseline until separately
adopted; Lean macros or another host may implement convenient syntax
without making reflection part of the semantic core.


### 2.10 du'u, nullary ka, and the reserved reification family

An influential community proposal — And Rosta's, on the Lojban
Wiki's "ka, du'u, si'o, ce'u, zo'e" page, endorsed there with
amendments and also recorded with dissent — holds that `du'u`, `ka`,
and `si'o` "are logically
identical. They all express n-adic relations, where n is the number of
overt or covert `ce'u` within the abstraction. A proposition is a
0-adic relation." The BPFK's *proposed* `ce'u` definition goes part of
the same way: `ce'u` is "almost solely used in `ka`", though
`si'o`/`du'u`/`su'u` clauses "can make some sense" with it. On the
proposal, the
abstractors differ only in what elided sumti default to. Is this core
wrong to give `du'u` its own primitive?

No — because the proposal and the primitive answer different
questions, and the core asserts both answers where they are typable.
As a claim about
**abstraction syntax** the doctrine is correct over `ka` and `du'u` —
the baseline's `ce'u`-capable abstractors — and holds there as a
theorem: `ce'u`-marking extracts λ, arity is the count of distinct
extracted variables, and the bare-`du'u` case is
the 0-adic one — whose extracted "relation" is the content itself,
since `PredTerm<⟨⟩>` applied at the empty record *is* `Content`
(§3.3). (`si'o` is the point where this core declines the proposal:
the conceptualizing mind is a lexical place of `SihoRel` — CLL's row,
kept by the BPFK's own proposed `si'o` definition — not an
elision-default rule, so `si'o` stays in the §9.2 relation family and
the all-`ce'u` reading joins the reserved family below. The carve-out
is itself evidence for the two-questions thesis: the proposal
conflates a place-structure fact with an elision default.) Abstracting nothing out of a bridi leaves its content; in that
exact sense `du'u` *is* nullary `ka`. What the doctrine never had the
machinery to ask is the **object** question: what sort of first-class
thing fills `djuno`'s x2, gets counted, identified, and anaphorically
retrieved. `Content` cannot be that thing in this model — it is
computation-typed, deliberately without equality, and putting it in
the domain of individuals would make effects quantifiable objects. So
the crossing the untyped doctrine leaves implicit gets a name:
`Reify`, with `Holds` its inverse and the round trip as axiom (§9.1).
A proposition is the *reification of* a 0-adic relation — the
doctrine's slogan, plus the bridge it needed all along.

The asymmetry with `ka` is then principled, not accidental. Property
places (`ckaji`, `mutce`) are consumed by *application* — the selbri
applies the property — so they take function-typed operands directly
and `lo ka` lowers straight to the λ. Proposition places are consumed
by *aboutness* — nothing applies them — so they take the reified
object, and all the sumti machinery (descriptions, anaphora,
quantification, `du` as `CoRef`) runs on it.

The experimental pair `me'ei`/`me'au` shows where this design is
deliberately unfinished. `me'au` uses an abstract-predicate sumti as
a selbri of the referent's arity; at the propositional case the model
covers it under §9.1's singleton condition — for a singleton
proposition reference `abu`, `me'au abu` is `(Holds p)` at the
presupposed sole member: disquotation rather than the truth-predicate
(`abu jetnu` claims *about* the object; the axiom pair aligns their
truth conditions without conflating their shapes). The plural case
has no baseline reading — silent distribution would breach the
no-default-distributivity stance — and is registered with the
universal reading as candidate. Above arity zero,
`me'au`'s inverse `me'ei` manufactures property *objects* — and this
baseline has none: `lo ka` is a transparent λ, so there is no referent
for `goi` to bind and no domain for property quantification. Rather
than either building the full family now or foreclosing it, §9.1
records the reservation: the `Reify`/`Holds` shape generalizes row by
row (Chierchia and Turner's nominalization/predicativization pair is
the standing prior art), `Proposition` is the row-⟨⟩ member, and the
rest is a registered gap. On identity the reservation is careful
about what is already decided: the axiom pair makes `Reify` and
`Holds` mutual inverses, so proposition identity is exactly content
identity — intensional and dynamic, finer than logical equivalence —
fixed by the axioms, not open; and any future row's crossing, being a
function over the extensional `PredTerm<ρ>`, identifies β/η- and
pointwise-equal predicates by congruence. What stays open is only the
adoption-shape question (whether each row repeats the bijective
shape; how row isomorphism and any cross-row operators are typed),
and that is what makes the reservation cheap: adopting the family
later fills a declared hole instead of reopening the bridge.


## 3. Pin arguments

Condensed; each pin's full context is in spec §13. The ones that were
genuinely fought:

- **P1/P22 (xorlo, inner `no`).** "No default quantifiers. At all." is
  the xorlo page verbatim; everything else follows from `Refer` +
  nonempty plural references. For inner `no` that type argument shows
  only that `lo no broda` cannot be a *reference*; it does not show the
  form is meaningless, and guskant's gadri commentary ("Cannot say
  zero") supplies both the reading and the reason to want one: her
  unofficial `lo no broda = naku su'oi da poi ke'a broda`, motivated by
  answer continuity — `lo xo prenu cu jmaji …` answered by `no`,
  elliptical for `lo no prenu cu jmaji …` — the pattern that also
  carries `go'i`-inherited frames. The pin therefore special-cases
  inner `no` at the mapping layer to the zero-count (`No`) schema over
  the description's property and the bridi frame: substitution into
  question frames works, nothing touches the nonemptiness of the
  reference type, and anaphora to the form is correctly inaccessible
  because `No` exports no witness. (Ruling the form defective outright
  might look simpler, but it would rest on the unverifiable premise
  that usage avoids it — and it breaks the answer-substitution pattern
  that motivates the reading; hence the special case.)
- **P2 (`ro` imports).** Saying `ro gerku cu blabi` commits the speaker
  to there being dogs, and the commitment survives wrapping: `naku ro
  gerku cu blabi` denies the universal while still granting dogs, and
  `xu ro gerku cu blabi` questions the universal while still granting
  them. Surviving negation and question force is the signature of
  presupposition, not of an at-issue conjunct (a conjoined `∃` would be
  negated and questioned along with the rest), so the import is a
  `Presuppose` on the description quantifier's restrictor. The
  non-importing reading is not lost: bare logic's `ro da` maps to plain
  `∀` with no presupposition, so mathematical discourse pays nothing.
  Cost: universal claims over empty restrictors are presupposition
  failures rather than vacuous truths — the standard
  natural-language trade.
- **P5 (collections and `joi`).** Three independent choices are bundled only
  because they meet at the same boundary. Bare collection bases remain
  non-maximal: the evidence is xorlo's abolition of default quantifiers (P1)
  together with Example 6.52's anaphora, not CLL 18.11 — original 18.11
  glosses the bare `lo'i ratcu` of Example 18.83 as "the set of all rats"
  (the rejected maximal reading), and the citation edition's non-maximal
  wording there is this project's own amendment (fork commit `6c580fb2`),
  corroborative record that cannot ratify the pin; `Local` prevents that
  hidden `Refer` from falsifying Example 6.52's surface-anaphora count. General `gunma`
  is non-exhaustive because its official gloss says “partially specified” and
  attested uses of `se gunma` name only one family member; complete
  descriptors and `joi` add the defined converse cover. Finally `joi1` beats
  `joi2`: only the
  whole-forming reading distinguishes it from `jo'u` without reviving covert
  distributivity. `SelectExactly 1` chooses one result whole without asserting
  global uniqueness; number-neutral group descriptors are unaffected.
  Alternatives and the type/category costs are worked in
  §1.7a; the reopening tests are a genuine `joi` use whose result must remain
  the original plural reference, or a component-basis counterexample that
  cannot be expressed by the indexed cover/contribution interfaces.
- **P9 (`kau` exhaustivity is absent).** Three candidates fought:
  default-exhaustive (adds a claim CLL never makes), a `Vague`
  exhaustivity parameter (posits a decision point that *no Lojban
  expression can settle* — an idle wheel: vagueness machinery is owed
  where the language could precisify, and `kau` has no such route), and
  absence. Absence won, with its consequence stated plainly: unmarked
  answerhood has the weakest (mention-some-compatible) truth conditions,
  and stronger readings come from the embedding predicate's lexical
  presuppositions or separately stated content. `MentionSome` is removed
  because it duplicated the unmarked form. `Exhaustive` is not retained as an
  uninterpreted marker: defining it would require both a pure answer-content
  function and typed selection membership/equivalence across plural, tuple,
  label, and predicate-valued answer domains. With no Lojban exponent to
  justify that new generic interface, the candidate is gap-registered. The
  parallel with tenselessness
  and distributivity is exact, and deliberate.
- **P10 (`le`).** The two supports for a dedicated description
  relation fell (§2.6), guskant's expansion supplied the
  precedent, and the anchoring clause answered act-vs-identification:
  `le` lowers through `skicu` with the describing event anchored to
  this utterance's locution — performative, true by construction.
  `voi` = audience-deleted `skicu`.
- **P11 (`Generic`).** See §1.9; the fixed-prototype design died on the
  split-normality witness.
- **P16 (KOhA keyed).** `ko'a du ko'a` must be true; per-site contextual
  holes would let the two sites diverge. One retrieval per key.
- **P17 (termsets, no maximality).** CLL ch. 16 §7 (Examples
  16.41–16.45; the gloss follows Example 16.45) glosses `ci gerku ce'e re
  nanmu cu batci` as: two picked groups, "every one of the dogs bites each of the
  men" — full product — and stops. The coordinate-closure strengthening
  ("and no other dog bites them") makes the sentence false in situations
  speakers plainly use it for, so it is a named optional profile, not
  the default. The bare-PA half is pinned *against* the letter of CLL
  ch. 16 §6, whose account of bare numeric quantification is global
  ("exactly two things, no more or less" — Example 16.34) and
  distributive (`PA broda` as `PA da poi broda`): this specification
  takes neutral witness-set
  exactness — the xorlo-era reading, the one consistent with termset
  composition and witness export — and keeps the CLL-literal global
  reading as
  the named `GlobalExactly`. The divergence is documented, not
  smuggled — and it carries a positive compositional argument:
  witness-set semantics is what composes *directly* with dynamic
  anaphora — the selection's witness is the referent `ri` binds —
  where the global reading exports at best the maximal extension of a
  size claim, making the non-exclusion facts (§4.10's fourth runner)
  and termset composition awkward; and neutrality is what keeps
  collective predicates expressible under quantifiers at all (`su'o
  prenu cu jmaji` — a reading a distributive default cannot state).
  Motivation by composition and coverage, not preference. Independent convergence:
  solpahi's "A Simpler Quantifier Logic" derives the same reading from
  plural logic alone (bare PA = plural-existential over a PA-membered
  witness), and notes the bonus this specification inherits: witness
  existentials commute, so `ci gerku cu batci re remna` and its
  `se`-conversion agree — the scope asymmetry of globally-exact
  quantifiers was an artifact.
- **P8 vs the present-tense temptation.** CLL
  ch. 10 makes tense optional; "untensed = present" is an anglophone
  reflex, not a rule. But pure absence was also wrong, as compatibility
  review showed: CLL 10.1 itself enumerates the readings of
  the tenseless example and says "context resolves which is correct",
  and the Partee-style stove case (a tenseless denial targets one
  contextually relevant occasion) demands a contextually anchored time
  on episodic readings. The amended pin: tenselessness is
  reading-multiple — episodic readings carry a `Context` time facet,
  habitual/gnomic readings carry nothing, and the semantics never
  inserts a default; the choice among readings is upstream, like every
  ambiguity.
- **P12 (implicit `ce'u` at first unfilled place, counting converted
  places)** — subsumes the x1 tradition, matches practice, and declares
  multi-candidate cases distinct readings rather than vagueness.
- **P14 (`tu'a`, bare `jai`, intended underspecification).** CLL 11.10 calls
  `tu'a` a convenience that loses overt information, but its door example
  conventionally recovers opening and its confusing cases invite repair; CLL
  9.12/11.10 likewise leaves bare `jai`'s raised role unstated. The project
  pins both as occurrence-specific intended values retrieved through
  admissibility-constrained `Context`, with recovery required only to
  discourse relevance-equivalence and dependencies declared per reading.
  Bare `jai`'s value is a role relation from the raised sumti to the old-x1
  abstraction moved to `fai`: `Fn<(Referents<T>, Referents<A>), Content>`,
  with T and A fixed by the resolved typed reading. CLL says “one of the
  sumti” and “an abstraction,” not specifically Entity and Eventuality, so
  hard-coding those two sorts would violate P13; `JaiRoleAdmissible` is the
  axiomatic constraint because the reflection-free core exposes no
  abstraction AST from which to enumerate inner roles. CLL 9.12 fixes the
  x1/`fai` routing, CLL 11.10 leaves the inner argument unstated, and the BPFK
  place-structure record independently describes the same raising.
  The rejected `Vague` analysis has the wrong negation and truth conditions:
  it ranges over every admissible abstraction/role rather than the one meant.
  A genuinely no-particular-value use would reopen the separate
  `SomeAdmissible` candidate. Official `ju'e` is the registered surface
  candidate, not yet a defined witness. Cost: the resolver carries real
  semantic responsibility, and speaker and hearer may associate different
  resolved terms with one utterance token.

- **P24 (universal clause eventuality; missing CAhA).** CLL 11.2 says `nu`
  captures the event or state of the bridi considered as a whole, while the
  grammar permits tense, CAhA, ROI, and ZAhO on `du` and other eventless
  selbri. `ClauseContent` supplies the common typed target. Direct lexical
  episodes preserve their event; `StateClause` handles equality, negative,
  quantified, generic, and compound claims; disjunction retains a successful
  branch event. For actuality, the tempting “bare assertion always actual”
  rule is too strong without a reading qualification: CLL 10.19 explicitly
  says missing CAhA can be actual or potential and that context disambiguates.
  The pin therefore treats omission as reading-multiple among the four named
  CAhA modes. This preserves ordinary actual `mi citka`, CLL's capability
  `ro datka cu flulimna`, and explicit `ca'a` as a mode-fixing contrast.

- **P26 (prenex scope; topic resolution).** The prenex half is
  CLL 16.2 read at face value plus the P18 surface-scope doctrine —
  the losing alternative (scope normalization independent of prenex
  order) contradicts CLL's own donkey examples. The topic half's
  evidence is CLL 19.4's fish (`le finpe zo'u citka` — "the sentence
  doesn't say" whether it eats or is eaten): the surface leaves a place
  choice unresolved, but that does not show that one speaker intends both or
  neither. A constrained `Context` retrieves one intended member of the
  `TopicResolution<ρ>` union; place-fill is available for a single open bridi,
  with coarse `srana`-aboutness (CLL Example 19.10's money topic) as the other
  arm.
  Cross-clausal place-linking remains a gap. Why not the Tanru link: types do
  not fit —
  a topic is a referent, not a modifier over the head's
  row. Why no segment-state effect: `ni'o` owns segments, and two
  owners of one state need an adjudication nothing asks for.
- **P27 (imperatives, vocatives, the active addressee).** CLL 2.14
  says `doi` *sets* `do` — binding language, exactly the `goi`
  mechanism — and mutating the ctx `Audience` instead would make
  "addressee of this utterance" ambiguous with "current do-value" and
  retroactively falsify utterance facts. The active-`do` binding with
  Audience fallback also makes `doi djan. ko klama` command John with
  no extra machinery — the objection that pure binding under-serves
  `ko` dissolves once `ko` reads the same active value. Force marks
  the nearest *performed* clause only: `lo nu ko klama` constructs
  content (the alternative — force extrusion from abstractions —
  would make `Reify` perform).
- **P30 (relation variables; templates).** `bu'a` needs second-order
  *quantification*, not second-order *objects*: the core's
  quantifiers are typed, so `∃` at `PredTerm<ρ>` expresses CLL 16.13
  directly, while reified predicate objects (§9.1's reserved family)
  would bring the identity-granularity questions along for nothing —
  no identity claims occur. The prenex constraint is CLL Example 16.107
  verbatim. `cei` stores more than a relation (CLL 7.5: fills, tense,
  negation ride along, later fills override), so the binding is a
  bridi template at the ⊳ layer — a `PredTerm` value would wrongly
  make `go'i`-style override inexpressible.
- **P32 (one performance).** `.i ja` decides it: a disjunction is one
  claim, not two acts. `ClauseOr` preserves the successful branch event and
  the host closes that `ClauseContent` once; uniformity carries one-performance
  force to `.i je`, whose `ClauseAnd` event is the joint State
  (harmless there — asserting a conjunction commits to both, and `∧`
  shares `Do`'s accessibility row, §5.4). The losing alternative (two
  acts plus a cross-act connective) has no act to carry `∨` at all.
  The earlier `.i joi = Do` claim is withdrawn: `JoiClause` now supplies its
  complete event/content contribution, while the surrounding structured
  `ConnectionPlan` performance remains a gap rather than a `Do` fallback.
- **P33 (tanru-unit jeks).** With a shared head, connecting whole
  units would duplicate the head predication (two houses from one
  `zdani`); binding one constrained-`Context` intended link per conjunct and
  connecting the link applications keeps one head and distributes classically
  (`H ∧ (l₁ ∨ l₂)` ≡ the unit-level disjunction) while keeping one
  discourse site per referent. Distinct heads have nothing to share,
  so they connect as whole predications.
- **P34 (`vu'o`).** CLL 8.8's own gloss ("both Frank and George are
  claimed to be men") is per-connectee; predicating collectively of
  the `Combine` would change collective predicates' truth conditions,
  and distributing to *members* would over-distribute into plural
  connectees. Immediate-connectee distribution is the only reading
  that preserves both the CLL claim and the connective's structure;
  the restrictive extension is recorded as ours.
- **P35 (ROI).** Conjoining a count onto the ordinary single-event
  closure leaves an uncounted existential event in scope — the count
  must *replace* the closure, over distinct eventualities in the
  interval. Under universal clause eventuality the counted events remain the
  component instances, while `StateClause` supplies the eventuality of the
  count claim itself; confusing those two levels recreates the original bug.
  The interval default follows CLL 10.9's own words
  ("unspecified size, at least part … in the past"): a recoverable
  anchor (`Context`) with genuinely loose extent (`Vague`).
- **P37 (`ji'i`).** CLL 18.9 distinguishes positions; one uniform
  tolerance would erase the rounding reading (suffix `ji'i` with
  `ma'u`/`ni'u` direction) that CLL states. Both positions denote
  `Number`-valued `Vague` families over different regions — tolerance about
  the anchor vs the rounding preimage of the stated numeral (each
  nonempty by VC1) — so the underlying quantity is always the bound
  Number, never an unconstrained "true value".
- **P39 (`CoveredBy` placement).** The dog-plus-cat countermodel requires a
  no-residue law, but it does not justify making descriptions stricter than
  predication. Official `lo` and the BPFK gadri equation identify the two;
  collective heads independently require per-row plural semantics. The
  adopted lexical-extension placement is therefore smaller and preserves the
  xorlo identity. Guskant's Condition₁/cut-bread argument motivates the
  atomless-safe overlap clause and cumulative mass profiles, not the placement
  decision. Cost, rejected alternative, and reopening witness are recorded in
  §1.7b.
- **P40 (composite personal pro-sumti).** Original CLL's mass equation loses
  on the no-inheritance probe: a group of humans is not thereby human, while
  bare `mi'o remna` is attested. Neutral `Combine` supplies distributive,
  collective, and reciprocal lexical satisfaction without equating one
  argument to the two-clause `.e` form; explicit `joi` remains available for
  a constituted group. The independent post-xorlo discussion converges on
  this shape, while current CLL only records the project's own amendment.
  Exact context constraints, costs, and reopening evidence are in §1.7c.

## 4. What would change our minds

A design-record note first, owed to accuracy: several of this document's
positions were genuinely contested before they settled — the drops of the closure and witness
primitives, the sort-hierarchy trims, the tanru/scalar formers' survival,
`Generic` over fixed typical references, termset non-maximality, and the
`kau` representation among them; this document records the losing
alternatives beside the winners, and one proposed reading (`na'e`
weaker than `¬`) was overruled by primary text (§1.8). One separation *was* found during
the rounds: the dependent-witness sentence `ro prenu cu ponse ci gerku
.i ri tatpi` genuinely separates an embedded quantifier's witness from
any single top-level plural — and was absorbed by generalizing the
mapping to a selected strong joint-locus reading, not by an
equivalence-preserving normalization of the compositional selection.

Standing invitations, recorded so future revisions know where to push:
evidence for a Lojban surface selector of the weak dependent-witness reading,
or a plural-information-state account that removes the current strong
reading's retroactivity (narrows §1.6); a facet-joining sentence
where dynamic `∧` mispredicts (revives a dedicated joining operator); a
sentence forcing world variables into terms (moves intension into the
syntax); a genericity theory that derives `Generic` while preserving the
`lo'e`/`le'e` contrast (demotes it to the library); evidence that
speakers systematically read unmarked `kau` exhaustively even in
non-`djuno` frames (reopens P9); community usage data on termset
maximality (reopens P17's default); and a construction where
set-*objecthood* at a lexical place does work that member-wise
predication plus `SetOf` cannot (reopens §2.8 — the hunt found
none; the candidate that fails is `lo selcmi cu simxu`, which the
two-sort typing resolves correctly and uniform set typing renders
ambiguous). Each was hunted during the design
rounds; where the hunts came back empty the invitations record the
negative result, kept falsifiable, and where a find was absorbed (the
dependent witness, above) the invitation is narrowed to what remains.
