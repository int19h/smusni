# Rationale for the Lojban semantic core

This document explains the constructions and decisions in [the specification](spec.md):
their purposes, alternatives, costs, and supporting evidence. Example links
identify worked terms or the source records used in the comparison.
Hypothetical model counterexamples are not presented as corpus evidence. Worked examples
are in [samples.md](samples.md). Sources are cited by author or title and
section; full citations and edition information are in the specification's
References section. [The decision ledger](decisions.md) distinguishes adopted
rules from unfinished work. This rationale is explanatory, not normative;
historical alternatives do not override the current specification.

## 0. Method

A primitive requires a necessity or factorization argument. A necessity
argument identifies a supported meaning for which the remaining core has no
adequate construction. A factorization argument identifies shared semantic
structure that a generic form represents more simply or consistently. Such
forms need not have a direct Lojban spelling. Derivable operations remain
library definitions. These criteria follow spec §1.1; convenience alone does
not justify a primitive.

The construct discussions state the semantic contrast, examples, candidate
reductions, reasons for the chosen signature, and costs. A counterexample to
one reduction is not a proof that every alternative architecture fails.
Where no general impossibility result is established, the argument is a
comparison of the stated alternatives.

Pins select among readings permitted by incomplete or conflicting evidence.
Their justification combines source evidence, compatibility with competent
usage, and formal consequences. Sources do not determine the decision by
themselves. Section 2 discusses cross-cutting design choices; §3 records the
reasons for individual pins.

## 1. The constructs

### 1.1 Labelled place rows

Lojban operations address places by label. Examples include
`klama fe ti tu`, with an explicit x2 fill; `mi klama ti zi'o`, with
place deletion; and `klama fi'a ti`, which asks which place receives a
fill. A representation using positional functions would still need a mapping
from these labels to argument positions.

The core uses labelled records for that mapping. `PredTerm<ρ>` is a
transparent alias for a row-function, `Record ρ → Content`, rather than
an additional primitive relation type. No analyzed distinction requires
separating relations with the same denotation at every complete row record.

`At` fills one labelled place by partial application; multi-place notation
expands to nested fills. Fills at distinct labels commute because their
operands are already values. This does not assert that effectful computations
producing those values commute. The type theory must support labelled records
and the compatible-label domain used by `fi'a` (spec §4.1 and §4.7).

Worked examples: [place filling and deletion](samples.md#1-predication-and-closure).

### 1.2 Clause formation and `Close`

A resolved bridi can be complete despite omitted arguments. Tense and
abstraction also need access to its eventuality before clause closure.
For example, `mi klama` needs contextual ordinary arguments and a going
event, while `ta pu du lo mi zdani` needs a past holding state even though
identity has no lexical event place.

Existentially closing every omitted ordinary argument would change negation:
`mi na klama` would say that there is no destination to which the speaker
goes. The selected reading instead denies going to the contextual destination.
Contextual closure therefore remains distinct from event closure.

Adding an event or situation argument to every relation is a coherent
alternative. It would nevertheless need to preserve ordinary binary equality
for guards and definitions, and value-producing functions such as addition.
Smusni uses `StateClause` to factor their declarative event interface instead
of introducing separate lifted versions for each operation.

`ClauseContent = EFn<(Referents<Eventuality>), Content>` leaves one
eventuality parameter open. `DirectClause` uses a lexical event;
`StateClause` supplies a holding state where required; `CloseClause`
closes the parameter while retaining its selected value as the closed
Content's event. `Close` abbreviates their actual-CAhA composition, not
a universal default for surface omission.

The existing operations do not supply the same holding-state construction.
Ordinary existential closure matches `CloseClause`'s run but does not
retain its local witness as the event intension. Nor can ordinary function
application overwrite that intension: `((λ e. ⊤) x)` must remain equal
to `⊤`, not acquire x as additional structured content. These distinctions
motivate the selected primitives.

The cost is an explicit composition policy for direct, joint, branch, and
holding events in spec §9.3. Equality and arithmetic still determine each
claim's truth. A mathematical holding state may be unbounded; its actuality
still follows the truth of the claim. Reconsider the factorization if
a uniform situation-argument design derives these same interfaces without
duplicating non-clausal operations.

Worked examples: [expanded closure](samples.md#1-predication-and-closure) and
[event and tense composition](samples.md#2-events-tense-facets).

### 1.3 The specificity triad: `Refer`, `Context`, `Vague`

The selected model distinguishes introduction, contextual retrieval, and
soritical vagueness. Their scope and truth behavior motivates separate
operations:

- Refer introduces a reference, as in `lo mlatu cu blabi .i ri jbena`.
  A sentence-local existential does not by itself retain a binding for the
  second sentence; a quantified encoding would need the same scope and
  continuity rules. A definite-description operator with uniqueness would
  add a condition xorlo lo does not require. The comparison with DRT/DPL is
  a dynamic indefinite at plural-reference type. Its reference-level
  restrictor may be effectful; a member-level property uses the pure
  CoveredBy lift (§1.7b).
- Context retrieves an intended value without introducing a new descriptive
  reference. Examples include omitted destinations, `co'e`, `zu'i`,
  tanru links, and `tu'a` abstractions. A free-variable encoding would still
  need the declared type, admissibility condition, dependencies, and site/key
  identity supplied by this interface. Recovery need only preserve differences
  relevant to the discourse; the resolved meaning nevertheless uses one value,
  not a disjunction of listener guesses.
- Vague represents sharpenings of one soritical concept or boundary, such as
  a “many” threshold, gradable cutoff, or approximate tolerance. There is no
  intended exact cutoff to retrieve. Treating unrelated topic or tanru
  resolutions as a supervaluated family would require all admissible
  resolutions, not the one intended. Existential choice would instead allow
  an unintended alternative to make a positive claim true and would deny all
  alternatives under negation. Neither gives the selected intended-value
  behavior. The VC law therefore applies to sharpenings of one concept,
  with correlated site values and supertruth where invoked.

The classification of each Lojban construct into this triad (or into
absence — no machinery at all) is itself normative (spec §6.1), with
the recovery test printed as the decision rule. The disputed entries settle
coherently: `co'e`/`do'e`, tanru, `tu'a`, bare `jai`, and topic links all
convey occurrence-specific intended values through constrained `Context`;
conventionality changes resolver priors, not semantic type. Gradable
predication splits — *which scale/domain* is `Context` (say the wrong one and
you have misunderstood), *where a soritical cutoff sits* is `Vague`; scalar
`OtherThan` directly denotes the complement region, not a hidden finer choice;
and unmarked distributivity is absence, not a parameter (see §2.5).
No analyzed construction requires the possible `SomeAdmissible` existential
choice former. Official `ju'e`, explicitly glossed as a vague non-logical
connective but left without compositional truth conditions, is the concrete
gap-level candidate; its source and usage adjudication must establish whether
it has genuinely no particular intended connection before that former can
enter the baseline.

Worked examples: [descriptive reference](samples.md#3-reference-and-descriptions) and
[contextual and vague values](samples.md#8-intended-underspecification-and-soritical-vagueness).

### 1.4 Projective content: `Presuppose` and `Supplement`

Projective commitments behave differently from at-issue conjunction.
An explicit `MaxRefer P` carries an inhabitedness condition even when
its result is used by a negated predicate. Ordinary bare `ro` has no
such import under P2. In `xu lo gerku noi blabi cu melbi`, the question
concerns beauty while whiteness remains a side commitment.

Putting each condition in an ordinary conjunction under negation or question
force would give it the wrong scope. `Presuppose` and `Supplement`
therefore have separate projection rules. They also differ from each other:
a presupposition may be satisfied by existing context, whereas a supplement
contributes a commitment anew.

`Supplement` has an explicit anchor. A side depending on a quantified
variable commits per instantiation within that binder, as in the relevant
reading of `ro gerku noi ke'a se cmene cu bajra`. The model must supply
the corresponding handlers and accessibility rules; an unscoped global side
condition would not preserve those dependencies.

Worked examples: [relative clauses and supplements](samples.md#4-relative-clauses-and-supplements).

### 1.5 The accessibility table

Truth conditions alone do not determine accessibility. The consequent of
`ganai da mlatu gi da ciska` can use the antecedent's variable;
disjunction keeps branch introductions local; negation exports no internal
introduction. Spec §5.4 states these dynamic rules. A model must realize
them; the table is the normative contract, not proof that the combined model
has already been constructed.

Biconditional and exclusive-or are primitive because no expansion in the
remaining core has been shown to preserve their once-per-operand evaluation,
accessibility, projective behavior, and event intension. In an effect-free
logic the usual truth-functional expansions suffice. With effects,
`(A → B) ∧ (B → A)` can evaluate each operand twice. Copying source text
also creates distinct contextual sites and can change handler placement.

Sharing a formed Content or function value can preserve its sites. It does
not, however, share the result of evaluating that value. `Let` shares inert
values; `Bind` shares a computation's returned value. Content's run returns
Unit, not a reusable truth value. Any proposed reduction must also preserve
the separate event intension. Each implication keeps its introductions local;
neither supplies new references to the other. This does not establish the
expansion's equivalence: its evaluation, site, projective, and event behavior
still has to match the primitive.

A proposed `TruthOf : Content → RefComp<Bool>` would add an explicit
truth-observation facility. Its typing, effect retention, and use outside
these two connectives would require their own semantics. It is not an
expansion using existing forms, and no supported Lojban construction has
established a need for it. The project therefore retains the two restricted
connectives instead of adding this general facility solely to derive them.
This is a comparison within the chosen calculus, not a general
inexpressibility theorem for effectful logic.

### 1.6 Reference continuity within scope

A reference introduced once can be shared by later uses within its scope.
For example, `lo mlatu cu blabi .i ri jbena` uses one cat reference for
both assertions, not independent selections for whiteness and birth.
The binding supplies this correlation without a term-level run identifier
or a witness-retrieval registry. The [binding and continuation examples](samples.md#12-direct-binding-notation)
distinguish the successful-reference route from the bounded route that also
preserves later assertions when a source fails.

This mechanism does not decide which surface constructions introduce a
reference that can survive into another sentence. Smusni retains ordinary
positive existential continuity, independently bound descriptions, and
supported in-scope dependent references. A numerical or universal quantifier
does not additionally construct an outward group or family merely because
a later anaphor asks for one. Section 1.6a explains this boundary; §1.14a
explains the source and performance machinery that remains necessary.

### 1.6a Why reference recovery stops at scope boundaries

We considered recovering references beyond their original scopes so that
ordinary quantified expressions could support more later anaphora. The
attraction is practical: a speaker can introduce several dogs with a count
and then want to say something about those dogs. The difficulty is not
binding an available group once and reusing it. It is determining which
group a quantifier supplies, when an embedded source can supply anything
outside its scope, and how dependent references remain correlated.

The current policy keeps ordinary reference continuity but declines these
additional group and family exports. This is a compatibility–complexity
choice, not a proof that richer dynamic semantics is impossible. The
[profile comparison](https://github.com/int19h/smusni/issues/90#issuecomment-5619006450)
distinguishes shared binding from reconstruction and records the limits of
the simplicity claim. Spec §5.6 states the current rule.

#### What recovery would provide

Consider the elicited example `su'o re gerku cu sipna .i ri cu cimei`
in a situation with four sleeping dogs. A reported judgment found the intended
three-dog continuation odd but not false. This supports the
possibility of a selected-group reading. It does not establish a community
usage pattern or explain the judgment of oddness. The [witness-policy
record](https://github.com/int19h/smusni/issues/15#issuecomment-5593166813)
retains the example and evidence; the [worked comparisons](samples.md#5-quantifiers-witnesses-anaphora)
separate such extensions from baseline lowerings. The direct-reference
`mei` bridge remains a mapping obligation; this is not a complete `cimei` lowering.

A recovery rule could associate the lower-bound antecedent with a reference
to selected individuals S, at least two dogs, and preserve it through the continuation.
S could contain two, three, or all four sleepers. A later predication would
constrain that same assignment, not choose a fresh red or tired group.
That is a coherent design target. It requires neither an exactly-minimum
choice nor prior salience as an additional premise. S and H below are sets
in the comparison, not additional Set or Group objects introduced by the Lojban.

The fragment contrast `su'o re gerku .i ro ri cu xunre` reinforces one
point: adding a predicate does not by itself explain why a selection should
become exhaustive. It does not supply a complete fragment interpretation or
a general export rule. Likewise, CLL v1.1 §7.6's same-referent rule constrains
reuse after a reference has been established; it does not uniquely specify
the output of every quantified antecedent. The source limitations and the
Bays/Llambías/Selpa'i discussions are recorded in spec References under
“RI witness-policy record,” “BPFK anaphora/variable notes,” and
“Quantified-reference discussions used in P42.”

#### The choices added by generalization

A reference-recovery extension must answer several distinct questions.

- Output of a count. The truth of a lower-bound claim does not select
  between a subgroup S and the complete qualifying population H. Exactly
  the minimum size, a contextually salient group, and a default H with
  optional subgroups are further coherent policies, each with its own
  additional rule. Exact counts must still exclude extra qualifiers;
  witness recovery cannot remove their truth-conditional upper bound.
- Support across logical boundaries. A true `A or B` need not establish
  a witness internal to A. Recovering an object that merely satisfies A's
  noun restriction can discard the relation that made it relevant;
  requiring a verifying witness can add commitment to A. Under exclusive-or
  that commitment also rules out B. Such readings may be coherent, but
  require more than preserving an already available reference. Negation
  presents the same distinction between an outside reference and a new
  source created inside the negative content.
- Dependent families. In `ro prenu cu ponse ci gerku .i ri tatpi`,
  an intended “each person's dogs” continuation needs more than an
  unstructured collection of dogs. It must preserve which dogs belong to
  which person and how later predication uses those dependencies. A joint
  quantifier spanning both sentences can express a stronger combined
  condition, but does not by itself export the first sentence's witnesses
  compositionally or preserve the two assertion occurrences. The
  [dependent-reference comparison](samples.md#5-quantifiers-witnesses-anaphora)
  displays that distinction.
- Reference realization. A proposed selected group must have a suitable
  representative in the plural carrier. Finite joins alone do not prove
  every desired clean group is admitted on a nonminimal carrier. This is
  a conditional coverage obligation, not an established need for a new
  universal comprehension axiom.
- Correlation and continuation. The group has to remain the same across
  uses, including when later claims fail. Reconstructing a previous S from
  the original noun and predicate alone need not recover S. Defining one
  source and sharing it can avoid that reconstruction problem, but still
  needs scope and performance laws. The [correlation controls](https://github.com/int19h/smusni/issues/89#issuecomment-5616741210)
  distinguish shared selection from independent reselection.

These questions do not form one unavoidable package: a language can permit
some extra exports and reject others. The concern is that a local rescue
for a numerical example does not determine a uniform policy for other
quantifiers, logical embeddings, dependencies, and later utterances.
The source record supplies arguments and examples, but not one complete,
uniform extension that the baseline can simply adopt.

#### Why the scope-based boundary is preferable here

The current rule determines availability from the resolved structure and
binder scope, without first computing whether the speaker's assertion is
true. New sources inside negation, disjunction, exclusive-or, or a closed
governor do not escape. Already available references remain available under
their existing scope rules. Supported in-scope dependencies, including the
[feeding-donkey example](samples.md#5-quantifiers-witnesses-anaphora), do not
require an additional outward family.

For a common positive use, a description can supply the group directly:

`lo su'o re gerku cu sipna .i ro ri cu xunre`.

On the stated finite, clean member-count and memberwise reading, this introduces one reference containing
at least two dog units and predicates redness of every member of that same
reference. The [description alternative and its limits](https://github.com/int19h/smusni/issues/89#issuecomment-5617191105)
show why much of the intended content remains expressible. This is not
a substitution theorem: collective predication, negation, and dependencies
can distinguish the description from an outer count.

The cost is therefore real bare-form incompatibility, not unrestricted
equivalence with the more permissive proposal. The advantage is a smaller
baseline export contract while retaining ordinary descriptions and a
plural-capable core. Explicit plural quantification and other richer profiles
can be developed without silently changing standard numerical quantifiers.

#### What this choice does not remove

Scope-based accessibility still needs reference introduction, plural carriers,
ordinary existential continuity, open answer sources, permitted quotation
crossings, and source/force association. A structurally available source can
lack a value; that is not an out-of-scope reference. Descriptions and inner
zero also retain their carrier and admission obligations.

In particular, `lo gerku cu sipna .i ri cu xunre` still requires a shared
source whose empty result makes the first assertion false and the later use
undefined. Preserving that distinction through captured content, replay, and
the event/proposition model remains the work discussed in §1.14a and the
[bounded continuation example](samples.md#121-a-source-preserving-pair-of-assertions).
It is not complexity eliminated by rejecting quantified-group recovery.

A richer export policy should be reconsidered if stronger usage evidence
or a compositional construction justifies its additional permissions and
costs. Merely lacking an implementation does not prove a reading impossible;
conversely, binding a selected reference in a prototype does not settle the
language's general accessibility rule.

### 1.7 The plural algebra, without covers

`Combine` and `Among` represent number-neutral reference, join, and
subreference. `mi jo'u do bevri lo pipno` predicates carrying of a plurality;
`ko'a me ko'e` expresses subreference. Outer `re lo mu plise` instead
counts individuals within an independently bound description; it is not a
neutral selected-pair argument under L3.9.

A set representation is equivalent within the fragment satisfying discipline
D in spec §4.8. Section 2.8 states all its premises and compares the designs.
The selected plural algebra does not assume atomistic generation, a boundary
motivated by guskant's Condition₁ proof and cut-bread interpretation. The
atomistic equivalence does not establish coverage of that case.

Both designs need to distinguish member-directed predication from predication
of set objects. The objection that a mathematical set cannot act does not
address a set representation used only to denote its members. Section 2.5
explains why unmarked predication has no covert distributivity parameter.
Explicit readings use `lu'a`, `Distrib`, and group gadri.

Collection gadri do not silently maximize their base. Bare `loi P`/`lo'i P`
first use the same ordinary non-maximal `Refer P` as `lo P`, under `Local`,
then refer to the group/set object constituted from that base. `Local` is
needed, not decorative: without projection of the hidden introduction,
CLL Example 6.52's `lo'i ratcu … .i ku'i lu'a ri …` would leave both the rats and the
set in the discourse store, while the text has introduced only the set sumti.
It retains the selected base as a lexical `Bind` value and all truth/
projective effects, hiding only its anaphoric slot. This preserves P1's
ordinary selection and the antecedent distinction in
CLL Example 6.52. The relevant support is xorlo plus that example, not the
maintained CLL's project-authored non-maximality wording; see the P5 discussion
in §3. The surface eligibility boundary remains explicit.
The outer restriction is singular-object-valued:
bare outer reference remains number-neutral, but each selected group/set must
individually have the complete base. The all-P base remains available through
explicit inner/descriptive `ro`, the library `MaxRefer`, or a context that
genuinely selects it; bare outer `ro` does not build that base. The cost is
only that mathematical users must state maximality when the context does not
already make it clear.

Worked examples: [plural references, groups and sets](samples.md#3-reference-and-descriptions).

### 1.7a Constitution: why `joi` is not another plural join

Decision. `joi` forms a constituted whole (`joi1`); `jo'u` remains the
plain plural join. The official dictionary calls `joi` “mixed together,
forming a mass” and `gunma` a whole composed of x2, while current CLL 14.14
contrasts a group that acts as one object with `jo'u`'s still-plural result.
The BPFK record is internally revealing: its English proposal describes
unchanged referents plus non-distributivity (`joi2`), but its formal equation
is `X joi Y = lo gunma be X .e Y` (`joi1`). Smusni uses the whole-forming reading because unchanged referents plus
non-distributivity add no content under the selected predication policy: `Combine` plus P4 already leaves
collective/distributive behavior to the lexical predicate. A covert
“do not distribute” flag would make `joi` a redundant `jo'u` plus the very
reading parameter P4 rejects. Contrast `mi joi do bevri lo pipno` (a group
whole carries) with `mi jo'u do bevri lo pipno` (the plural argument is
neutral; `bevri` decides what configurations satisfy it).

One type-preserving mass constructor would not cover the required result types:
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

Why the layers. Official `gunma` is glossed as partially
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

Why a basis. Components are not atoms. People may be team members;
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

Cross-locus payoff. The same event instance gives `.i joi` its compound
event and gives ordinary conjunction its model-level `joint_M`. The canonical
conjunction basis is associative, transparent to its own nested wholes, and
treats `hold_M(⊤)` as null, so the clause-event interface and the connective
share one composition of joint events. `JoiClause` supplies content but
does not settle performance roles, UI targeting, or transcript spans; those
remain #6. Property rows with no declared contribution basis, `pe'e joi`, and
`joi nai` likewise remain bounded gaps.

Canonical aggregate identity versus organizations. Explicit `joi` and
`lu'o` must succeed for arbitrary nonempty components and must not select one
of several rival “bare aggregates” accidentally supplied by a model. The
adopted answer is a primitive, rigid `Aggregate κ g` classification plus
one-way rigidity (R), existence (E), within-class uniqueness (A), and local
complete-cover functionality (F). `Massify` restricts its result reference to co-refer with the
canonical aggregate's lift. Selecting a reference with count one does not
entail that contract on a nonminimal carrier. This reference constraint
applies at the construction's governing scope, not through an invariant-
description hoist. Descriptors remain descriptions: `loi`/`lei`/`lai` may refer
to the canonical aggregate or to an independently individuated team, family,
body, committee, or other organization whose complete current cover happens
to be the same.

<a id="example-coincident-organizations"></a>

Two constructed countermodels fix the boundary. First, budget and ethics committees may
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
example supports persistent described wholes rather than mutable bare
constructor outputs. The 1994 sumti-paper draft states the extensional
candidate; Clifford's 2002 “intensional, with all the horrors” response exposes
its identity/anaphora costs. Llambías' 1995 `re loi broda` puzzle exposes the
counting problem, and Selckiku's 2011 pinkie-and-bug example supports arbitrary
explicit aggregation without its proposed inheritance gloss. Bays and
Llambías' 2011 exchange supplies both the complete-constituents reading and
the need for first-order group objects when groups are quantified over. These
sources motivate and test the project law; none independently ratifies it.

Rejected alternatives are therefore: global or situation-local uniqueness
over all groups (organization collapse); fully model-given manufacture
(no success or identity guarantee for `joi`/`lu'o`); no group objects (loses
outer counting, equality, anaphora, and nested partitions); distinct group
sorts for aggregates and organizations (makes their possible identity
ill-typed); and the rigid-cover biconditional (collapses permanent
organizations). The cost of the adopted primitive classification is explicit
model structure, but it is exactly the distinction the surface constructors
need and is factored by both `joi` and `lu'o`.

Costs and source limits. Contemporary CLL's clean group prose is partly
this project's own amendment and cannot ratify the choice by itself. Original
CLL supplies the blue/red and joint-cause phenomena but not a coherent
polymorphic model; the 2018 wiki proposals likewise assume the hard event/
property realization step. The indexed interfaces are therefore a
prescriptive construction justified by coverage and type discipline, not a
claim that the sources already contained it. Complete constitution is exact
relative to the selected base; P39 now makes the base's own no-residue
behavior part of its resolved lexical extension, without imposing a count
profile on mass terms.

Worked example: [group constitution](samples.md#3-reference-and-descriptions).
The [event/property mixture examples](samples.md#14-meanings-without-analyses)
are explicitly marked as lacking complete analyses.
The [coincident-organization countermodels](#example-coincident-organizations)
above test the identity laws; they are not corpus observations.

### 1.7b Count and mass coverage: lexical extension, not descriptor repair

<a id="example-dog-plus-cat"></a>

The no-residue condition is needed because if `gerku(r)` at plural type were left wholly
unconstrained, a model could make it true of three dogs plus a cat, while
`CardBasis r gerku = 3` simply ignored the residue. `CoveredBy` closes that
hole and remains meaningful without atoms: every subreference must overlap a
P-unit, but a P-unit may itself be indefinitely divisible. Guskant's
Condition₁ proof and cut-bread interpretation are the motivating witness for
that second conjunct, not a proof of the project's lexical placement.

Two placements are coherent. The rejected descriptor-specific repair made
`lo R` select only `R(r) ∧ CoveredBy(unit_Rℓ,r)` while leaving nuclear
`R(r)` weaker. The selected lexical-extension rule makes the resolved `R_p`
itself obey that equation wherever its lexicon place/reference mode declares
a unit profile; `lo R` stays literally `Refer R_p`. The official dictionary
and the BPFK gadri table both say `lo broda = zo'e noi broda`, so the
descriptor-only alternative creates an unsupported asymmetry. It also buys
nothing for collective heads: `lo bevri be lo pipno` may denote a team that
carries the piano even when no member does, so such rows need their own direct
plural condition under either design. Adding a descriptor layer on top merely
duplicates the per-row distinction.

The same point blocks a lexeme-wide count/mass Boolean. Official `nanba`
means a quantity of or container of bread; substance portions can be
cumulative and divisible, while container and kind modes have different
units or direct plural conditions. The schema is therefore per place and
resolved reference mode. Count profiles, cumulative substance profiles,
singleton-container profiles, and direct collective/kind conditions are
lexical alternatives, never a covert choice at application time. Actual row
values remain #12 work.

The same no-residue condition is shared by the other relevant operations. All exporting
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

The member-level lift uses the same no-residue law for a `Refer` restrictor
written over the *member* sort — the hidden `lo'i`/`loi` base `λx. gerku x`,
or the outer collection property `λg. CompleteGunmaAt κ g base`, which has
no lexical row to supply a plural extension. Its denotation is the defined
lift `Refer Q ≝ Refer (λr. CoveredBy Q r)`; nothing new enters, because
P39's equation and `MaxRefer` already are this lift. Each rejected
completion fails a witness. *Singleton-only* (one member, which is `Q`)
loses xorlo's number-neutrality and contradicts L3.6's several-object
result. *Some member is `Q`* lets `lo gerku` carry a cat into `ri`.
*`Distrib` alone* — the textbook plural-logic restrictor, "X are Fs" iff
each of X is F — is right wherever every plurality has individuals among
it, and that is exactly the assumption §4.8 declines: a unitless subreference may overlap a nonminimal bread-unit embedding while
having no represented T-unit among it, making `Distrib gerku` vacuous there.
The overlap condition blocks dog-reference to that residue. Guskant's Condition₁
motivates the non-atomic boundary under her individual definition; it does not
prove that every Smusni first-order lift is minimal or that every loaf has no units. *Reference-level only* forces
L3.6 to spell its per-object condition by hand, which is the lift again.
*Lexical-only* is silent for every non-lexical restrictor. The lift is pure
by construction — it sits under `∀`/`∃` — so a member property whose
formation needs contextual sites (official `gerku`'s breed place, a `gunma`
basis) has them bound outside the `Refer` and shared, as the comprehension
forms already require; site identity makes the hoist meaning-preserving.
The reference-level restrictor itself is `EFn`, because `lo nu mi klama`
must sequence its omitted-place sites inside the event property (L9.6), and
`Local` still projects a hidden base's introductions exactly as §5.2 says.
The record supports the shape from both sides. The BPFK definition
`lo [PA] broda = zo'e noi ke'a broda [gi'e zilkancu li PA lo broda]` applies
the restrictor to the plural referent and counts by the unit `lo broda`;
guskant's commentary gives plural constants a reference-level axiom
(`ganai C broda gi su'oi da zo'u da broda`) and the atomless Condition₁;
xorxes's "`{lo broda}` always refers to brodas" (2014-02-07, "Individuals
and xorlo", Message-ID in the References) is the member-level intuition the
lift makes exact; and plural logic's distributive restrictor (Boolos, McKay,
Oliver & Smiley) together with Link's sum-closure of the singular noun are
the literature's two halves of the same equation, the atomistic and the
lexical one. Cost: the two spellings of one restrictor coincide only for
count-profile rows, so a specimen should write each row at one level.

Worked examples: [description restrictions](samples.md#3-reference-and-descriptions) and
[counted-reference comparisons](samples.md#5-quantifiers-witnesses-anaphora).

### 1.7c Composite personal pro-sumti are plural, not constituted groups

Decision. `mi'o` is `Combine Speaker Audience`: the same neutral plural
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

Cost and reopening. This diverges from original CLL and requires three
explicit “others” context projections. It does not solve positive `mi'o …
mei`: #24 must add or reject a plural carrier instance without changing the
pronoun. Reopen P40 only for ordinary unmarked uses that require properties of
a constituted group which its members lack; collective or reciprocal plural
predication and cardinality alone do not qualify.

Worked examples: [composite personal references](samples.md#3-reference-and-descriptions).
The dated usage sources and their limits are in spec References under the
composite-personal-pro-sumti discussion.

### 1.8 `DropPlace`, `Tanru`, `Scalar`

The three relation formers represent different operations. In
`mi klama ti zi'o`, DropPlace removes a role rather than filling it.
Tanru retains an intended modification link, as in `sutra klama`.
Scalar contrast, as in `ta na'e melbi`, denies the predicate's region
and asserts membership in a contrasting region of the resolved domain.

CLL15.4's account of selbri negation as an affirmative alternative relation
motivates the stronger-than-denial analysis. A weaker-than-negation
analysis would not preserve that contrast. OtherThan denotes the domain-relative
complement, Opposite its antipodal region, and Neutral its between-region;
the latter is not necessarily an arithmetic midpoint. No finer alternative is
silently selected. Shared formers state these productive patterns while
lexical entries supply the domains and scales.

The official tanru row provides meaning at x4 and usage/instance at x5.
This supports an occurrence-specific interpretation without itself proving
the complete operator semantics. CLL5.2's warning about misunderstanding
also supports intended but fallibly recovered links; it does not require
every listed link to be true simultaneously.

Worked examples: [place deletion](samples.md#1-predication-and-closure) and
[tanru and scalar contrast](samples.md#8-intended-underspecification-and-soritical-vagueness).

### 1.9 `Generic`

`lo'e` and `le'e` express generalizations rather than reference to a
particular specimen. The intended generic readings of
`lo'e cinfo cu se kerfa lo clani` and
`lo'e cinfo cu se jbena lo cinfo` use different normality classes:
maned males and females giving birth. A single fixed typical-lion referent
does not represent both generalizations under those interpretations.

An ordinary universal would exclude exceptions, while an existential would
state only the existence of an instance. The selected operator instead
relates a pure restrictor and a nuclear predicate through a
predicate-sensitive normality ordering. Its modes are Typical and
Stereotypical; the latter fixes Speaker as holder for `le'e`.

The cost is an axiomatic normality interface, not a derivation from the
other core forms. Generic anaphora and further inference remain gaps.
A lexical relation such as `fadni` may inform a future account, but its
place structure alone does not define this operator.

Worked examples: [generic descriptions](samples.md#3-reference-and-descriptions).

### 1.10 `Reify` and the abstraction relations

The core distinguishes proposition, amount, experience, concept, and other
abstraction sorts. For example, the selected readings of
`lo du'u mi klama cu se djuno do` and `lo ni mi klama cu barda` use a
Proposition and an Amount respectively. Substituting one sort for the other
does not preserve those typed readings. This is not a claim that every
alternative lexical use is meaningless; such a use needs its own supported
row and, where necessary, an explicit crossing.

`Reify` and `Holds` provide the Proposition–Content interface. They are
primitive because the remaining forms do not supply that representation and
evaluation pair with the required round trips. Section 2.10 compares this
choice with the analysis of propositions as nullary relations.

For `ni`, `jei`, `li'i`, `si'o`, `su'u`, `pu'u`, and `zu'o`,
CLL supplies place structures, including scale, experiencer, or conceptualizer
places (CLL 11.3, 11.5, 11.6, 11.9). Smusni represents these as relations
parameterized by content. Reference then applies outside the relation:
`lo ni …` and `le ni …` use the ordinary gadri distinction, relative clauses
restrict or supplement the resulting reference, and omitted places receive
contextual fills.

Separate object constructors for every abstractor would need corresponding
rules for these operations. The relational treatment reuses the existing
rules at the cost of longer terms. This is a factorization argument, not a
proof that constructor-based alternatives cannot be defined.

`jei` yields an epistemology-relative TruthValue object. CLL 11.6 presents
a possible numeric [0,1] treatment without establishing its conventions.
Under P38, the baseline therefore has no `TruthValueDegree` crossing.
Its proposed signature remains in spec §14 for future evidence-backed
adjudication. The current mapping does not silently alternate between
TruthValue and Number results.

Worked examples: [abstractions](samples.md#9-abstractions).

### 1.11 Acts, performance, tokens, signs

The same content can be asserted, questioned, commanded, or displayed.
Quotation also distinguishes an act from its performance:
`mi cusku lu ko klama li'u` reports a directive without issuing it.
`lo'u mi do du le'u` quotes text without requiring a grammatical analysis,
and `la'e lu mi klama li'u` explicitly crosses from a sign to its content.

The core separates three objects: a reusable act package, one performance
occurrence, and the utterance token or span associated with that occurrence.
Constructing or quoting a package does not perform it. `ActContent`
projects the raw assertion payload; `RealizedContent` projects content
under a selected performance's captured context.

This separation supports repeated performance and occurrence-specific
indicators. Two performances of one act have the same package but different
occurrence handles. A raw-act target would not distinguish them. A token
alone is also insufficient when the token or span is associated with a host,
attached displays, or other components. `ActOccurrence` associates the act,
token, role, and semantic capture; terms receive an opaque handle rather
than access to that record's fields.

The capture preserves utterance-context resolution, not a fixed truth result,
reference-selection outcome, projective discharge, or precisification.
At each captured site it retains the original partial resolver over every
declared dependency tuple. A later override reaching a new tuple uses that
resolver or yields projective undefinedness; it does not switch to the new
speaker's resolution.

CLL 7.6 distinguishes ordinary GOhA reuse from `ra'o` reinterpretation of
antecedent pro-sumti. It does not require every omitted place or tanru link
to be resolved again. Smusni therefore combines the raw template with the
occurrence capture: marked pro-assign sites are rebuilt under `ra'o`,
while unrelated captured sites remain unchanged. Wholesale raw replay was
rejected as a broader rule than that source supports.

Other representations of packages and captures are possible, but must
preserve these distinctions. The selected interface costs additional token,
occurrence, and capture structure while keeping that structure separate
from an evaluator log.

Worked examples: [acts and questions](samples.md#6-acts-questions-answers),
[quotation](samples.md#10-signs-and-mention), and
[performance binding](samples.md#12-direct-binding-notation).

### 1.11a Queries, answerhood, and question objects

The Query interface factors a typed answer domain and its answer-content
function across polar, entity, relation, place-label, and other questions.
Ask uses a query to construct a question act; Answer selects Content from
its answer-content function; QuestionOf represents the query as a first-order
Question object. This separates a query, an answer's content, and an object
representing the query. In a du'u answerhood construction, Reify supplies the
additional Content-to-Proposition crossing.

This is a factorization argument for the shared interface, not proof that
every individual constructor must be primitive. Polar, OpenQ, Answer, and
QuestionOf retain their declared primitive status. A lambda formulation need not duplicate contextual sites:
one inert Content value can be shared. Sharing that value must
not be confused with evaluating it once or with combining its evaluations.

A reduction comparison remains required. For example, a Boolean case split
using dynamic conjunction and disjunction must preserve accessibility,
projective behavior, definedness, and the complete event intension, not merely
its answer-wise truth conditions. No such equivalence is asserted here.
Likewise, a first-order Question representation is part of the selected
interface, not a complete lexical analysis of every question-selecting word.
The outstanding necessity/factorization comparison is recorded in spec §14;
documenting it does not add an expansion or change the language's behavior.

Worked examples: [questions and answerhood](samples.md#6-acts-questions-answers).

### 1.12 Indicators: displayed content with lexicon discipline

Indicators require a relation, target, intensity, polarity policy, and
host-force profile. The examples separate these components:

- `.au mi sipna` expresses desire without asserting sleep. The lexical
  host-force profile determines whether the host remains asserted.
- `.uinai cai` displays intense unhappiness. The lexical pairing selects
  the opposite emotion before degree applies. `Scalar Opposite` is only
  the documented fallback under CLL15.7.
- `mi jinvi lo du'u ti'e do klama` targets hearsay at embedded content.
  An assertion-only annotation would not supply this use; the display
  interface must also support content-level targets.
- `pei` questions the attitude. Its typed query domain must therefore
  expose the relevant attitude alternatives.

The core supplies the shared interface and the lexicon supplies its
instances. Lexical entries carry the corresponding semantic obligations;
a generated list of labels would not define their target, pairing, or force
behavior. This division follows the lexical discipline in §2.6.

Worked examples: [indicators and their targets](samples.md#7-indicators).

### 1.12a Discursives: reuse without an invented primitive tally

Discourse relations can reuse existing lexical relations where their rows
and meanings fit the required comparison. `mintu` for `mi'u` retains
its standard place; `drata` is the same-standard otherness candidate; `simsa`
offers similarity (its third place is a respect/property, not automatically the
same type as mintu's standard). `frica` and `jmina` are plausible ingredients for
`ku'i` and `ji'a`, but a neutral comparison act (`karbi`) is not already contrast,
and adding a token is not automatically argumentative addition.

An existential standard is coherent unless its admitted domain makes sameness
trivial; the dictionary does not say that every imaginable property is admitted.

<a id="example-comparison-standards"></a>

As a constructed comparison, independent existential sameness need not chain:
a red circle matches a red square in color; that square matches a blue square
in shape; the endpoints match in
neither. Sharing a standard, or restricting to standards agreeing on the
relevant entries, can preserve chaining. The adjudicated ordinary default is
recovered criteria, with sharing keyed to the comparison chain and a recoverably
new criterion allowed. Explicit and admissible existential readings remain
distinct alternatives, not silently replaced by Context. Nai complements at
the same bound standard; changing existential scope would express a different
claim. Exact rows, admissibility and nonassertive target adaptation remain work
(spec References, Round2 agreed contracts, Q11).

“Me too” can compare distinct propositions under a role-aligning standard;
it need not force a new Case sort or property-object reification. Occurrence
handles can be relata of a nonidentity relation without an object-language
inspector. Existing display machinery expresses the relation claim without
the translator verifying its truth. No strict-new-proposition law for ji'a or
net primitive saving has been demonstrated. Source: BPFK Highlight Discursives,
dated IRC cases and the DISC/ARCHIVE reports in spec References.

The broader CLL13.12 inventory is a candidate ledger, not certified reductions:

| Words | Candidate ingredients | Work still owed |
|---|---|---|
| va'i, ta'u | valsi, tanru | Rewording/expansion relation, not just wordhood. |
| li'a, ba'u | klina, banli | Discourse clarity/exaggeration dimensions. |
| zo'o | display machinery | Actual humor relation; no unique CLL gismu bracket. |
| sa'e, to'u, do'a, sa'u | satci, tordu, dunda, sampu | Discourse precision/brevity/generosity/simplicity, not literal length or giving. |
| pa'e, je'u, su'a | pajni, jetnu, evidential/display machinery | Roles and force; displaying truth is not performing the host. |
| ju'o, la'a | djuno, lakne | Certainty/probability, without treating certainty as automatically factive knowledge. |
| ta'o | tanjo mnemonic | Trigonometric tangency does not define an aside. |
| ra'u, mu'a | ralju, mupli | Relevant comparison collections/properties. |
| zu'u, da'i | discourse/force organization | Framing/scenario semantics, not supplied by a mnemonic. |
| ke'u | krefu | Recurrence of content/case versus words/event. |
| po'o | logical/comparison machinery | Same-level alternatives, own-subpart exclusion, overlap and projection. |

Worked examples: [discourse-relation displays](samples.md#7-indicators).
The [changing-standard comparison](#example-comparison-standards) above is a
constructed test of the proposed relation, not an attested exchange.

### 1.13 Why facet joining is plain conjunction

The analyzed tense and modal facets conjoin predicates of a shared event.
Binding identifies the event; a separate connective is not needed solely
to establish a common locus.

The placement of negation distinguishes
`mi klama ti sepi'onai ti`, which denies the instrumental conjunct,
from bridi negation of the whole conjunction. The respective structures are
`klama ∧ ¬pilno` and `¬(klama ∧ pilno)`. Tense chains such as
`pu pu` also use conjunction's left-to-right accessibility for their
anchors.

This analysis is limited to exact facet conjunction. Constitution-bearing
sumti, property, and event `joi` use the indexed interface of spec §4.9.
Those uses require a declared result type and basis. Missing row or performance
rules remain gaps; neither ordinary conjunction nor a generic Vague connector
supplies them.

Worked examples: [tense and facet joining](samples.md#2-events-tense-facets).

### 1.14 `Bind`

`Bind` sequences a value-returning computation with a scoped body. For
example, the successful-source pattern for
`lo mlatu cu blabi .i ri jbena` binds one reference across two acts:

`{Bind [$cat :: Referents Entity] (Refer P) (Do a₁ a₂)}`.

The body supplies a continuation, of model-level shape `λcat. Do a₁ a₂`.
It can use an already available function by applying it to `$cat`.
Ordinary functions here are not captured evaluator continuations; passing
one explicitly would not inherently add hidden control behavior. The
direct notation is retained because respelling this continuation alone
would not simplify the semantic account.

`Let` is immediate value application. Both forms use ordinary lexical
naming; `Bind` additionally passes the source result to its body with
the corresponding state and obligations. Applying a function to a
computation value does not implicitly substitute that computation's result.
The effect join keeps a performance operand at the performance level.

An alternative effectful `Run` could supply the same sequencing through
evaluation rules, with ordinary `Let` following from call-by-value
application. Spec §5.2 gives a hypothetical spelling. This does not
inherently sacrifice pure β-laws: substituting an already obtained value
differs from copying the effectful expression that obtains it. The useful
comparison is the complete value, evaluation, scope and effect contract,
not the number of binder spellings. No new `Run` form is adopted here.

Explicit state/outcome operations offer a different possible simplification:
they could make sequencing and some scoped boundaries definitions over shared
operations. The cost includes the state/outcome interface, its laws, and
restrictions on which observations ordinary terms may use. An opaque state
type prevents inspection but does not alone prevent discarding or reusing
a state argument. Neither mathematical state nor a restricted function
encoding is inherently processor residue. Actual factoring and interface
coupling must be compared; a carrier change need not rewrite every term.

Kuna illustrates both named sequencing for `Dx`/`Act` and lambda-built
sequencing for `Cont`; its named `Bind`/`Ref` effects concern discourse
keys, not that sequencing operation. A named AST constant is not evidence
of mathematical irreducibility. Eberban's context operations and ordinary
anaphora provide another architecture (§2.3–§2.4). These comparisons
identify alternatives; they do not establish a uniquely minimal calculus.

### 1.14a `PerformSource`: failure is not absence of a later utterance

`PerformSource` preserves an assertion and its continuation when a permitted
description source yields no referent, without making strict Bind return a
value it did not obtain. Its bounded formation and laws are in spec §7.1.1
and L8.13; spec References, “Source-preserving assertions,” records their
derivation and controls. It adds no exception to P43.

In `lo gerku cu sipna .i ri cu xunre`, an empty dog source makes the
first assertion false and the later reference use undefined. A fresh Refer
for the second use would assert existence again and could choose a different
reference. Putting the source before an ordinary Bind-scoped discourse would
instead suppress the continuation on failure. A source bound only within
the first assertion does not by itself scope the second.

The selected construction factors source preparation, one actual Host, and
a reusable read in its continuation. The first assertion and later read use
different failure behavior but share the original reference when one is
obtained. No optional-reference or null-entity sort is introduced.

The retained laws also distinguish the rejected alternatives. Removing the
Act on source failure loses its content projection; making every first
failure U loses ordinary F; one closed Act per source alternative does not
supply one shared projected Content. Restoring the entry state would erase
earlier eligible prefixes. The selected laws instead retain reached,
scope-eligible prefixes and legally closed sides while projecting locals.
Later true assertions do not erase earlier falsity.

A finite witness construction is not the full information-state, effect,
run/event, and quotient model. The reusable read must preserve source
coordinates across later uses and replay. In particular, the Empty fibre of
a captured payload remains F at a world where evaluating the whole source
anew might succeed. F01-C08 records this difference, not complete GOhA coverage.
No-return Bind coordinates retain partial event intensions.

The fragment permits one exportable description per Host. Existing successful
multi-description Bind routes remain, but multiple source failures, arbitrary
effects or guards, other forces, and full model closure are not supplied.
The [implementation-status ledger](decisions.md#derived-artifact-status)
distinguishes structural encoding from general source execution and model proof.

Worked example: [source-preserving assertion continuation](samples.md#121-a-source-preserving-pair-of-assertions).

### 1.15 `ClauseContent`, `StateClause`, and `EventOfContent`

The clause-event interface supports tense, event abstraction, and CAhA on
both lexical events and eventless predications. Examples include
`ta pu du lo mi zdani`, `lo nu ta du lo mi zdani`, and
`li re su'i re ca'a du li vo`. Identity keeps its ordinary binary meaning;
StateClause supplies its declarative holding-state interface.

Direct lexical clauses retain their own event. Wrapping every going in a
second state of that event's occurrence would redirect tense and BAI away
from the going itself. Composed clauses have explicit policies: quantified
claims use a holding state, ClauseAnd uses a holding-state joint, disjunction
is branch-relative, and negation uses a negative holding state. Bare Content
conjunction has the separate event-composition law in spec §9.3; it does not
make every joint event a State.

StateClause creates event-open content, CloseClause closes its parameter
while retaining the selected witness, and EventOfContent projects the event
intension without running the content. Ordinary existential closure matches
the run but does not by itself preserve the structured event component.
None of these operations returns a Boolean or exposes syntax. Reify and
Holds retain their distinct Proposition–Content interface.

Fine's truthmaker semantics provides a comparison for conjunctive fusion,
disjunctive alternatives, and explicit negation policies. It does not decide
the Lojban mapping. Smusni's adopted negative-clause coverage requires a
negative-state treatment; its separate event and holding-fusion laws still
owe the combined model and inheritance checks in spec §14.

Described eventualities need not be actual; fasnu records occurrence at a
world. Under P24, missing CAhA permits the four resolved modes rather than
defaulting to actuality. CLL10.19's bare duck-swimming and burning examples
motivate retaining capability readings. Explicit ca'a fixes actual mode.
A mathematical holding state may be temporally or spatially unbounded;
ordinary temporal and spatial relations determine the resulting claims.

Binary identity also permits state-sensitive descriptions without itself
varying. A physical quantity's value may differ across times or worlds when
its value-description is evaluated within each StateClause. Binding that
value outside gives the de re reading. Arithmetic constants and operators
remain rigid. The additional event intension must participate in Content
identity and in the model construction tracked by issue #10.

Worked examples: [event and state clauses](samples.md#2-events-tense-facets) and
[the complete two-assertion example](samples.md#11-the-spiral-sentence-with-an-explicit-alias).

## 2. Design essays

### 2.1 Limits of a truth-conditional first-order translation

A translation assigning only a closed first-order truth condition to each
sentence does not by itself specify discourse accessibility, projective
commitments, or speech-act force. For example, an existential witness closed
inside one sentence is unavailable to a separately translated continuation.
The truth conditions of the supported strong donkey reading can be stated
classically, but its anaphoric composition needs a rule.

This does not make the relevant phenomena inexpressible in first-order
modeling. One can encode states, pluralities, signs, forces, and operations
on them as additional domains and relations. Such an encoding must still
define their semantic behavior. Smusni instead exposes the relevant types
and compositional operations directly. Its additions to a truth-conditional
calculus are justified individually, not by claiming that first-order logic
cannot represent their models.

### 2.2 Truth, definedness, and uncertainty

Eberban's logical framework includes true, false, and unknown. Smusni
distinguishes several phenomena that should not be identified merely by
calling them unknown: listener ignorance, contextual resolution failure,
projective definedness, unanswered questions, and content not asserted under
its current force.

Total at-issue claims are bivalent. The adopted interpretation-status rules
also use T, F, and U, with strong-Kleene composition for genuine undefinedness:
T-or-U is T, F-and-U is F, and unresolved p-or-not-p is U
(spec §7.1.1 and §14 Q14). U is not a third truth value of an otherwise total
claim and is not a measure of what a listener knows.

A three-valued table does distinguish undefinedness from ordinary falsity.
What it does not supply alone is the project's separate projection,
accommodation, force, and reference-retention rules. The choice is therefore
not that two values eliminate all uses of unknown. It is to represent truth,
partial interpretation, and other semantic dimensions separately, with
explicit rules for their interaction. The combined construction remains
incomplete.

### 2.3 Explicit contextual operations

Eberban threads a context argument through its predicates. Smusni instead
uses an utterance-context record, named deictic projections, occurrence-bound
`Context` computations, and explicit `InContext`/`ShiftedGround`
operations.

Either architecture can make contextual dependence explicit in its formal
definition. Smusni's choice exposes retrieval sites, admissibility constraints,
and dependency profiles in the core term, which helps readers distinguish
shared resolution from independent retrieval. It costs additional notation
and requires scope and capture laws. The advantage is local visibility of
these distinctions, not a claim that implicit parameters are inherently
unverifiable or semantically inadequate.

### 2.4 World dependence and dynamic denotation

The model is world-indexed, but core terms do not bind world variables.
The analyzed attitude, capability, and description cases have not established
that an object-language world binder is necessary. Some of those cases still
lack complete typed consumers, notably delayed de-dicto descriptions and
`da'i` (spec §5.7 and §14). Their unfinished treatment cannot be used as a
proof that every possible world-sensitive reading is already covered.

Dynamic meanings can be represented mathematically as static higher-type
objects, such as functions on information states. Likewise, after fixing
a supported reading and its parameters, many declarative truth conditions
can be expressed as classical formulas. Neither observation removes the
need to define composition. A closed truth-condition translation of one
sentence does not retain its witness for a separately translated anaphor.

Smusni uses typed computation categories and visible sequencing to state
these dependencies. The mapping supplies the selected binding structure;
the model must validate its accessibility and effects. The bounded
`PerformSource` construction addresses one source-preserving assertion
case. It is not a general proof of equivalence between the documentary
calculus and a completed dynamic model.

Toaq's Kuna provides a comparison using algebraic effect constructors.
Eberban's reference grammar provides contextual updates through the `an`
family and latest-instance anaphora through `ze`; it therefore has both
conversational state and ordinary witness reference. The inspected grammar
leaves multiply evaluated and donkey cases unfinished. The relevant
comparison is how each architecture states dependencies and projective
commitments, not whether one can mention state at all. Smusni's own remaining
source, force, and model obligations must be included in that comparison.

### 2.5 Why there is no distributivity parameter

P4 treats unmarked plural predication as neutral. A predicate holds of a
plural reference, and its lexical semantics determines which configurations
satisfy it. The core does not add a covert cover variable selecting a
collective, distributive, or cumulative reading.

The xorlo description of unmarked gadri as unspecified for distributivity
motivates this choice, but does not by itself prove that every parameterized
analysis is wrong. The project prefers direct plural predication because it
does not require an extra contextual resolution for each unmarked use.
Different arrangements of piano carrying can satisfy the same neutral claim
without being different selected values of a hidden parameter.

When a reading explicitly requires distribution or a constituted group,
`lu'a`, `Distrib`, and group constructions state that requirement.
The lexicon's subreference-monotonicity and collective-capability fields
describe predicate behavior; they are not per-occurrence cover choices.
This follows the plural-logic approach discussed in §1.7b and §2.8.

### 2.6 Why the lexicon is a first-class interface

Lexical entries determine argument types, intensional behavior, permitted
place deletion, plurality behavior, and indicator profiles. The core states
the required interface in spec §10; each adopted field value is itself a
semantic ruling. A template or fixture value is not an established lexical
fact.

The constitution interface follows the same policy. Group and event rows
declare admissible decomposition bases; a supported property-`joi` row
supplies its `MixAt`/`ContributesAt` instance. Missing instances remain
coverage gaps.

The adopted `gunma` and `selcmi` rows use plural-reference x2 for
components or members. Their published place structures already distinguish
the whole from those components, so the project did not need an additional
place-structure replacement for that distinction. The xorxes lujvo `selcmi`
is used in the LLG-approved 2020 gadri expansion
`lo'i [PA] broda = lo selcmi be lo [PA] broda`. The maintained CLL chapter 6
reproduces this in project-authored wording, not independent corroboration.
See spec References, “BPFK Gadri” and “Non-importing ro decision.”
Ordinary plural subreference uses `Among`, not the set-selecting x2 of `cmima`.

The `le` treatment is based on `skicu`. Its official x4 is a description
property, not a medium of expression. Guskant's gadri commentary explicitly
expands `le broda` through

`zo'e noi mi ke'a do skicu lo ka ce'u broda`.

This is direct intellectual provenance for the use of `skicu`; it is not
a claim that every community analysis used that construction. Smusni's
additional anchoring clause identifies the describing event with this
utterance's locution. The resulting `SpeakerDescribes` definition preserves
non-veridical description without existentially selecting an unrelated
describing event.

A dedicated `DescribedBy` predicate could encode a similar relation, but
the project has not identified a needed distinction that would justify
duplicating the adopted lexical interface. The row and anchoring argument
also do not constitute a complete lexical semantics of `skicu`; that
semantics remains subject to the same lexicon discipline.

### 2.7 Semantic structure versus implementation structure

A semantic construction must denote a linguistic distinction or factor shared
semantic structure. Processor-specific registries, serialization choices,
diagnostic taxonomies, and run identifiers do not become semantic objects
merely because an implementation uses them.

Useful checks include invariance under alpha-conversion and equivalent
serialization, a stated semantic role, and an account independent of a
particular program. A generic core form may pass through factorization rather
than a direct surface example; spec §1.1 does not require every form to have
a Lojban spelling.

Semantic undefinedness must also be distinguished from implementation errors.
The T/F/U interpretation-status rules and partial operations have semantic
content. A checker diagnostic is evidence about its attempt to analyze a term,
not another value in that term's domain. Likewise, a gap records the limits
of the specification without inventing a denotation for an unanalysed reading.

These are review criteria, not proof that the present core is free of every
implementation-dependent assumption.

### 2.8 Why lexical arguments are plural references, not sets

A set-typed lexicon is a substantive alternative to `Referents<T>`.
Eberban's “Dictionary conventions” uses the nonempty set type `tce` and
marks places whose satisfaction is preserved under subsets with `*`.
Brismu's “Sets, not Masses” also uses sets over individuals. The 1994
baselined gismu list contains a less uniform precedent: roughly thirty
place glosses have set annotations, including the `simxu`, `cuxna`,
`kampu`, `cmima`, and `-mei` group and `sisku` x3.

There is an equivalence in the fragment satisfying discipline D of spec §4.8.
Its premises include nonemptiness, atomistic generation, singleton separation
and primeness, identity determined by represented units, representation of
every nonempty unit set with the required infinite joins, and compatibility
with subsorts. Under all those premises,

`Referents<T>/CoRef ≅ NonEmptySet<T>`,

with `Combine` represented by union and `Among` by subset. Lexical
predication must concern the represented members, and discourse-introduction
identity remains separate from extensional identity. Representation sets must
also remain distinct from first-order set objects.

The objection that a crowd can be large while a mathematical set cannot is
therefore irrelevant to that representation. Eberban's `bure` example
illustrates member-directed predication: the set represents the participants,
and the lexical definition states how they satisfy eating.

Smusni retains plural-reference types for the following reasons.

1. D is stronger than the selected plural algebra. In particular, Smusni
   does not require atomistic generation. Guskant's Condition₁ proof and
   divisible-bread interpretation motivate this boundary. Counting uses a
   declared unit property through `CardBasis`, not a universal atomic
   basis. A set treatment outside D is not ruled out, but it needs a
   representation of that additional coverage; the isomorphism above does
   not establish one.
2. Inside D, changing the representation does not remove the semantic
   distinctions. Nonemptiness, member-directed versus object-directed
   predication, and introduction identity still require rules. Lists,
   groups, and first-order set objects also remain. Eberban's “from scratch”
   chapter distinguishes wrapped collection objects from their unwrapped
   representation. Smusni exposes the corresponding reference/object
   distinction through separate types. This compares the stated designs,
   not every possible set-based architecture.
3. The intended level of predication must be explicit. In
   `lo selcmi cu simxu lo ka tavla`, talking concerns participants, not
   automatically the members of any set object mentioned. A uniform set
   type still needs a way to distinguish predication of several set objects
   from predication of one set's members. Solpahi's “A Simpler Quantifier
   Logic” identifies this ambiguity. The reference/object split provides
   that distinction without a per-use implicit unwrapping rule.
4. The historical dictionary annotations are inconsistent as a uniform
   type discipline. The collective predicate `sruri` lacks the set
   annotation, while `simxu` retains it. Guskant and solpahi give
   plural interpretations of this material. This supports reconsidering
   the old annotations; it does not establish that every historical use of
   “set” meant plural reference. A per-place semantic audit remains
   necessary under either design.
5. Brismu's stated equiconsistency comparison with monadic second-order
   logic does not by itself decide this choice. Equiconsistency is weaker
   than equivalence of semantic representations. Smusni already has
   higher-type functions and comprehension, so its costs must be assessed
   in that setting. Sets may be used in the metatheory without making
   lexical arguments denote first-order set objects.

One feature adopted from Eberban is its explicit subset-preservation
criterion. Smusni's lexical plurality field records the analogous
subreference-monotonicity property using `Among`. Collective capability is
a separate fact: absence of a distributivity guarantee does not imply that
a predicate fails of every member. Neither field creates a hidden reading
parameter under P4. Eberban's cumulative conventions for examples such as
eating are not adopted as a general default.

Solpahi's article, published in 2016 and revised in 2017, is also a reform
proposal. It motivates the counted plural helpers but does not establish
ordinary plural PA. Guskant and xorxes distinguish plural constants from
ordinary singular variables. A collective predicate can hold of a plural
reference without holding of an individual, so existential generalization
across those domains is not licensed.

Ordinary `lo`, including `lo ro` and `lo su'o`, supports positive
collective predication. Descriptions nevertheless differ from plural
quantifiers under negation and other embeddings. The baseline keeps
individual `su'o` and globally exact finite numerical PA; the shared core
retains its plural helpers. P43 excludes additional outward quantified-group
export without redefining those helpers. Numerical termsets and remaining
count/effect domains have their own open construction requirements.

### 2.9 Why binders are direct forms, not executable quotations

Smusni uses direct `λ`, `Let`, and `Bind` formation. Scope,
alpha-equivalence, capture-avoiding substitution, and inert binder positions
are structural judgments (spec §4.4 and §5.2). The [binding examples](samples.md#12-direct-binding-notation)
show this distinction: braces delimit scope; they do not construct quoted
source code.

Harper's treatment of abstract binding trees provides a reference for this
direct binding discipline; see spec References.

An executable-quotation design offers a real attraction. Atoms, quotation,
and application could provide one uniform grammar, with binders expressed
as functions over typed quoted syntax. Typed multi-stage calculi provide
relevant comparisons (Nanevski, Pfenning and Pientka; Taha and Sheard;
Davies and Pfenning, in spec References).

That uniformity requires additional semantic structure: staged expression
types, representations of binder telescopes and environments, capture and
hygiene rules, site-preserving interpretation, and explicit treatment of
values crossing stages. No supported Lojban reading requires executable
quotation of the core's own notation. Adding this machinery merely to make
binders look like other calls would therefore optimize notation without
a sufficient necessity or factorization argument.

Unrestricted access to operand syntax is not an acceptable shortcut.
Wand's fexpr result shows how observation of arbitrary caller syntax can
destroy useful contextual equivalence. Restricted staged designs need not
have that defect, but their restrictions and equational theory must be stated.
The failure of an unrestricted design is not a proof that all reflection
is impossible.

Direct formation avoids that extra interface without removing effect
sequencing: carrier-level bind and its term-level `Bind` remain.
It also leaves ordinary linguistic use and mention intact. Lojban quotations,
signs, utterance tokens, `InterpretContent`/`InterpretAct`, and explicit
`Perform` still distinguish quoted material from an act's performance.
The [quotation examples](samples.md#10-signs-and-mention) require that
distinction, not executable core code.

A predicate describing a function, computation, or act does not execute it.
Relations such as `xusra`, `danfu`, and `smuni` can therefore be
useful semantic vocabulary without replacing the binder or force operators
they describe. This is the same interface boundary that prevents adding a
general `TruthOf` solely to reduce two connectives (§1.5).

The choice should be revisited if a supported meaning requires executable
core self-description. Such an extension must provide explicit stages,
complete hygiene and capture rules, a nontrivial equational theory, and
a boundary preventing implicit inspection of ordinary terms. Host-language
macros may provide convenient notation without making reflection part of
Lojban's semantic core.

### 2.10 du'u, nullary ka, and the reserved reification family

And Rosta's proposal on the Lojban Wiki page “ka, du'u, si'o, ce'u, zo'e”
treats the three abstractors as n-adic relations whose arity depends on
`ce'u`, with propositions as the nullary case. The page records support,
amendments, and dissent; it is a proposal, not a ratified rule. The proposed
BPFK `ce'u` definition also permits some uses outside `ka`. These sources
motivate comparison between abstraction, arity, and nominalization; they do
not specify Smusni's object/reference interface. See the corresponding
entries in spec References.

Smusni adopts the arity analysis for its supported `ka` and `du'u`
fragment. Each distinct extracted `ce'u` variable becomes a lambda
parameter. With no extracted variables, the result is Content:
`PredTerm<⟨⟩>`, applied at the empty record, is Content by spec §3.3.
In this limited sense, unparameterized `du'u` has the same content as a
nullary property abstraction.

The analysis does not settle every abstractor. Smusni retains `SihoRel`'s
conceptualizing-mind place, following the CLL row also retained in the
proposed BPFK `si'o` definition. The general explicit-`ce'u` treatment of
`si'o` remains a gap. That BPFK page also assigns implicit `ce'u` to every
unfilled place in `si'o`; it does not explain the complete composition of
this default with the conceptualizer row. This is a project choice about the row and its
composition, not evidence that Rosta's broader proposal is incoherent.

A separate choice concerns how content participates in reference, counting,
and identity. Smusni uses `Proposition` as a first-order sort and
`Reify : Content → Proposition` as its explicit crossing from Content.
`Holds` recovers the represented content. The round-trip axioms in spec
§9.1 require that this crossing preserve the structured dynamic denotation,
including projective effects and clause-event intension. Reification does
not remove those features.

This separation is a design decision, not an impossibility argument against
content-taking alternatives. Content already has semantic identity, despite
having no object-language equality operator. It can be constructed, shared,
and passed as an operand without being evaluated; constructing `Reify c`
likewise does not evaluate `c`. Calling both “first-class” would therefore
not distinguish them. The relevant distinction is between a computation
denotation and its representation in the first-order domain.

The selected interface lets proposition references use the ordinary
description, quantification, anaphora, and identity operations. Direct
property operands instead have function types and may be applied by their
consumers. These are the selected interfaces, not complete lexical analyses:
a word's English gloss does not establish whether it must take a function or
an object, nor does an object-taking place prohibit evaluation of represented
content elsewhere. In particular, the illustrative `djuno` row is not a
proof that a direct-content semantics of knowledge is impossible.

The experimental `me'ei`/`me'au` pair motivates a possible extension to
reified predicates. At arity zero, `me'au` uses the defined `Meau0`
schema: a projective singleton condition supplies the proposition to
`Holds`. A claim using `jetnu` is structurally different from evaluating
that represented content, even where their truth conditions agree. The
baseline does not silently distribute `Holds` over plural proposition
references; that reading remains a candidate in spec §14.

Above arity zero, Smusni has no first-order reified-property sort.
Nevertheless, it already supports function-typed quantification at
`PredTerm<ρ>` through P30. The missing facility is object-style property
reference and its associated crossings, not property quantification in
general. The direct `lo ka` lambda does not itself introduce a first-order
discourse referent.

Spec §9.1 reserves a row-indexed reification family, following the
nominalization/predicativization distinction of Chierchia and Turner.
Any crossing defined as a function on extensional `PredTerm<ρ>` must
respect that domain's equality. Whether each row has the same bijective
interface, and how row isomorphisms or cross-row operations are typed, remain
undecided. At arity zero the round-trip contract is adopted: proposition
identity tracks structured content identity, not merely logical equivalence.
Constructing a combined model satisfying that contract and the other
dynamic laws remains a separate obligation in spec §14.


Worked examples: [abstraction types](samples.md#9-abstractions) and
[signs and interpreted content](samples.md#10-signs-and-mention).

### 2.11 The resolved-reading datum and hoisting

The lowering relation consumes a resolved-reading record, RR, rather than
guessing a reading from surface text. The record supplies the interpretative
choices marked ⊳ in spec §11, including reference resolution, attachment, template use,
tense and CAhA readings, dependency profiles, and binder scope. Mechanical
rewrites such as numeral syntax or implicit-`ce'u` expansion have no
choice to record; their conditions belong to the lowering rules.

RR is input data for that relation, not a semantic object. It holds no
world, information state, or performance capture and does not occur inside
a core term. Separating it from the denotation makes coverage claims precise:
a lowering rule must work on the resolved input it declares, not silently
supply additional choices. The distinction between resolved input and
derived term is illustrated by the [in-situ scope examples](samples.md#13-in-situ-scope).

Hoisting addresses a different problem. A lexical predicate with unfilled
ordinary places may require contextual values, while a comprehension or
quantifier restrictor requires a pure property. L0.1 binds the necessary
contextual sites outside that pure position, giving it the resolved lexical
property already used by the unit-profile rules. A new core operator called
“pure projection” would obscure this binding structure rather than explain it.

This move is licensed only when the site's dependencies remain available
and unchanged. A contextual site retrieves once per dependency tuple per
performance and introduces no descriptive reference. Independent hoists can
commute; dependent hoists must follow their dependency order. A site that
depends on the comprehension's own variable cannot simply be moved outside.
The [expanded predication examples](samples.md#1-predication-and-closure)
show what contextual closure supplies; the [count examples](samples.md#5-quantifiers-witnesses-anaphora)
show why the resulting property must satisfy the pure-position rules.

Vague sites follow the same restriction through their shared profile value:
one precisification belongs to each parameter site, rather than a fresh
choice for each instantiation. Moving a dependency-independent site preserves
that correlation. Hoisting an introduction is different. Moving a `Refer`
or selection would choose its quantifier scope and reference lifetime;
L0.1 supplies no general law permitting that change.

Consequently, a reference-producing computation cannot occupy a pure
position merely because some alternative placement would type-check.
Its reference must already be bound outside, or its use must meet the
specific negation-local qualification below. An alternative pure construction
would need its own typed consumer and equivalence argument. This is not
a proof that every equivalent pure representation is impossible.

Negation-local reference purity (P45) permits a temporary reference
introduced and consumed wholly inside a negative Content test without
counting that introduction as an outward effect of the property. The
reference remains under the negation; its dependence and cardinal scope
are not changed. Only the reference-introduction effect is removed.
Contextual, projective, and opaque-call effects, and obligation records,
remain. `Local` retains its effectful contract.

The alternative is to classify all internal introduction activity as impure,
including introductions that negation seals. That would reject the current
negated-selection expansions of `No`, `AtMost 1`, `FewerThan 1`,
and `Exactly 0` in pure set conditions. Preserving those readings would
then require a separately proved pure replacement, rather than simply using
their existing expansions. The chosen rule preserves direct-versus-expanded
typing and expresses the relevant observation boundary explicitly.
Its cost is an operation-specific purity rule, not a theorem that every
non-exporting operator is pure.

Double negation still exports no internal witness; equality of truth
conditions alone does not establish equality of dynamic or event behavior.
The full model and other-connective effect questions remain separate.
Spec References, “Negation-local purity: P45 reconciliation,” records the
original hoisting, scope and purity arguments and their provenance.
The older checker and the name DPL do not independently establish this rule.

Finally, restrictor closure and host mode are separate. `Close` in L0.1
selects actual mode for the restrictor's predication: `lo bajra` describes
actual runners even under a capability claim about them. Inheriting the
host's CAhA mode into every description would be a different coherent rule,
but the source review did not establish a reading requiring it.
The main clause's unmarked CAhA remains reading-dependent. A minimal pair
requiring the description itself to inherit capability would reopen this
boundary.

## 3. Pin arguments

The following summarizes arguments for selected pins. Spec §13 gives the
normative decisions; the cited discussions retain their alternatives.

- **P1/P22 (xorlo, inner `no`).** "No default quantifiers. At all." is
  the xorlo page verbatim. Inner `no` is a separate adopted negative-frame
  policy, not a theorem that nonempty references must have positive unit counts.
  It does not declare the form meaningless; guskant's gadri commentary ("Cannot say
  zero") supplies both the reading and the reason to want one: her
  unofficial `lo no broda = naku su'oi da poi ke'a broda`, motivated by
  answer continuity — `lo xo prenu cu jmaji …` answered by `no`,
  elliptical for `lo no prenu cu jmaji …` — the pattern that also
  carries `go'i`-inherited frames. The pin therefore special-cases
  inner `no` at the mapping layer to the uncounted plural-negative (`PluralNo`) schema over
  the description's property and the bridi frame: substitution into
  question frames works, nothing touches the nonemptiness of the
  reference type, and anaphora to the form is correctly inaccessible
  because `PluralNo` exports no witness. (Ruling the form defective outright
  might look simpler, but it would rest on the unverifiable premise
  that usage avoids it — and it breaks the answer-substitution pattern
  that motivates the reading; hence the special case.)
- **P2 (non-importing bare/restricted `ro`).** Both `ro broda` and
  `ro da poi broda` use universal conditional closure. An empty restriction
  is vacuous, not an existence assertion or presupposition. The LLG-ratified
  gadri expansion aligns those forms; BPFK Inexact Numbers supplies direct
  quantified equations supporting this analysis. Explicit `ro lo …` retains
  the reference requirement of its description. The [universal and count
  examples](samples.md#5-quantifiers-witnesses-anaphora) keep these operations separate.
  The advantages are uniform individual quantification and ordinary pure
  negation duality. The compatibility cost is departure from CLL v1.1
  §16.8's restricted import. At-issue import and presuppositional import are
  coherent alternatives, but introduce different commitments and negation
  behavior. Cowan and Clifford's arguments for import remain part of that
  comparison, not evidence that the sources were unanimous. Spec References,
  “Non-importing ro decision” and “ro edition/discussion record,” give the
  primary arguments and distinguish ratified text from project-authored
  amendments. The library's importing `MaxRefer`/`Every` is unaffected.

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
  descriptors and `joi` add the defined converse cover. Finally, only the whole-forming reading distinguishes `joi` from
  `jo'u` under the selected absence of covert distributivity. The local reference-level manufacture repair fixes one aggregate lift or one
  event-whole CoRef class; number-neutral group descriptors are unaffected.
  Alternatives and the type/category costs are worked in
  §1.7a; the reopening tests are a genuine `joi` use whose result must remain
  the original plural reference, or a component-basis counterexample that
  cannot be expressed by the indexed cover/contribution interfaces.
- **P9 (`kau` exhaustivity is absent).** Unmarked answerhood does not
  assert that the answer lists every satisfier. The [question and answer
  examples](samples.md#6-acts-questions-answers) use the weakest,
  mention-some-compatible answer content; stronger requirements can come
  from a lexical consumer or a separate claim. A default-exhaustive rule
  would add a condition the cited CLL account does not state. A `Vague`
  exhaustivity parameter would instead insert a hidden choice without
  a Lojban expression that fixes it. Neither is required by bare `kau`.
  A separate `MentionSome` marker would duplicate the unmarked form.
  An `Exhaustive` definition would need a pure answer-content function
  and suitable selection membership/equivalence for plural, tuple, label,
  and predicate-valued answer domains. Those are real additional interfaces,
  not semantics supplied by naming an uninterpreted marker. The candidate
  therefore remains a gap rather than changing unmarked answerhood.

- **P10 (`le` and `voi`).** Guskant's gadri expansion supplies the
  `skicu` description relation (§2.6). Smusni anchors its describing
  event to this utterance's locution. Without that anchor, an existential
  describing event could be an unrelated earlier description, making the
  restriction weaker than intended. The same reason applies to `voi`:
  deleting the audience place does not remove the need to identify the
  describing act. `SpeakerDescribes` and
  `SpeakerDescribesUnaddressed` define these two properties once, so
  specimens can use short names with exactly the expanded denotation.
  A separate primitive duplicates the lexical interface; writing the full
  property every time duplicates its definition. The [description examples](samples.md#3-reference-and-descriptions)
  and [relative-clause examples](samples.md#4-relative-clauses-and-supplements)
  show the shared construction.

- **P11 (`Generic`).** Section 1.9 compares the selected normality interface with the
  fixed-specimen alternative under the stated generic readings.
- **P16 (KOhA keyed).** `ko'a du ko'a` must be true; per-site contextual
  holes would let the two sites diverge. One retrieval per key.
- **P17 (numerical termsets).** The explicit CLL16.7 dog/person example
  motivates the provisional full-product treatment of that termset.
  Pure ordinary `su'o` coordinates use the joint individual locus of
  L5.3, not counted plural selections; see the [termset examples](samples.md#5-quantifiers-witnesses-anaphora).
  A constructed contrast exposes the collective cost: three people collectively
  moving two pianos need not satisfy all six individual pairwise predications.
  Equal scope alone does not prove distribution, and global exact
  quantifiers do not generally commute.
  Ordinary finite numerical PA is individually and globally exact.
  Witness-local counting composes conveniently with explicit plural bindings,
  but gives a different answer when extra individuals qualify. It is
  appropriate to the comparison inspired by solpahi's plural reform, not
  a substitute for the established standard count. The source and
  countermodel record is in spec References, “Conservative profile adoption
  and ordinary exactness” and the SUHO/ARCHIVE discussions.

- **P43 (accessibility; comparison with P42).** Section 1.6a explains why
  the baseline keeps ordinary existential and independent-reference
  continuity without constructing extra outward numerical groups or
  dependent families. The rejected broader recovery policy would add
  output-selection, scope, dependency, and continuation contracts.
  A positive `lo su'o n` description often provides the wanted reference,
  but is not interchangeable with an outer count in every embedding.
  Source/force realization, open answers, permitted quotation crossings,
  partial values, and the plural carrier remain shared obligations.
  This choice does not alter exact-count truth or the non-importing universal.

- **P44 (bare me'i defaults to ro).** The baseline uses the BPFK-specific
  less-than-all convention rather than CLLv1.1 §18.9's blanket pa default.
  Its explicit definition, omitted-bound rule and example, plus the recovered
  2002 advocacy and 2004 drafting, are stronger evidence than treating the
  old shorthand as immune to correction. Categorical symmetry supplies a
  useful distinct short form for not-all; synonymy alone would not prove the
  pa alternative wrong. The compatibility cost is that a CLL reader could
  understand bare me'i as zero; explicit me'i pa and no retain that meaning.
  The core negates IndividualEvery, rather than comparing infinite
  cardinalities: a proper subset may have the same cardinality as its domain.
  Default choice, existence requirements and reference accessibility remain
  distinct; the new rule neither adds a positive satisfier nor exports its
  counterexample. Strong contrary usage evidence or a concrete compositional
  defect can motivate reconsideration, not merely missing ratification metadata.
  No new corpus-prevalence claim is made. See spec References, Bare me'i
  default: P44 adoption and history, for original sources and rejected
  import packages; the broader 2002 debate was not unanimous.

- **P8: no default present tense.** CLL
  ch. 10 makes tense optional; an English present-tense translation does not
  establish a Lojban default. Treating every missing tense as pure absence would also be too strong: CLL 10.1 itself enumerates the readings of
  the tenseless example and says "context resolves which is correct",
  and Partee's stove example motivates the comparison with contextually
  anchored episodic time. Partee discusses English past tense; applying that
  comparison to tenseless Lojban and choosing Context are this project's
  arguments, not conclusions of her paper. The accessible author handout and
  original-paper attribution are given in spec References, “Partee.”
  Under the pin, tenselessness is
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
  x1/fai routing, and CLL 11.10 leaves the inner argument unstated. The
  proposed definition and notes in BPFK Section: Place Structure cmavo also
  describe bare-jai raising from the abstraction at fai. They are independent
  proposed wording, not a ratification record; see spec References.
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
  branch event. For actuality, the proposed “bare assertion always actual”
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
  Cross-clausal place-linking remains a gap. A topic reference and a Tanru
  modifier have different types; the latter is not a direct replacement for
  the selected TopicResolution interface. Topic resolution does not itself
  change discourse segments; ni'o/no'i supply those transitions. Additional
  segment effects would require a separate rule and supporting evidence.
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
  would require an additional object-identity policy not needed by this
  particular quantified reading, which makes no identity claim.
  The prenex constraint is CLL Example 16.107
  verbatim. `cei` stores more than a relation (CLL 7.5: fills, tense,
  negation ride along, later fills override), so the binding is a
  bridi template at the ⊳ layer. A bare residual PredTerm value does not
  itself retain those earlier fills, tense, and negation for override.
  This does not prove that a richer predicate-based representation is impossible.
- **P32 (one performance).** `.i ja` decides it: a disjunction is one
  claim, not two acts. `ClauseOr` preserves the successful branch event and
  the host closes that `ClauseContent` once; uniformity carries one-performance
  force to `.i je`, whose `ClauseAnd` event is the joint State.
  Conjunction and `Do` both allow left-to-right reference flow, but their
  truth and assertion-return behavior differs under §5.4/§7.1.1. An analysis
  that separately asserts both operands would not represent disjunction;
  a more general cross-act alternative would need an explicit force account.
  `JoiClause` supplies the event/content contribution of `.i joi`.
  Its surrounding structured performance remains a gap: `Do` alone supplies
  neither that constitution relation nor the required component roles.
- **P33 (tanru-unit jeks).** With a shared head, connecting whole
  units would repeat the head predication, potentially repeating effects or
  changing site/event structure. This does not entail two distinct houses:
  the same argument can satisfy both occurrences. Binding an intended link
  from constrained Context for each conjunct and
  connecting the link applications retains one head evaluation. For pure
  truth conditions, H ∧ (l₁ ∨ l₂) has the usual distributive equivalence;
  this does not authorize copying an effectful head or its sites.
  Distinct heads have nothing to share,
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
  count claim itself; confusing those two levels would count the claim's state instead of its instances.
  The interval default follows CLL 10.9's own words
  ("unspecified size, at least part … in the past"): a recoverable
  anchor (`Context`) with genuinely loose extent (`Vague`).
- **P37 (`ji'i`).** CLL 18.9 distinguishes positions; one uniform
  tolerance would erase the rounding reading (suffix `ji'i` with
  `ma'u`/`ni'u` direction) that CLL states. A point-valued family distinguishes tolerance from rounding but
  makes approximate equality to a fixed number fail supertruth whenever its
  admissible region contains other values. The chosen claim-level treatment
  instead uses vague tolerance, an exact constrained value inside the claim,
  ordinary equality/arithmetic there. Actual counts/identified values are tested,
  not reselected. Compatibility is a chosen cost, not certainty about two
  independent measurements. Aliases share one value; shared tolerance alone
  does not correlate error. Preserve unreduced expressions when no further
  reading is established, without a universal precision floor or full reducer.
  Typed scope/effect/cardinal/retention realization remains work (spec §12/§14).
- **P39 (`CoveredBy` placement).** The [dog-plus-cat countermodel](#example-dog-plus-cat) requires a
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
- **P41 (scope and dependent descriptions).** A referential description
  can vary with its governing variables. Invariance is one possible
  dependency profile, not a consequence of being referential. Guskant's
  gadri commentary §3.2.2 permits Skolem-like constants: their values can
  depend on the surrounding assignments while remaining fixed for a given
  assignment. Prohibiting that dependence would lose readings without
  gaining a distinction between reference and quantification.
  This does not make `lo` an implicit existential quantifier. Binding
  must still occur where all declared dependencies are in scope; an
  annotation cannot capture an unavailable variable. The [in-situ scope
  examples](samples.md#13-in-situ-scope) distinguish these placements.
  The unresolved work concerns profile realization, pure restrictors,
  attitude consumers and export, not whether co-variation is legitimate.
  Spec References and the [scope/dependency record](https://github.com/int19h/smusni/issues/62)
  preserve the supporting analysis and correction history.

## 4. What would change our minds

The comparisons above identify both the benefits of the selected rules and
their costs. Reconsidering a rule requires evidence or a construction that
changes that balance. For example, §1.6a separates the benefits of wider
anaphoric recovery from its additional export contracts; a proposed extension
must justify both, rather than merely demonstrate one successful binding.

Reopening evidence would include:

- A query-constructor reduction preserving the full laws listed in §1.11a,
  or a stronger necessity/factorization argument for retaining the individual
  primitives. The current interface alone is not an irreducibility proof.

- An established Lojban expression selecting a weak dependent-witness
  reading, or a compositional plural-information-state account that improves
  the supported dependency treatment. Extending reference beyond P43 would
  require a separate compatibility and complexity decision, not merely a
  different implementation of the baseline.
- A facet-joining example whose effects are not correctly represented by
  dynamic conjunction. This would motivate reconsidering a dedicated
  joining operator.
- A supported construction requiring explicit world variables in core terms,
  rather than world dependence confined to denotation.
- A genericity theory deriving `Generic` from existing forms while
  preserving the `lo'e`/`le'e` distinction.
- A consistent pattern of exhaustive unmarked `kau`, especially outside
  `djuno` frames where lexical requirements might explain the reading.
  This would bear on P9.
- Usage and formal arguments discriminating the remaining numerical-termset
  policies under P17.
- A lexical construction whose set-object semantics cannot be represented
  adequately by the selected distinction between plural reference and
  first-order sets. Section 2.8 analyzes `lo selcmi cu simxu`; a different
  counterexample could require revisiting that comparison.

The earlier searches did not establish such counterexamples. That is a
bounded research result, not proof that none exists. Any revision must state
which argument or evidence changes and trace its consequences through the
specification and derivative documents.
