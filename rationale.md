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

### 1.2 `Close` as a defined operation

**Job.** An unmarked bridi with omitted places still makes a complete
claim. **Witness.** `mi klama` — committed to a contextually recoverable
destination and an event, not to "some destination" and not to nothing.
**Why not existential closure of omitted places?** Negation: `mi na
klama` does not mean "there is no destination I go to"; the contextual
destination stays fixed under negation, an existential would not. **Why
not a primitive?** Because its expansion — event quantification plus one
`Context` per defaultable place — *is* its content; a primitive would
just hide the expansion. The spec therefore defines it normatively and
keeps the name for exposition. **Cost.** Fully explicit terms are
verbose; that is the assembly-language bargain.

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
- **`Context`** — *recover*. Witness: `mi klama` (destination), `co'e`
  (the relation we both know), `zu'i` (the usual value). Why not `Refer`?
  Nothing is introduced or described — `mi na dunda` denies the giving of
  the contextual thing, not the existence of a describable gift. Why not
  a free variable? Free variables have no discipline: `Context` declares
  its type, its dependencies, and its site/key identity (one retrieval
  per site per performance — which is exactly why `mi .e ti klama` shares
  one destination, and why `ko'a du ko'a` is reflexively true under the
  keyed rule).
- **`Vague`** — *waive*. Witness: the tanru link (`sutra klama` — CLL
  says the relation is constitutively open), `tu'a lo cukta`
  ("something about the book" — deliberately withheld), `so'i` (no fact
  fixes where "many" starts). Why not `Context`? The recovery test: no
  cooperative hearer is expected to land on one value, and communication
  has not failed when they don't. Why not ambiguity (several readings)?
  The speaker uttered *one* reading whose meaning is the constrained
  family; disambiguation upstream cannot help. The composition law
  (spec §6.5) makes the family compute like a meaning: pointwise lifting,
  consistent choice per binding site, supertruth where truth simpliciter
  is needed.

The classification of each Lojban construct into this triad (or into
**absence** — no machinery at all) is itself normative (spec §6.1), with
the recovery test printed as the decision rule. The borderline entries
were fought over and settled as follows: `co'e`/`do'e` sit with `zo'e` in
`Context` because CLL presents them as the ellipsis family — recovery
expected; the tanru link stays `Vague` because CLL's ch. 5 catalogue of
"possible relations" is offered as examples, not as a recovery target —
after context has done all it can, a family remains; gradable predication
splits — *which scale* is `Context` (say the wrong scale and you've
misunderstood), *where the cutoff sits* is `Vague` (sorites); and
unmarked distributivity is **absence**, not a parameter (see §2.5).

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
case (`ro prenu cu ponse ci gerku .i ri tatpi`) generalizes the same rule
one scope level up via donkey normalization, rather than adding
machinery. **Cost.** The normalization rules must be stated per
configuration; the exotic ones are gap-registered rather than guessed.

### 1.7 The plural algebra, without covers

**Job.** Number-neutral reference with subreference and join. **Witness.**
`mi jo'u do bevri lo pipno` (a plurality acts; no set object exists to
act), `re lo mu plise` (subreference selection). **Why not sets?** In
the nonempty, atomistic, member-wise fragment the two designs are
intertranslatable — the honest answer is an equivalence-plus-choice,
argued in full in §2.8. The short form: sets used the way a set-typed
lexicon actually uses them (nonempty, predication reading the members,
never the set-object) are a plurality wearing `{}` clothing, and the
clothing costs more than it carries — the plural axioms return as
side conditions, the member-wise/object-wise distinction moves from
the type system into per-place convention, and coverage is lost where
Lojban is deliberately non-atomistic. (The familiar objection — "the
crowd can be large while the set is abstract" — attacks set-*object*
predication, which no serious set-typed design proposes; this document
does not lean on it.) **Why no distributivity/cover
parameter?** See §2.5 — the strongest single "less is more" decision in
the core. **Cost.** Marked readings need marks (`lu'a`, `Distrib`,
group gadri) — which Lojban has.

### 1.8 `DropPlace`, `Tanru`, `Scalar`

Three relation formers, three witnesses: `mi klama ti zi'o` (a relation
with the role *gone* — neither `zo'e` nor closure can remove a role);
`sutra klama` (constitutive modification vagueness — §1.3); `ta na'e
melbi` (scalar otherness is not `¬` — it is *stronger*: CLL 15.4, a
selbri negation "asserts that a relationship exists other than that
stated" and "remains an assertion of some specific truth", so `na'e P`
denies P's stated region *and* positively asserts an admissible
alternative on the recovered scale; `to'e` asserts the antipode, `no'e`
the midpoint. An earlier analysis had `na'e` weaker than
`¬`; the primary text overruled it, and the King-of-France passage of
CLL 15.4 — selbri negations "still make affirmative claims" — is the
decisive witness). Why not lexicalize scalar forms per predicate? The
operators are productive across the whole lexicon; three formers beat
thousands of entries.

The `Tanru` analysis has independent lexical corroboration: the gismu
`tanru`'s official row gives the compound its "meaning ⟨4⟩ in
usage/instance ⟨5⟩" — occasion-relative resolution as a dictionary
fact, adopted as the operator's shadow relation in spec §16.5.

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
gibberish — the sorts are real. **Why is only `Reify` primitive?**
Because `du'u` is the one genuine level crossing (content to object); the
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

### 1.11 Acts, performance, tokens, signs

**Job.** Force, quotation, and reported speech. **Witnesses.** One content
under four forces (`do klama` / `xu` / `ko` / displayed); `mi cusku lu ko
klama li'u` (a directive described, not issued — construction ≠
performance); `lo'u mi do du le'u` (quoting the unparseable — signs carry
text, not meaning); `la'e lu mi klama li'u` (a sign and what it expresses
are different things, and Lojban crosses between them explicitly).
**Why opaque quotation boundaries?** Anaphora and presupposition must not
leak out of mentioned material, or quotation collapses into use.
**Cost.** Tokens and signs enlarge the ontology; every element is
independently witnessed.

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

**Job (dissolved).** An earlier design kept a dedicated non-logical
joining operator for tense/modal facets sharing an event. **Why it
died.** No witness separates it from dynamic `∧`: the shared event is an
explicit variable, so "locus identity" is carried by binding, not by a
connector; and the tag-negation paradigm *derives* from `∧`-placement
what a dedicated operator would have to stipulate — `mi klama ti
sepi'onai ti` negates just the instrument conjunct (`klama ∧ ¬pilno`)
while bridi `na` negates the whole (`¬(klama ∧ pilno)`), and tense
chains (`pu pu`) need precisely `∧`'s left-to-right accessibility for
their anchor anaphora. What survives of the old operator: sumti `joi` as
group formation, discourse joining as `Do`, and the genuinely
unspecified connection as a `Vague` relation (spec §6.1). **Cost.**
None found; the decomposition is pure simplification.

### 1.14 `Bind`

**Job.** Run an effectful computation once and use its result under a
binder — the seam between the pure λ-fragment and the dynamics.
**Witness.** `lo mlatu cu blabi .i ri jbena`: the introduction must run
*once*, with its witness reused across two performed acts —
`(Bind ((x (Refer P))) (Do a₁ a₂))`. **Why not ordinary
λ-application?** Under call-by-value they would coincide — and that is
the honest gloss: `Bind` *is* application under mandatory call-by-value
at computation types, made visible. Making application itself carry
that behavior would fracture the λ-fragment's equational theory:
β-substitution copies the argument's *text*, so an effectful argument
would re-run per use site unless every effectful application were
specially marked — and that marking is `Bind`, demoted from syntax to a
side condition. The core prefers the discipline visible: β-equality
holds unconditionally in the pure fragment, and every
effect-sequencing point is a `Bind` node the accessibility table can
name (witness-export width is stated in terms of it). **Why not the
CPS/state encoding?** `Bind` is famously λ-definable if `RefComp<T>` is
spelled as its state-threading function type — but then information
states and continuations become first-class term values, and the term
language acquires meanings no Lojban sentence has: state inspection,
double-shot continuations (backtracking), and truth-capture-without-
effects — the reflection operator §1.5 deliberately refuses — all free
of charge and all requiring ban-conditions to re-exclude. It also
freezes §5.1's carrier into the definition (any model refinement — the
`da'i` gap entry already commits to adding a world index — would
rewrite the type of every term ever written) and turns the definition
from an interface with many models into a description of one machine.
**Comparative note.** Kuna, the one loglang implementation with real
dynamics, makes the same choice: its expression language is a typed
λ-calculus plus named effect constructors and named combinators
(`and_then` — monadic bind — among its built-in constants), not a CPS
expansion; exactly one of its effects (`Cont`, scope-taking) is
deliberately continuation-typed. Eberban has no `Bind` because it has
no computation layer at all — see §2.4. **Cost.** Two binder forms
(`Let`/`Bind`) where one calculus habit expects one; the distinction
is load-bearing and must be taught.

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
semantics is static semantics at a higher type**, twice over. A whole
discourse's truth conditions are always classically statable — the
donkey normalization's output *is* a classical formula; normalization
is the desugaring, performed by the mapping. And sentence meanings are
statable statically too, at the state-transformer type — §5.1's
carrier is a plain set-theoretic function space. What cannot be
recovered by any desugaring is *compositional locality*: no assignment
of ordinary truth-condition-type meanings to sentences makes `.i`
conjunction and lets `su'o gerku cu klama .i ri melbi` come out right,
because the witness closes inside sentence one before sentence two
exists. A semantics of Lojban discourse must either raise the sentence
type (the transformer model) or globalize the translation (per-
configuration normalization); this core does the second in the mapping
for the supported fragment and justifies those rules uniformly with the
first in the model — with `Bind` as the visible seam (§1.14).

The comparison with Eberban sharpens here. Eberban is a *sentence*
logic with a threaded context parameter: its binding particles desugar,
in its own refgram's equations, to conjunction, ∃-closure, and argument
routing in static HOL, and its cross-sentence references are
context-resolved named variables — retrieval, like this core's keyed
KOhA, not binding. Nothing propositional is thereby inexpressible
(HOL states any classical truth condition, given restructuring into
one sentence with shared variables); what is absent is the anaphoric
route — binding into a closed existential across a sentence boundary,
covariant donkey pronouns — and the two-dimensional layer (projective
vs at-issue commitment). Lojban's grammar makes exactly those things
core (`ri`, `go'i`, witness export, `noi`), so its definition cannot
decline the discourse level; the day Eberban takes on discourse, it
faces the same fork, and the fork is a fact about the phenomena, not a
house style.

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
is curated data. No collection entry needed legislating after all —
source verification showed
official `gunma` x2 is already the components and `selcmi` (a xorxes
lujvo; there is no CLL gloss) already takes its members as x2; both are
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
exact official fit, no dictionary change. (Review history worth
keeping: a dedicated `DescribedBy` relation was the draft analysis
until two supports for keeping it fell — a false claim that `skicu`'s
x4 was a "medium of expression", and a spurious requirement that core
relations be definable independently of the dictionary, which nothing
imposes, since the lexicon program defines gismu semantics.)

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
subset, the singleton lift is `x ↦ {x}`, and
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
  because `No` exports no witness. (An earlier revision ruled the form
  defective outright and leaned on an unverified claim that usage
  avoids it; the claim is withdrawn and the special case adopted.)
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
- **P9 (`kau` exhaustivity is absent).** Three candidates fought:
  default-exhaustive (adds a claim CLL never makes), a `Vague`
  exhaustivity parameter (posits a decision point that *no Lojban
  expression can settle* — an idle wheel: vagueness machinery is owed
  where the language could precisify, and `kau` has no such route), and
  absence. Absence won, with its consequence stated plainly: unmarked
  answerhood has the weakest (mention-some-compatible) truth conditions,
  and stronger readings come from the embedding predicate's lexical
  presuppositions or explicit markers. The parallel with tenselessness
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
- **P17 (termsets, no maximality).** CLL ch. 16 §7 (its examples
  16.42–16.45, print numbering) glosses `ci gerku ce'e re nanmu cu
  batci` as: two picked groups, "every one of the dogs bites each of the
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
export rule to joint-locus normalization, not by refuting the
simplification.

Standing invitations, recorded so future revisions know where to push:
a witness-separating configuration that joint-locus normalization cannot
absorb (narrows §1.6); a facet-joining sentence
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
