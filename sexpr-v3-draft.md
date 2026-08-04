# Experimental smusni S-expression design, draft 6

Status: reductive redesign after the owner review and independent Opus, Kimi,
Qwen, and Gemini sweeps. This draft is not yet approved for implementation. It deliberately
treats the current `SemanticGraph` and XML as evidence and completeness oracles,
not as the ontology that the notation must reproduce.

The central correction inherited from draft 2 is this:

> A semantic distinction may require a typed atom. A serialized field does not
> require a printed constructor.

The intended normal form is one typed application graph. Record-shaped output
is confined to real token/data boundaries and temporary projection failures.

## 1. The kernel is smaller than the semantic vocabulary

The denotational representation kernel has only:

```text
Atom                         lexical root, intrinsic, variable, or literal
Apply(f, x)                  typed application
Fill(pred, place, x)         application to one predicate place
Lambda(parameters, body)     numbered function abstraction
Let(bindings, body)          acyclic graph identity sharing
LetRec(bindings, body)       recursive graph identity sharing
```

`Utterance` and `Sign` later appear as two typed *surface binder sugars* for
real token boundaries. They are not additional denotational primitives: each
elaborates to a `Let` binding of the graph-owned token identity plus application
of an intrinsic token-entry constructor to inert, saturated predicate terms.
Section 9.2 gives the exact types. No other printed form binds an identity.

The concrete S-expression uses a list for left-associated `Apply`, ordinary
operands for consecutive `Fill`, Lisp keyword operands such as `:3 value` for
common labelled fills, `(At p value)` for a computed or modal place designator,
`λ` for `Lambda`, and `Let`/`LetRec` for sharing. Logical operators, quantifiers,
reference operators, relation formers, effect operations, and act constructors
are typed atoms in this graph. Their meanings still differ; a uniform tree shape
does not collapse their types.

This distinction prevents two opposite mistakes:

- keeping `Relative`, `Displayed`, `Quantity`, or `Facet` merely because the
  current model has similarly named records;
- pretending that `∀`, `Presuppose`, `Refer`, `Assert`, and `klama` are all
  ordinary first-order predicates merely because they use application syntax.

## 2. Value families and level crossings

```text
Referents<K>                a nonempty, number-neutral referential value of kind K
Set<K>                 an extensional set of singular K-values; may be empty
PredTerm<ρ>            a predicate term with remaining place row ρ
Fn<A1, ..., An, B>     an ordered, beta-reducing function
Content<Γ, Δ; E>       inert dynamic content, with context change Γ -> Δ
RefComp<Γ, Δ, A; E>    a dynamic computation returning a reference value A
Query<Γ, Δ; E>         an inert polar or open question computation
Act<F, Γ, Δ; E>        a first-class illocutionary act
Discourse<Γ, Δ; E>     a performed discourse computation
Sign<K>                a raw sign value of sign kind K
Fact<K>                a saturated inert PredTerm about token kind K
TranscriptEntry<Γ,Δ;E> a recorded utterance token and its analyzer facts
```

These are renderer types, not a promise that `SemanticSort` already has every
same-named variant. Model relations map to `PredTerm` (or `Fn` when explicitly
abstracted), formulas to `Content`, referent sorts to `Referents<K>`, utterance nodes
to `TranscriptEntry`, and sequences in performing position to `Discourse`.
Event-sorts map from `EventualitySort`; `Sign<K>`, `Act`, and the dynamic
computation types are notation-level distinctions recovered from object kind,
position, force, and effect metadata. Binder annotations are generated through
this declared mapping, never guessed from constructor text.

Surface binder annotations may write `Content`, `(RefComp A)`, `Query`,
`Discourse`, `TranscriptEntry`, or `(Act Assertion)` when the context/effect
indices are inferred locally. Each is an intentional existential erasure of
`Γ`, `Δ`, and `E`, not a distinct untyped family. Force parameters are not
erased: an act binding keeps a type such as `(Act Assertion)`.

`Referents<K>` is deliberately abstract. Its free, discrete model is a nonempty set
of singular `K` values, but the public type is not equated with `Set⁺<K>`.
Ratified xorlo permits generic reference, while the fuller plural algebra and
non-atomic material cases come from an explicitly unofficial analysis. The
notation accommodates those cases without claiming that analysis as the
standard. Every
**referential** lexical place of semantic kind `K` accepts `Referents<K>`, and a
singular bound variable of kind `K` singleton-lifts when it fills such a place.
This includes the distinguished event place and generated event-facet referent
arguments; a singular event binder therefore lifts at the fill. Higher-order
property/content/function places and raw mathematical operands keep their own
types and are not wrapped. A plain predication over
`Referents<K>` is a primitive number-neutral lexical relation; it does not hide an
`Each`, `Group`, cover, or cumulative-closure operator. No distributivity,
cover, or cumulative-closure law is supplied by the notation. Explicit source
distributivity and group formation remain explicit operations or referents.

The free-set implementation model is consequently useful but not exposed as an
identity. A set of people is an abstract set object; it is not the
number-neutral people reference which can walk or eat. Brismu's set-theoretic
foundation is adopted at the metalogical/extension layer, not as an equation
between ordinary Lojban arguments and object-language sets.

`Set<K>` is the ordinary mathematical set used for extensions, cardinality,
and object-language set values. It is not the type of a plain plural argument.

`PredTerm` is the non-Lojban-specific name for the user's proposed central
family. A root, a partially filled root, and a root with every numbered place
filled are all predicate terms. Saturation is only `PredTerm<empty>`; it neither
closes nor asserts the term. Eventuality information and higher-order
composition can still be added afterward.

There is therefore no semantic `Selbri`/`Bridi` type split in this proposal.
Those remain useful Lojban syntax categories: a grammar `selbri` denotes or
builds a `PredTerm`, and a grammatical bridi supplies fills plus a source-owned
closure site. `be`, `fi'o`, descriptions, and `me du'u` demonstrate why the
syntax boundary is not a semantic one. Root, partially filled, and fully filled
terms differ only in their remaining place row; `Close`, then an explicit act
constructor such as `Assert`, performs the later semantic crossings.

Only functions beta-reduce. Applying a predicate term fills one place. A typed
property position may eta-expand a predicate term over its next effective open
referential place. This need not be original x1: earlier places may already be
filled, deleted, or permuted. Since ordinary lexical places are number-neutral
referential places, that argument is itself a reference value:

```text
AsProperty(r) = λ (($x (Referents K))). Close(FillNext(r, $x))
```

This is why `(Refer mlatu)` may stay concise even though the core input of
`Refer` is `Fn<Referents<Entity>, Content>`. The coercion is typed and limited to property-consuming
positions; it is not a silent identification of predicates, functions, and
content.

A raw function likewise fills only a place whose declared type accepts that
function or property. An ordinary referential place does not silently reify a
`Fn`; it needs a source-backed level crossing or uses typed fallback. This
keeps higher-order functions first class without confusing them with property
objects.

The important crossings are:

```text
Close       : PredTerm<ρ> -> Content
Reify       : Content -> Referents<Proposition>
Interpret   : Sign -> Content | Act
Assert      : Content -> Act<Assertion>
Express     : Content -> Act<Expressive>
Perform     : Act<F> -> Discourse
```

`Close` supplies contextual defaults at the graph-owned closure site. For an
eventive predicate term whose event place is otherwise unbound, closing at a
content boundary existentially binds one local event. The binder may be silent
only when the event is unshared, has no non-default properties, and is not
externally referenced. Thus concise `(Assert (klama Speaker))` elaborates to
`Assert(∃(λe. klama(Speaker, Eventuality=e)))`. It is
normally implicit at a typed `Content` boundary and prints only when the same
predicate term is also referenced as a predicate term. `Reify` and `Interpret`
are never implicit: use and mention are not interchangeable.

Effectful reference computations have one further crossing. It is polymorphic
over the dynamic host in which the computation is sequenced:

```text
BindRef[H] : RefComp<Γ, Δ, Referents<K>; E1>
             x Fn<Referents<K>, H<Δ, Θ; E2>>
             -> H<Γ, Θ; E1 + E2>

H<Γ,Δ;E> in RefHost = RefComp<Γ,Δ,A;E>
                    | Content<Γ,Δ;E>
                    | Query<Γ,Δ;E>
                    | Act<F,Γ,Δ;E>
                    | TranscriptEntry<Γ,Δ;E>
                    | Discourse<Γ,Δ;E>
```

`Let (($x (Referents K) ref-comp)) body` is the explicit surface spelling of
this bind at whichever closed `RefHost` family contains `body`. This is why a
binding may properly dominate one act, two acts under `Do`, or a transcript
entry. Only a `RefComp`-typed initializer sequences reference effects. A pure
`Let` that shares `Content`, `Act`, `PredTerm`, a function, or another ordinary
value is inert identity sharing; merely evaluating that binding does not
perform an act or run effects contained inside the shared value.

`Singleton : K -> Referents<K>` is a one-way crossing. It is implicit when a
singular lambda variable fills an ordinary referential place. It prints only
when a source construction has produced one raw object which must remain one
referent, for example the `List` made by `ce'o`; there is no reverse implicit
coercion from `Referents<K>` to `K`.

For concision, a `RefComp` in a `Referents`-consuming operand position may omit
its printed bind. Inline reference syntax is still effectful: it is surface
sugar for `BindRef` at a mechanically computed dynamic site, not evaluation at
the textual occurrence. A **dynamic site** is one of the closed `RefHost`
families above. A pure predicate term, function, set, list, or tuple is not a
site. The graph's reference category, dependency data, and recorded scope
boundaries determine the site:

- a fixed contextual reference binds at the widest legal site which dominates
  every graph-authorized use: normally the enclosing `Act`, the least common
  `Discourse` host for cross-act uses, or a `TranscriptEntry` when the identity
  belongs to that token;
- a `mayDependOn S` contextual value binds inside the innermost binder in `S`,
  or lambda-lifts over exactly `S` when no such computation site exists;
- a variable is already a value and never becomes a `RefComp`;
- `Joi`, `Presuppose`, `Supplement`, and administrative event closure (the
  existential event binder and facet conjunction inserted by `Close`) are
  transparent only within the already selected host. `Reify` first establishes
  its declared local `Intensional` host and is transparent only inside that
  host;
- omission is allowed for a single-use computation when the site is unique and
  the path to it crosses no visible scope-bearing operator whose reading would
  become ambiguous. Crossing `¬`, `∨`, `→`, `↔`, `⊕`, an object-language quantifier,
  a recorded intensional or opaque boundary, or a dependency lambda therefore makes the `Let`
  explicit when the bind itself would cross that boundary. A single-use
  computation wholly contained in the unique local host established by
  `Reify`, another intensional input, or `Refer` may remain inline there; so may
  an inline form beneath `Joi` or an administrative event shell.

Multiple binds at one site sequence in printed left-to-right operand order. An
explicit `Let` is also mandatory for shared identity, for a
dependency-explicit function binding, and whenever a source expansion reuses a
base identity even if the final pretty-printed body happens to contain one
variable occurrence. “Single use” is counted in the semantic graph before
surface contraction. These rules are a deterministic inline/`Let` tie-break,
not a prettifier choice. They keep common
`(klama Speaker (Refer zarci))` concise and requires an explicit act-wide `Let` for
`(¬ (melbi (Refer gerku)))`; the latter is never read as a fresh existential
choice under negation.

A `RefComp` occurring under a pure constructor such as `Tuple`, `Set`, a
predicate term, or a function value is never coerced to a pure `Referents`
value. Its bind is scheduled at a legal enclosing host. A `RefComp` argument may
itself be that local host, which is how a de-dicto description remains inside a
recorded intensional argument instead of acquiring document-level actuality.
Sharing, crossing a visible scope boundary, or dependency abstraction makes the
bind explicit. If the graph supplies no legal dynamic site, the local typed
fallback records that projection defect.

Scope boundaries are data, not renderer guesses. Every relation place and
constructor input that can contain a dynamic value has a closed generated
policy:

```text
ScopePolicy = Extensional | Intensional | Opaque
```

`Extensional` permits the ordinary widest legal host. `Intensional` establishes
a local host for the argument unless the graph explicitly records a de-re owner
outside it. `Opaque` forbids reference/effect escape. Every applicable graph
edge therefore carries `ScopePolicy` plus an optional graph-owned de-re host;
neither field may be omitted by a builder constructor.

The intrinsic input table is closed by precedence over the complete registry
in section 13.1:

1. The input of `Mention`, every input of `StructuredQuote`, and the sign input
   of `Interpret` are `Opaque`. `OpaqueQuote` has raw text rather than a dynamic
   input. Interpretation creates a new graph-declared result outside the quoted
   sign; it does not release the sign's effects.
2. The content/query inputs of `Reify`, `Answer`, `QuestionOf`, `Measure`,
   `TruthValue`, `ExperienceOf`, `ProcessOf`, `ActivityOf`, `Concept`,
   `Abstract`, and `SentenceSign` are `Intensional`. The property inputs of
   `Refer`, `Typical`, and `Stereotypical` establish the corresponding local
   `Intensional` reference computation. Each is subject to an explicit de-re
   owner; other ordinary operands of these constructors use the default below.
3. Every other input position of every registered intrinsic is `Extensional`
   within the dynamic host already selected for its operands. This explicitly
   includes `Polar`, `OpenQ`, `Close`, `Presuppose`, `Supplement`, `Joi`, every
   truth-functional connective and quantifier, the remaining higher-order and
   relation-transformer inputs, act/discourse constructors, collection/math
   constructors, and all token/fact predicates. Their specialized handlers
   still distinguish at-issue content, branch or binder accessibility,
   projective effects, force, and performance.

Thus `Polar` and `OpenQ` are only injections into the `Query` sum; they do not
themselves trap a fixed description. A direct question may bind that description
at its `Ask` host. An embedded question receives its local intensional boundary
from `Answer`, `QuestionOf`, or the lexical attitude place which consumes it.
Likewise, an independent fixed reference may cross an extensional logical
operator, while the operator's dynamic handler separately controls export of
branch- or binder-local introductions.

A subreference occurring inside a `Refer` property remains in that outer
reference computation by default: for example, the doctor reference in the
property corresponding to `lo cukta be lo mikce` does not silently acquire an
act-wide bind. A graph-owned de-re owner can deliberately lift it when the
discourse records that independent identity.

Attitude and other lexical places come from a **new required generated
relation-place policy artifact**. The implementation does not yet possess that
verified table: it must derive and validate one against relation/place metadata
before normal output is licensed. A generated coverage check must enumerate
every lexical place which can contain a dynamic value. Registry closure supplies
every intrinsic input through the precedence rule above; unknown or
contradictory lexical entries use typed fallback. The planner never infers
intensionality from a root's spelling or place sort.

`AsProperty` is likewise an elaboration-only coercion and is never printed.

At the top level, `(Smusni 0 act)` performs the act by document convention.
`Perform` prints when an act-valued expression occurs outside such a performing
position. Pure `Let` and `LetRec` are transparent on this performing spine: a binding
form in a performing position performs its body. Thus assertion remains
explicit without adding `Perform` to every ordinary sentence.

## 3. Dynamic content and effects

The useful denotational model remains an indexed dynamic computation:

```text
Content<Γ, Δ; E> = D<Γ, Δ, Unit; E>
Pure  : A -> D<Γ, Γ, A; empty>
Bind  : D<Γ, Δ, A; E1> x (A -> D<Δ, Θ, B; E2>)
        -> D<Γ, Θ, B; E1 + E2>
```

`D`, `Pure`, and `Bind` are metalanguage definitions of the effect model, not
printed PascalCase atoms; surface sequencing uses the registered forms below.
The row `E` is an ordered sequence of reference introductions,
presuppositions, and supplements. `E1 + E2` is stable left-to-right
concatenation, not an unordered effect set. Expressives are first-class `Act`
values rather than members of this row.

The reference rule is explicit. Evaluating `Refer P` chooses the graph's
number-neutral reference `$r`, emits an introduction of `$r`, and emits the
closed supplement `(P $r)`. `BindRef` evaluates that `RefComp`, closes every
effect over `$r` and all other values in scope at the selected host, routes
presuppositions and supplements to that host's declared handlers in source
order, extends the body context with `$r`, and only then evaluates the
continuation. Projection can relocate a closed effect to its handler but cannot
move an open term or recapture a variable. These are semantic rules for
`Refer`/`BindRef`; an implementation must not reconstruct them from display
shape.

`Do` is the printed discourse sequencing operation. Logical conjunction also
sequences dynamic content, while disjunction, negation, implication, questions,
and attitudes install their own accessibility/effect handlers. A monad alone
does not decide which branch referents escape; the typed operators do.

Projective phenomena are not one undifferentiated flag. The first normal form
keeps three operations whose update behavior differs:

```text
Presuppose : Content x Content -> Content
Supplement : Content x Content -> Content
Express    : Content -> Act<Expressive>
```

`(Presuppose p q)` has at-issue body `q` and triggers the presupposition `p`.
The presupposition may be satisfied, filtered, or accommodated and normally
projects through negation and questioning.

`(Supplement q s)` has at-issue body `q` and speaker-committed non-at-issue
supplement `s`. It is the normal lowering of `noi` and comparable parenthetical
content. It is not a synonym for presupposition.

`Express` constructs an expressive act, as needed for indicators and other
use-conditional material. It is not truth-conditionally conjoined with the host
assertion. An utterance may realize both an assertion act and an expressive act.

The first two forms intentionally have different readable orders:
`Presuppose(trigger, body)` but `Supplement(body, side-content)`. This is fixed
syntax, not a positional guess.

The minimum additional effect laws are:

- `¬`, `Ask`, and conditional/disjunctive embedding target the at-issue body,
  while a `Presuppose` trigger is offered to the nearest presupposition handler;
- an antecedent or earlier conjunct may satisfy/filter a later presupposition;
- `Supplement` side content normally projects to the nearest utterance-level
  supplement handler, retains its explicit anchor/orientation, and is not made
  an antecedent, disjunct, or direct question target by the host operator;
- a supplement created inside a reference computation first closes over the
  reference and every other value in scope at that computation site. Projection
  moves that closed effect to its handler; it does not move open syntax or
  rebind its variables. A supplement already in side-content position is
  flattened into the same side-content sequence in source order;
- a relation input or quotation with declared `Intensional`/`Opaque` policy
  provides the corresponding local host, so neither description content nor
  its effects are hoisted mechanically to document scope;
- `Express` is an `Act`, never an operand of `¬`, `∨`, or another content
  operator; `Do` sequences it with other performed acts.

These are denotational/elaboration requirements. The renderer preserves the
effect nodes and does not attempt pragmatic accommodation itself.

This separation follows the dynamic-semantics literature: presupposition and
anaphora can be modeled as effects over continuations, while supplements form a
distinct non-at-issue dimension. It also prevents draft 2's `Import`,
`Incidental`, `Displayed`, and `AssertionEffect` fields from becoming one vague
replacement enum.

## 4. Filling predicate places

Semantically there is one operation:

```text
Fill : PredTerm<{p:T} + ρ> x p x T -> PredTerm<ρ>
```

The printed contractions are:

- a plain operand fills the next effective place after the last printed fill;
- `:n value` fills original numbered place `n`; it is used when that place is
  skipped or non-next, and is the preferred common labelled-place notation;
- `:Eventuality value` fills the distinguished neo-Davidsonian event place;
- `(At p value)` is the core labelled fill retained for a computed place
  designator or the `PredTerm`-valued designator produced by a fully expanded modal;
- “distinguished event place” means the predicate term's separate
  neo-Davidsonian `Eventuality` place, not every ordinary numbered place whose
  value happens to be event-sorted (such as `pilno` x3);
- a numeric keyword or numeric `p` in `At` always denotes the root's original
  place identity;
- `(DropPlace r p)` removes original numbered place `p`; it is `zi'o`, not a
  fill, and cannot target the distinguished event place;
- place conversion is a relation former such as `(Se r)` or `(Te r)`; plain
  operands then follow effective order while `At` retains original identities.

Examples:

```lisp
(klama Speaker (Refer zarci) :5 (Refer karce))
((DropPlace dunda 2) Speaker This)
(pilno :2 (Refer karce) $e)                 ; x1 skipped, then x3 follows x2
(pilno (Refer karce) :3 $e)                 ; x1 filled, x2 skipped
(broda (At (pilno :2 (Refer karce)) This))  ; PredTerm-valued modal designator
```

There is no modal-specific argument-printing rule.

Unshared implicit `zo'e` is silent. Shared or dependency-bearing contextual
values use ordinary binding and higher-order application:

```lisp
; one fixed contextual referent
(Let (($z (Referents Entity) Context)) ... $z ... $z ...)

; one contextual value that may vary with x
(Let (($z (Fn Entity (RefComp (Referents Entity))) Context))
  ... ($z $x) ...)
```

The function arguments are exactly the binders on which the value may depend.
The context may still supply a constant function, so this preserves “may
depend”, not “must depend”. `MayDependOn` and `Fixed` record nodes disappear.

## 5. Modal and tag normalization

The BPFK gives both a binary paraphrase and a unary bridi-operator account:

```text
broda fi'o brode ko'a  =  broda .i joi ko'a brode
fi'o selbri sumti zo'u sentence
  = lo nu sentence cu jai selbri fai sumti
```

Consequently unary tags have no `Modal` node. They lower to the same ordered,
nonlogical content connector as `.i joi`:

```text
Joi : Content x Content -> Content
```

`Joi` is used rather than mathematical `⊔`: `⊔` conventionally denotes a
commutative join, whereas bridi-operator order is scope-significant. Multiple
tags nest in attachment order.

At the content level, `Joi` evaluates left-to-right: the right operand may use
referents introduced by the left, but the left may not use right-only referents
unless a lexical binder dominates both. Singleton `Assert` may scope over a unary-tag
`Joi` expansion. Two independently forced utterances connected at discourse
locus remain separate acts under `Do` or a typed discourse-level `Joi`; the
renderer does not erase their force boundary merely because the connector word
is the same.

```lisp
; mi klama sepi'o lo karce
(∃
  (λ (($e Eventuality))
    (Joi
      (klama Speaker :Eventuality $e)
      (pilno :2 (Refer karce) $e))))

; mi klama fi'o pilno lo karce
(∃
  (λ (($e Eventuality))
    (Joi
      (klama Speaker :Eventuality $e)
      (pilno (Refer karce) :3 $e))))

; mi klama sepi'o
(∃
  (λ (($e Eventuality))
    (Joi
      (klama Speaker :Eventuality $e)
      (pilno :3 $e))))

; mi klama fi'o broda lo karce; no licensed host-event place
(Joi
  (klama Speaker)
  (broda (Refer karce)))
```

The binary paraphrase does not by itself fill another place of the tag selbri:
the connection remains inextricable but unspecified. The BPFK unary account
also says that a selbri-specific bridi-operator meaning may relate the host
content through an additional place, and offers the first post-x1
content-admitting place only as an orientative rule. Consequently the renderer
never chooses such a place. The shared `$e` above prints because the semantic
graph already records the builder's closed, dictionary-grounded strengthening
for `pilno` x3 (purpose); an arbitrary relation with no recorded host-event
place remains the final unlinked `Joi` example. Thus `Joi` preserves the
unspecified connection, while any more specific relation is visible only when
it is already source/model data. Other elided tag places remain implicit.

Binary `fi'o ... gi ... gi ...` forms lower to ordinary application of the
modal predicate to event/content abstractions at their graph-recorded places.
Contradictory tag negation is `¬` over the tag content; scalar negation is the
relation-level scalar former; compound tags become nested `Joi` applications.
Each `Adjunct.modifiers` displayed-content modifier lowers through the same
typed relation-transformer rules as section 9.3, targeting the bound adjunct
content or predicate term. Because `Express` is an act rather than `Content`,
the resulting expressive act is co-realized at the nearest utterance handler;
it is never inserted as a `Joi` operand. If the graph lacks the anchor needed
to place that act, the modifier uses typed local fallback.
`introduced_by` is provenance. A residual adjunct shape that cannot be expressed
this way is a projection defect and uses local typed fallback, never a normal
`Modal` record.

## 6. Logic and quantification are higher-order

Logical operators are functions over `Content`:

```text
¬             : Content -> Content
∧, ∨          : Content^n -> Content, n >= 2
→, ↔, ⊕       : Content x Content -> Content
∀, ∃          : Fn<T, Content> -> Content
Card          : Fn<T, Content> -> Number
Property<T>   = Fn<T, Content>
GQ<T>         = Fn<Property<T>, Content>
CardGQ<T>     ⊂ GQ<T>
```

Quantifier meanings are first-class higher-order values. The registered
cardinality and universal families are written `(Exactly n)`, `(AtLeast n)`,
`(AtMost n)`, `(MoreThan n)`, `(FewerThan n)`, `Some`, `No`, and `Every`, each
as a `GQ<T>`. `Restrict : GQ<T> x Property<T> -> GQ<T>` supplies the ordinary
conservative restrictor for those registered quantifier families. For example,
`(Restrict Every mlatu)` is the generalized quantifier which maps scope `S` to
`∀x. mlatu(x) → S(x)`; it does not mean `Every(mlatu ∧ S)`. Saturated
cardinality cases normally reduce all the way to the conventional glyph and
`Card` form below. `Exactly`, `AtLeast`, `AtMost`, `MoreThan`, and `FewerThan`
are additionally the closed `CardGQ<T>` family. The named values remain visible
when a quantifier itself is an operand of an equal-scope selection, `Counted`,
or `Witnesses`.

Quantifiers therefore use `λ`; they do not introduce a second binder grammar:

```lisp
(∀ (λ (($x Entity)) (→ (mlatu $x) (jbena $x))))
(∃ (λ (($x Entity)) (∧ (mlatu $x) (jbena $x))))
```

The glyphs retain their conventional classical meanings. `∧` and `∨` use the
ordinary associative variadic contraction, with at least two operands; there
are no hidden nullary truth constants. The other connectives are binary. In
particular, `∀` does not silently acquire existential import.

CLL's restricted universal carries an importing/projective non-vacuity
commitment. That effect is explicit:

```lisp
(Presuppose
  (∃ (λ (($y Entity)) (mlatu $y)))
  (∀ (λ (($x Entity))
       (→ (mlatu $x) (jbena $x)))))
```

This answers draft 2's unexplained `(Import Projective)` completely:

- `Projective` meant that the restriction is committed non-empty even under
  negation or questioning;
- the default absence of `Presuppose` means no such domain-import effect;
- `Restrict` was only a field wrapper and disappears;
- a genuinely non-importing restricted universal is simply the classical
  `∀`/`→` form without `Presuppose`.

Bare count quantification such as `su'o ci mlatu` has ratified expansion through
a singular domain variable (`PA da poi mlatu`). Its higher-order value is
`(Restrict (AtLeast 3) mlatu)`; after application to the containing scope it
reduces to mathematical cardinality of a property extension:

```lisp
(≥
  (Card
    (λ (($x Entity))
      (∧ (mlatu $x) (jbena $x))))
  3)
```

`no` is `¬` over the corresponding existential (or equivalently zero
cardinality where that counting basis is licensed). Exact, at-least, at-most,
greater-than, and less-than counts use `=`, `≥`, `≤`, `>`, and `<` over `Card`.
Other scales use typed functions such as `Portion`, `Ordinal`, `Amount`,
`Extent`, and `Frequency`. Contextual determiners such as “enough” or “too many”
remain named higher-order operators because they do not reduce to a fixed
number.

Keep three surface cases separate; none is an abbreviation for another:

```text
PA broda       singular domain quantification: PA da poi broda
PA lo broda    outer, distributive quantification over a fixed description
lo PA broda    one fixed number-neutral reference with an inner count
```

This is the ratified xorlo distinction. In particular, `ro mlatu` is not
`ro lo mlatu`, and the former's restricted-universal import remains the explicit
`Presuppose` shown above.

An inner *cardinal* quantifier is the higher-order property transformer:

```text
Counted : CardGQ<T> x Property<Referents<T>>
          -> Property<Referents<T>>
Counted(q, P) = λr. P(r) ∧ q(λx. Among(x,r))
```

Thus the concise form is `(Refer (Counted (Exactly 3) gerku))`. This is not a
special numeral field: the same shape retains any registered cardinal inner
quantifier, for example `(Refer (Counted (AtLeast 3) gerku))`. It expands through
the same source-licensed singular member property used by `Card`; if that basis
cannot be recovered, it falls back locally rather than inventing atomicity.

`Every` is deliberately not accepted by `Counted`. The universal inner form
`lo ro broda` is maximal reference, not “a reference containing everything in
the universe.” It expands separately:

```lisp
(Refer
  (λ (($r (Referents Entity)))
    (∧
      (broda $r)
      (∀ (λ (($x Entity))
        (→ (broda $x) (Among $x $r)))))))
```

This maximal-reference expansion is licensed only when the source/model
supplies the singular `Among` basis used by its universal. For a non-countable,
generic, or material restriction without such a basis, the renderer uses local
typed fallback: the closed registry contains no semantics-preserving normal
form for that case, and projection never invents atomicity. For `lo su'o broda`,
ordinary `Referents` nonemptiness already supplies the
at-least-one condition, so the extra cardinal conjunct may be omitted as a
tautology. `lo no broda` cannot construct an ordinary nonempty reference and
takes the source-backed failure/negated-existence path described in section 7.

An outer quantifier applied to an existing reference expression is different.
For fixed `$dogs : Referents<Entity>`, `re le gerku cu blabi` reduces to:

```lisp
(=
  (Card
    (λ (($x Entity))
      (∧
        (Among $x $dogs)
        (blabi $x))))
  2)
```

This is explicitly distributive over singular referents among `$dogs`. `ro`
uses `∀` with `Among` in the antecedent; `su'o` and `no` use nonzero and zero
cardinality. The plain unquantified predication `(blabi $dogs)` remains
number-neutral and is not synonymous with any of those memberwise forms.

`Card (λx. Among x r ∧ P x)` is emitted only when an explicit inner count or
outer quantifier supplies a singular counting basis. The singular values are
the values substitutable for the source's ordinary bound variable, not
metaphysical atoms. A generic or material reference is therefore not silently
assigned cardinality zero. If the graph cannot recover the source-licensed
member relation or contradicts it, projection uses local typed fallback and a
collected diagnostic instead of inventing a `Card` formula.

When a quantifier's selected witnesses are subsequently referenced, the
truth-conditional `Card`/∀ formula is not enough. The old two-operand form
`Witnesses(source, property)` is also insufficient: it forgets whether the
originating quantifier was exact, lower-bounded, universal, or another
generalized quantifier. The graph-owned witness reference is instead bound by:

```text
Witnesses : GQ<T> x Property<T>
            -> RefComp<Γ, Δ, Referents<T>; E>
```

The first operand is the originating generalized quantifier, including any
independently present restriction; the second is its nuclear-scope property.
Thus bare `ci da gerku` supplies `(Exactly 3)` and the property `gerku`, while a
source `poi` restriction would be retained with `Restrict` in the first operand.
`Witnesses` denotes the discourse referent exported
by that successful dynamic quantifier application. It is neither defined as an
arbitrary satisfying subset nor silently fixed as the globally maximal
property extension: numeral anaphora admits local, global, and pragmatic
witness-selection analyses, and the current graph owns the identity. Keeping
the GQ makes those choices inspectable and prevents an exact and an at-least
reading from collapsing to the same datum.

The at-issue truth condition still prints independently over the original
restriction and scope; it is never replaced by a cardinality claim about the
chosen witness reference, which would be vacuous for an exact quantifier and
wrong for a lower bound. The binding form is mechanically triggered only when
the graph records a later-accessible referent whose selection source is this
quantifier. A zero-witness quantifier does not yield the nonempty
`Referents<T>` type; an attempted escaped anaphor then uses the graph's
inaccessibility/typed-fallback path. `Witnesses` replaces the record-shaped
`SelectionSource::WitnessSet` in normal output. `WitnessOf` remains only for a
graph relation that independently constrains an already existing witness
referent.

```lisp
; ci da gerku .i re da blabi
(Let (($dogs (Referents Entity)
        (Witnesses (Exactly 3)
          (λ (($x Entity)) (gerku $x)))))
  (Do
    (Assert
      (= (Card (λ (($x Entity)) (gerku $x))) 3))
    (Assert
      (=
        (Card
          (λ (($x Entity))
            (∧ (Among $x $dogs) (blabi $x))))
        2))))
```

Termsets can be genuinely polyadic: ordinary nesting would choose a dependency
order absent from the source. The CLL's cardinal example is nevertheless not an
irreducible `PolyQuant` record. It can be reduced with ordinary first-class sets
and higher-order quantification. For determiner quantifiers `Qi`, lexical
restrictions `Pi`, selected sets `Si`, and nuclear relation `R`, first define
the coordinate extension relative to the other selected sets:

```text
Ei(xi; S-i) =
  Pi(xi) ∧
  ∀ x1 ... x(i-1) x(i+1) ... xn.
    (∧j≠i xj ∈ Sj) → R(x1,...,xn)

∃ S1 ... Sn.
  ∧i [(Restrict Qi Pi) (λxi. xi ∈ Si)]
  ∧i [∀xi. xi ∈ Si ↔ Ei(xi; S-i)]
```

The biconditionals are the coordinate form of Sher's maximal each-all
condition for branching generalized quantifiers. The right-to-left direction makes each `Si`
coordinate-wise exhaustive, rather than permitting an arbitrary smaller
subset of a qualifying rectangle. Without it, `Exactly n` would collapse into
`AtLeast n`: whenever four dogs qualify, one could simply choose a three-dog
subset. With it, the two quantifiers remain distinct. The equations may have
multiple incomparable solutions; the existential says that some mutually
closed Cartesian rectangle satisfies all `Qi`, not that there is a unique
greatest rectangle. See [Ways of Branching
Quantifiers](https://philosophyfaculty.ucsd.edu/faculty/gsher/ways-of-branching-quantifiers.pdf),
definition 6.C.

Thus `ci gerku ce'e re nanmu cu batci` becomes:

```lisp
(∃ (λ (($dogs (Set Entity)))
  (∃ (λ (($men (Set Entity)))
    (∧
      (= (Card $dogs) 3)
      (= (Card $men) 2)
      (∀ (λ (($x Entity))
        (↔
          (∈ $x $dogs)
          (∧
            (gerku $x)
            (∀ (λ (($y Entity))
              (→ (∈ $y $men) (batci $x $y))))))))
      (∀ (λ (($y Entity))
        (↔
          (∈ $y $men)
          (∧
            (nanmu $y)
            (∀ (λ (($x Entity))
              (→ (∈ $x $dogs) (batci $x $y)))))))))))))
```

The coordinate selectors are mutually referential by design: each `Ei` mentions
all of the other selected sets. Both existential set binders therefore prefix
one shared conjunction. Their classical order is immaterial because existential
binders of the same force commute over that conjunction, not because the
selectors are independent. The scope-sensitive individual quantifiers have not
been nested. This is the
branching/equal-scope reading: one fixed three-dog set, one fixed two-man set,
every Cartesian-product pair in the biting relation, and no additional dog or
man which qualifies relative to the other selected set.

The worked cardinal form contracts
`(Restrict (Exactly n) Pi)(λxi. xi ∈ Si)` to `(= (Card Si) n)` only because the
forward biconditional entails `Si ⊆ Pi`. Other quantifier conditions retain the
general `Restrict` application unless an equally justified reduction exists.

This mutually exhaustive lift is total in the first profile only for positive
exact and lower-bound cardinal quantifiers, `Some`, and importing `Every`, and
only where the graph supplies the singular extension basis used by `Pi`.
Downward-entailing or zero-witness quantifiers do not acquire a vacuous empty
selected set; generalized non-cardinal and unsupported branching lifts use
local typed fallback rather than a false reduction. Effects belonging to a
term's GQ remain at that termset site. An importing `Every` keeps its explicit
`Presuppose`. If a selected participant identity escapes, the graph binds its
ordinary `Witnesses(full-GQ, nuclear-scope)` computation at the accessibility
site; the raw mathematical `Set` used in this formula is not itself a walking,
biting, or anaphorically referenced plurality.

The existing tersmu nesting is not a semantic precedent. Its own documentation
says that termset quantification was intentionally ignored, and the implementation
is still a work in progress. The builder must therefore preserve equal-scope
termset structure for this lowering; if it has already collapsed the source to
an ordered nest, that model loss is a correctness defect, not renderer input to
imitate.

Logical glyph recognition still requires exact truth-table and source-connector
evidence. The renderer never turns an arbitrary stored `∨(¬P,Q)` into `→`.

## 7. Reference, descriptions, and relative clauses

There is one typed reference operator, not a semantic copy of the Lojban gadri
inventory:

```text
Refer : Property<Referents<T>>
        -> RefComp<Γ, Δ, Referents<T>; E>
```

`Refer` is intentionally an English PascalCase intrinsic. Conventional `ι`
denotes a unique definite description, while Hilbert `ε` conventionally
chooses a single witness. Neither convention accurately advertises xorlo's
context-resolved, number-neutral reference. A renderer contraction may later
use a symbol if the calculus adopts a precisely documented choice semantics,
but the experimental tree should not smuggle in singularity or uniqueness.

`Refer` is an effectful dynamic reference computation, not a pure choice
function. Ratified xorlo defines `lo broda` as `zo'e noi ke'a broda`, so a
description's own predication is a projecting descriptive commitment rather
than part of the containing assertion, denial, or question's at-issue nucleus.
Schematically, in a surrounding content continuation `Q`:

```lisp
; Q (Refer P)
(Let (($r (Referents T) Context))
  (Supplement (Q $r) (P $r)))
```

The three common source gadri families reduce compositionally before printing:

```lisp
; lo P
(Refer P)

; le P: skicu x1 describes x2 to x3 as satisfying x4
(Refer (skicu Speaker :3 Audience :4 P))

; la name: cmene x1 is the name of x2 according to x3
(Refer (cmene (NameSign "alis") :3 Speaker))
```

In the latter two forms, x2 is the next effective open referential place, so
the `AsProperty` coercion eta-expands over the referred value. This is why
`AsProperty` is defined over the next effective open place rather than original
x1. `le` contributes the speaker's `skicu` description rather than directly
asserting `P`; `la` contributes the builder-recorded lowercase naming
predication. Their full continuation forms are:

```lisp
; Q applied to a le-reference
(Let (($r (Referents T) Context))
  (Supplement
    (Q $r)
    (skicu Speaker $r Audience P)))

; Q applied to a la-reference
(Let (($r (Referents Entity) Context))
  (Supplement
    (Q $r)
    (cmene (NameSign "alis") $r Speaker)))
```

The effects are created at the description's embedding site and project only
to the nearest handler installed for that site. A description inside `djica`,
quotation, or another attitude therefore does not create a document-level
actual-existence commitment. `Let` sequences the effects when binding the
returned reference, and the closed-effect rule in section 3 preserves its
locally bound anchor during projection.

This deliberately follows ratified xorlo even where the current work-in-progress
builder labels a `lo` restriction as `PredicationMode::Restrictive`. That mode
is retained as source/provenance evidence while the description is corrected
to projecting `noi` semantics; it is not semantic authority over the notation.

The common eta-expansion remains implicit, so the normal forms stay short:

```lisp
(Refer cukta)
(Refer (skicu Speaker :3 Audience :4 gerku))
(Refer (cmene (NameSign "alis") :3 Speaker))
```

Composite personal pro-sumti use the same plural algebra, not the abolished
mass machinery. `mi'o` is `(Combine Speaker Audience)`; `mi'a` and `do'o`
combine `Speaker` or `Audience` with the graph's appropriately exclusive
contextual-other reference, binding that `Context` when its identity/effects
require it.

The property is a property of the number-neutral reference value, not silently
an `Every` over atomic members. Thus collective, generic, and non-atomic
descriptions remain possible. An inner numeral is an additional constraint
inside the same property:

```lisp
; fully reduced lo ci gerku
(Refer
  (λ (($r (Referents Entity)))
    (∧
      (gerku $r)
      (=
        (Card
          (λ (($x Entity))
            (Among $x $r)))
        3))))
```

The concise contraction is `(Refer (Counted (Exactly 3) gerku))`. `Counted`
applies a generalized quantifier to the reference's singular member property;
it is not an outer quantifier. The constraint cannot be asserted after
selecting an unconstrained `(Refer gerku)`, because that would give it the wrong
force under negation, questioning, and attitudes.

Ordinary reference computations are nonempty. A literal zero inner count does
not construct an empty `Referents<K>`: under the ratified constant semantics
`lo no broda` has no ordinary description denotation and lowers only through a
source-backed negated-existence construction or a referential-failure fallback.

Draft 2's relative-clause record is eliminated using the established
desugarings.

### 7.1 `poi`

For a quantified existential host, the restriction is conjunction; for a
universal it occurs in the antecedent of implication. On a description, `poi`
refers contextually to a subreference of the host and commits that supplied
subreference to the clause, equivalently `lo me <sumti> je <clause>`. The
formalism neither computes nor entails a maximal satisfying subset. Expanding
`le` makes the two descriptive commitments explicit:

```lisp
; le gerku poi blabi, in a surrounding body Q
(Let (($base (Referents Entity) Context))
  (Supplement
    (Q
      (Refer
        (λ (($r (Referents Entity)))
          (∧
            (Among $r $base)
            (blabi $r)))))
    (skicu Speaker $base Audience
      (λ (($r (Referents Entity))) (gerku $r)))))
```

`$base` is the contextual reference described by `le`; `skicu` is its
speaker-oriented supplemental description. `blabi` is an ordinary, veridical
condition on the selected subreference. By the `Refer` rule above, the `Among` and
`blabi` property is selection material inside the description and therefore
backgrounded rather than a target of the containing assertion or question.
This is structurally distinct from `noi` below: `poi` is conjoined inside the
selecting property, while `noi` is a supplement about the already selected
referent. No individual-level `Filter`, `Restrictive`, or `Veridical` node is
necessary, and collective or non-atomic relative predication is not forced
into memberwise distribution.

### 7.2 `voi`

The builder and the BPFK account already express nonveridical restriction as a
description claim. The reduced form prints that predication while keeping the
`le` base description supplemental:

```lisp
; le gerku voi blabi, in a surrounding body Q
(Let (($base (Referents Entity) Context))
  (Supplement
    (Q
      (Refer
        (λ (($r (Referents Entity)))
          (∧
            (Among $r $base)
            (DescribedAs Speaker $r
              (λ (($s (Referents Entity))) (blabi $s)))))))
    (skicu Speaker $base Audience
      (λ (($r (Referents Entity))) (gerku $r)))))
```

The whiteness property is used under the graph's three-place `describedAs`
relation and is not asserted of `$r`. The current builder supplies speaker,
described referent, and property; it supplies no audience place. Consequently
the PascalCase intrinsic is required unless a lowercase three-place dictionary
root is independently verified. It must not be collapsed into the four-place
`skicu` used for `le`'s base-description supplement, since that would fabricate
an audience and make two different semantic relations look identical.

### 7.3 `noi`

Incidental content becomes a supplement at the narrowest scope containing its
anchor and every referenced identity. The description is bound first and the
supplement predicates of that first-class referent outside the selecting
property:

```lisp
; lo cukta noi mi nelci ke'a, in a surrounding body Q
(Let (($r (Referents Entity) (Refer cukta)))
  (Supplement
    (Q $r)
    (nelci Speaker $r)))
```

This preserves attachment, speaker commitment, projection, and accessibility,
and makes the restrictive/incidental contrast visible without a `Relative`
record. Multiple `poi` clauses conjoin inside the property; multiple `noi`
clauses sequence as supplements; `zi'e` preserves the source attachment order
but contributes no logical connective of its own. Relative `goi` assignments
likewise become identity binding or an ordinary association predication.

Source `le` has the source-backed expansion into contextual reference plus a
speaker `skicu` supplement shown above. No `Le` intrinsic survives in this
profile; the concise form is `Refer` applied to the partially filled `skicu`
term. The renderer must elaborate that property to the same effect calculus
when relative-clause scope or sharing requires the continuation expansion.
If the graph says that contextual reference may depend on an enclosing `$x`,
the expansion lambda-lifts exactly that dependency rather than freezing it:

```lisp
(Let (($base (Fn Entity (RefComp (Referents Entity))) Context))
  (Supplement
    (Q ($base $x))
    (skicu Speaker ($base $x) Audience
      (λ (($r (Referents Entity)))
        (gerku $r)))))
```

The context may still supply a constant function; the annotation preserves
“may depend”, not “must differ”.

### 7.4 Set/group gadri, nonlogical connections, and LAhE crossings

Set and group gadri are number-neutral descriptions of set/group referents.
They elaborate through ordinary predications, with the base reference bound
once:

```lisp
; lo'i prenu
(Let (($people (Referents Entity) (Refer prenu)))
  (Refer
    (selcmi
      :2 $people)))

; loi ci prenu
(Let (($people (Referents Entity) (Refer (Counted (Exactly 3) prenu))))
  (Refer
    (gunma
      :2 $people)))
```

The outer `Refer` remains number-neutral: the first result is `Referents<Set<Entity>>`
and the second `Referents<Group<Entity>>`, not a statically forced singleton.
`le'i`/`lei` use the `skicu` property for the base; `la'i`/`lai` use the
`cmene` property. This follows the
ratified `selcmi`/`gunma` expansions and deliberately treats groups as ordinary
referents with ordinary properties.

The four referential nonlogical connections are not one generic composition
operator:

| source | reduced value | result level |
|---|---|---|
| `X jo'u Y` | `(Combine X Y)` | ordinary number-neutral reference |
| `X joi Y` | `(Refer (Counted (Exactly 1) (gunma :2 (Combine X Y))))` | one group referent |
| `X ce Y` | `(Refer (Counted (Exactly 1) (selcmi :2 (Combine X Y))))` | one set referent |
| `X ce'o Y` | `(Singleton (List X Y))` | ordered-sequence referent |

Only `jo'u` stays at the ordinary-reference level. `joi`, `ce`, and `ce'o`
form one group, set, or sequence object respectively. That semantic singleton
law is explicit for all three: `Counted (Exactly 1)` constrains the relational
descriptions, while `Singleton` crosses the already constructed raw `List` to
a referential value.
The corresponding gadri remain different: bare `loi` and `lo'i` are
number-neutral descriptions and can refer to a group or groups, or a set or
sets.

CLL describes the connected operands in this parallel family as individuals.
In the ordinary source-proven singleton case the table is exact. If the graph
instead supplies plural operands, `joi`/`ce` use the graph's flat component or
member reference, and `ce'o` uses its recorded ordered element stream. The
renderer does not silently make the first two flat while treating each opaque
plurality as one list element; absent that structural evidence it uses local
typed fallback.

`lu'i`, `lu'o`, and `vu'i` use the same constructors/relations, but apply to one
already assembled operand rather than being gadri:

```lisp
; lu'i S
(Refer (Counted (Exactly 1) (selcmi :2 S)))

; lu'o S
(Refer (Counted (Exactly 1) (gunma :2 S)))

; vu'i S -- the source supplies a sequence but no explicit ordering rule
(Let (($set (Referents (Set K))
        (Refer (Counted (Exactly 1) (selcmi :2 S)))))
  (Refer (Counted (Exactly 1) (porsi :3 $set))))
```

The elided x2 of `porsi` remains contextual only when the source supplies no
order. If `S` is already an ordered sequence or the graph records its ordering
rule, `vu'i` preserves that value/rule instead of detouring through an unordered
set and choosing a new contextual order. `Counted (Exactly 1)` records the
single object constructed by `lu'i`, `lu'o`, and `vu'i`, including where the
lexical relation alone would not prove uniqueness.

The `lu'i` reduction uses the standard dictionary reading of `selcmi` as “the
set whose members are x2” and therefore extensional set identity. Guskant notes
that this exact-membership sharpening was not independently settled as a
general official axiom; the notation records that provenance rather than
presenting the expansion as a theorem of bare place structure alone.

`lu'a` is the reverse crossing and also makes the containing predication
distributive. It therefore cannot survive merely as a value constructor whose
result is passed to a number-neutral lexical place. For a set or group `$s`, a
host property `P` lowers to:

```lisp
(∀
  (λ (($x K))
    (→
      (cmima $x $s)
      (P $x))))
```

For an ordinary number-neutral operand, the antecedent is `(Among $x S)`.
When the member reference itself is graph-owned for later anaphora, bind the
source-backed description `(Refer (cmima :2 $s))` and use that same identity in
the quantified lowering. A `lu'a` of an empty set cannot yield the nonempty
reference required by a sumti and produces local typed fallback plus a
collected semantic diagnostic. No `SetOf`, `GroupOf`, `SeqOf`, `Members`, or
generic `Mass` intrinsic remains in normal form.

`lo'e` and `le'e` have no agreed reduction comparable to the expansions above.
They remain the registered `Typical` and `Stereotypical` higher-order reference
operators, rather than receiving an invented set/group analysis.

## 8. Abstractions and events

The abstraction syntax is uniform, but its output types are not. The normal form
eliminates a generic `Nu`/`Ka` record while retaining irreducible level
crossings.

### 8.1 Property and relation abstractions

CLL describes a property as an intension which, when applied to an object,
yields truth. That is exactly a function value:

```lisp
; lo ka ce'u prami mi
(λ (($x (Referents Entity)))
  (prami $x Speaker))
```

Multiple distinct `ce'u` produce a multi-argument function. A bare abstractor
used predicatively can be elaborated as the singleton relation whose x1 equals
that function; the common `lo ka` value needs neither `Refer` nor `Ka` in the
printed result.

### 8.2 Event abstractions

`lo nu P` is a description of eventualities for which `P` holds:

```lisp
(Refer
  (λ (($e (Referents Eventuality)))
    (cilre Speaker :Eventuality $e)))
```

`mu'e` and `za'i` use binder subsorts `Achievement` and `State`. `pu'u` and
`zu'o` cannot be reduced merely by changing that binder type: their source place
structures also preserve x2 (“stages” and “repeated actions”). They therefore
use the level crossings below. An omitted extra place remains contextual; a
present builder operand is never discarded.

### 8.3 Other abstractions

Some abstractors cross semantic levels and remain named operators:

```text
Reify       : Content -> Referents<Proposition>                 du'u
Measure     : Content x Referents<Scale>? -> Referents<Amount>  ni
TruthValue  : Content x Referents<Epistemology>?
                                      -> Referents<TruthValue>  jei
ExperienceOf: Content x Referents<Entity>? -> Referents<ExperientialContent>
                                                            li'i residue
ProcessOf   : Content x Referents<Eventuality>? -> Referents<Process> pu'u
ActivityOf  : Content x Referents<Eventuality>? -> Referents<Activity> zu'o
Concept     : Content x Referents<Mind>? -> Referents<Concept>       si'o
Abstract    : Content x Referents<T>? -> Referents<AbstractNature> su'u
SentenceSign: Content -> Sign<Sentence>                         sentence-sign abstraction
```

These are not a generic `(Abstraction (Kind ...) (Body ...))` record. Their
different signatures are the semantics. The optional second operands of
`Measure`, `ProcessOf`, `ActivityOf`, `ExperienceOf`, `Concept`, and `Abstract`
preserve the six extra abstraction places represented by the current builder;
one is omitted only when the source/model omits it. `TruthValue` also admits its
ordinary `jei` epistemology place when a source/model supplies it, although the
current builder does not yet expose that place through the same six-way table.
For example, a graph which records the stages of `lo pu'u broda` prints
`(ProcessOf (Close broda) $stages)`, not merely a process-sorted event lambda.
`SentenceSign` covers the distinct builder kind which also uses
`abstractionOf` but returns a sign and has no extra place.

### 8.4 Event properties

Every event facet lowers to one or more ordinary predications sharing the event
identity. The mapping must be total over the model fields. Where a BPFK/CLL
source and place structure license a dictionary root, the lowercase root is
preferred:

```lisp
(∃
  (λ (($e Eventuality))
    (∧
      (klama Speaker (Refer zarci) :Eventuality $e)
      (purci $e Now))))
```

Where no exact content root is licensed, a PascalCase intrinsic predicate is
used. Anchors, endpoints, magnitudes, directions, recurrence counts, actuality,
and motion are operands, not `Facet` fields. Sticky/inherited builder state and
source markers are provenance. `Facet` is never intended normal form.

Tanru composition remains one honest vague relation former:

```lisp
((Tanru blanu zdani) This)
```

`OfKind` is rejected because it asserts a particular modifier-head relation the
language does not guarantee.

## 9. Acts, utterances, indicators, and questions

### 9.1 Acts remain first class

```text
Assert    : Content -> Act<Assertion>
Ask       : Query -> Act<Question>
Command   : Referents<Entity> x Content -> Act<Directive>
Mention   : A -> Act<Mentioning>
Express   : Content -> Act<Expressive>
Vocative  : Referents<Entity> -> Act<Address>
```

The force index is a closed literal family:
`Assertion | Expressive | Question | Directive | Mentioning | Address`.
`Mention` is the callable act constructor; `Mentioning` is its force value, so
constructor and literal never collide.

Predication modes disappear:

- asserted content is the operand of `Assert`;
- restrictive content occurs in a property/quantifier lambda;
- inert content occurs outside a force constructor;
- incidental content is `Supplement`;
- displayed content is an `Express` act or supplement;
- performative readings use the source-backed act constructor.

The current model's force and mode enums are disposed as follows. Utterance
forces `Assert`, `Ask`, `Command`, `Mention`, and `Vocative` select the matching
act above. `Quote`, `Parenthetical`, and `Subordinated` are embedding statuses,
not extra illocutionary forces: quotation yields an inert `StructuredQuote`, a
parenthetical is handled as `Supplement`, and subordinated material remains
inert `Content`/`Discourse` at its embedding site. They are never implicitly
performed. A missing host/embedding relation uses typed local fallback rather
than inventing force.

Imperative `ko` supplies the deictic `Audience` at its ordinary predicate place
and selects that same referent as the command addressee. Thus `ko klama` has the
shape `(Command Audience (klama Audience))`; it does not require a separate
imperative predication mode.

`PredicationMode::Definitional` is currently assigned mechanically to the
ordinary identity/`du` relation, including `li re su'i ci du li mu`. It is a
builder relation annotation, not evidence for a definition act, and is dropped
after the relation becomes `=`. The utterance's `Assert` force therefore yields
`(Assert (= (+ 2 3) 5))` without a mode-mismatch diagnostic. Restrictive,
incidental, displayed, inert, and performative modes are likewise checked
against their typed lambda/effect/act positions before being discarded. Only a
mismatch left after these declared mappings is a semantic diagnostic, never
`(Mode ...)` output.

### 9.2 Utterance tokens are real boundaries, but their facts are predications

An utterance record survives only when token identity, metadata, quotation, or
multiple co-realized acts matter. Everything about the token is expressed as an
ordinary predicate term under that transcript boundary:

```text
Transcript      : Referents<Utterance> x Fact<Utterance>* -> TranscriptEntry
SignEntry       : Sign<K> x Fact<Sign>* -> Sign<K>
Realizes        : Referents<Utterance> x Act -> Fact<Utterance>
SpeakerOf       : Referents<Utterance> x Referents<Entity> -> Fact<Utterance>
AudienceOf      : Referents<Utterance> x Referents<Entity> -> Fact<Utterance>
```

`Fact<K>` is only a type refinement of a saturated inert `PredTerm`; there is
no printed `Fact` wrapper and these predications are not closed or asserted.
The surface binder
`(Utterance $u fact...)` elaborates to a `Let` binding of the graph-owned
utterance-token atom followed by `(Transcript $u fact...)`. `(Sign $s fact...)`
does the same with `SignEntry`. The token atom is an existing graph identity,
not a newly quantified discourse entity. These are the two binder sugars named
in section 1, so token facts remain bridi while no seventh kernel operation is
introduced.

```lisp
(Let (($c Content (klama Speaker (Refer zarci)))
      ($a (Act Assertion) (Assert $c)))
  (Utterance $u
    (Realizes $u $a)
    (SpeakerOf $u Speaker)
    (AudienceOf $u Audience)))
```

`SpeakerOf` is deliberately distinct from the indexical atom `Speaker`.
Likewise use `AudienceOf`, `LocutionOf`, `DeicticTimeOf`, and `DeicticPlaceOf`.
Transcript facts are analyzer/record facts, not speaker assertions. An
utterance record in a performing position (under `Smusni` or `Do`, modulo
transparent `Let`/`LetRec` bindings) performs the acts named by `Realizes`; an
embedded record is a value.

An ordinary predication can still report an utterance:

```lisp
(Assert (Utters Speaker $u))
```

This asserts that the speaker uttered `$u`; it neither performs `$u` nor asserts its
content. `Utters` is printed only if the semantic/document graph actually
contains that relation.

### 9.3 Indicators and metalinguistic material

`Displayed`, `Family`, `Polarity`, `AssertionEffect`, `Experiencer`, `Target`,
`TargetFocus`, and `Anchor` disappear.

Each known indicator relation is a typed higher-order predicate. Its ordinary
arguments are the experiencer, the actual target value, and when semantically
needed the utterance anchor. Content and predicate terms are bindable values, so
focus is the target's type/identity rather than an enum.

Polarity, intensity, phase, and modifiers are relation transformers:

```text
Scalar : ScalarDirection x PredTerm<ρ> -> PredTerm<ρ>
Degree : DegreeValue x PredTerm<ρ> -> PredTerm<ρ>
Phase  : PhaseKind x PredTerm<ρ> -> PredTerm<ρ>
```

An `Adjunct.modifiers` value transforms the displayed relation attached to that
specific adjunct. The target relation/act/content is therefore bound first and
passed as an operand to the transformer or indicator predicate; modifiers are
never emitted as free-floating co-realized acts with no target identity.

The old `assertion_effect` chooses the surrounding act construction and is not
printed: a host assertion is present or absent; a performative uses its act; the
indicator itself is normally `Express`.

The model stores one primary `UtteranceForce`; additional `Realizes` facts are
synthesized only from displayed-content nodes anchored to that utterance. They
do not imply that the force field itself was multi-valued.

```lisp
(Let (($c Content
        (¬
          (djica Speaker
            (Refer
              (λ (($e (Referents Eventuality)))
                (cilre Speaker :Eventuality $e)))))))
  (Utterance $u
    (Realizes $u (Assert $c))
    (Realizes $u
      (Express
        (Contrast Speaker $c $u)))))
```

Here `$c` is the target and `$u` the anchor; no `ActContent` sentinel or
`TargetFocus` taxonomy exists. If a predicate-expression locus is targeted, the
bound target has type `PredTerm`, and the act closes it explicitly where
content is needed.

Unknown indicator relations use a typed local projection fallback until the
semantic relation table is complete; they do not resurrect `Displayed`.

### 9.4 Questions

The general direct forms are:

```lisp
(Ask (Polar (klama Audience)))
(Let (($market (Referents Entity) (Refer zarci)))
  (Ask
    (OpenQ
      (λ (($x (Referents Entity)))
        (klama $x $market)))))
(Ask
  (OpenQ
    (λ (($p (OpenPredTerm (Referents Entity))))
      (Close ($p This)))))
```

Polar questions consume closed content; wh questions consume a lambda; multiple
wh slots are multiple lambda parameters. Direct and indirect questions share a
first-class sum type:

```text
Query      = Polar<Content> | OpenQ<Fn<A1,...,An,Content>>
Ask        : Query -> Act<Question>
QuestionOf : Query -> Referents<Question>
Answer     : Query -> Content
```

`Ask` performs the query. `QuestionOf` crosses the same inert query to an
object-language question referent only when an ordinary predication needs that
object identity. `Answer` is the conventional question-to-proposition
answerhood operator: for an indirect `kau` question it supplies the
contextually/exhaustively true answer content consumed by the enclosing
attitude or abstraction. It works for both polar and open questions, so the old
polar-only `Whether` atom is removed. The exact exhaustivity/presupposition
profile must come from the graph and source-backed question lowering; the
renderer never chooses one pragmatically.

For `(Polar C)`, the answer domain is exactly the positive content `C` and its
negative content `(¬ C)`. The graph records which contextually true alternative
the `Answer` node denotes; the renderer neither infers polarity from surface
words nor silently defaults to the positive answer. `Unresolved` prints only
when the graph explicitly declares that semantic value; missing or incomplete
answer data uses typed fallback. Open answers analogously retain the
graph-selected argument tuple and exhaustivity profile.

For example, the embedded question in `lo du'u makau cortu` lowers without a
`Question` record:

```lisp
(Reify
  (Answer
    (OpenQ
      (λ (($x (Referents Entity)))
        (cortu $x)))))
```

If the graph records a particular presupposed answer, that value and the
ordinary dictionary relation `danfu` make it explicit. For open-question
function `$f` and answer `$a`, the query value is `(OpenQ $f)` and the shape is
`(Presuppose (danfu $a (QuestionOf (OpenQ $f))) ($f $a))`. The function is
applied; the `Query` sum value is not. A polar query uses its selected
positive/negative answer content instead of function application. No
`TargetFocus`, answer slot, or special question field is needed. Sorts derive
argument/relation/place/connective/tense/math/quantity question kinds.
Non-default asker/respondent are act arguments or ordinary report predicates.

## 10. Discourse, composition, respectively, math, and signs

### 10.1 Discourse sequence

Ordinary sequence is `Do`. `Sequence` is not normal form.

```text
Do       : Performable ... -> Discourse
Performable = Act | Discourse | TranscriptEntry
NewTopic : Discourse -> Discourse
Resume   : Discourse -> Discourse
Label    : LabelLevel x Math x A -> A
```

An `Utterance` transcript entry in a performing position, including beneath
transparent `Let`/`LetRec` bindings in an operand of `Do`, performs every act
named by its `Realizes` predications. The same entry inside quotation, mention,
or an ordinary value position is inert; `PerformUtterance` is the explicit
spelling when position does not imply performance.

`Joi` also has its declared discourse overload. It combines already performed
discourse computations rather than wrapping their acts in a modal record:

```lisp
(Smusni 0
  (Joi
    (Perform (Assert broda))
    (Perform (Ask (Polar brode)))))
```

`NewTopic` and `Resume` print only for the matching
`ParagraphTransition::{NewTopic, ResumePriorTopic}`. `Label` prints only from
an `OrdinalLabel`; its level and math value are operands and it wraps the
graph-recorded target. These operators are not inferred from paragraph layout.

Connection claims are the actual logical or nonlogical content. Bound events
are lambda/quantifier binders. An elided discourse operand is `PriorDiscourse`
or `FollowingDiscourse`. A sequence record survives only if the sequence itself
has externally referenced token identity; its internal facts are ordinary
predications just like an utterance record.

### 10.2 Nonlogical values and respectively

Use established mathematical constructors when the semantics matches:

```text
Set, List, Tuple, ∪, ∩, ×, Interval
```

Do not preserve `Composition`, `Operator`, `Collective`, or endpoint field
records. Constructor-entailing values are consumed. Complement, exclusions,
scalar negation, and endpoints become operands or higher-order operators.

Referential composition uses the same ontology as descriptions rather than a
separate `Mass` value family. `jo'u` is number-neutral `Combine`; referential
`joi` forms a `gunma` reference, `ce` forms a `selcmi` reference, and `ce'o`
forms an ordered sequence. Their fully expanded shapes are ordinary predicate
applications or the conventional list constructor:

```lisp
; X joi Y
(Refer
  (Counted (Exactly 1)
    (gunma
      :2 (Combine X Y))))

; X ce Y
(Refer
  (Counted (Exactly 1)
    (selcmi
      :2 (Combine X Y))))

; X ce'o Y
(Singleton (List X Y))
```

The group and the set are referents; neither is identified with the underlying
number-neutral reference value supplied as its members.

Argument-level `fa'u` supplies ordered respective values. `Tuple` is a value
constructor only where the receiving type admits an ordered tuple value;
otherwise the respective predication lowers directly to standard higher-order
zipping:

```lisp
(ZipWith
  (λ (($person (Referents Entity))
      ($destination (Referents Entity)))
    (klama $person $destination))
  (Tuple $alice $bob)
  (Tuple (Refer zarci) (Refer briju)))
```

Restricted/quantified streams are collection expressions supplied to
`ZipWith`; `Stream`, `Slot`, `Items`, and `DistinctPartition` field records are
not normal form.

### 10.3 Math and quantities

Literals print directly. Known operators use conventional glyphs:

```lisp
(= (+ 2 3) 5)
```

Grouping nodes disappear once the tree exists. Named/unknown operators are
atoms. Mixed-radix values, arrays, and intervals retain their real tree
structure, not a generic `(Math (Operator ...) (Operands ...))` wrapper.

### 10.4 Signs and quotation

Structured and opaque quotation are distinct level-crossing constructors:

```text
StructuredQuote : Referents<Utterance>|Discourse -> Sign<Structured>
OpaqueQuote     : Text -> Sign<Opaque>
```

The first overload quotes a graph-owned utterance token such as `$u`; the graph
resolves its structured transcript entry. The second quotes an inline discourse
computation. No undeclared bare `Utterance` type is involved.

When sign identity or multiple facts matter, retain a sign token boundary and
express its properties as predications:

```lisp
(Sign $s
  (TextOf $s "...")
  (Denotes $s $x)
  (Quotes $s $u))
```

Delimiter spelling is provenance unless it is itself quoted content. Letteral
structure is sign content. `Sign`, like `Utterance`, is a justified token/data
boundary; `Kind`, `Mode`, `Quotation`, and `Target` field records are not.

## 11. Identity, recursion, and ill-scoped graphs

`Let` and `LetRec` remain because they are familiar lexical binding forms and
make scope visible. A document-linear `$x@value` label is rejected: it is not a
standard convention, lets a definition's reach depend on print order, and
confuses graph identity with semantic binding.

The planner should instead:

1. inline a single-use acyclic identity when no semantic boundary is crossed;
2. enumerate the closed `RefHost` candidates which dominate the introduction
   and every graph-authorized use, respect each recorded `ScopePolicy`, and
   choose the widest legal candidate below any dependency binder or non-de-re
   intensional/opaque boundary;
3. place cyclic identity groups in `LetRec`;
4. lambda-lift a graph value only over semantic binders recorded in its
   `mayDependOn`/scope-dependence set, then apply that function at each use; a
   graph value recorded as `fixed` remains one identical value and is never
   weakened into a varying function merely to obtain a printable scope;
5. distinguish graph-identity bindings from quantifier/function variables by
   type and ownership.

The candidate hosts form an accessibility lattice, not a textual-parent rule.
An act is the normal host for one fixed reference used through extensional
negation, disjunction, or implication. The least common discourse host is
required when a graph-owned witness is used by multiple acts under `Do`; the
binding must dominate `Do`, not be duplicated inside its acts. A transcript-
owned identity may instead stop at its `TranscriptEntry`. An intensional input
is its own local `RefComp`/content/query host unless the graph explicitly gives
the reference a de-re owner. `mayDependOn` keeps the site under its binder or
lambda-lifts exactly the recorded dependencies.

Only a `RefComp` initializer elaborates to `BindRef` and sequences its effects
before the body at that selected host. A pure `Let` over `Content`, `Act`,
`PredTerm`, `Query`, `TranscriptEntry`, or `Discourse` is ordinary graph sharing:
it does not execute the shared value. Effects inside such a value run only when
the enclosing semantic operator interprets or performs it. Thus `Let` never
strips effects from `Refer`, `Context`, `Presuppose`, or `Supplement`, but
neither does it accidentally perform an act merely by naming it.

These rules address draft 2's large `definition-site-does-not-dominate-use`
fallback class without abandoning lexical scope.

If the graph is actually ill-scoped, the renderer must not silently repair it.
A shared `fixed` value for which no dominating legal `Let` site exists is such
an ill-scoped graph, not a candidate for lambda lifting.
A local `(IllScoped ...)`/`(Unbound $x Type)` marker plus a collected semantic error
is preferable when it preserves the relevant subgraph; otherwise the final
typed structural fallback remains available. Such output is a projection defect
or graph defect, not an intended normal form.

## 12. Diagnostics, provenance, and fallback

Semantic diagnostics never appear in the S-expression. The renderer returns
them separately from the datum, preserving owning object, severity, message,
source when available, multiplicity, and deterministic order. For this
experimental pass they may be collected without display, as requested. A later
change can route them through the standard CLI stderr renderer; this draft does
not require inventing diagnostic codes from message text.

Source spans, `introduced_by`, explicit-versus-elided defaults, relation
metadata, dictionary derivations, and grouping syntax are provenance. Word cards
remain an optional, parseable sibling section because `--show-defs` explicitly
asks for reference data; they are not semantic content.

Local `(Object Type ...)` and whole-document `TypedGraph` are transitional
fallback artifacts only. They preserve total output while the model/projection
is incomplete, but every occurrence is counted and reported by reason. There is
no golden-output or percentage expectation in this experimental phase. The
design target is to drive them toward zero through total semantic lowerings,
especially for descriptions, event facets, questions, signs, predication side
data, and graph sharing.

`Unresolved` remains semantic output only when the graph itself says the meaning
is unresolved. It is never an implementation fallback.

## 13. Constructor-family audit

| draft-2 family | classification | draft-4 normal form |
|---|---|---|
| root, application, labelled fill | primitive plus concise fill sugar | ordinary operands, `:n`/`:Eventuality`, and core `At` for computed/modal places |
| `DropPlace`, `Se`/conversion, scalar relation formers | primitive relation algebra | keep as applications |
| `Modal`/adjunct record | derived/fallback | `Joi` or ordinary modal-predicate application |
| `Restrict`, `Import` | derived/record noise | logical `→`/`∧` plus `Presuppose` |
| `Cardinality`, `Quantity` fields | derived | comparison over `Card`; named GQ only for irreducible cases |
| `Quantify` record | derived where source semantics is known | nested unary quantifiers, or equal-scope mutually exhaustive selected sets plus a Cartesian-product condition; typed fallback for an unsupported polyadic lift |
| `SelectionSource` | derived except when witness identity escapes | ordinary `WitnessOf` restriction or bound `Witnesses` computation |
| `Relative` taxonomy | derived | `Among`/conjunction, `DescribedAs`, `skicu`, or `Supplement` |
| `Lo`, `Le`, `La` | one irreducible reference operation plus derived properties | `Refer`; source `le` and `la` become partially filled `skicu` and `cmene` properties |
| `loi`/`lei`/`lai`, `lo'i`/`le'i`/`la'i` | derived gadri | bind the corresponding `Refer` base once, then `Refer` over `gunma`/`selcmi` predication; result remains number-neutral |
| `lu'a`/`lu'i`/`lu'o`/`vu'i` | derived level crossings | `lu'i`/`lu'o` through `selcmi`/`gunma`; `vu'i` through `selcmi`+`porsi`; `lu'a` as member description plus distributive host quantification |
| `lo'e`, `le'e` | irreducible/underspecified reference operators | `Typical`, `Stereotypical` |
| `Ka`, common `Nu` | derived | function or event-description lambda |
| `Du'u`, `Ni`, `Jei`, `Li'i`, `Pu'u`, `Zu'o`, `Si'o`, `Su'u` | irreducible level crossings | `Reify`, `Measure`, `TruthValue`, `ExperienceOf`, `ProcessOf`, `ActivityOf`, `Concept`, `Abstract` |
| `Facet` record | derived/fallback | total family of event predications |
| `OfKind`, `TanruLink` record | misleading/fallback | `(Tanru modifier head)` |
| logical connectives | primitive higher-order functions | exact glyphs |
| nonlogical composition records | primitive value constructors plus record noise | `Joi`, `Combine`, `Set`, `List`, `Tuple`, `∪`, `∩`, `×`, `Interval`; referential `joi`/`ce`/`ce'o` elaborate through `gunma`/`selcmi`/`List` |
| `RespectivelyValue`, `Respectively`, `Stream` | derived | `Tuple` and `ZipWith` |
| `Mode` | derived/error signal | typed position, effect, or act |
| `Act` wrapper | record noise | direct `Assert`, `Ask`, `Express`, etc. |
| `UtteranceForce::Quote/Parenthetical/Subordinated` | embedding status, not force | `StructuredQuote`, `Supplement`, or inert embedded content/discourse; typed fallback if the host is missing |
| `PredicationMode::Definitional` on identity/`du` | builder relation annotation | ordinary `=` under the enclosing source act; discard without mismatch diagnostic |
| `Sequence` record | derived or rare identity boundary | `Do`, `NewTopic`, `Resume`, logical/nonlogical operators |
| `Utterance` | real token/transcript boundary | retain; contents are `Realizes`, `SpeakerOf`, etc. predications |
| `Displayed`, family/target/focus/assertion fields | derived/fallback | actual bound target, relation transformers, `Express`, act selection |
| `Adjunct.modifiers` | displayed-content effects on a tag | bind the tag's actual target, transform the registered relation, then co-realize the resulting `Express` act at the nearest graph-declared utterance effect host |
| `Question` record | derived/fallback | `Ask` of `Query`; `QuestionOf` only for question-object identity; `Answer` for indirect question-to-proposition crossing |
| `Math` record | derived/fallback | literals, glyph application, structured special values |
| `Sign`/quotation fields | real sign boundary plus record noise | `OpaqueQuote`, `StructuredQuote`, or sign facts |
| warnings | diagnostic only | separate collected channel |
| word cards | optional reference-data boundary | parseable sibling section |
| `(Object ...)`, `TypedGraph` | transitional fallback artifacts | counted, never intended normal form |

### 13.1 Closed intrinsic signature registry

The first implementation uses a closed registry. A lowercase content word gets
its place row from the verified dictionary/relation metadata. Every PascalCase
intrinsic and every glyph must occur below (or in a total generated event-facet
table) before it can print. Adding an unregistered spelling is a projection
error, not an invitation to infer arity from the current object record.

Abbreviations used in the table:

```text
Property<T>       = Fn<T, Content>
GQ<T>             = Fn<Property<T>, Content>
CardGQ<T>         ⊂ GQ<T>
Query<Γ,Δ;E>      = Polar<Content<Γ,Δ;E>>
                    | OpenQ<Fn<A1,...,An,Content<Γ,Δ;E>>>
Interpretable     = Content | Act
Performable       = Act | Discourse | TranscriptEntry
Fact<K>           = saturated inert PredTerm about a token of kind K
Seq<T>            = Tuple<T...> | List<T> | another ordered collection<T>
Collection<T>     = Set<T> | List<T> | another registered collection<T>
Bound<T>          = Open<T> | Closed<T>
PredTerm          = ∃ρ. PredTerm<ρ>       surface existential row erasure
OpenPredTerm<T>   = ∃p,ρ. PredTerm<{p:T}+ρ>, with p next in effective order
Version           = natural-number schema version
Document          = one top-level notation datum
Math              = Number | registered typed structured mathematical value
NumberedPlace     = original numbered place
ArgumentPlace     = NumberedPlace | distinguished Eventuality place
PlaceDesignator   = ArgumentPlace | typed PredTerm-valued modal designator
SignKind          = Name | Sentence | Structured | Opaque
```

`Ordered(A)` and equality comparability are type constraints, not value
constructors. Kernel syntax—application lists, keyword fills, `λ`, `Let`, and
`LetRec`—is declared by the grammar and is exempt from the callable-intrinsic
registry. Packaging `PredTerm<ρ>` as surface `PredTerm` forgets only the row
index; it does not close, assert, or otherwise change the predicate term.
`OpenPredTerm<T>` is the row-erased family whose next effective place is known
to accept `T`; applying bare `PredTerm` is ill-typed because its hidden row may
be empty, and applying merely nonempty row-erased data would not establish that
the next operand has the required type. The `mo` question above therefore
binds `(OpenPredTerm (Referents Entity))`, which makes `($p This)` well typed.

The parameter of `Sign<K>` ranges over `SignKind`, not over the referential-kind
mapping below. A sign can separately singleton-lift to `Referents<Sign>` when
an ordinary sumti place requires the sign object.

Three uses of the spelling are separate and positionally disambiguated:
`Sign<K>` is the raw sign value family, `Sign` in `Referents<Sign>` and
`Fact<Sign>` is the referential/token kind, and `(Sign $s ...)` is the surface
binder sugar for a graph-owned sign token. A raw sign is not already a subtype
of `Referents<Sign>`; the one-way `Singleton` crossing is semantically real.

Referential kind parameters come from one closed generated mapping, initially
including `Entity`, `Eventuality`, `Achievement`, `Process`, `Activity`, `State`,
`Time`, `Place`, `Number`, `Proposition`, `Amount`, `Scale`, `Epistemology`,
`TruthValue`, `ExperientialContent`, `Concept`, `AbstractNature`, `Question`,
`Sign`, `Utterance`, `Name`, `Mind`, `DeicticGround`, `List<A>`, `Set<K>`, `Group<K>`, and
`WitnessSet<K>`. Raw mathematical `Number`, raw `Text`, signs, functions, acts,
contents, and discourse computations remain value families in their native
positions. A raw number singleton-lifts only when it fills a referential
`Number` place; a sign similarly crosses to `Referents<Sign>` only at a sumti
position. A model sort without a declared mapping is a projection error or
typed fallback.

Type constructors and referential-kind atoms occupy the **type namespace**;
callable intrinsics occupy the **term namespace**. Consequently spellings such
as `Amount`, `Concept`, `TruthValue`, `Set`, and `List` are unambiguous by
position even when both namespaces contain them. Registry validation checks
type-disjointness within each namespace; it does not reject a deliberate
type/term homonym.

| family / printed atoms | signature | provenance |
|---|---|---|
| `Smusni` | `Version x Performable -> Document` | document convention |
| `Close` | `PredTerm<ρ> -> Content` | typed closure crossing |
| `BindRef` / explicit `Let` | `RefComp<Γ,Δ,Referents<K>;E1> x Fn<Referents<K>,H<Δ,Θ;E2>> -> H<Γ,Θ;E1+E2>` for closed `H in RefHost` | dynamic bind; `BindRef` is elaboration-only |
| `AsProperty` | `PredTerm<{p:Referents<K>}+ρ> -> Property<Referents<K>>`, where `p` is the next effective open referential place | elaboration-only eta expansion |
| `FillNext` | `PredTerm<{p:T}+ρ> x T -> PredTerm<ρ>` using the first remaining effective place `p` | elaboration-only operation used in the `AsProperty` definition; never printed as an atom |
| `Reify` | `Content -> Referents<Proposition>` | `du'u` / proposition object |
| `Interpret` | `Sign<K> -> Interpretable` | explicit sign interpretation |
| `Assert`, `Express` | `Content -> Act<Assertion|Expressive>` | utterance force / displayed content |
| `Perform` | `Act -> Discourse` | explicit off-spine performance |
| `Polar` | `Content -> Query` | polar-query injection |
| `OpenQ` | `Fn<A1,...,An,Content> -> Query` | open-query injection; distinct from interval `Open` |
| `Ask` | `Query -> Act<Question>` | ask force |
| `Command` | `Referents<Entity> x Content -> Act<Directive>` | command force |
| `Mention` | `A -> Act<Mentioning>` | polymorphic mention of any typed notation value `A` |
| `Vocative` | `Referents<Entity> -> Act<Address>` | vocative force |
| `Presuppose` | `Content x Content -> Content` | trigger, then at-issue body |
| `Supplement` | `Content x Content -> Content` | at-issue body, then side content |
| `¬` | `Content -> Content` | exact logical negation |
| `∧`, `∨` | `Content^n -> Content`, `n >= 2` | associative variadic contraction of exact conjunction/disjunction |
| `→`, `↔`, `⊕` | `Content x Content -> Content` | exact binary truth-functional connective |
| `∀`, `∃` | `Fn<T,Content> -> Content` | classical quantification |
| `Card` | `Property<T> -> Number`; overloaded for raw `Set<T>|List<T> -> Number` | cardinality of a property extension or an explicit constructor/mekso collection; no direct `Referents<T>` overload |
| `=`, `≠` | `A x A -> PredTerm<empty>` for equality-comparable `A` | identity/math relation |
| `<`, `≤`, `>`, `≥` | `A x A -> PredTerm<empty>` where `Ordered(A)` | ordered comparison |
| `+`, `−`, `×`, `÷` | `Number x Number -> Number` | verified mathematical operator; `×` is type-overloaded below |
| `Among` | `(T x Referents<T>) | (Referents<T> x Referents<T>) -> PredTerm<empty>` | `me`/subreference relation; set inclusion is a valid discrete model, not the public definition. The sharpened “among” wording is a working-document clarification never separately voted, though the ratified gadri expansions rely on it |
| `Combine` | `Referents<T> x Referents<T> -> Referents<T>` | number-neutral commutative idempotent `jo'u` combination |
| `Singleton` | `T -> Referents<T>` | one-way singleton lift; implicit at lexical fills, explicit for a source-constructed raw object such as `ce'o`'s `List` |
| `∈` | `T x Collection<T> -> PredTerm<empty>` | actual mathematical/collection membership, not plural `Among` |
| `:n`, `:Eventuality` | keyword-fill syntax, not values | common original-place and event-place labels |
| `At` | core labelled-fill syntax `PlaceDesignator x T`, not a value | computed or PredTerm-valued modal place designator; numeric original identities remain accepted |
| `DropPlace` | `PredTerm<ρ> x NumberedPlace -> PredTerm<ρ-p>` | `zi'o`; the distinguished event place is not a numbered `zi'o` target |
| `Se`, `Te`, other verified conversions | `PredTerm<ρ> -> PredTerm<permute(ρ)>` | place conversion |
| `Tanru` | `PredTerm x PredTerm -> PredTerm` | vague tanru relation former |
| `Scalar` | `ScalarDirection x PredTerm<ρ> -> PredTerm<ρ>` | scalar relation transformation |
| `Degree` | `DegreeValue x PredTerm<ρ> -> PredTerm<ρ>` | degree relation transformation |
| `Phase` | `PhaseKind x PredTerm<ρ> -> PredTerm<ρ>` | phase relation transformation |
| `Joi` | `(Content x Content -> Content) | (Discourse x Discourse -> Discourse)` | ordered nonlogical `joi` at the source-recorded locus |
| `Refer` | `Property<Referents<T>> -> RefComp<Γ,Δ,Referents<T>;E>` | number-neutral contextual reference; source `lo`, `le`, and `la` differ through their property argument |
| `Exactly`, `AtLeast`, `AtMost`, `MoreThan`, `FewerThan` | `Number -> CardGQ<T>` | registered cardinal generalized-quantifier values |
| `Some`, `No`, `Every` | `GQ<T>` | registered existential, zero, and universal generalized-quantifier values; universal import remains external `Presuppose` |
| `Restrict` | `GQ<T> x Property<T> -> GQ<T>` | conservative restrictor transformation for registered quantifier families |
| `Counted` | `CardGQ<T> x Property<Referents<T>> -> Property<Referents<T>>` | inner cardinal quantification over the source-licensed singular member property; `Every` uses maximal-reference lowering |
| `Typical`, `Stereotypical` | `Property<Referents<T>> -> RefComp<Γ,Δ,Referents<T>;E>` | irreducible `lo'e`/`le'e` reference operations |
| `NameSign` | `Text -> Sign<Name>` | derived name-sign value from a name descriptor; not a token fact; source `la` supplies it to a `cmene` property |
| `Context` | `RefComp<Γ,Δ,Referents<K>;E>` or a dependency-explicit `Fn<...,RefComp<...,Referents<K>;...>>` | contextual `zo'e` value |
| `Speaker`, `Audience`, `This`, `Now`, `Here` | respectively `Referents<Entity>`, `Referents<Entity>`, `Referents<Entity>`, `Referents<Eventuality>`, `Referents<Place>` | deictic constants; `Now` follows the current eventuality-sort model mapping |
| `Proximal`, `Medial`, `Distal` | `Referents<T> x Referents<DeicticGround> -> PredTerm<empty>` | graph-recorded deictic proximity only |
| `DescribedAs` | `Referents<Entity> x Referents<T> x Property<Referents<T>> -> PredTerm<empty>` | current builder's three-place `voi` relation |
| `WitnessOf` | `Referents<T> x Referents<WitnessSet<T>> -> PredTerm<empty>` | selection-source restriction |
| `Witnesses` | `GQ<T> x Property<T> -> RefComp<Γ,Δ,Referents<T>;E>` | effect-preserving export of the graph-owned witness reference from that full quantifier application |
| `Portion`, `Ordinal`, `Amount`, `Extent`, `Frequency` | `ScaleValue x Property<T> -> GQ<T>` | non-cardinal quantity scale; exact scale kind is typed |
| `Measure` | `Content x Referents<Scale>? -> Referents<Amount>` | `ni`, preserving optional scale x2 |
| `TruthValue` | `Content x Referents<Epistemology>? -> Referents<TruthValue>` | `jei` |
| `ExperienceOf` | `Content x Referents<Entity>? -> Referents<ExperientialContent>` | non-event-property `li'i` residue; avoids collision with an event sort |
| `ProcessOf` | `Content x Referents<Eventuality>? -> Referents<Process>` | `pu'u`, preserving optional stages x2 |
| `ActivityOf` | `Content x Referents<Eventuality>? -> Referents<Activity>` | `zu'o`, preserving optional repeated-actions x2 |
| `Concept` | `Content x Referents<Mind>? -> Referents<Concept>` | `si'o` / builder `conceptOf` |
| `Abstract` | `Content x Referents<T>? -> Referents<AbstractNature>` | `su'u` / builder `abstractionOf`, preserving optional x2 |
| `SentenceSign` | `Content -> Sign<Sentence>` | builder sentence-sign `abstractionOf` kind |
| `QuestionOf` | `Query -> Referents<Question>` | inert object-language question value |
| `Answer` | `Query -> Content` | source-backed question-to-true-answer proposition crossing for indirect questions |
| `Do` | `Performable* -> Discourse` | discourse sequencing |
| `PerformUtterance` | `TranscriptEntry -> Discourse` | explicit transcript performance off the spine |
| `NewTopic` | `Discourse -> Discourse` | `ParagraphTransition::NewTopic` only |
| `Resume` | `Discourse -> Discourse` | `ParagraphTransition::ResumePriorTopic` only |
| `Label` | `LabelLevel x Math x A -> A` | recorded `OrdinalLabel`, wrapping its graph target |
| `PriorDiscourse`, `FollowingDiscourse` | `Discourse` | graph-recorded elided discourse operand |
| `Set` | `T* -> Set<T>` | variadic extensional set constructor; raw sets also arise from typed mekso/set values |
| `List` | `T* -> List<T>` | variadic ordered list constructor |
| `Tuple` | `A1 x ... x An -> Tuple<A1,...,An>` | heterogeneous/ordered product value |
| `∪`, `∩` | `Set<T> x Set<T> -> Set<T>` | union/intersection |
| `×` | also `Set<A> x Set<B> -> Set<Tuple<A,B>>` | type-directed Cartesian product overload |
| `Open`, `Closed` | `T -> Bound<T>` | interval endpoint openness |
| `Interval` | `Bound<T> x Bound<T> -> Interval<T>` | typed endpoints and openness |
| `ZipWith` | `Fn<A1,...,An,Content> x Seq<A1> x ... x Seq<An> -> Content` | respective predication |
| `StructuredQuote` | `Referents<Utterance>|Discourse -> Sign<Structured>` | structured quotation of a graph-owned utterance token or inline discourse |
| `OpaqueQuote` | `Text -> Sign<Opaque>` | opaque quotation |
| `Transcript` | `Referents<Utterance> x Fact<Utterance>* -> TranscriptEntry` | utterance token boundary |
| `SignEntry` | `Sign<K> x Fact<Sign>* -> Sign<K>` | sign token boundary |
| `Utterance`, `Sign` | binder sugars for `Let` plus `Transcript`/`SignEntry` | graph-owned token identity |
| `Realizes` | `Referents<Utterance> x Act -> Fact<Utterance>` | analyzer fact; additional acts may be synthesized from displayed anchors |
| `SpeakerOf`, `AudienceOf` | `Referents<Utterance> x Referents<Entity> -> Fact<Utterance>` | transcript metadata |
| `LocutionOf`, `DeicticTimeOf`, `DeicticPlaceOf` | `Referents<Utterance> x A -> Fact<Utterance>` | polymorphic metadata operand `A` whose concrete sort is checked against the graph relation |
| `Utters` | `Referents<Entity> x Referents<Utterance> -> PredTerm<empty>` | only an actual graph/document relation, never inferred from `Realizes` |
| `TextOf`, `Denotes`, `Quotes` | `Sign<K> x A -> Fact<Sign>` with the relation-selected concrete sort of `A` | sign-token facts |
| `Contrast`, `MetalinguisticNegation`, registered indicator relations | relation-table signature over experiencer, typed target, and required anchor -> `PredTerm<empty>` | displayed-content relation registry |
| `IllScoped`, `Unbound` | typed defect markers preserving the failed value/type | projection defect plus collected error |
| `Object`, `TypedGraph` | typed structural fallback, not semantic intrinsics | temporary totality mechanism |
| `Unresolved` | model-declared unresolved semantic value | semantic graph only |

Pascal event-facet predicates use a separate total generated table from each
model facet to one typed signature over the shared event. A second closed
generated literal table enumerates every non-callable Pascal atom for
`ScalarDirection`, `DegreeValue`, `PhaseKind`, `LabelLevel`, `ScaleValue`,
`Force`, scope policy, sign kind, and event subsort. The closed sign kinds are
`Name`, `Sentence`, `Structured`, and `Opaque`; the closed force values are `Assertion`, `Expressive`, `Question`,
`Directive`, `Mentioning`, and `Address`; the closed scope policies are
`Extensional`, `Intensional`, and `Opaque`. `Strong`,
`Opposite`, and event subsort names are therefore typed literal atoms, not an
open exception to registry closure. The abstraction names `Concept`,
`ExperienceOf`, `Abstract`, and `SentenceSign` above are the notation spellings
of the current builder relations rather than a second vocabulary.

## 14. Validation during experimentation

No byte-for-byte output expectations are added yet. Required checks are
structural and semantic:

- every output is one parseable `(Smusni 0 ...)` document;
- repeated rendering is byte-identical;
- every variable is lexically bound, explicitly marked ill-scoped, or appears
  only in typed fallback;
- every shared identity is inlined once or bound consistently by `Let`/`LetRec`;
- every effectful reference bind is printed at the same `RefHost` selected by
  the accessibility planner; its ordered introduction, presupposition, and
  supplement effects are closed and routed exactly once before its body;
- every input position of every registered intrinsic receives exactly one
  `ScopePolicy` after the closed precedence rules in section 2 are applied;
  every dynamic-capable lexical place independently has a non-optional entry
  in the exhaustive generated relation-place policy artifact and an optional
  typed de-re owner; unknown relation/place metadata is rejected rather than
  guessed from spelling;
- every model field has a declared lowering, provenance exclusion, diagnostic
  disposition, or explicit temporary fallback;
- no semantic diagnostic node occurs on stdout, and collection preserves every
  diagnostic exactly once;
- constructor names are type-disjoint within their namespace (`Speaker` versus
  `SpeakerOf`, etc.); declared type/term homonyms remain positionally distinct;
- every printed binder annotation unifies with the closed registry signature,
  including reference-valued `ce'u`/`ma`/`ZipWith` parameters and force-indexed
  acts;
- every callable PascalCase name and glyph is registered, and every
  non-callable Pascal atom occurs in the generated literal table;
- kernel syntax and every type abbreviation used by a binder or signature are
  declared, including existential `PredTerm` row erasure, `Version`, `Document`,
  `Math`, `Collection`, and the `Ordered` constraint;
- every escaped witness retains its originating generalized quantifier plus
  nuclear scope, while the independent truth condition still counts or
  quantifies the original restriction/scope rather than the witness value;
- direct-question descriptions can bind at the declared `Ask` host, while
  embedded-question descriptions remain below the `Answer`, `QuestionOf`, or
  lexical intensional boundary unless their graph-owned de-re host says otherwise;
- polar and open direct/indirect questions all retain the same `Query`, with
  `QuestionOf` and `Answer` used only at their declared level crossings;
- a `RefComp` nested in a `Refer` property remains inside that outer reference
  computation unless the graph supplies an explicit de-re owner; validation
  includes a nested-description case as well as ordinary description scope;
- equal-scope termsets retain a coordinate participant selection for
  each term, a Cartesian-product nuclear condition, and coordinate-wise
  exhaustivity. A countermodel with four qualifying dogs and two qualifying
  men makes `(Exactly 3)` false while `(AtLeast 3)` remains true. The renderer
  rejects an already ordered model nest as lossless termset input;
- every builder-supplied extra abstraction place for `ni`, `pu'u`, `zu'o`,
  `li'i`, `si'o`, and `su'u` is preserved or explicitly recorded as omitted;
- corpus reports show local/whole fallback counts and reasons, without imposing
  an experimental threshold, and include the draft-2 measured fallback rows
  (CLL object fallback 73%, Alice-lines 92%, full-Alice whole fallback 100%) as
  a comparison baseline rather than a pass/fail gate;
- representative CLL and corpus examples cover relative clauses, abstractions,
  event facets, all connective loci (`∧`, `∨`, `→`, `↔`, and `⊕`), termsets, respectively, questions,
  indicators, quotations, sharing, recursion, and multi-utterance discourse.
- restricted-universal lowering mechanically validates the ratified equivalence
  `naku ro da poi F cu G` = `su'o da poi F ku'o naku G`: both retain the same
  projecting nonempty-`F` commitment while their at-issue content normalizes to
  `∃x.(F(x) ∧ ¬G(x))`.

Once the renderer exists, its generated output replaces the hand-written
samples as the review corpus. The present file remains design input only and is
never copied into golden expectations.

## 15. Deliberate conclusions

- “Predicate terms and lambdas all the way down” is accurate at the typed
  application-graph layer. It does not make logical operators or acts ordinary
  first-order predicates.
- Predicate saturation, content closure, assertion-act construction, and act
  performance are four distinct stages.
- Unary modals are `.i joi` connections in normal form; their internal argument
  places remain ordinary fills.
- Conventional `∀` stays conventional. Lojban's importing commitment is an
  explicit `Presuppose` effect.
- Cardinal and universal quantifiers are first-class higher-order values;
  `Counted` handles the cardinal inner family, maximal-reference lowering
  handles inner `Every`, and `Witnesses` preserves an escaped dynamic witness
  without replacing the original truth condition. Equal-scope positive
  termsets reduce to mutually exhaustive selected sets plus their
  Cartesian-product condition rather than inheriting the work-in-progress
  tersmu nesting.
- `Refer` is the one number-neutral reference operation. Source `le` and `la`
  differ compositionally through `skicu` and `cmene` properties, not extra
  gadri-shaped intrinsics; `ι` and `ε` are avoided because their established
  singular/uniqueness associations would misdescribe xorlo.
- `poi`, `voi`, and `noi` need no relative-clause record taxonomy. Their
  at-issue/background and veridical/description differences remain in ordinary
  predicates plus `Supplement`.
- Properties are higher-order functions; event abstractions are event-binding
  properties; only real semantic level crossings retain abstractor intrinsics.
- Facts about utterances and signs are predications, while their token/record
  boundaries remain because recorded facts are not speaker assertions.
- Acts and their content/predicate targets are first-class bound values. Focus
  is identity and type, not an extensible enum.
- Presupposition, supplementary content, and expressive acts remain distinct.
- Fallback serialization is useful for totality during development but is not
  part of the target notation.
