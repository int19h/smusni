# Human-readable smusni S-expression format

This document specifies version 0 of the human-readable `smusni` output format.
It is a typed, semantics-oriented projection of the tersmu graph. It is not a
transliteration of Lojban grammar and it is not a prettified XML tree.

The format has four goals:

1. preserve every semantic distinction represented by the input graph;
2. reduce grammar-shaped and record-shaped structures to a small compositional
   kernel;
3. remain readable to people familiar with conventional S-expressions,
   mathematical notation, and ordinary functional notation;
4. remain total while the semantic projection is incomplete, by using an
   explicit typed structural fallback rather than guessing.

The keywords **MUST**, **MUST NOT**, **SHOULD**, and **MAY** are normative.
Examples are illustrative unless they are explicitly labelled as expansions.
The companion [samples](samples.md) exercise the rules in this document.

## 1. Semantic commitments

### 1.1 Predicate terms

The central relational value is a **predicate term**:

```text
PredTerm<ρ>
```

`ρ` is the ordered row of places that are still open. A lexical root is a
predicate term with its whole row open. Filling one place produces another
predicate term with a smaller row. A term with no numbered places left is still
a predicate term; saturation does not assert it and does not by itself close an
event variable or any other graph-owned default.

This deliberately treats the following as values of one family rather than as
different syntactic categories:

- a bare content predicate such as `klama`;
- `klama` with some arguments filled;
- `klama` with every numbered argument filled;
- a predicate term used under a modal, description, abstraction, or
  higher-order operator.

The word *predicate term* is used instead of *selbri*, *bridi*, *predication*,
or *proposition*. The first two are tied to Lojban surface grammar. The latter
two commonly suggest a completed or closed proposition, which is not required
here.

### 1.2 Functions

The other central value is a typed function:

```text
Fn<(A1 ... An), B>
```

Functions have ordered positional parameters. They are introduced by `λ` and
applied with ordinary S-expression application. Properties, generalized
quantifiers, open questions, relation-valued questions, event descriptions,
and eta-expanded place conversions are functions.

Predicate terms and functions are distinct because their application rules are
distinct. A predicate term has a named effective place row, supports labelled
fills and contextual closure, and retains lexical place provenance. A function
has only its declared ordered parameters and never acquires implicit predicate
places.

### 1.3 Closure, force, and performance

Four operations that Lojban surface syntax often leaves close together remain
distinct:

```text
fill a predicate place : PredTerm<ρ+p> × value -> PredTerm<ρ>
close predicate content: PredTerm<ρ> -> Content
construct an act       : Content -> Act
perform an act         : Act -> Discourse
```

`Content` is an evaluable, dynamically scoped proposition-like value. `Assert`
constructs an assertion act from content. It is never an implicit consequence
of filling a place. `Perform` is used only when the graph distinguishes an act
value from its performance; a top-level act in a `Smusni` document is performed
by the document convention.

Logical operators, quantifiers, presupposition, reference, and force are typed
higher-order intrinsics. Calling them “predicates” would not remove their
control or effect semantics. A dictionary predicate such as `zilvlina` cannot
replace logical disjunction unless the graph explicitly represents that
ordinary lexical predication.

### 1.4 Utterances and signs

Facts about an utterance or sign are ordinary predicate terms wherever
possible. Token creation, token identity, and actual performance are not
ordinary assertions and therefore remain explicit token boundaries.

Asserting that a person utters an act is not the same operation as performing
that act. The notation can represent both, but it MUST NOT conflate use with
mention.

## 2. Concrete syntax

### 2.1 Character and atom rules

Output is UTF-8 normalized to NFC. Whitespace separates tokens and is otherwise
insignificant. Consumers MAY accept semicolon line comments; the renderer MUST
NOT emit comments.

Strings use JSON escaping and double quotes. Integers are canonical decimal
without a leading plus sign or redundant leading zeroes. Exact non-integers use
`(/ numerator denominator)` with a positive denominator in lowest terms.

The namespaces are visually disjoint:

- lowercase symbols are lexical content roots: `klama`, `sepi'o`;
- PascalCase symbols are registered intrinsics, types, or closed literals:
  `Assert`, `Entity`, `Projective`;
- conventional mathematical glyphs are registered intrinsics: `λ`, `∀`, `∧`;
- `$name` is a lexically bound variable;
- `:2` and `:Eventuality` are literal place labels;
- `%1`, `%2`, ... are fallback-object identities and occur only inside
  structural fallback.

A bare symbol consists of Unicode letters or a leading namespace marker,
followed by letters, digits, apostrophe, hyphen, underscore, or period. A
lexical spelling that is not safe as a bare symbol uses conventional Lisp
vertical-bar escaping: `|...|`, with `\|` and `\\` escapes.

PascalCase spellings are closed by this version of the specification. Unknown
semantic constructors do not become new PascalCase atoms; they use typed
fallback.

### 2.2 Datum grammar

The grammar below describes canonical output. `datum` is recursively typed;
the grammar alone does not make an ill-typed application valid.

```text
document       ::= (Smusni 0 performable [words])
words          ::= (Words word-card*)

datum          ::= atom | string | integer | variable | list
list           ::= (datum*)
application    ::= (datum argument*)
argument       ::= datum | place-fill

place-fill     ::= :positive-integer datum
                 | :Eventuality datum
                 | (At datum datum)

lambda         ::= (λ ((variable type)+) datum)
quantifier     ::= (∀ ((variable type)+) datum)
                 | (∃ ((variable type)+) datum)
let            ::= (Let ((variable type datum)) datum)
bind           ::= (Bind ((variable type datum)) datum)
let-rec        ::= (LetRec ((variable type datum)+) datum)

utterance      ::= (Utterance ((variable UtteranceToken)) utterance-item+)
sign           ::= (Sign ((variable (SignToken sign-kind))) sign-item+)

type           ::= type-atom
                 | (Referents type)
                 | (Set type) | (List type)
                 | (Tuple (type*))
                 | (Fn (type*) type)
                 | (PredTerm row)
                 | (RefComp type)
                 | (Act force)
                 | (Query (type*))
                 | (QuantifiedContent type) | (GQ type)
                 | (Sign sign-kind) | (SignToken sign-kind)
                 | (PlaceOf relation-id type)
row            ::= (Row row-slot*)
row-slot       ::= (positive-integer type) | (Eventuality type)
performable    ::= datum     ; statically Act, Discourse, or TranscriptEntry
```

`λ` always prints a complete ordered typed parameter list. Placeholder lambdas,
implicit `$1` parameters, middle-dot holes, and bracket lambda sugar are not
version-0 syntax.

`Let` and `Bind` each have exactly one binding in canonical output. Multiple
nonrecursive bindings are nested. This removes any ambiguity between parallel
and sequential binding.

`LetRec` is the only multi-binding form. Its initializers are mutually visible,
but recursion is permitted only for inert functions and predicate-term values.
An initializer MUST NOT perform a `RefComp`, act, discourse, presupposition, or
supplement. Recursive content graphs that cannot be represented as guarded
functions use typed fallback.

### 2.3 Application

Ordinary application is type-directed:

- if the head is an `Fn`, the arguments fill its ordered parameters;
- if the head is a `PredTerm`, its arguments fill predicate places according to
  section 4;
- if the head is a registered intrinsic, its registered signature applies.

Application is not implicitly left-associated. `($f a b)` is one application
of `$f` to two arguments. Curried application prints as `(($f a) b)` when its
types require two applications.

An empty list is not a value. Empty typed collections print `(Set Entity)` and
`(List Entity)`, where the first operand is the element type. Nonempty
collections omit the type only when it is uniquely recoverable:

```lisp
(Set Entity)
(Set $x $y)
(List (Referents Entity))
(List $first $second)
```

### 2.4 Document packaging

Version 0 has exactly one top-level datum:

```lisp
(Smusni 0 performable)
```

If `--show-defs` is requested, an optional `Words` section is the third child:

```lisp
(Smusni 0
  performable
  (Words
    (Word klama "x1 goes to x2 from x3 ...")))
```

`Words` is reference data, not semantic content. Warnings and errors MUST NOT
appear in the datum; section 16 defines their separate channel.

A consumer that does not support version `0` MUST reject the document rather
than interpreting it as another version.

## 3. Types and level crossings

### 3.1 Core value families

```text
PredTerm<ρ>                  predicate term with effective open row ρ
Fn<(A1 ... An), B>          ordered function
Content                     closed dynamic proposition-like value
RefComp<T>                  dynamic computation introducing a value T
Act<F>                      first-class act with force F
Discourse                   performed act/discourse computation
TranscriptEntry             utterance token plus facts and realized acts
Query<(A1 ... An)>          polar when the tuple is empty, open otherwise
QuantifiedContent<T>        Content with a graph-owned quantifier execution id
Referents<T>                nonempty, number-neutral plural reference
Set<T>                      extensional mathematical set
List<T>                     ordered mathematical list
Tuple<(A1 ... An)>          heterogeneous ordered product
Sign<K>                     sign value of kind K
UtteranceToken              graph-owned utterance identity
SignToken<K>                graph-owned sign identity
PlaceOf<R,T>                one of R's current places accepting T
```

`QuantifiedContent<T>` is a subtype of `Content`. Event sorts `Achievement`,
`Process`, `Activity`, and `State` are subtypes of `Eventuality`; the only
implicit event coercion is the one-way upcast to `Eventuality`.

Ordinary Lojban sumti places use `Referents<T>`, not raw `T`. A raw `T` MAY
singleton-lift at such a fill. The reverse conversion is never implicit.

### 3.2 Properties and generalized quantifiers

```text
Property<T> = Fn<(T), Content>
GQ<T>       = Fn<(Property<T>), QuantifiedContent<T>>
```

A property is a function, not a special record. A generalized quantifier is a
higher-order value which accepts its nuclear-scope property. Restrictor,
importing behavior, and counting basis are retained in the constructed `GQ`.

### 3.3 Explicit crossings

The following crossings are semantic operations, not harmless type coercions:

| From | To | Operation |
|---|---|---|
| `PredTerm<ρ>` | `Content` | `Close` |
| `Content` | `Act<Assertion>` | `Assert` |
| `Content` | `Proposition` | `Reify` |
| `Query<A>` | `Question` | `QuestionOf` |
| `Act` | `Discourse` | `Perform` |
| `TranscriptEntry` | `Discourse` | `PerformUtterance` |
| `T` | `Referents<T>` | `Singleton`, optionally elided at sumti fills |
| `Sign<K>` | `Content` | `InterpretContent` |
| `Sign<K>` | `Act` | `InterpretAct` |

`InterpretContent` and `InterpretAct` are separate because a static result type
cannot be recovered from an undifferentiated `Interpret : Sign -> Content|Act`.

### 3.4 Binding

`Let` names an inert value and preserves graph identity without evaluating an
effect. Its initializer is evaluated in the surrounding lexical environment.

`Bind` runs a `RefComp<T>`, binds its result, and evaluates its body in the
updated dynamic context. It is the only printed dynamic-value binder:

```lisp
(Bind (($x (Referents Entity) (Refer property)))
  body)
```

The body determines the host family: `Content`, `Act`, `Discourse`, or another
registered dynamic host. A `Bind` never silently becomes pure `Let`, and a
`Let` never runs a reference computation.

### 3.5 Contextual and deictic values

`Context` is a type-directed `RefComp<Referents<T>>`. It performs an ordinary
contextual resolution at its dynamic evaluation point. It is used only where a
contextual value is semantically present; silent predicate-place defaults are
inserted by `Close` instead of printing `Context` repeatedly.

The closed deictic constants are:

```text
Speaker  : Referents<Entity>
Audience : Referents<Entity>
This     : Referents<Entity>
Now      : Referents<Eventuality>
Here     : Referents<Place>
```

Additional graph-specific deictics use a registered typed predicate over an
explicit `DeicticGround`; they are not minted as ad hoc constants.

## 4. Predicate rows and place filling

### 4.1 Effective rows

Every predicate term carries an **effective row**. Its public numbered labels
belong to the relation expression visible at that point. They are not claimed
to be universal semantic roles.

Internally, a surviving lexical slot also carries provenance
`(normalized lexical root, original dictionary ordinal)`. That provenance is
used only for dictionary metadata, arity validation, and lexical scope-policy
lookup. It is a root-relative coordinate, not a human-visible semantic name.

### 4.2 Fill cursor

For a lexical predicate application, the numbered cursor starts at the first
current numbered place.

1. A plain operand fills the cursor place and advances to the next surviving
   current place.
2. `:n value` fills current place `n` and moves the cursor to the first
   surviving place after `n`. Earlier skipped places remain open.
3. `:Eventuality value` fills the distinguished event place and does not move
   the numbered cursor.
4. `(At place value)` fills a computed current place and makes the numbered
   cursor statically unknown. No later plain operand is permitted in that
   application; later literal or computed labelled fills are permitted.

Thus:

```lisp
(pilno :2 $car $event)
```

fills current x2 with `$car`, then fills current x3 with `$event`; x1 remains
open for `Close`.

Duplicate fills, a nonexistent place, an incompatible value, a second event
fill, or a fill of a deleted place is a projection error. A computed place is
typed `PlaceOf<R,T>` and carries a finite candidate set. Its candidate set MUST
exclude places already filled or deleted and places that reject `T`; otherwise
the application uses local typed fallback.

### 4.3 `At`

`At` exists only for a genuinely computed place, principally a graph-preserved
`fi'a` question or variable:

```lisp
(OpenQ
  (λ (($p (PlaceOf klama (Referents Entity))))
    (klama (At $p This))))
```

Literal numeric positions use `:n`, not `(At 2 value)`. Predicate-term-valued
modal designators do not exist. Modals normalize through `Joi` as specified in
section 10.

### 4.4 `zi'o`

`DropPlace` represents semantic deletion of a numbered place:

```text
DropPlace : PredTerm<ρ> × current numbered place -> PredTerm<ρ-p>
```

Surviving current labels do not renumber after deletion; the deleted label is a
visible hole and plain traversal skips it. `DropPlace` cannot delete the
distinguished event place.

### 4.5 Place conversion

Source `se`, `te`, `ve`, and `xe` are consumed during semantic elaboration.
Ordinary output prints the base lexical predicate with values mapped to the
appropriate base-root places. No `Se`, `Te`, `Ve`, or `Xe` intrinsic exists.

If a converted relation itself escapes as a first-class value, it is
eta-expanded as an ordered function. For a binary relation:

```lisp
(λ (($x A) ($y B))
  (root :2 $x :1 $y))
```

The receiving place must expect the corresponding `Fn` type. A graph that
requires an escaped converted `PredTerm` with labelled-place behavior, rather
than an ordered function, cannot be represented by pretending the lambda is a
predicate term and therefore uses typed fallback.

### 4.6 Relation formers

`Tanru`, `Scalar`, `Degree`, `Phase`, and `DropPlace` are registered relation
formers. Each declares its result row and a total mapping from every surviving
surface slot to lexical provenance. A former with unknown row behavior cannot
print in normal form.

`Tanru modifier head` preserves the head's effective row and records only the
semantically represented vague modification. It MUST NOT invent a specific
dictionary predicate.

## 5. Closing predicate content

### 5.1 Semantics of `Close`

`Close` converts a closeable predicate term to `Content`. It performs all and
only the following graph-licensed closure steps:

1. every remaining defaultable ordinary referential place receives a fresh
   `Context` reference computation;
2. graph-shared defaults remain shared through an explicit `Let` or `Bind`;
3. an open distinguished event place receives a local existential event when
   the root/event former licenses one;
4. existing event facets and references determine the event variable's scope;
5. no higher-order, function, content, sign, or act place receives an invented
   default.

Each silent ordinary default is distinct unless explicit graph identity says
otherwise. A default may depend on every lexically accessible binder at its
closure site. With no accessible binder it is a fixed contextual computation.

If any remaining place is not registered as defaultable, or event ownership is
ambiguous, `Close` is not defined for that row and the affected value uses typed
fallback. Saturation alone never licenses closure.

### 5.2 When `Close` may be omitted

Canonical output omits `Close` exactly when all of these conditions hold:

- the expression is syntactically inline and not referenced elsewhere;
- its effective row is statically known;
- the surrounding registered operand position requires `Content`;
- closure uses only the standard defaults above;
- no default or event identity must be named outside the expression.

Consequently this is canonical:

```lisp
(Assert (klama Speaker))
```

and elaborates as if the inline predicate term were wrapped in `Close`.

A bound, shared, row-erased, nonstandard, or independently targeted predicate
term prints `Close`:

```lisp
(Let (($p (PredTerm (Row)) (klama Speaker)))
  (Assert (Close $p)))
```

Expected-type insertion is available at every registered `Content` operand,
including logical operators, `Reify`, `Polar`, and abstraction operators. It is
never available merely because the expression appears at top level.

## 6. Dynamic content and accessibility

### 6.1 Context model

The notation does not print a generic `State` or `DiscourseMonad` wrapper.
Nevertheless, `Content`, `RefComp`, acts, and discourse operators have an
explicit dynamic interpretation:

```text
Content<Γ,Δ;E>
RefComp<Γ,Δ;T;E>
```

`Γ` is the input discourse context, `Δ` the successful output context, and `E`
the ordered side effects. This typing is usually inferred and omitted from
surface binder annotations.

The dynamic interpretation is what gives anaphora the correct accessibility
across connectives. `Assert` does not create this behavior; it performs content
whose accessibility behavior is already defined.

### 6.2 Accessibility table

The following rules are normative. “Exports” means available to a later
successful continuation.

| Form | Evaluation and accessibility |
|---|---|
| `(∧ a b ...)` | left to right; each successful operand sees and exports the preceding context |
| `(Joi a b ...)` | left to right at the recorded nonlogical locus; same context flow as conjunction, but retains nonlogical connection identity |
| `(∨ a b ...)` | branches share the same input; branch-local introductions do not escape unless the graph supplies one merged identity valid in every successful branch |
| `(¬ a)` | `a` sees the input; ordinary introductions inside it do not escape |
| `(→ a b)` | `b` sees successful introductions from `a`; neither antecedent-local nor consequent-local introductions escape the conditional by default |
| `(↔ a b)` | expands to the two directed conditionals with branch-local contexts; no new identity escapes by default |
| `(⊕ a b)` | alternatives share input; branch-local identities do not escape |
| `(∀ ... body)` | bound variables and body introductions are local |
| `(∃ ... body)` | the bound variable may export only when the semantic graph declares the existential discourse referent exportable |
| generalized quantifier | variable is local; only its registered witness handle can escape |
| `(Presuppose trigger body)` | resolve or accommodate `trigger`, then evaluate `body`; trigger referents are visible in `body` and to the successful outer continuation |
| `(Supplement body side)` | evaluate `body`, then `side` against the body's context; only graph-declared shared identities export from `side` |
| `(Bind ... body)` | run the computation, bind its result, then evaluate the body; export follows the body's host rule |
| `(Reify content)` | closes a proposition object; ordinary introductions do not escape the reified content |
| `Answer`, `QuestionOf` | query-local variables do not escape the crossing |
| lexical `Intensional` place | traps ordinary reference raising at that argument boundary |
| lexical `Opaque` place | traps all reference raising and de-re export |
| `Assert`, `Ask`, `Command`, `Express` | construct acts; context export occurs when the act is performed |
| `(Do a b ...)` | performs left to right; each successful item sees the context exported by earlier items |

No connective is permitted to inherit an unspecified “usual” accessibility
rule.

### 6.3 Dynamic reference placement

Every dynamic reference edge has:

- its lexical evaluation site;
- the free-variable dependencies of its property;
- a lexical place policy, when it is an argument of a lexical root;
- an optional graph-owned de-re host.

The closed lexical policies are:

- `Extensional`: the reference may be hosted outside the lexical argument;
- `Intensional`: it remains inside that lexical argument unless an explicit
  legal de-re host is present;
- `Opaque`: it remains inside and rejects an escaping de-re host.

Surface current coordinates map through row provenance to the lookup key
`(root, original ordinal, dynamic family)`. Missing, contradictory, or
unattested policy metadata fails closed; spelling, argument type, nearby rows,
and converted surface position are never heuristics.

If the graph supplies a de-re host, that exact host is used after legality and
dependency checks. Otherwise the computation is placed at the lowest enclosing
legal host that dominates its evaluation site and all dependencies. Ties are
broken by lexical containment, then source order. If no unique host exists, the
smallest affected dynamic subgraph uses typed fallback.

### 6.4 Side-effect handlers

`Presuppose`, `Supplement`, expressive acts, and utterance facts are separate
effect families. A construct handles only its declared family. The nearest
enclosing legal handler wins; equal-depth candidates are ordered by source
order. Effects generated inside a supplement do not become at-issue content.
Effects generated inside opaque or reified content cannot be hosted outside
that boundary.

When no explicit utterance token survives, the top-level document convention
provides the act-performance handler, but it does not invent utterance identity
or metadata.

## 7. Acts, discourse, utterances, and signs

### 7.1 Acts are first-class values

The force constructors are:

```text
Assert  : Content -> Act<Assertion>
Ask     : Query<A> -> Act<Question>
Command : Referents<Entity> × Content -> Act<Directive>
Express : Content -> Act<Expressive>
Mention : A -> Act<Mentioning>
Vocative: Referents<Entity> -> Act<Address>
```

The content or target of any act may be bound by `Let` and referred to by
ordinary predicates. No `TargetFocus` enum is used; the target's identity and
static type say whether it is a clause, predicate term, act, sign, event, or
other value.

`Do` sequences performables:

```text
Do : Performable+ -> Discourse
```

It evaluates left to right and preserves graph/source order. `Perform act`
performs an act that was constructed off the main discourse spine.
`PerformUtterance entry` performs the acts realized by a transcript entry.

`NewTopic discourse` and `Resume discourse` remain only when the semantic graph
records the corresponding paragraph transition. Mere source paragraph layout
is provenance and does not print.

### 7.2 Utterance-token boundary

`Utterance` is a fresh-token binder and transcript constructor, not `Let` sugar:

```lisp
(Utterance (($u UtteranceToken))
  (SpeakerOf $u Speaker)
  (Realizes $u (Assert content)))
```

Every item is a saturated fact about the same `$u`, or a registered realized
act. Items are evaluated in order. Multiple `Realizes` facts mean co-realized
acts in that order; they are not silently conjoined into one assertion.

Registered utterance facts include `SpeakerOf`, `AudienceOf`, `LocutionOf`,
`DeicticTimeOf`, `DeicticPlaceOf`, `Realizes`, and ordinary lexical relations
such as `Utters` when the graph actually contains them. A fact is analyzer
content about the token, not automatically a speaker assertion.

The boundary MUST remain when the token is referenced, quoted, supplied with
metadata, realizes multiple acts, or is itself returned as data. A simple
single act with no surviving token fact contracts to the act itself.

### 7.3 Sign-token boundary

`Sign` similarly binds a fresh sign token:

```lisp
(Sign (($s (SignToken Sentence)))
  (TextOf $s "mi klama")
  (Denotes $s (Reify (klama Speaker))))
```

The closed sign kinds are:

```text
Name Sentence Quotation Word Letteral MathExpression Connective Text
Structured Opaque
```

Raw sign constructors include `NameSign`, `SentenceSign`, `StructuredQuote`,
and `OpaqueQuote`. A sign token and a raw `Sign<K>` are distinct. Either can
singleton-lift only where a sumti place expects a referential sign object.

`InterpretContent` and `InterpretAct` are used only when interpretation itself
is represented. Quotation, denotation, and token facts do not imply
interpretation.

## 8. References, plurality, sets, and descriptions

### 8.1 Number-neutral references

`Referents<T>` is an abstract nonempty plural-reference domain. It is not
defined as `Set<T>`, a mereological sum, a group individual, or a mass. This
keeps ordinary predicate places neutral about singular versus plural reference
while allowing explicit mathematics when the graph requires it.

The minimum public algebra is:

```text
Singleton : T -> Referents<T>
Among     : T|Referents<T> × Referents<T> -> Content
Combine   : Referents<T> × Referents<T> -> Referents<T>
```

`Among` is a reflexive, transitive subreference preorder after singleton
lifting. `Combine` is associative, commutative, and idempotent. Each operand is
`Among` its combination, and a common upper bound contains the combination.
There is no empty `Referents<T>` identity.

The format deliberately assumes no atoms, covers, distributivity of lexical
predicates, cumulative closure, collective/distributive default, or identity
between `Combine` and set union. Any such commitment is an explicit predicate
or operator.

### 8.2 Sets and counting

`Set<T>` is the ordinary free extensional set structure over `T`:

```text
SetOf : Property<T> -> Set<T>
∈     : T × Set<T> -> Content
∪, ∩  : Set<T> × Set<T> -> Set<T>
×     : Set<A> × Set<B> -> Set<Tuple<(A B)>>
Card  : Set<T>|List<T> -> Number
```

Exact counting is over an explicit singular basis supplied by source/model
metadata. It is never applied directly to `Referents<T>`. Infinite cardinality
is a `Cardinal` value; arithmetic comparisons with a finite natural retain
their standard mathematical meaning. A semantic model that supplies only an
approximate, vague, mass, or otherwise non-cardinal quantity uses its registered
quantity operator or typed fallback, not `Card` by analogy.

Mass readings and plural logic can be built with explicit sets, subreference,
group, part, collective, and distributive predicates. The format does not make
`Mass` a primitive merely because a source gadri historically received a mass
gloss.

### 8.3 `Refer`

```text
Refer : Property<Referents<T>> -> RefComp<Referents<T>>
```

`Refer P` contextually obtains a number-neutral reference and emits `P` of that
same reference as its descriptive side condition. The caller MUST NOT repeat
that side condition manually. Its continuation expansion is:

```lisp
(Bind (($r (Referents T) (Refer $P)))
  $body)
```

where the computation selects `$r`, contributes `($P $r)` through its declared
reference effect, and then evaluates `$body` once. `Refer` is neither iota nor
epsilon: those symbols conventionally suggest uniqueness or singular choice
that xorlo descriptions do not generally carry.

The main gadri lower compositionally:

| Source family | Property supplied to `Refer` |
|---|---|
| `lo P` | the veridical property `P` |
| `le P` | the graph's speaker-description property, normally using `skicu`, with `P` as descriptive content rather than asserted classification |
| `la N` | a naming property using a `NameSign` and `cmene`/the graph's naming relation |
| `lo'e P` | `Typical P`, an irreducible contextual reference operation |
| `le'e P` | `Stereotypical P`, an irreducible speaker-description operation |

There is no `Lo`, `Le`, `Relative`, or gadri-record constructor in normal form.

### 8.4 Relative clauses and associations

Relative-clause taxonomy is eliminated into ordinary composition:

- restrictive `poi` contributes a veridical predicate to the reference
  property's selection condition;
- descriptive `voi` contributes the represented `DescribedAs` predication;
- supplementary `noi` contributes `(Supplement body side)` at its graph-owned
  anchor;
- multiple clauses combine with their actual logical or nonlogical connector;
- `goi` identity/assignment becomes `Let`, `Bind`, or the represented naming or
  association predicate, depending on its graph semantics.

Restrictive and nonrestrictive status is therefore visible in composition and
effect placement, not in an enum. Veridicality remains in the predicate that is
actually contributed.

Set and group descriptions are also ordinary reference properties, such as
membership in `SetOf P` or a registered `GroupOf` relation. They do not create
special gadri constructors.

## 9. Logic and quantification

### 9.1 Logical operators

The canonical logical intrinsics are:

```text
¬ : Content -> Content
∧, ∨ : Content^n -> Content, n >= 2
→, ↔, ⊕ : Content × Content -> Content
∀, ∃ : ((variable type)+) × Content -> Content   ; binder forms
```

Associative conjunction and disjunction flatten without reordering. A
one-operand occurrence contracts to that operand; zero operands do not print.
The dynamic rules in section 6 are part of these operators' meaning.

All logical operators can be understood extensionally as higher-order
relations over content, but they remain intrinsics because their truth and
accessibility behavior is exact. Dictionary words print only when the graph
represents those dictionary predicates.

### 9.2 Generalized quantifiers

The common quantifier constructors are:

```text
Some      : Property<T> -> GQ<T>
No        : Property<T> -> GQ<T>
Every     : Property<T> -> GQ<T>
Exactly   : Natural × Property<T> -> GQ<T>
AtLeast   : Natural × Property<T> -> GQ<T>
AtMost    : Natural × Property<T> -> GQ<T>
MoreThan  : Natural × Property<T> -> GQ<T>
FewerThan : Natural × Property<T> -> GQ<T>
```

Natural arguments are nonnegative exact integers. Applying a `GQ<T>` to a
nuclear-scope property produces `QuantifiedContent<T>`.

`Some`, `No`, and the cardinal quantifiers have their standard set-theoretic
truth conditions over the registered singular counting basis. Source `ro`
uses `Every`, whose meaning includes a projective nonempty-restrictor
presupposition. The primitive `∀` is the nonimporting mathematical universal.
There is no separate `(Import Projective)` node and no unstated import default.

For example, `((Every P) Q)` elaborates in effect to:

```lisp
(Presuppose
  (∃ (($x T)) ($P $x))
  (∀ (($x T)) (→ ($P $x) ($Q $x))))
```

with all required singleton lifts and dynamic placement retained. This also
preserves importing behavior under negation.

`Restrict` survives only as the higher-order conservative operation:

```text
Restrict : GQ<T> × Property<T> -> GQ<T>
```

Record-shaped “restriction metadata” never prints.

### 9.3 Inner and outer cardinality

An inner count constrains one fixed number-neutral reference through its
source-licensed singular-member property. An outer count quantifies singular
satisfiers. These are not interchangeable.

The canonical mathematical reduction uses `SetOf`, `Card`, membership, and
ordinary predicates. A count is never inferred from the apparent number of
referents in a `Combine` value.

`lo no P` follows the exact-zero generalized-quantifier path when the source
semantics supplies one; it does not attempt to construct an empty
`Referents<T>`, which is impossible by definition.

### 9.4 Witness export

A shared generalized-quantifier application may be bound as
`QuantifiedContent<T>`. Its successful execution owns a witness handle:

```text
Witnesses : QuantifiedContent<T> -> RefComp<Referents<T>>
```

`Witnesses $q` is legal only in a dynamic continuation in which the same `$q`
identity has already succeeded. It does not execute `$q`, duplicate its truth
condition, or reconstruct a witness from a bare `GQ`. The type/effect checker
tracks this success token through `Assert`, conjunction, and `Do`.

```lisp
(Let (($q (QuantifiedContent Entity)
        ((Exactly 3 (λ (($x Entity)) (gerku $x)))
         (λ (($x Entity)) (bajra $x)))))
  (Do
    (Assert $q)
    (Bind (($dogs (Referents Entity) (Witnesses $q)))
      (Assert (tatpi $dogs)))))
```

Retrieval before successful execution, through a branch in which execution is
not guaranteed, or outside an intensional/opaque boundary is ill-scoped and
uses typed fallback.

### 9.5 Simultaneous termsets

A genuinely simultaneous termset uses `PolyQuant`:

```text
PolyQuant : Tuple<(GQ<A1> ... GQ<An>)>
            × Fn<(A1 ... An), Content>
            -> QuantifiedContent<Tuple<(A1 ... An)>>
```

```lisp
(PolyQuant
  (Tuple $dogs $people)
  (λ (($dog Entity) ($person Entity))
    (nelci $dog $person)))
```

Ordinary nesting imposes an asymmetric scope order. For homogeneous classical
quantifiers that happen to commute this may not change truth conditions, but
generalized quantifiers such as `Exactly`, `Most`, and mixed quantifiers do not
commute in general. A source/model claim of equal polyadic scope therefore MUST
NOT be rendered as arbitrary nesting.

`PolyQuant` is licensed only when the graph preserves the participant
quantifiers, coordinate restrictions, one polyadic nuclear scope, and the
required exhaustivity/selection profile. Otherwise the termset uses typed
fallback. No renderer heuristic reconstructs simultaneous scope from an
already ordered nest.

## 10. Modals, nonlogical connections, and events

### 10.1 Modal normalization

Every unary tag is semantically expanded through its `fi'o` predicate and an
ordered `Joi` connection at the source-recorded locus. Its payload is an
ordinary predicate term whose own places are filled normally.

```lisp
(∃ (($e Eventuality))
  (Joi
    (klama Speaker :Eventuality $e)
    (pilno :2 $car :3 $e)))
```

`sepi'o` and direct `fi'o pilno` may map their source operands to different
places; the verified modal expansion supplies that map. They still use the same
`pilno` root and contain no `Modal` or modal-valued `At` node.

Compound tags preserve their actual logical or nonlogical connector and
negation. Elided tag operands receive the same explicit/default treatment as
other predicate places. Arbitrary `fi'o` accepts any graph-valid predicate term,
including one assembled with `be`, functions, or reified content.

### 10.2 `Joi`

`Joi` is an ordered nonlogical connector over `Content` or `Discourse`. It
retains a source/model distinction that cannot be replaced by truth-functional
`∧`, while using the accessibility rule in section 6.

When the source nonlogical connective denotes a different registered
operation—interval, union, sequence, mixture, respective pairing, or another
typed collection operator—the corresponding typed operator prints instead.
Unknown nonlogical families use fallback.

### 10.3 Event places and facets

The distinguished `:Eventuality` place is separate from numbered lexical
places. It prints whenever an event identity is shared, constrained, targeted,
or otherwise cannot be hidden by `Close`.

Event properties are ordinary predicate terms of the event:

```lisp
(∃ (($e Eventuality))
  (∧
    (klama Speaker :Eventuality $e)
    (purci $e)))
```

No generic event-property record prints. Each represented facet must lower to
a registered lexical predicate or typed intrinsic with a declared event
signature. An unknown facet uses local fallback rather than being dropped.

## 11. Abstractions and higher-order values

### 11.1 Properties and relations

Source `ka` and relation abstractions are lambdas whenever they merely abstract
ordered `ce'u` places:

```lisp
(λ (($x (Referents Entity)))
  (melbi $x))
```

Multiple `ce'u` occurrences follow their graph-owned parameter identities and
order. Free variables remain free only within the surrounding lexical scope;
the final document has no unbound variables.

A first-class place permutation is likewise a lambda, as described in section
4.5. No `Property` or `Relation` record is needed around the function.

### 11.2 Event abstractions

An event abstraction binds the event explicitly when it is shared or returned:

```lisp
(λ (($e Eventuality))
  (klama Speaker :Eventuality $e))
```

`EventOf : Content -> Referents<Eventuality>` is used only for the semantic
crossing from closed content to an event object. More specific graph event
sorts use `AchievementOf`, `ProcessOf`, `ActivityOf`, or `StateOf` when the
crossing itself carries those aspectual commitments.

### 11.3 Other abstraction crossings

The fixed-arity crossings are:

```text
Reify              : Content -> Proposition
Measure            : Content -> Referents<Amount>
MeasureOn          : Content × Referents<Scale> -> Referents<Amount>
TruthValue         : Content -> Referents<TruthValue>
TruthValueBy       : Content × Referents<Epistemology> -> Referents<TruthValue>
ExperienceOf       : Content -> Referents<ExperientialContent>
ExperienceFor      : Content × Referents<Entity> -> Referents<ExperientialContent>
ProcessOf          : Content -> Referents<Process>
ProcessThrough     : Content × Referents<Eventuality> -> Referents<Process>
ActivityOf         : Content -> Referents<Activity>
ActivityThrough    : Content × Referents<Eventuality> -> Referents<Activity>
Concept            : Content -> Referents<Concept>
ConceptFor         : Content × Referents<Mind> -> Referents<Concept>
Abstract           : Content -> Referents<AbstractNature>
AbstractAs         : Content × Referents<T> -> Referents<AbstractNature>
SentenceSign       : Content -> Sign<Sentence>
```

There are no optional `?` operands. A graph-present extra place selects the
explicit longer-arity spelling. A genuinely contextual argument prints
`Context` at that place. Missing source information that is not semantically a
contextual default uses fallback rather than silently choosing the shorter
form.

## 12. Questions and answers

### 12.1 Query values

```text
Polar : Content -> Query<()>
OpenQ : Fn<(A1 ... An), Content> -> Query<(A1 ... An)>
```

A question's variable domain is explicit in the lambda type. Supported domains
include ordinary arguments, relation functions, current places, connectives,
tense/modal values, mathematical operators, attitudes, quantities, and typed
heterogeneous tuples. For example, a relation question binds the ordered
function type required at that site; it does not bind a row-erased predicate
term and hope application is valid.

A place question binds `PlaceOf<R,T>` with a finite compatible candidate row.
A mixed multiple question uses a multi-parameter lambda and an answer tuple in
the same order.

`Ask` turns a query into a direct question act. `QuestionOf` turns it into an
inert question object. They do not assert or answer it.

### 12.2 Answers

`Answer` always states the answer selection profile:

```text
Answer : Query<A> × AnswerSelection<A> -> Content
```

The closed selection forms are:

```text
(PolarAnswer Yes|No|Unknown)
(TupleAnswer (Tuple value...) Exhaustive|MentionSome)
(ContextualAnswer Exhaustive|MentionSome)
UnresolvedAnswer
```

`ContextualAnswer` is the contextually true answer operator used when the
semantics commits to answerhood but does not encode the selected value. It does
not pretend the graph recorded a polarity or tuple. `UnresolvedAnswer` is
permitted only when unresolved answerhood is itself a semantic value; a
projection failure uses fallback instead.

Query-local variables never escape through `Answer`. A de-re reference inside
an embedded question escapes only through a legal graph-owned host.

## 13. Math, quantities, sequences, and quotation

### 13.1 Mathematical values

Common exact operators use conventional symbols:

```text
= ≠ < ≤ > ≥ + − × ÷ ∈ ∪ ∩
```

`Set`, `List`, `Tuple`, `Interval`, `Open`, and `Closed` construct typed
mathematical values. `ZipWith` represents respective application to ordered
collections:

```text
ZipWith : Fn<(A1 ... An), Content>
          × List<A1> ... × List<An> -> Content
```

Arrays, powers, nondecimal bases, subscripts, operator denotation, and
questioned operators print only through a registered typed math constructor.
An unknown operator is not emitted as an unregistered atom; the smallest
unknown math value uses fallback.

### 13.2 Quantities

Exact cardinal quantities reduce to set/cardinality mathematics. Registered
non-cardinal scales use typed operators such as `Amount`, `Extent`, `Frequency`,
`Portion`, and `Ordinal` with their explicit `Scale` value and property.

Approximate, indefinite, comparative, and vague quantities retain their actual
typed operator when the graph supplies one. They MUST NOT be rounded into an
exact `Number` or cardinal comparison.

### 13.3 Quotation and signs

```text
OpaqueQuote     : Text -> Sign<Opaque>
StructuredQuote : UtteranceToken|Discourse -> Sign<Structured>
NameSign        : Text -> Sign<Name>
SentenceSign    : Content -> Sign<Sentence>
```

Word, letteral, connective, math-expression, and text signs retain their typed
sign kind and structured operands when represented. Opaque quotation preserves
exact quoted text and does not claim an internal interpretation.

## 14. Registered normal forms

### 14.1 Callable intrinsic registry

The following groups are closed for normal version-0 output. Polymorphic type
variables are inferred from operands.

| Group | Intrinsics |
|---|---|
| kernel crossings | `Close`, `Reify`, `QuestionOf`, `InterpretContent`, `InterpretAct`, `Singleton` |
| force/performance | `Assert`, `Ask`, `Command`, `Express`, `Mention`, `Vocative`, `Perform`, `PerformUtterance`, `Do` |
| dynamic effects | `Presuppose`, `Supplement`, `Refer`, `Context`, `Typical`, `Stereotypical`, `Witnesses` |
| logic | `¬`, `∧`, `∨`, `→`, `↔`, `⊕`, `∀`, `∃`, `Joi` |
| quantification | `Some`, `No`, `Every`, `Exactly`, `AtLeast`, `AtMost`, `MoreThan`, `FewerThan`, `Restrict`, `PolyQuant` |
| reference/plural | `Among`, `Combine`, `SetOf`, `GroupOf`, `DescribedAs` |
| relation formers | `DropPlace`, `Tanru`, `Scalar`, `Degree`, `Phase` |
| abstractions | `EventOf`, `AchievementOf`, `ProcessOf`, `ProcessThrough`, `ActivityOf`, `ActivityThrough`, `StateOf`, `Measure`, `MeasureOn`, `TruthValue`, `TruthValueBy`, `ExperienceOf`, `ExperienceFor`, `Concept`, `ConceptFor`, `Abstract`, `AbstractAs`, `SentenceSign` |
| questions | `Polar`, `OpenQ`, `Answer`, `PolarAnswer`, `TupleAnswer`, `ContextualAnswer` |
| collections/math | `Set`, `List`, `Tuple`, `Card`, `Interval`, `Open`, `Closed`, `ZipWith`, `=`, `≠`, `<`, `≤`, `>`, `≥`, `+`, `−`, `×`, `÷`, `∈`, `∪`, `∩` |
| signs | `OpaqueQuote`, `StructuredQuote`, `NameSign` |
| discourse | `NewTopic`, `Resume`, `Label`, `PriorDiscourse`, `FollowingDiscourse` |
| token facts | `Realizes`, `SpeakerOf`, `AudienceOf`, `LocutionOf`, `DeicticTimeOf`, `DeicticPlaceOf`, `TextOf`, `Denotes`, `Quotes`, `Utters` |
| quantity | `Amount`, `Extent`, `Frequency`, `Portion`, `Ordinal` |
| fallback | `Fallback`, `TypedGraph`, `Object`, `Field`, `Ref`, `RawList`, `RawAtom`, `RawString`, `RawNull` |
| packaging | `Smusni`, `Words`, `Word` |

`Let`, `Bind`, `LetRec`, `λ`, `∀`, `∃`, `Utterance`, `Sign`, `At`, place keywords, and
collection element-type operands are grammar forms, not callable intrinsics.

Closed literal families include force, sign kind, answer exhaustivity, answer
polarity, scalar direction, degree, phase, label level, scale, and lexical scope
policy. A literal is valid only in a signature position that names its family;
the same spelling MAY occur in two disjoint families.

The closed deictic term constants are `Speaker`, `Audience`, `This`, `Now`, and
`Here`. `PriorDiscourse` and `FollowingDiscourse` are graph-owned discourse
constants. Scale literals such as `DistanceScale` occur only in a scale-typed
position. Registered indicator relations such as `Contrast` and generated event
facets such as `LongDuration` belong to their versioned generated tables.

### 14.2 Lexical and generated registries

Lowercase roots obtain their row, place types, event licensing, defaultability,
and normalized identity from the versioned semantic dictionary. Dynamic lexical
places additionally require a generated policy row with this schema:

```text
normalized-root, original-ordinal, dynamic-family, scope-policy, evidence-id
```

Event facets, model indicator relations, quantity scales, and other generated
families have the same closure requirement: the implementation ships a
versioned source table, validates it without network access, and fails closed on
missing or contradictory rows. Generated tables extend only the family named by
their schema; they cannot mint arbitrary PascalCase constructors.

### 14.3 Required desugarings and forbidden record shapes

| Input-model family | Normal form |
|---|---|
| predication/selbri records | `PredTerm` application and fills |
| assertion flag | explicit `Assert` or another force constructor |
| modal/tag record | modal predicate plus `Joi` |
| place conversion | base-root remapping or eta-expanded `λ` |
| relative-clause record | reference property, predicate, connector, or `Supplement` |
| description/gadri record | `Refer`/typed reference operation and a property |
| quantifier record | higher-order `GQ`, primitive binder, or `PolyQuant` |
| event-property record | predicates of one event variable |
| abstraction record | `λ` or an explicit level crossing |
| utterance metadata record | token binder plus facts |
| sign/quotation record | typed sign value or token facts |
| sequence record | `Do` and actual discourse operators |
| warning nodes | separate diagnostic channel |

The following do not occur in normal output:

```text
Modal Relative Lo Le Se Te Ve Xe Import ProjectiveRecord TargetFocus
WithWarnings Warning Warnings SelectionSource OpenPredTerm Interpretable
```

`Projective` may occur only as a typed literal in a registered family that
actually requires it; source `Every` import does not print a separate node.

### 14.4 Projection-completeness dispositions

Every semantic-model constructor and field has exactly one disposition:

1. normal compositional lowering;
2. provenance-only suppression with a declared reason;
3. separately collected diagnostic;
4. local typed fallback;
5. whole-document typed fallback.

The implementation maintains an exhaustive generated disposition ledger. New
model fields fail the build until classified. In particular, the ledger must
cover masses, quantities, relation/connective/tense/math values, argument
bundles, experience and locution events, every formula/connective family,
reciprocals, place/connective/tense questions, composition exclusions,
collective marking, scalar negation, intervals, arrays, math operator
denotation, approximate quantities, names and `goi`, every sign kind, paragraph
transitions, all event facets, and every displayed-content assertion effect.

Classification as fallback is acceptable for version 0; silent omission or an
open wildcard is not.

## 15. Canonical rendering

Canonical output is deterministic from the typed projection graph.

1. Bindings are planned before printing. Shared acyclic values are bound at
   their least common legal scope; unshared values inline when the normal-form
   rule permits it.
2. Strongly connected components print as one `LetRec`. SCCs and members use
   stable graph order with source span as the first key and stable object id as
   the second. Semantic operands are never sorted merely because an operator is
   mathematically commutative.
3. Variables are alpha-renamed by first binder occurrence. Preferred stems are
   `$x` for entities/references, `$e` for events, `$p` for predicate/function
   values or places, `$q` for queries/quantified content, `$u` for utterances,
   `$s` for signs, and `$v` otherwise; decimal suffixes avoid collision.
4. Plain predicate operands print until a skip is necessary. Literal labelled
   fills then follow the cursor rules. Computed fills print `At`. Event fills
   print after numbered fills unless source/effect order requires an earlier
   named event.
5. Associative operators flatten in graph order. They never reorder dynamic
   operands. Redundant one-item wrappers contract only where specified.
6. Strings use JSON escaping, symbols and text are NFC, exact numbers use the
   rules in section 2, and fallback fields preserve declared model-field order.
7. The pretty-printer uses two-space indentation. A list stays on one line when
   its canonical flat form is at most 88 Unicode scalar values and contains no
   child already forced multiline; otherwise the head stays after `(` and each
   argument begins on its own indented line. The closing parenthesis aligns
   with the opening list.
8. Output ends with one newline and contains no trailing whitespace.

Whitespace-insensitive parsers may accept other layouts, but the renderer MUST
produce this one so repeated rendering is byte-identical.

## 16. Diagnostics and typed fallback

### 16.1 Separate diagnostics

The renderer returns three products internally:

```text
stdout document, ordered diagnostics, projection statistics
```

The CLI writes only the `Smusni` datum to stdout. Diagnostics use the same
standard stderr rendering as `gentufa`. Each failed projection edge contributes
exactly one stable diagnostic code and one message; wrapper failures do not
duplicate child diagnostics. Statistics are API data unless separately
requested.

### 16.2 Local fallback

When an expected static type is known, the smallest failed subgraph prints:

```lisp
(Fallback Content "smusni.unsupported.example"
  (Object %1 "ModelType"
    (Field "fieldName" (RawAtom "value"))
    (Field "child" (Ref %2))))
```

`Fallback expected-type reason-id raw-value` inhabits only the stated expected
type and is semantically opaque. The reason id is a stable ASCII string. It is
not a warning node and does not replace the separately collected diagnostic.

The raw grammar is closed:

```text
(Object %id "type-name" (Field "field-name" raw)*)
(Ref %id)
(RawList raw*)
(RawAtom "atom-and-type")
(RawString "text")
(RawNull)
```

Every graph object identity is assigned one `%id`; sharing and cycles use
`Ref`. Fields occur in declared model order. Type names and atoms are strings so
unknown model constructors cannot escape into the normal PascalCase namespace.

### 16.3 Whole-document fallback

If no well-typed local expected position exists, the body is:

```lisp
(TypedGraph "Performable" raw-root)
```

`TypedGraph` is valid only directly under `Smusni`. An unbound variable,
ill-scoped witness, invalid de-re owner, unknown row, or impossible effect host
uses the same fallback mechanism with a precise reason id; there are no
underspecified `Unbound` or `IllScoped` semantic values.

Fallback is part of version-0 totality but not a target semantic normal form.

## 17. Validation requirements

Version-0 conformance requires structural and semantic validation, not golden
output expectations:

- every result is one parseable, well-typed `(Smusni 0 ...)` datum;
- repeated rendering is byte-identical;
- every variable and fallback reference is bound exactly once and used within
  its legal scope;
- every shared identity is represented once by `Let`, `Bind`, `LetRec`, or a
  token binder;
- every predicate fill resolves against the current row and every lexical
  policy lookup resolves through original-slot provenance;
- every implicit `Close` is reconstructible from syntax, expected type, and
  registered row defaults;
- every `RefComp` is performed once at one legal host and every side effect is
  handled once;
- the accessibility table is exercised for every connective, quantifier,
  reification boundary, and discourse operation;
- every generalized-quantifier witness is retrieved only after the same
  quantified content succeeds;
- importing universal behavior is preserved under negation;
- equal-scope termsets are never silently converted to ordered nesting;
- all query domains and answer selections typecheck;
- utterance/sign facts refer to their bound token and performance remains
  distinct from reported facts;
- every model field is classified by the exhaustive disposition ledger;
- stdout contains no diagnostic node, and diagnostics are collected once in
  stable order;
- local and whole fallback counts and reason ids are reported on representative
  CLL and corpus suites without imposing an experimental threshold.

The corpus suite must include complex relative clauses, multiple connected
relatives, `goi`, all connective loci, compound and negated tags, arbitrary
`fi'o`, abstractions with extra places, shared event facets, de-re/de-dicto and
opaque references, direct and embedded questions, multi-variable questions,
termsets, respectively, recursion, quotations and every sign kind, indicators,
multiple utterances, math/quantity structures, and both local and whole fallback.

## 18. Summary of the model

The normal form is “predicate terms and lambdas all the way down” at the
application-graph layer, with a small number of irreducible semantic controls:

- predicate-place filling;
- lambda/function application;
- contextual closure;
- dynamic binding and effect handling;
- exact logical and quantificational control;
- act construction and performance;
- graph-owned token identity;
- explicit semantic level crossings.

Everything else should be decomposed into those operations and ordinary
predications when the decomposition preserves the semantic graph. A named
record constructor is warranted only when eliminating it would lose a real
type, scope, effect, identity, order, or interpretation distinction.
