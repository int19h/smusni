# Experimental smusni S-expression design, draft 1

Status: reconciled working specification for a second design review. This is a
semantic projection from `SemanticGraph`, not a textual recoding of either the
current flat `smusni` renderer or XML. The object model and XML are evidence and
completeness oracles; neither fixes the ontology or the printed tree shape.

## 1. The central object: an open predicate term

The general, non-Lojban-specific term is **predicate term**. In type sketches it
is abbreviated `Pred`:

```text
Pred<NumberedRow, Seal>
Seal = Open | Sealed
```

A root such as `klama`, a root with some places filled, and a root with every
numbered place filled are all predicate terms. They differ only in their
remaining numbered row. No separate semantic type is justified merely because
Lojban syntax calls one source phrase a *selbri* and another a *bridi*.

```text
Fill : Pred<{p:T} + ρ, Open> × p × T → Pred<ρ, Open>
```

`Pred<∅, Open>` is **saturated**, but it is not closed: event and modal
attachments may still be added. Filling, even the final numbered fill, never
forms a proposition and never asserts anything. This is the reason for the
`Seal` parameter and the separate closing operation.

“Predicate term” is preferred over the alternatives:

- *predication* commonly suggests an occurrence in which application has
  already begun, and in some traditions suggests saturation;
- *proposition* is reserved for closed content;
- *relation* is a reasonable implementation synonym, but often suggests an
  extensional set of tuples rather than an intensional expression;
- *frame* and *predicate frame* import FrameNet or valency-frame expectations
  that are narrower than this family.

The printed form normally contains none of these words. A root is `klama`; its
applications are `(klama Speaker)` and `(klama Speaker (Lo zarci))`.

### Functions

Functions are the other fundamental value family:

```text
Fn<A₁, …, Aₙ, B>
```

They have only ordered numbered parameters. `λ` constructs them. Predicate
terms and functions share one typed application syntax, but remain distinct
types: beta reduction applies only to `Fn`, while applying a `Pred` fills one
place and leaves the other places and modal capacity open.

## 2. Closure, dynamic content, and force

Closing an open predicate term fills its remaining contextual arguments,
seals further attachments, and yields inert content. Assertion is a later,
explicit operation.

The right semantic target for closed content is not merely a truth value. It is
a context-change potential in the tradition of DRT and Dynamic Predicate Logic.
Use a parameterised discourse computation:

```text
𝒟<Γ, Δ, A>
Pure  : A → 𝒟<Γ, Γ, A>
Then  : 𝒟<Γ, Δ, A> × (A → 𝒟<Δ, Ε, B>) → 𝒟<Γ, Ε, B>

Content<Γ, Δ> = 𝒟<Γ, Δ, Unit>
CloseΓ : Pred<ρ, Open> → Content<Γ, Δ>
Assert : Content<Γ, Δ> → Act<Assertion, Γ, Δ>
```

The two context indices record the discourse referents accessible before and
after a computation. This is a parameterised/indexed monad, not an ordinary
unindexed state monad. A plain monad can thread a context, but cannot express in
its type that a negated or disjunct-local referent is unavailable afterward.

The dynamic operators define their accessibility behavior:

- conjunction composes left to right, so output referents from the first
  operand may be available in the second;
- disjunction evaluates branches from the same input and exports only the
  referents licensed by the graph's branch merge;
- negation is a scoped test: referents introduced inside it do not normally
  escape;
- an implication makes antecedent referents available inside its consequent,
  but does not normally export antecedent- or consequent-local referents after
  the implication;
- quantifiers and abstractions delimit or export referents according to their
  typed operator and the graph's binder ownership.

These are semantic laws and planner invariants. The ordinary output does not
wrap every expression in `𝒟`, `Pure`, or `Bind`. S-expression nesting, `λ`,
quantifier binders, `Let`/`LetRec`, and explicit discourse operators show the
accessibility structure. `(Do ...)` is reserved for genuine discourse
sequencing that cannot be mistaken for truth-functional conjunction.

The graph already materializes contextual referents, scope dependence, and
event binders. The renderer's `CloseΓ` is therefore an *inverse elaboration*:
it suppresses graph nodes that exactly match this notation's contextual
defaults. It never creates a second set of referents or moves a binder.

## 3. Small semantic calculus

The representation needs the following semantic operations:

```text
Root(name, signature)
Apply(operator, operand)
At(predicate, place-designator, value)
DropPlace(predicate, original-place)
λ(parameters, body)
CloseΓ(context, predicate)
DynamicOperator(typed operands)
Act(force, content)
Record(utterance-token, act, transcript-facts, expressed-side-content)
```

Conversion, scalar negation, description, abstraction, composition, tense,
math, and quotation are typed intrinsic roots built with the same application
operation. They do not require a second generic tree mechanism.

All generic rewriting is signature-directed. It may cross only operands marked
extensional. Intensional operands and opaque signs are never beta-reduced or
re-associated merely for compactness.

## 4. Concrete S-expression conventions

- The output is exactly one `(Smusni 0 ...)` form. The CLI/MCP format name
  remains `smusni`; this deliberately replaces the old format under the same
  public name.
- A list is application. `(f a b)` means `((f a) b)`.
- Applying a predicate with a plain operand fills the lowest remaining
  effective numbered place. Applying a function fills its next parameter.
- A lowercase Lojban content word is a predicate root: `klama`, `cukta`,
  `nelci`.
- PascalCase identifies an intrinsic, force, sort, role, enum value, or typed
  contextual constant: `Assert`, `Lo`, `Entity`, `Speaker`.
- Conventional symbols are used when they have a stable conventional reading:
  `λ`, `∀`, `∃`, `∧`, `∨`, `¬`, `→`, `↔`, `⊕`, `=`, `≠`, `<`, `≤`, `>`,
  `≥`, `+`, `−`, `×`, `÷`.
- Bound/shared variables begin with `$`: `$x`, `$event`, `$book`. They cannot
  collide with content roots or intrinsics.
- `(At p v)` fills a non-next place. A numeric `p` is always the root
  predicate's original place identity, even after `DropPlace`.
- `(DropPlace r p)` is `zi'o`: it removes original place `p`. Plain operands
  thereafter traverse the effective row, but numeric `At` labels retain
  original identities.
- `(λ (($x Entity) ($y Entity)) body)` is the only multi-binder shape. Binder
  sorts are always printed in draft 1.
- `(Let (($x Sort value) ...) body)` names shared acyclic values;
  `(LetRec ...)` handles self-reference and cycles. A single-use acyclic value
  is normally inlined.
- Strings use JSON escaping. Numbers are value forms only when the graph has
  computed that value; general mekso remains structured.
- A lowercase predicate root is never coerced to an entity. Write `(Lo zarci)`,
  not bare `zarci`, in an entity place.

### Numbered, event, and modal fills

```lisp
klama
(klama Speaker)
(klama Speaker (Lo zarci))
(klama Speaker (At 5 (Lo karce)))
(klama Speaker (At Eventuality $e))
((DropPlace dunda 2) Speaker This)
```

The last form fills original x1 and original x3: deleting x2 changes the
effective row without erasing original place identity.

A modal place designator is itself a predicate term or a unary function that
constructs one. The tag argument is applied to that designator. Fully desugared
`sepi'o lo karce` can therefore expose its canonical `pilno` relation and its
shared host event without an implicit SE trick:

```lisp
(At
  (λ (($tool Entity))
    (pilno (At 2 $tool) (At 3 $e)))
  (Lo karce))
```

The contextual x1 of `pilno` is omitted under the normal `zo'e` rule; x2 is
the tag argument and x3 is the host eventuality. Direct `fi'o pilno` may use
the predicate root itself because the tag value fills effective x1. `Convert`
is available when a converted relation must remain visible:

```lisp
(Convert 2 pilno)                 ; se pilno
(Convert 3 pilno)                 ; te pilno
```

Arbitrary `fi'o` is never guessed into event conjunction. It remains a modal
fill unless the graph supplies a licensed event-property analysis.

## 5. Higher-order operators

Logical operators are typed higher-order intrinsics over dynamic content. They
do not themselves assert and do not require nullary lambda thunks merely to
remain inert:

```text
∧, ∨, →, ↔, ⊕ : Content × Content → Content
¬             : Content → Content
```

Their ordered operands remain ordered because accessibility can make dynamic
conjunction non-commutative even when classical truth conditions coincide.

Quantifiers are higher-order. The binder form is readable surface sugar for
applying a quantifier intrinsic to restriction/body lambdas:

```lisp
(∀ (($x Entity))
  (Restrict (mlatu $x) (Import Projective))
  (jbena $x))
```

Conceptually this elaborates to an application whose operands include
`(λ (($x Entity)) (mlatu $x))` and
`(λ (($x Entity)) (jbena $x))`. Termsets retain a simultaneous `Quantify`
form; the renderer never invents a nesting order.

Connective symbols are printed only under declared mechanical recognition
rules. In particular, `∨(¬P,Q)` becomes `(→ P Q)` only when the connector truth
table/provenance and graph shape establish that exact implication. Otherwise
the graph's operator structure prints directly. Shared contextual operands of
predicate-locus connections remain shared through `Let`.

## 6. Descriptions, abstraction, and relation formation

`Lo`, `Le`, and `La` are reference constructors, not existential quantifiers.
They consume a predicate term whose effective x1 is available:

```lisp
(Lo cukta)
(Lo (cukta (At 2 Speaker)))
(Lo (λ (($x Entity)) (∧ (cukta $x) (nelci Speaker $x))))
```

This is a declared semantic projection. The graph may store the described
referent recursively, and may encode `le` through `skicu`; the concise notation
inverts those constructions when and only when speaker/audience, sharing,
relative-clause status, and scope can be recovered. Non-default facts remain
explicit.

Abstractors are typed higher-order roots. Their shared syntax does not make
their meanings interchangeable:

```lisp
(Ka (λ (($x Entity)) (prami $x Speaker)))
(Nu (cilre Speaker))
(Du'u (melbi (Lo cukta)))
```

`Lo (Nu content)` is a deliberate two-step semantic rendering of a described
event-kind referent even when the current graph stores both layers in one
object.

Tanru projection uses `(OfKind head modifier)` only when the typed recognition
boundary proves the projection. `blanu zdani` is:

```lisp
(OfKind zdani blanu)
```

If recognition declines, the renderer preserves `TanruLink`, head, modifier,
relation label, and fallback graph structure explicitly. It never prints the
underlying graph conjunction as if that were the intended lexical meaning.

Other relation formers use named intrinsics: `Convert`, `Scalar`, `Me`, `Moi`,
`Zei`, `Jai`, `NuhA`, and typed composition constructors. There is no implicit
stringly relation expression.

## 7. Events and event properties

A local generated event and its immediately local existential binding are
silent only when the event is unshared and every facet has its default. A
shared, scoped, or modified event is explicit:

```lisp
(∃ (($e Eventuality))
  (∧
    (klama Speaker (Lo zarci) (At Eventuality $e))
    (Before $e Now)))
```

Eventuality properties are ordinary typed predicate terms where that
desugaring is licensed. This applies systematically to:

- time/space anchors, offsets, paths, intervals, and spans;
- aspect and event contour;
- recurrence and interval modifiers;
- actuality;
- motion and spatial direction;
- event class, abstraction kind, and explicit descriptors.

The intrinsic names are PascalCase because these are semantic-model relations,
not invented Lojban content words. A facet whose relation-level semantics has
not been established uses an explicit typed `Facet` form preserving every
field; it is not silently dropped.

## 8. Nonlogical composition, math, questions, and displayed content

Nonlogical composition never uses a bare list, because a bare list is
application. It uses typed constructors such as:

```lisp
(Joint a b)
(Mass a b)
(Set a b)
(SequenceValue a b)
(Stream a b)
(Respectively (Stream a b) (Stream c d) fn)
(Union a b)
(Intersection a b)
(CrossProduct a b)
(Interval Ordered Closed Open a b)
```

Collectivity, complement, excluded members, distinct partition, endpoint
inclusion, and operator parameters print when present.

Simple computed integer/rational values print as numbers. General quantities
and mekso preserve form, scale, comparison set, operator, grouping, arrays,
intervals, named operators, subscripts, and questions through `Quantity` and
`Math` intrinsics. The fixed Unicode arithmetic table is a convenience, not a
total operator inventory; named-operator fallback is required.

Questions remain typed objects when their structure matters:

```lisp
(Ask
  (Question Argument Direct
    (λ (($x Entity)) (klama $x (Lo zarci)))))
```

The concise fill-in form may be `(Ask (λ ...))` only when asker, respondent,
domain, slots, focus, and presupposed answer are all the notation defaults.

Displayed content and act modifiers use their own typed forms, preserving
family, polarity, intensity, phase, assertion effect, experiencer, target,
focus, anchor, and modifiers. `Incidental` marks speaker-expressed non-at-issue
content; it is not transcript metadata.

## 9. Acts, utterances, and records

Force is explicit:

```lisp
(Assert content)
(Ask question-or-content)
(Command target content)
(Mention value)
(Quote sign)
(Parenthetical content)
(Subordinated content)
(Vocative addressee content)
```

`Assert` is not a descriptive predicate and is not reducible to a relation
such as `xusra`. A report uses an ordinary content predicate inside the one
actual outer assertion:

```lisp
(Assert (xusra $alice (Lo (Du'u content))))
```

An utterance token remains an object when identity or metadata matters. Its
properties are rendered as typed predicate terms under record semantics:

```lisp
(Utterance $u
  (Assert content)
  (Speaker $u $alice)
  (Audience $u $bob)
  (LocutionEvent $u $locution)
  (DeicticTime $u Now)
  (DeicticPlace $u Here)
  (Incidental side-content)
  (Displayed displayed-content))
```

This demonstrates that most facts about an utterance can indeed be a bunch of
predicate terms. The `Utterance`/record boundary remains necessary to say that
speaker/time/audience facts are analyzer/transcript commitments rather than
part of what the speaker asserted. `Incidental` and `Displayed` remain
speaker-expressed strata, distinct from transcript facts.

The wrapper may be omitted only under a checked planner predicate: the force is
ordinary and printed by the act; the token is unshared; no asides, vocative,
displayed content, ordinal label, or external target refers to it; the locution
event and deictic ground are default and unreferenced; and the document shape
does not require utterance identity.

## 10. Concise defaults and preserved distinctions

The human profile suppresses only these named defaults:

- an elided/implicit `zo'e` place whose generated referent is unshared and whose
  scope dependence is exactly the default at that closure site;
- the explicit-vs-elided provenance distinction for ordinary `zo'e`;
- a local unmodified generated eventuality and its immediately local binder;
- default current speaker/audience/time/place transcript facts;
- direct consecutive numbered fills;
- single-use acyclic graph identity.

Default contextual values are distinct only when the graph says they are
distinct. A graph-shared contextual referent, a non-default dependency set, or
an externally referenced contextual value is printed with `Let`/`LetRec` and a
`Context` value. Thus a shared elided tail across a predicate connection is not
misrendered as independent closures.

These are never defaults:

- assertion or any other force;
- `ce'u`/lambda binding;
- `zi'o`/place deletion;
- non-default scope or discourse accessibility;
- modal attachment, connector locus, or genuine underspecification;
- incidental/displayed assertion status;
- shared identity.

## 11. Total typed elaboration architecture

The implementation is a read-only projection from the typed `SemanticGraph`:

1. a typed S-expression datum AST with a single escaping/pretty-printing path;
2. a typed reference/scope planner using `SemanticObject::references_into`,
   binder ownership, use scopes, SCCs, dominators, and least common scopes;
3. a semantic elaborator that reconstructs predicate terms from
   filled/elided/deleted graph arguments and applies the declared reductions;
4. a completeness contract with one disposition for every model surface;
5. a structured word-card section inside the one `(Smusni 0 ...)` document.

It does not serialize to JSON to dispatch on string fields, render XML and
parse it back, or duplicate the XML renderer's giant traversal. Existing XML
planning algorithms may be lifted into a typed renderer-neutral module when
that reduces duplication without making this experiment depend on an XML
rewrite.

Every surface has exactly one disposition:

1. direct semantic form;
2. declared semantics-preserving elaboration;
3. named concise default;
4. ordinary-profile provenance suppression; or
5. explicit typed structural fallback.

The fallback is `(Object Type (Field name value) ...)` for a faithfully
preserved but not yet semantically reduced graph surface, or `(Unresolved ... )`
when the semantics themselves are unresolved. Neither is a silent omission or
an `UNKNOWN` sentence.

## 12. Experimental validation without golden expectations

The old flat-smusni parity suite and its frozen output files are retired, not
rewritten. This pass adds no new byte-for-byte output expectations.

Required checks instead are:

- render every graph-building fixture without panic;
- parse every output as exactly one S-expression document;
- render twice byte-identically;
- prove all printed variables/references are bound at their use sites;
- prove every shared graph identity is either inlined once or bound once and
  referenced consistently;
- count every deletion, event binder, adjunct, question, displayed-content
  node, nonlogical composition, scope-dependence annotation, and typed fallback
  against an independently computed graph summary;
- audit the notation completeness contract with no unclassified inventory
  entries;
- reject the retired declaration syntax and keep `--show-defs` inside the one
  parseable document;
- retain named structural regression tests for the old `zi'o` panic and other
  discovered defects without pinning presentation bytes.

After implementation, generated output—not hand-written guesses—is reviewed on
corpus examples covering descriptions and relative clauses, all connective
loci, abstractions, termsets/quantifier bundles, respectively distribution,
events/tense/modals, questions, displayed content, quotations, mekso, sharing,
and cycles.

## 13. Deliberate departures from first-round review recommendations

- The current graph's total argument map does not force a `Relation` versus
  `Predication` ontology. Reconstructing an open predicate term from
  `Filled`/`Elided`/`Deleted` is the intended semantic projection.
- Ordinary unshared `zo'e` remains silent, per the owner's concision rule.
  Sharing and non-default dependence become explicit at the smallest scope
  that preserves them; every elided place is not printed as `SOME`.
- Eventuality and modal designators remain legitimate place designators in the
  projection even though the current object model stores them in separate
  fields. Their distinct types prevent category confusion.
- `Lo`/`Le`/`Nu` may invert the current self-referential/skicu/combined-object
  representation when the reduction is semantics-preserving. The current graph
  shape is not the desired printed ontology.
- The public format name remains `smusni`, as explicitly required by the owner.
