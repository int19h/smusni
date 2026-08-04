# Experimental smusni S-expression design, draft 2

Status: approved for implementation after final Opus and Kimi convergence
reviews. This is a semantic projection from `SemanticGraph`, not a textual
recoding of XML and not an assertion that the current graph is the ideal
ontology. Compact inverse elaborations are permitted only under named
recognition rules. Every other surface has a faithful typed fallback.

## 1. The smallest useful semantic families

### 1.1 Predicate terms

The central non-Lojban-specific term is **predicate term**, abbreviated
`PredTerm` in implementation sketches:

```text
PredTerm<NumberedRow>
```

A root such as `klama`, a partially filled root, and a root with no numbered
places remaining are all members of this one family. Saturation is only the
special case `PredTerm<∅>`; it neither closes nor asserts the predicate term.
Eventuality and modal attachments may still be added after all numbered places
have been filled.

```text
Fill : PredTerm<{p:T} + ρ> × p × T → PredTerm<ρ>
```

There is deliberately no `Open | Sealed` parameter. Nothing in the calculus
constructs a sealed predicate term: closing changes semantic family and yields
content.

“Predicate term” is preferred because it names an intensional expression with
places without implying saturation, truth, or an extensional set of tuples. It
also avoids collision with this repository's existing relation sort and
`PredicationNode`. The Rust type should be called `PredTerm`, not `Pred`.

### 1.2 Functions

Functions are distinct higher-order values:

```text
Fn<A₁, …, Aₙ, B>
```

They have ordered numbered parameters and are constructed by `λ`. Predicate
terms and functions share application syntax, but only functions beta-reduce.
Applying a predicate term fills a place and leaves the result open.

### 1.3 Content, acts, and discourse computations

Closing a predicate term supplies its remaining contextual arguments at a
particular graph-owned closure site and yields inert semantic content. It does
not assert that content.

The metalanguage may give content a dynamic denotation:

```text
𝒟<Γ, Δ, A>
Pure  : A → 𝒟<Γ, Γ, A>
Then  : 𝒟<Γ, Δ, A> × (A → 𝒟<Δ, Ε, B>) → 𝒟<Γ, Ε, B>

Content<Γ, Δ> = 𝒟<Γ, Δ, Unit>
CloseΓ : PredTerm<ρ> → Content<Γ, Δ>
Assert : Content<Γ, Δ> → Act<Assertion, Γ, Δ>
Perform : Act<F, Γ, Δ> → Discourse<Γ, Δ, Unit>
```

`Δ` is not arbitrary: it is `Γ` extended by exactly the contextual referents
and graph-owned binders materialized at that closure site and permitted to
escape it. The indices track the discourse-referent interface. A richer model
may separately index conversational state such as commitments, issues, and
participants; those coordinates must not be confused with referent
accessibility.

This answers the “discourse monad” question precisely:

- a dynamic content denotes an anaphoric context-change potential;
- `Assert` lifts content to an illocutionary act;
- `Perform`, not `Assert` alone, executes that act as a discourse update;
- ordered discourse composition is `Then`/`Do` at the metalanguage level.

The ordinary S-expression does not print `𝒟`, `Pure`, or `Then`. It prints
resolved identities, lexical binder scopes, ordered discourse items, and force.
At the top level `(Smusni 0 act)` performs the act by document convention;
inside `Quote`, `Mention`, or an utterance record an act is merely a value unless
an explicit `Perform` occurs.

This preserves a crucial distinction:

```lisp
(Assert (xusra $alice (Lo (Du'u content))))
```

performs the current assertion that Alice asserts `content`. It does **not**
perform Alice's reported assertion. Likewise `(Assert (Utters $x $y))` asserts
that an uttering event occurred; it is not equivalent to performing `$y`.
`Utters : Entity × Utterance → Content` is deliberately a PascalCase intrinsic,
not an English-looking dictionary root.  It may render only an explicit graph
or document relation connecting an agent to an utterance token; an utterance
record's metadata never licenses the renderer to invent that report. No current
`SemanticGraph` surface licenses it, so the first implementation does not emit
it; it is an illustrative extension point for an explicit future document
ontology, not a completeness-registry mapping.

### 1.4 How far “predicates all the way down” goes

Event properties, modal relations, and most facts about an utterance token can
be ordinary predicate terms. Logical connectives and quantifiers should not be
pretended to be ordinary first-order dictionary predicates merely for uniformity:
they are typed higher-order functions over `Content` and `Fn` values. Reifying
their operands as entities so that a dictionary predicate can consume them
would add a semantic operation and change the type.

The real uniformity is one typed application tree, not one ontological type.

## 2. Core operations and printed application

The semantic calculus needs:

```text
Root(name, signature)
Apply(operator, operand)
At(predicate, numbered-or-event-place, value)
DropPlace(predicate, original-place)
Modal(predicate-term, modal-fields)
λ(parameters, body)
CloseΓ(context, predicate)
DynamicOperator(typed operands)
Act(force, content)
Perform(act)
UtteranceRecord(token, act, transcript-facts, expressed-side-content)
```

The concrete conventions are:

- Output is exactly one `(Smusni 0 ...)` form. The CLI/MCP format token remains
  `smusni` and replaces the old flat format.
- A list is typed application: `(f a b)` means `((f a) b)`.
- Applying a predicate term with a plain operand fills the lowest remaining
  effective numbered place. Applying a function fills its next parameter.
- `(At p v)` labels a non-next numbered or event place within the surrounding
  application. Numeric `p` always names the root's original place identity.
  Inside `(Modal ...)`, every graph-recorded filled place is labelled, including
  original x1, so a converted or partly elided modal place map is self-describing.
- `(DropPlace r p)` is `zi'o`: original place `p` is absent. Plain operands walk
  the remaining original places in order; numeric labels never renumber.
- `(Modal m)` attaches the already assembled modal predicate term `m`. It is
  not a numbered operand.
- Lowercase Lojban content roots remain lowercase. PascalCase names intrinsics,
  roles, sorts, force, modes, enum values, and contextual/indexical atoms.
- Stable conventional symbols are used for `λ`, `∀`, `∃`, `∧`, `∨`, `¬`, `→`,
  `↔`, `⊕`, `=`, `≠`, `<`, `≤`, `>`, `≥`, `+`, `−`, `×`, and `÷`.
- Bound/shared variables begin with `$`. `@` names a graph object identity in
  typed fallback and compact diagnostic references; the namespaces cannot
  collide.
- Strings use JSON escaping. No comments are needed for parseability.

Declared atoms include `Speaker`, `Audience`, `Now`, `Here`, `This`, `That`,
`Yonder`, and `Context`. `(Named "alis")` preserves the graph's sign/name text;
it never substitutes an English gloss. Non-default deictic grounds use explicit
typed forms rather than a bare atom.

Examples:

```lisp
klama
(klama Speaker)
(klama Speaker (Lo zarci))
(klama Speaker (At 5 (Lo karce)))
(klama Speaker (At Eventuality $e))
((DropPlace dunda 2) Speaker This)
```

No lowercase predicate root is coerced to an entity. Write `(Lo zarci)`, not
bare `zarci`, in an entity place.

## 3. Implicit closure and concise defaults

`CloseΓ` is explicit in the semantics but normally implicit in the printed
tree. A typed boundary that consumes `Content` closes an open predicate term at
that boundary. Such boundaries include `Assert`, connective operands,
quantifier restriction/body positions, abstraction content, and question
bodies. Closure never supplies `ce'u`, performs an act, or moves a binder.

The ordinary profile suppresses exactly the following, when the listed
condition succeeds:

- an implicit/elided `zo'e` referent that is unshared and whose dependence says
  nothing beyond “may depend on every binder accessible at this closure site”;
  with no accessible binder, graph `Fixed` is that default;
- explicit-versus-elided provenance for ordinary `zo'e`;
- a local generated event, including a default locution event, whose facets are
  all default and which is neither shared nor externally referenced;
- an utterance record's deictic-ground fields for current speaker, audience,
  time, and place when their values are the declared indexical atoms and are
  neither shared nor externally referenced;
- direct consecutive numbered fills, except where a named self-description rule
  requires labels, as for every filled place in §2's modal place map;
- a single-use acyclic graph identity under the deterministic rule below;
- an exact computed integer/rational number whose descriptor is ordinary `li`,
  whose form/scale are captured by the value position, and whose surface spelling
  has no remaining semantic contribution;
- fields whose value is implied by a typed position under a named rule below.

A contextual value is silent exactly when the checked predicate above
succeeds.
Sharing, non-default dependence, external reference, and genuine
underspecification are never defaults. A non-default value prints, for example:

```lisp
(Context (MayDependOn $x $y))
(Context Fixed)
```

`Context` has one shape. Its sort comes from the binding or argument position
and is not repeated inside the value. Bare `Context` is the default-dependence
value; a parenthesized form carries a non-default dependence policy.

The planner inlines an identity exactly when it has one post-elaboration use,
is acyclic and not externally referenced, and inlining crosses no binder,
opacity, attachment, diagnostic, or definition-site boundary. Otherwise it uses
`Let`/`LetRec` at the least common legal scope. Term size alone never changes
the choice, so deterministic output does not depend on a prettiness threshold.

## 4. Binder scope and compact-rendering eligibility

Every compact binder has an ordinary lexical scope:

- `(λ (bindings) body)` binds only `body`.
- `(∀ (bindings) restriction body)` and `(∃ (bindings) restriction? body)` bind
  their restriction and body operands.
- `(Cardinality (bindings) quantity restriction? body)` binds its restriction
  and body operands.
- `(Quantify (binding-specs) body)` binds all declared variables throughout all
  simultaneous binding specs and `body`; it never invents a nesting order.
- `(Let (bindings) body)` binds only `body`; acyclic binding values cannot refer
  to their own or later binders.
- `(LetRec (bindings) body)` binds every binding value and `body`.
- `(Utterance $u ...)` binds `$u` throughout that record.
- an explicit `(Lo|Le|La (bindings) base attached...)` description binds every
  base property and attached clause; the described-event form in §9 follows
  the same rule for abstraction content and facets. The binder identifies the
  graph's description parameter in the base with the described referent used by
  attached clauses; this is a checked description elaboration.

Every binder list is a list of entries whose first two fields are the variable
and its sort.  A declaration entry ends there, an ordinary `Let`/`LetRec` entry
adds its value, and a `Quantify` entry adds its typed operator, restriction, and
other binding fields.  Thus declaration lists have the shared shape:

```lisp
(λ (($x Entity) ($y Entity)) body)
```

and value bindings have the shape `(($x Entity value) ...)`.  Constructor-
specific trailing fields are never positionally guessed: their grammar is
defined by the constructor that owns the list.

The compact planner must prove that every graph binder dominates every printed
use under these lexical rules **after** any connective/quantifier recognition.
It must also prove unique binder ownership, scope-dependence containment,
definition-site dominance, representable cycles, and convergent declaration
placement.

If any compact-scope condition fails, the renderer does not hoist a binder and
does not reinterpret accessibility. It emits the whole-document typed-graph
form described in §14. This covers at least the existing XML incompatibility
classes `MultipleBinderOwners`, `BinderDoesNotEncloseUse`,
`ScopeDependencyWithoutEnclosingBinder`, `UnrepresentableCycle`,
`DefinitionSiteDoesNotDominateUse`, and
`DeclarationPlanningDidNotConverge`.

This is required for real graphs such as `ganai da prenu gi da melbi`, where the
builder currently puts an existential binder under the negated operand while a
sibling consequent uses the variable. The renderer preserves that graph in
typed form; it does not silently repair a possible builder scope error.

## 5. Numbered places, deletion, and modal predicate terms

### 5.1 Numbered places

Direct fills use ordinary application; only gaps need `At`:

```lisp
(klama Speaker (Lo zarci) (At 5 (Lo karce)))
```

`DropPlace` preserves original identities:

```lisp
((DropPlace dunda 2) Speaker This)
```

The operands fill original x1 and original x3; x2 does not exist.

### 5.2 Modal places

The canonical rendering of a modal attachment is the modal predicate term
already assembled from the graph's own place map:

```lisp
(∃ (($e Eventuality))
  (klama Speaker
    (At Eventuality $e)
    (Modal
      (pilno
        (At 2 (Lo karce))
        (At 3 $e)))))
```

For `sepi'o lo karce`, this says exactly what the graph says: canonical `pilno`
x2 is the tool, x3 is the host event, and contextual x1 is silent. It requires
no reconstruction of a tag-place parameter from the untyped `introduced_by`
string.

The same form degrades without invention:

```lisp
; direct fi'o pilno lo karce: tag at x1, host event at x3
(Modal (pilno (At 1 (Lo karce)) (At 3 $e)))

; arbitrary fi'o broda lo karce: graph has no licensed event link
(Modal (broda (At 1 (Lo karce))))

; sepi'o with its tag sumti elided
(Modal (pilno (At 3 $e)))
```

No bare-root or unary-λ shortcut is canonical in draft 2. Such sugar may be
considered later only if typed model data proves the tag landing place and the
full expansion, including every shared place. Surface strings are never reparsed
to infer it.

A plain modal uses `(Modal predicate-term)`. Other `Adjunct` fields use a typed
modal record so nothing disappears:

```lisp
(Modal
  (Predicate (pilno (At 2 (Lo karce)) (At 3 $e)))
  (Negation Contradictory)
  (Modifiers ...)
  (Component ...))

(Modal
  (Body content)
  (Component ...)
  (IntroducedBy "fi'o"))
```

`Negation`, scalar negation, modifiers, `body`, and `component` receive a
semantics-preserving compact form only under an independently documented rule;
otherwise this typed modal record is the ordinary fallback, not `Unresolved`.

## 6. Connectives and dynamic accessibility

Logical operators are typed higher-order intrinsics:

```text
∧, ∨, →, ↔, ⊕ : Content × Content → Content
¬             : Content → Content
```

Their operands remain ordered. Glyphs print only under exact recognition rules
over operator, truth table, connector provenance, locus, and child shape. In
particular, the graph's `∨(¬P,Q)` prints as `(→ P Q)` only when the stored
connector proves the implication reading. Otherwise the graph's operator shape
prints directly.

The usual dynamic laws remain the denotational account: conjunction sequences
updates; disjunction introduces nothing outside its branches; negation is a
test; an implication makes antecedent referents accessible inside its consequent
but not afterward; quantifier behavior depends on its typed operator.

These laws are **not renderer planner invariants** and the renderer never
re-resolves them. A separate accessibility audit may compare the resolved graph
with the laws. That audit must:

- reason about introduction sites rather than an invented “branch merge”;
- select laws by recognized connector semantics, so a TFTT implication does
  not receive the raw `∨` and `¬` rules;
- report, not rewrite, a graph that violates the expected law.

Compact output still obeys the lexical binder rules of §4. Dynamic
accessibility never licenses a free `$variable` in the printed tree.

## 7. Quantifiers and quantities

Quantifier glyphs have exact recognition rules:

- `∀` requires the graph's universal operator and an `All` count quantity; the
  glyph captures that quantity, so the otherwise-default `Quantity` object is
  suppressed.
- `∃` requires the graph's existential operator, or a graph-owned generated
  event binder. It is not a generic spelling for `Cardinality`.
- plural universal/existential operators use glyphs only when the plural
  commitment is either represented by the binder sort or printed explicitly.
- `Cardinality`, `None`, and non-default quantities retain typed forms.

```lisp
(∀ (($x Entity))
  (Restrict (mlatu $x) (Import Projective))
  (jbena $x))

(Cardinality (($x Entity))
  (AtLeast 3)
  (Restrict (broda $x))
  (brodi $x))
```

Termset/quantifier bundles use one simultaneous binder:

```lisp
(Quantify
  (($x Entity
     (Cardinality
       (Quantity (Form AtLeast) (ValueText "su'o") (Scale Count)))
     (Restrict (broda $x)))
   ($y Entity Forall (Restrict (brode $y) (Import Projective))))
  (brodi $x $y))
```

`Forall` inside a `Quantify` binding spec is the field-position spelling of the
same recognized universal-plus-`All`-count pair as `∀`; it captures that default
quantity. A universal binding with any other quantity prints the full typed
`Quantity` instead.

Every binding variable is in scope throughout the simultaneous specs and body.
No sub-form pretends to bind a variable used by its sibling.

Non-default `source_variable` and `selection_source` fields print inside that
binding spec. The former is `(SourceVariable $x)`. The latter preserves both
fields of `SelectionSource`, for example
`(SelectionSource (Kind WitnessSet) (Variable $x))`; every future kind uses the
same typed-field shape. Only the ordinary source-span object is subject to the
profile's provenance suppression.

General quantities preserve form, numeric or textual value, scale, comparison
set, and source meaning through `(Quantity ...)`.  Shorthands such as `(AtLeast
3)` require an actual numeric graph value; a textual `su'o` is not silently
rewritten to `1`.  Computed exact numeric values use bare numbers only under
§3's named default. General mekso uses `(Math ...)`; the fixed Unicode table is
a convenience and every unknown/named operator has a named fallback.

## 8. Descriptions and relative clauses

`Lo`, `Le`, and `La` are reference constructors, not existential quantifiers.
The common cases remain concise:

```lisp
(Lo cukta)
(Le cukta)
(La (Named "alis"))
```

An explicit description binder scopes over its base property and every attached
clause:

```lisp
(Le (($x Entity))
  (cukta $x)
  (Relative Restrictive Veridical
    (nelci Speaker $x)))
```

Relative clauses are never blindly conjoined into the base property. The
renderer preserves their attachment, kind, and graph `veridical` value:

```lisp
(Relative Restrictive Veridical content)     ; poi
(Relative Restrictive Nonveridical content)  ; voi
(Relative Incidental content)                ; noi
```

The model omits `Some(true)` by invariant, so absent `veridical` means the
veridical default; `Some(false)` prints `Nonveridical`. `introduced_by` remains
provenance unless it carries a distinction not captured by these typed fields.

This prevents non-veridical `le` description content from swallowing the
veridical commitment of `poi`, and keeps `poi` distinct from `voi`. An
incidental clause remains attached at the narrowest description scope that
contains all of its uses; it is not hoisted to an utterance record merely to
make its non-at-issue status visible.

The graph's recursive `skicu` encoding of `le`, and its self-reference, is
inverted exactly when speaker, audience, binder, sharing, attachment, and
veridicality all satisfy the recognition rule. Otherwise `LetRec` or typed
fallback preserves the graph.

## 9. Abstractions, described eventualities, and tanru

Abstractors are typed higher-order intrinsics:

```lisp
(Ka (λ (($x Entity)) (prami $x Speaker)))
(Nu (cilre Speaker))
(Du'u (melbi (Lo cukta)))
```

The common `lo nu` form is:

```lisp
(Lo (Nu (cilre Speaker)))
```

When the described eventuality itself has facets, `Lo` binds it explicitly and
the facets remain properties of that referent rather than being moved into a
matrix event conjunction:

```lisp
(Lo (($e Eventuality))
  (Nu $e (cilre Speaker))
  (Before $e $matrix-event))
```

Where the fixed recognition table proves that a relation-level intrinsic encodes
the complete facet, `Before` and similar predicate terms replace `Facet`.
Otherwise `Facet` preserves its complete typed field inventory. This is a
deterministic recognition rule, not a stylistic choice.

Tanru projection uses `(OfKind head modifier)` exactly when the existing typed
recognition proof succeeds. The projection's completeness disposition explicitly
accounts for the graph head conjunct and any modifier event binder that the
projection semantically absorbs. If that proof fails, the output retains
`TanruLink`, head, modifier, relation label, and graph structure.

Other predicate-term formers use named intrinsics such as `Convert`, `Scalar`,
`Me`, `Moi`, `Zei`, `Jai`, and `NuhA`. None is reconstructed from a magic string.

## 10. Events and event properties

A generated event is explicit whenever it is shared, referenced, or has a
non-default facet:

```lisp
(∃ (($e Eventuality))
  (∧
    (klama Speaker (Lo zarci) (At Eventuality $e))
    (Before $e Now)))
```

The intrinsic table is fixed and documented with the implementation. It may
cover time/space anchors, offsets, paths, intervals and spans; aspect and event
contour; recurrence; actuality; motion/direction; event class; abstraction
kind; and descriptors. The exact table is a recognition table, not a naming
heuristic. Every unrecognized facet uses typed `(Facet ...)`.

The typed `Facet` form preserves its complete current-model field inventory.
The concise intrinsic table may consume a field only when its recognition rule
states how that field is encoded.

## 11. Nonlogical composition, math, and questions

Bare lists are application, so composition uses typed constructors. Referent
composition and respectively distribution are distinct:

```lisp
(Joint a b)
(Mass a b)
(Set a b)
(SequenceValue a b)
(RespectivelyValue a b)
(Union a b)
(Intersection a b)
(CrossProduct a b)
(Interval Ordered Closed Open a b)
(Interval Unordered Closed Closed a b)
(Interval Centered Open Open center radius)
(ConnectiveQuestion ...)

(Respectively
  (Stream a b)
  (Stream c d)
  (λ (($x Entity) ($y Entity)) body))
```

The *i*th stream is paired with the *i*th lambda parameter, so stream order
preserves the graph's explicit `slot` identity.  A stream with a non-default
restriction or quantity uses typed `(Stream (Slot $x) (Items ...) (Restrict
...) (Quantity ...))` fields rather than the positional concise form.

Collectivity, scalar negation, complement, excluded members, endpoint inclusion,
and operator parameters print when present. `DistinctPartition` belongs to the
typed `RespectivelyDistribution` form rather than referent `Composition`.

Questions retain their typed structure when it matters:

```lisp
(Question Argument Direct
  (Asker Speaker)
  (Respondent Audience)
  (Domain Entity)
  (Body (λ (($x Entity)) (klama $x (Lo zarci)))))
```

The concise `(Ask (λ ...))` form prints exactly when asker is `Speaker`,
respondent is `Audience`, domain is derivable from the slot sort, slots have the
ordinary direct-fill shape, and focus and presupposed answer are absent.

## 12. Force, utterance records, and document sequence

Force is explicit and distinct from predication:

```lisp
(Assert content)
(Ask question-or-content)
(Command target content)
(Mention value)
(Quote sign-or-act)
(Parenthetical content)
(Subordinated content)
(Vocative addressee content)
```

An act directly under `(Smusni 0 ...)` or in a performing `Do` sequence is
performed by the document convention. `Perform` prints only where an act-valued
expression occurs outside a performing position and execution must be explicit.
Quoted and mentioned acts are inert.

The default ordered discourse is:

```lisp
(Smusni 0
  (Do
    (Assert content-1)
    (Assert content-2)))
```

`Do` prints exactly for an ordinary same-topic continuation with no sequence
side fields. Otherwise the full sequence prints:

```lisp
(Sequence SameTopicContinuation
  (Items item-1 item-2)
  (Content ...)
  (ConnectionClaims ...)
  (BoundEventualities ...)
  (OrdinalLabels ...)
  (NonlogicalConnection ...)
  (ElidedConnectionOperand PriorDiscourse))
```

The other relation form is structural rather than an atom:

```lisp
(Sequence
  (ParagraphBoundary
    (Transition NewTopic)
    (Additional ResumePriorTopic ...))
  (Items ...)
  ...)
```

`Additional` is omitted when empty, and `ResumePriorTopic` is also valid as the
primary transition. Other absent fields are omitted. A
sequence whose graph `force` is `Subordinated` prints as `(Subordinated
(Sequence ...))`; it is never mistaken for an ordinary performing `Do`.

An utterance token remains a record when identity or metadata matters:

```lisp
(Utterance $u
  (Act (Assert content))
  (Speaker $u $alice)
  (Audience $u $bob)
  (LocutionEvent $u $locution)
  (DeicticTime $u $deictic-time)
  (DeicticPlace $u $deictic-place)
  (Displayed displayed-content))
```

The head binds `$u`. Transcript facts are predicate terms under the record
boundary; the other variables above are schematic identities bound by the
surrounding tree. Default unreferenced deictic fields are suppressed under §3.
Transcript facts are not part of asserted content. `Relative Incidental` and
`Displayed` remain speaker-expressed strata, not analyzer facts. A direct
top-level utterance record performs its `Act`; an embedded record merely denotes
the recorded token unless `Perform` is explicit.

Within an utterance record, `ActContent` is a typed role referring to that
record's act content. It replaces an explicit target reference exactly when the
graph target is that content; otherwise the target identity prints.

The wrapper is omitted exactly when the token is unshared; no metadata, displayed
content, vocative, aside, ordinal label, incidental stratum, or external target
needs it; the locution/deictic fields are default and unreferenced; and document
shape does not require token identity.

An utterance reached through a quotation remains inside its sign object; it is
not projected directly into an utterance record:

```lisp
(Sign
  (Kind Quotation)
  (Quotation
    (Mode "parsed")
    (Utterance ...)
    (Delimiter "...")
    (Text "...")))
```

Nesting distinguishes `Quotation.text` from `SignNode.text`. Absent quotation
fields are omitted. Other `Sign` kinds and fields retain the same typed-field
treatment. `Quote` consumes the sign value.

## 13. Predication modes, diagnostics, and provenance

`PredicationMode` is omitted exactly when the typed position entails the same
mode:

- act content entails `Asserted`;
- description bases and typed `Restrict` operands entail `Restrictive`;
- `Ka` relation bodies entail `Restrictive`;
- other recognized abstraction bodies entail `Inert`;
- `Relative Incidental` entails `Incidental`;
- displayed-content predicate positions entail `Displayed`.

`Definitional`, `Performative`, and any mismatch with the entailed mode print as
`(Mode mode value)`, a type-preserving wrapper around the predication or content.

Semantic diagnostics never disappear. They attach to the smallest represented
value through a type-preserving wrapper:

```lisp
(WithWarnings value
  (Warning
    (Severity Warning)
    (Message "relation place structure is unavailable")))
```

If the source object is projected away, the same diagnostic moves to a document
`(Warnings ...)` section with a typed `(SourceObject @id)`. Every diagnostic
lives on a semantic object, so this identity is always available. The move
changes attachment only, never multiplicity, severity, or message.
The document `Warnings` child follows represented semantic content and precedes
the optional word-card section.

Source spans, explicit-vs-elided `zo'e`, and surface spellings are ordinary
profile provenance suppressions only when §3 or another named rule says so.
They remain available in the typed-graph fallback and a future verbose profile.

Descriptor recognition consumes `Descriptor.veridical` only when its constructor
entails the same value. Otherwise typed `(Descriptor ... (Veridical true|false)
...)` preserves it; this is distinct from `RelativeClause.veridical`.

## 14. Total typed fallback

The implementation is a read-only typed projection:

1. a typed S-expression datum AST and one printer/escaping path;
2. a typed reference/scope planner over `SemanticObject::references_into`,
   graph binders, use sites, SCCs, dominators, and least common scopes;
3. a semantic elaborator containing only declared recognition rules;
4. a completeness registry giving every model field one disposition;
5. structured word cards inside the single document.

It never renders XML and parses it back, dispatches through `serde_json::Value`,
or parses `introduced_by` strings to recover semantics.

Each surface has exactly one disposition:

1. direct semantic form;
2. declared semantics-preserving elaboration;
3. named concise default;
4. ordinary-profile provenance suppression; or
5. explicit typed structural fallback.

Local unrecognized surfaces use `(Object Type (Field name value) ...)`.
Planner failures that make compact binding/reference structure dishonest use a
whole-document form:

```lisp
(Smusni 0
  (TypedGraph
    (Root @utterance_5)
    (Def @entity_7 Referent
      (Field Sort Entity)
      ...)
    (Def @formula_10 Formula
      ...)))
```

Every graph object is defined exactly once; every link is an `@id` reference;
all enum variants and semantically relevant fields print in model order. This is
a human-readable typed S-expression projection, not embedded JSON. `(Unresolved
...)` is reserved for semantics the graph itself marks unresolved, not for an
unimplemented renderer branch.

XML compact-*shape* incompatibilities use the local typed `(Object ...)`
fallback. Only binder, scope, ownership, definition-site, cycle, and planning
failures named in §4 escalate to whole-document `TypedGraph`; copying XML's
larger fallback set would needlessly destroy compact coverage.

## 15. Validation without new golden expectations

The old flat renderer, parity test, regeneration arm, and frozen smusni output
files are retired after the new renderer lands behind the unchanged token. This
experimental pass adds no new byte-for-byte output expectations.

Required structural checks:

- every graph-building fixture renders without panic, including named `zi'o`,
  binder-does-not-enclose-use, paragraph-root `ni'o mi klama`, and selbri-
  question tanru `ti mo zdani` regressions; typed recognition must decline to
  its specified fallback rather than inherit the current panics;
- every output parses as exactly one S-expression document;
- repeated rendering is byte-identical;
- every compact variable is lexically bound under §4;
- every shared graph identity is either inlined once or defined once and used
  consistently;
- every typed-graph fallback defines all objects and has no dangling `@id`;
- printed argument states, modal argument places, deletions, event binders,
  adjunct fields, relative-clause veridicality, quantities, questions,
  displayed content, nonlogical composition, scope-dependence annotations,
  diagnostics, and fallbacks reconcile with an independently computed graph
  inventory after declared projection exemptions;
- completeness registration has no unclassified model field or enum variant;
- `--show-defs` remains inside the single parseable document;
- retired declaration syntax and legacy golden machinery are absent.

After implementation, sample documents are renderer-generated and reviewed on
corpus examples covering relative clauses (`poi`/`voi`/`noi`), all connective
loci, binder incompatibilities, abstractions with facets, termsets and
cardinality, respectively at both surfaces, events/tense/modals, questions,
displayed content, quotations, mekso, sharing, cycles, and document sequences.
The corpus report must state the whole-document `TypedGraph` fallback count and
rate for single-line units and representative multi-utterance documents, broken
down by fallback reason.

## 16. Implementation sequence

One work item is feasible; no separate prerequisite refactor is required. Use
green commits:

1. typed Datum/printer, typed planner, whole-document fallback, and structural
   test helpers;
2. compact elaborator plus completeness registration and word cards behind the
   existing `smusni` token;
3. retirement of the old renderer, parity/golden machinery, and fixtures;
4. corpus exercise and correction of only implementation defects — no new
   golden output files.

Existing XML planning algorithms may be lifted into a renderer-neutral typed
module where useful, but this experiment does not depend on rewriting XML.

## 17. Deliberate conclusions

- Predicate terms and functions are the two open value families; content,
  acts, and discourse updates remain distinct typed layers.
- Assertion is explicit and separate from predication. Performance is the
  discourse effect; top-level performance is a documented convention.
- Accessibility motivates an indexed denotation, but monadic plumbing does not
  print and graph accessibility is audited rather than re-resolved.
- Modal attachments are themselves full predicate terms. Their graph place map
  is canonical; no tag-place λ is reconstructed from surface strings.
- Relative clauses retain attachment and veridicality; they are not flattened
  into a description property merely for compactness.
- Logical operators share application syntax with everything else but remain
  higher-order operators, not disguised dictionary predicates.
- Facts about an utterance token may be predicate terms, while the record
  boundary distinguishes transcript commitments from what the speaker asserts.
- Compactness is never purchased by emitting a free variable or deleting a
  graph-recorded shared place. Typed fallback is a valid result, not failure.
