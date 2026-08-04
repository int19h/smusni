# Experimental smusni S-expression design, draft 0

Status: pre-review working draft. This is a renderer/elaboration design, not a
claim that the current XML surface or the current JSON object taxonomy is the
ideal semantic ontology.

## 1. The central object: a relation with remaining places

Use one semantic family:

```text
Relation<Row>
```

`Row` is the ordered, typed set of places that remain available. A lexical root
such as `klama` is a relation with all of its places available. Filling one place
captures a value and returns another relation with that place removed from the
remaining row:

```text
Fill : Relation<P + {p:T}> × p × T → Relation<P>
```

This makes zero-filled, partly filled, and fully filled expressions ordinary
states of the same thing. A fully filled relation is the nullary case,
`Relation<∅>`. It is inert propositional content, not an assertion. Ordinary
omitted places are closed with distinct contextual values only when a consumer
requires nullary content:

```text
CloseΓ : Relation<P> → Relation<∅>
Assert : Relation<∅> → Act<Assertion>
```

`Assert` remains explicit. `CloseΓ` is explicit in the calculus but normally
implicit in this concise rendering at a typed boundary such as `Assert`, `∧`,
`¬`, a quantifier body, or an abstraction that requires propositional content.
It must not move across a binder or opaque/intensional boundary.

### Terminology

The provisional implementation term is **relation**; **relation term** is the
unambiguous prose form. This is conventional mathematics rather than a new
Lojban-specific category: partial application of an n-place relation yields a
relation of lower arity, and the zero-place case is proposition-like. It also
avoids the common implication that a *proposition* is closed or that an
*assertion* has been performed.

Two alternatives remain under review:

- **frame** is intuitive because frames have slots and fillers, but “semantic
  frame” already denotes the richer Fillmore/FrameNet construct;
- **predicate frame** is established in valency/functional grammar, but can
  suggest a lexical signature rather than the signature plus its captured
  fills.

`selbri` remains a syntactic category and a provenance fact, not a distinct
semantic type. A syntax position that asks for a selbri may elaborate to any
`Relation<Row>` suitable for that position, including a relation produced by
partial filling, abstraction, conversion, or composition. Likewise, *bridi* is
useful Lojban terminology for the source construction but does not warrant a
second semantic family.

## 2. The small calculus

The irreducible representation operations are:

```text
Atom(name, signature)
Apply(operator, operand)
At(place, value)                 -- labelled relation application
λ(parameters, body)             -- function abstraction
CloseΓ(context, relation)
Act(force, typed content)
Perform(act)                     -- discourse update boundary
Record(utterance, act, facts)    -- transcript/document boundary
```

Graph identity, variables, literals, types, scope constraints, diagnostics,
and opacity/intensionality marks are structural data, not additional semantic
operations.

`Apply` is deliberately higher-order. Applied to a function, it fills the next
numbered function parameter. Applied to a relation, it fills the next available
numbered place. `At(place, value)` selects a non-next place; its designator is a
positive number, `Event`, or another relation term for a modal place. Thus the
user's proposed single-place fill is the relation-typed instance of ordinary
higher-order application, rather than a parallel tree constructor.

The type/signature of every intrinsic says whether an operand is extensional,
intensional, or an opaque sign. Generic beta reduction and graph rewriting may
cross only extensional operands.

## 3. Concrete S-expression conventions

The first version optimizes for a readily inspectable tree, not minimum
punctuation.

- One list is application: `(f a b)` is left-associated application of `f` to
  `a`, then `b`.
- A lowercase atom is a Lojban content root: `klama`, `cukta`, `nelci`.
- A PascalCase atom is an intrinsic, type, force, role, or distinguished place:
  `Assert`, `Lo`, `Event`, `Entity`.
- Conventional mathematical operators use their conventional symbols:
  `λ`, `∀`, `∃`, `∧`, `∨`, `¬`, `→`, `↔`, `⊕`, `=`, `≠`, `<`, `≤`,
  `>`, `≥`, `+`, `−`, `×`, `÷`.
- `(At p v)` labels a fill. Plain operands fill the next available numbered
  places, so the overwhelmingly common numbered sequence stays silent.
- `(Without r p)` removes a place (`zi'o`) and returns a relation with a new
  effective row. It never inserts a value.
- `(Let ((id Sort value) ...) body)` gives shared graph nodes identities.
  Single-use acyclic values are normally inlined. Recursive sharing uses
  `LetRec`.
- `(x Sort)` is a typed binder. The sort may be omitted only when the immediate
  signature determines it without ambiguity.
- Strings use JSON escaping. Standard semicolon line comments are permitted.
- The renderer prints one outer `(Smusni 0 ...)` document so `--show-defs`
  word cards and multiple utterances remain part of one valid S-expression.

Examples of relation application:

```lisp
klama                              ; no places filled
(klama mi)                         ; x1 only
(klama mi zarci)                   ; x1, x2
(klama mi (At 5 karce))            ; x1, x5; x2–x4 remain contextual
(klama mi (At Event e))            ; explicit neo-Davidsonian event place
(klama mi (At pilno karce))        ; modal place designated by relation pilno
(klama mi (At (pilno (At 2 ko'a)) karce))
                                    ; a structured fi'o-style modal designator
((Without klama 3) mi zarci)       ; x3 does not exist in the derived relation
```

The first four forms are notation sugar for repeated single-place application;
they are not a second semantic node shape.

## 4. Intrinsics are typed higher-order roots

Logical operators are functions over nullary relations:

```text
∧, ∨, →, ↔, ⊕ : Relation<∅> × Relation<∅> → Relation<∅>
¬             : Relation<∅> → Relation<∅>
```

They are not assertion acts, and their operands are not nullary lambdas unless
an operator's intensional signature actually requires a thunk.

Quantifiers are higher-order binders. Restricted forms keep restriction and
body separate; distributivity, importing/projective commitment, source-set
selection, and exact cardinality are typed attributes, not reconstructed from
English keywords:

```lisp
(∀ (x Entity)
  (Restrict (mlatu x) (Import Projective))
  (jbena x))

(∃ (e Eventuality)
  (klama mi (At Event e)))

(Exactly 3 (x Entity)
  (Restrict (mlatu x))
  (viska mi x))
```

`Lo`, `Le`, and `La` remain named reference constructors because xorlo does not
license reducing an unquantified description to an existential at its point of
use. They consume a relation whose effective x1 is available. Lambda notation
is used where the relation really has deliberately bound parameters:

```lisp
(Lo klama)
(Lo (klama (At 2 mi)))
(Lo (λ (x Entity) (klama x mi)))
```

Abstractors remain typed higher-order roots. Their shared syntax does not make
their meanings identical:

```lisp
(Ka (λ (x Entity) (prami x mi)))
(Nu (klama mi zarci))
(Du'u (melbi cukta))
```

Tanru composition is relation formation, not conjunction. Until the
underspecified link is resolved, use the readable intrinsic selected in the
XML design but with its corrected argument order:

```lisp
(OfKind zdani blanu)               ; a blue-kind-of zdani relation
((OfKind zdani blanu) ti)
```

No conventional mathematical symbol expresses this deliberately
underspecified composition, so a keyword is clearer than an overloaded `∘`.

## 5. Formulae, acts, and utterances

A nullary relation is propositional content. It still does nothing by itself:

```lisp
(Assert (klama Speaker zarci))
(Ask (klama Speaker zarci))
(Command Audience (klama Audience zarci))
```

`Assert` constructs assertoric force; it is not the descriptive relation
`Asserts`. A report about somebody else's assertion is therefore nested in the
ordinary way:

```lisp
(Assert (Asserts alis (Reify (klama alis zarci))))
```

This reports Alice's assertion and performs only the outer assertion. A
top-level act is performed by the `Smusni` document convention; a quoted or
reified act is merely mentioned.

An utterance token remains a first-class object where identity or metadata
matters. Its metadata is a list of nullary relations recorded by the analyzer,
not silently added to the speaker's asserted content:

```lisp
(Utterance u1
  (Assert (klama alis zarci))
  (Speaker u1 alis)
  (Audience u1 bob)
  (Time u1 t1)
  (Medium u1 Speech))
```

This is surface sugar for `Record(u1, act, facts)`. The metadata entries all
have the same relation-term representation as other content. The enclosing
`Utterance`/`Record` gives them constitutive transcript status instead of
at-issue assertoric force. When all metadata is the ordinary current deictic
ground and the token is not shared, the renderer may print only the act.

Questions require content appropriate to their force:

```lisp
(Ask (λ (x Entity) (klama x zarci)))  ; fill-in question
(Ask (klama do zarci))                 ; truth question
(Question (λ (x Entity) (klama x zarci)))
                                         ; inert/embedded question value
```

Answers, fragments, vocatives, and expressives remain distinct acts or context
updates. They must not be coerced into assertions merely to fit a bridi-only
tree.

## 6. Events and modals

Generated, locally closed event variables stay silent in the common case. They
become explicit when shared, quantified at a non-default scope, or modified:

```lisp
(Assert (klama Speaker zarci))

(Assert
  (∃ (e Eventuality)
    (∧ (klama Speaker zarci (At Event e))
       (pilno karce e))))
```

The latter is licensed only when the lexical modal analysis actually supplies
that event relation. Arbitrary `fi'o` remains a labelled modal fill rather than
being guessed into a neo-Davidsonian conjunct:

```lisp
(Assert (klama Speaker zarci (At (broda (At 2 ko'a)) ko'e)))
```

Operator order is preserved. Proposition-, event-, predication-, and act-level
attachments remain typed alternatives; the renderer must not flatten them into
an unordered property map.

## 7. Defaults and information policy

Concise output suppresses only defaults defined by this notation:

- ordinary unfilled places close as distinct contextual values;
- a generated local event and its existential closure are silent unless its
  identity or scope matters;
- ordinary current speaker/audience/time/place grounding is silent;
- direct numbered fills use the next available place;
- single-use acyclic graph values inline;
- assertion is never a default and is never suppressed.

Explicit `zo'e` and elided places may have the same ordinary semantic reading,
but provenance can distinguish them. The default human profile suppresses that
provenance. `ce'u` is never a default: it is a lambda-bound variable. `zi'o` is
never a default: it changes the relation row through `Without`.

Silence must not resolve genuine underspecification. Scope dependence,
unresolved modal attachment, tanru connection, nonlogical connective structure,
and unknown semantic surfaces receive a compact explicit constructor or a
`Warning`; they are not guessed.

## 8. Relationship to the current graph and XML

The first implementation is a total read-only elaboration from
`SemanticGraph`; it does not replace the object model. It may reuse proven
planning machinery (scope, sharing, binder ownership, typed relation-expression
recognition) factored out of the XML renderer. It must not render XML and parse
it back, and XML wording or omission policy is not authority.

Every graph surface gets one disposition:

1. rendered directly;
2. rendered through a semantics-preserving elaboration;
3. suppressed as a named notation default;
4. suppressed as provenance in the ordinary human profile; or
5. emitted as an explicit unresolved/diagnostic form.

The implementation must remain total. A graph construct that the concise tree
cannot honestly elaborate uses a typed fallback S-expression preserving its
fields, not an `UNKNOWN` sentence or a silent drop.

The old frozen `smusni` byte expectations are retired, not rewritten. This
experimental pass adds no new golden output expectations. Tests should cover
totality, balance/parseability, deterministic output, graph-reference
integrity, and absence of the old declaration notation without freezing sample
bytes.

## 9. Questions for the two design reviewers

1. Is `Relation`/`RelationTerm` the least misleading general term, or does
   `Frame`/`PredicateFrame` better communicate captured slots without importing
   too much Frame Semantics?
2. Is the identification `Relation<∅> = inert propositional content` sound for
   the graph calculus, provided assertion/force stays separate?
3. Should ordinary list application be one typed `Apply` for functions and
   relations, or should relation filling remain visibly distinct?
4. Is `(At place value)` sufficiently readable for skipped, event, and modal
   places? Propose a better established S-expression convention if not.
5. Which defaults above erase a meaningful distinction or move scope?
6. Does the `Utterance`/record treatment correctly distinguish metadata facts,
   reported acts, and performed acts?
7. Which current graph/XML surfaces cannot be represented totally under these
   constructors without adding another primitive?

## 10. Research anchors

- CLL 9.2: a selbri plus ordered sumti makes a bridi; omitted places have the
  same ordinary meaning as explicit `zo'e`.
- CLL 9.12: modal places coexist with numbered places; bare `jai` is explicitly
  vague.
- CLL 11.1: a whole bridi is packaged into a selbri by abstraction; uniform
  syntax does not imply uniform semantics.
- CLL 19.5: questions expose typed blanks, and legal answer utterances need not
  be bridi or claims.
- xorlo guidance: an unquantified `lo` phrase is not silently an existential
  quantifier at its point of use.
- FrameNet/frame-semantic work: frames have named roles filled by arguments,
  which motivates but also semantically loads the term *frame*.
- Functional Grammar uses *predicate frame* and *open predication*, evidence
  that predication need not always mean a closed assertion; it still does not
  name the zero/partial/full family as cleanly as `Relation<Row>`.
- Standard logic calls variable-containing content an open formula and a
  variable-free formula a sentence/proposition; this supports reserving
  proposition for the nullary case and assertion for discourse force.

