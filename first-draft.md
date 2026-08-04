# Revised draft: a uniform typed application graph for tersmu

## Question

Can aggressively desugared Lojban use one small, uniform application graph—root terms, labelled filling, higher-order abstraction/application, and explicit discourse acts—without collapsing semantic distinctions that Lojban needs? Can logical operators, quantifiers, events, and facts about utterances all share that graph shape?

## Revised verdict

Yes for the graph representation; no for a one-sort semantic reduction. The strongest defensible version is:

1. lexical and intrinsic roots create inert typed terms, including relations/selbri;
2. `Fill` is labelled partial application and never asserts;
3. lambda abstraction and application create functions, including functions over relations, propositions, events, and acts;
4. a small family of intrinsic higher-order roots constructs formulae, quantification, reference, abstraction, relation composition, and discourse acts;
5. `Assert` consumes propositional content and produces an illocutionary act; it is not an ordinary truth-valued predicate;
6. a transcript may record that act, while actual performance remains a discourse-level operation or top-level convention.

This gives “typed application and lambda all the way down,” not literally “ordinary bridi all the way down.” `And`, `ForAll`, `Lo`, `Nu`, a tanru-composition operator, and lexical predicates may share one node/application shape, but their signatures and denotations differ. Uniform shape alone is no semantic achievement; the payoff comes from types, explicit scope, explicit level-crossing operations, and preservation of underspecification.

The core should therefore be minimal in constructors, not in semantic sorts or denotational axioms.

## Three layers that must not be conflated

### Representation layer

A tiny graph calculus can use only atoms, labelled filling, lambda/application, binding, and force/action nodes. Logical operators and quantifiers can be atoms in this graph.

### Denotational layer

Intrinsic atoms require meanings. Calling `And` a predicate does not define conjunction; calling `ForAll` a predicate does not define quantification. A logical basis, lexical axioms, reference resolution, abstraction semantics, and event interpretation remain.

### Discourse/evaluation layer

An inert content graph is not yet a conversational move. Assertion, questioning, directing, expressing an emotion, addressing someone, and answering a prior question have different update behavior. They can be represented as action values with bridi-described metadata, but recognizing or performing the action remains a use-level operation.

This division explains both why a very small object model is plausible and why a pure unordered bag of truth-valued predications is insufficient.

## The revised typed core

### Values and types

At minimum the graph needs these *sorts*, even if they all share one generic node representation:

- `Ref<K>`: typed discourse referents—individuals, pluralities, events, utterance tokens, signs, reified contents, sets, numbers, and so on;
- `Rel<Row>`: an inert relation/selbri intension with a typed row of places;
- `Pred<Row, States>`: an occurrence of a `Rel` with its ordered fill history and per-place states, still not a formula and not truth-evaluable by itself; `Start : Rel<Row> -> Pred<Row, Defaults>` and `Fill : Pred -> Pred` make the distinction operational;
- `Prop`: inert, scope-bearing propositional content; this must remain structurally or hyperintensionally represented, not reduced merely to a truth value or set of worlds;
- `Fn<A..., B>`: a numbered-argument function, possibly higher-order;
- `Act<K>`: an utterance/discourse act such as assertion, question, directive, address, or expressive;
- `TranscriptEntry`: document-layer constitutive metadata, deliberately neither `Prop`, `Act`, nor `Ref`;
- graph identities, variables, literals, scope handles/constraints, and discourse context.

Useful explicit level crossings include:

```
CloseΓ       : Context x Pred -> Prop
ReifyProp    : Prop -> Ref<Proposition>
ReifyAct     : Act -> Ref<Act>
ContentOf    : Ref<Proposition> -> Prop
QuoteStruct  : DiscourseSequence -> Ref<Sign>
QuoteOpaque  : Text -> Ref<Sign>
Interpret    : Ref<Sign> -> Ref
SignOf       : Ref -> Ref<Sign>
Lo/Le        : Rel<Row> x Context -> Ref<K>  requires Row[1] = Ref<K>
AsSelbri     : Pred<Row,States> -> Rel<EffRow(Row,States)>
X1Abstract   : Rel<Row> -> Fn<Ref<K>, Prop>
Nu           : Intensional<Prop> -> Rel<[1:Ref<Event>]>
Ka           : Fn<Args, Prop> -> Rel<[1:Ref<Property<Args>>]>
Du'u         : Intensional<Prop> -> Rel<[1:Ref<Proposition>, 2:Ref<Sign>]>
Assert  : Prop -> Act<Assertion>
Perform : Act -> DiscourseUpdate
Record  : Ref<Utterance> x Set<Prop> -> TranscriptEntry
```

`EffRow` removes `Absent` places, closes over `Filled` places, and retains surviving place order plus origin-place provenance; whether user-facing effective indices renumber after `zi'o` is an explicit semantic-policy choice, not silently inherited from the base row. `Lo`/`Le` require an effective unfilled/defaultable x1 of sort `Ref<K>`. The exact `NU` signatures need a defended abstraction theory, but the syntactic result is a one-place selbri/relation; a gadri such as `lo` selects a referent from its x1 domain. `Lo(Rel)` may be rendered through named sugar `LoFn(X1Abstract(Rel))`, but the two are not competing primitives. Every crossing must be named.

Function/operator signatures also mark each argument as `Extensional`, `Intensional(index)`, or `OpaqueSign`. Beta reduction and extensional structural equivalence are valid only in positions whose signatures license them; quotation and propositional-attitude content are not traversed by generic rewrites.

### Root

`Root(name, signature) -> typed inert term`

Content roots are lowercase Lojban words. Intrinsic semantic roots are PascalCase. A lexical selbri root yields a `Rel`; an intrinsic root may yield a relation, proposition constructor, reference constructor, scope operator, or act constructor. A root has no underlying term; it is the end of the construction chain.

### Single-place filling

`Fill(predication, place, value) -> predication'`

The operation is persistent and inert. It is typed labelled partial application over `Pred`, not `Prop`. `Place` is a closed typed sum such as `Lexical(n) | Event | Intrinsic(name)`; the row signature determines which designators and value sorts are legal. Ordinary notation may flatten a chain only when doing so preserves the order of all scope-bearing operators. Modal/tag order cannot be flattened into an unordered place map.

Lexical place designators contain an integer index. Eventive analyses may additionally use a distinguished event designator, but its presence on every lexical root is not assumed. A modal payload can itself be a partially filled relation, but its attachment is a typed, ordered higher-order operation over a host predication or proposition—not an unordered extra argument of `And` or of the host lexical relation.

### Four observable states for a lexical place

The crucial refinement is that “not explicitly filled” has several meanings:

1. `Default`: ordinary omission, resolved as contextual `zo'e` when content is closed for use;
2. `Bound(id)`: a `ce'u` occurrence referring to a lambda binder, not a contextual omission;
3. `Absent`: `zi'o`, which changes the relation by removing a place;
4. `Filled(v)`: an explicit value.

There must be only one canonical binder mechanism. Internally, `Bound(id)` is the observable state of `Filled(Var(id))`; `Lambda` owns the binder. It is not a second independent kind of binding. This lets one binder occur in several places without duplicating it and prevents both every omitted place becoming a function parameter and every `ce'u` becoming `zo'e`.

The typing has concrete exclusion power. In `ka ce'u prami zo'e`, x1 is `Filled(Var(0))` and x2 is `Default`; beta-application may replace the former, while contextual closure may resolve only the latter. In `broda zi'o`, closure is forbidden from inventing a value for the absent place. A generic untyped property bag would not enforce either distinction.

### Lambda and application

`Lambda([1..n], body) -> Fn<T1..Tn, B>`

`Apply(fn, [v1..vn]) -> B`

Functions need numbered arguments, but their result and arguments may be bridi, references, other functions, or actions. Internally, de Bruijn indices or stable binder IDs would make capture impossible; the human form can use compact named or numbered binders.

`Fill` and `Apply` should stay conceptually distinct. `Fill` incrementally specializes a labelled relational template and leaves other places defaultable. `Apply` beta-reduces deliberately bound parameters.

### Formula formation, closure, and assertion

Whenever a syntactic bridi becomes propositional content, there is a local formula-formation/closure operation:

`CloseΓ(context, predication) -> Prop`

It introduces distinct contextual dependency terms for `Default` places, preserves binder dependence, fixes the local scope of event/quantifier closure, and may leave genuinely unresolved scope as constraints. “Resolve” need not mean choosing a concrete referent immediately. Each omitted occurrence is independently introduced unless syntax explicitly shares it.

Closure occurs inside subordinate content as well as at top level: the bridi inside `du'u`, `nu`, a modal operand, or a connective must become content at that local boundary. It cannot be postponed wholesale until assertion, because many contents are never asserted and because doing so would move closure outside the binders on which contextual terms may depend.

`Assert(p : Prop) -> Act<Assertion>`

`Assert` applies only after the desired fills, modals, operators, binders, and local closure have assembled a `Prop`. It gives that content assertoric force. It neither fills omitted places nor returns a truth-valued predication.

If the object model wants a single general effect boundary, use `Perform(Assert(p))`. In a transcript-oriented model, a top-level list may conventionally denote performed/recorded acts, making `Perform` unprinted but still part of the document semantics. Either way, `Assert` is not reducible to `asserts(speaker, ReifyProp(p))` without changing use into mention. Examples below write `Close(pred)` as renderer shorthand for `CloseΓ(context,pred)`.

## Higher-order operations

### Logical connectives

They fit the uniform graph shape, but their operands are formulae rather than arbitrary partial relations:

```
And : Prop x Prop -> Prop
Or  : Prop x Prop -> Prop
Not : Prop -> Prop
If  : Prop x Prop -> Prop
Iff : Prop x Prop -> Prop
```

Thus an implication is an intrinsic root with two filled higher-order arguments, and only the outer act asserts it:

```
Assert(If(P, Q))
```

not `If(Assert(P), Assert(Q))`.

Closed operands need not be wrapped in nullary lambdas. `p` and the thunk `lambda(). p` are not assumed interchangeable: under intensional operators they can differ in evaluation index and opacity. Lambdas are essential when an operand contains a bound variable or when the operator's signature explicitly demands an intension/thunk.

Connectives over open predications require a separately typed pointwise lifting. A shared *referent* may be filled into each operand before local closure while unrelated omitted places remain distinct. A shared *quantified term* must instead raise one binder over the whole connection, with that same variable referenced in every operand; duplicating the quantifier would wrongly allow different witnesses and break cross-operand anaphora. Consequently `Fill(And(P,Q), 3,v)` is a type error. Surface bridi-tail normalization is roughly `LiftAnd(shared_terms, P, Q)`, which lowers either to `And(Fill(P,...), Fill(Q,...))` for shared constants or to `Quantify(x, And(P(x),Q(x)))` for shared quantified terms. No connection may be lifted across an abstraction or other opaque/intensional boundary.

Dictionary predicates can sometimes be connected by lexical axioms. `zilvlina` is defined directly over two `du'u` arguments as logical disjunction, but normalization to `Or` needs an explicit `Ref<Proposition> -> Prop` interpretation/coercion; it is not a free collapse of use and mention. `vlina` and `kanxe` are three-place: x1 is the disjunction/conjunction as an object, while x2 and x3 are the two `du'u` propositions. They are therefore not the same two-argument operator. More importantly, using a Lojban word does not eliminate the logical primitive: its lexical truth-condition is precisely what supplies the connective semantics.

`Not` above covers contradictory propositional negation only. Scalar `na'e`/`no'e`/`to'e` forms relations, while metalinguistic `na'i` is non-truth-conditional; they require different typed operators. `naku` is a movable scope boundary whose passage across quantifiers changes their force, not merely a Boolean child node placed after all quantifier processing.

Brismu makes the same foundational point in another form: it chooses a connective basis, takes implication as primitive, and bootstraps the rest with axioms/definitions. It explicitly cannot define the entire logical basis out of ordinary content relations.

### Quantifiers

Explicit quantifiers are paradigmatic higher-order binders. One binder identity is shared by sibling restriction and body formulae; this preserves cross-branch dependence/anaphora while keeping restriction and scope distinct. Importing/projective commitments attach to the restriction, and distributivity attaches to the quantifier:

```
All(bind = x,
    distribution = distributive,
    restrict = ProjectiveNonempty(R(x)),
    body = B(x))
Some(distribution = distributive,
     bind = x,
     restrict = R(x),
     body = B(x))
Exactly(n, distribution = distributive,
        bind = x,
        restrict = R(x),
        body = B(x))
```

The importing Lojban restricted universal is not simply derivable as classical `forall x. R(x) -> B(x)`: that formula is vacuously true when no `R` exists, while the adopted importing analysis carries a projective domain commitment on `R`. Nor is merely conjoining existence in the ordinary at-issue body an adequate substitute. Locating the commitment on the restriction makes its survival under negation mechanically testable.

This is not merely an encoding trick. Generalized-quantifier semantics standardly treats determiners as higher-order relations between restriction and scope. It accommodates explicit Lojban numeric quantifiers better than hard-wiring only `forall` and `exists`.

Under xorlo, however, this is the *explicit-quantifier path*, not the default interpretation of a gadri sumti. An unquantified `lo P` is a context-dependent, number- and distributivity-neutral plural constant. Outer quantification over `PA lo P` ranges distributively over members/referents of that constant; bare `PA P` has the distinct restricted-quantification analysis. Inner counts and `mei`-style cardinality are relation formation, not quantifier force.

Quantifier scope cannot be recovered from a flat unordered bag of predications. It needs nested lambdas, explicit handles, or scope constraints. MRS/DMRS is an instructive comparison: its elementary predications look much like the proposed bridi graph, but it retains handles and restriction/body links precisely because a flat predicate graph cannot carry scopal semantics by itself.

### Descriptions

Descriptions are reference constructors over selbri with a designated x1:

```
Lo : Rel<Row> x Context -> Ref<K>       requires Row[1] = Ref<K>
Le : Rel<Row> x Speaker x Context -> Ref<K>  requires Row[1] = Ref<K>
La : Sign/Predicate x Speaker x Context -> Ref
```

`lo broda be ko'a` first derives `AsSelbri(broda(2=ko'a))`, whose effective x1 remains available, and supplies that relation to `Lo`. Its function view is named sugar, `X1Abstract(AsSelbri(broda(2=ko'a))) = lambda x. Close(broda(1=x,2=ko'a))`, not a silent identification of `Rel`, `Pred`, and `Fn`.

Current xorlo does not justify replacing bare `lo P` by an existential quantifier at its occurrence. Unquantified descriptions are context-dependent plural constants; outer quantification is a separate operation. The gadri commentary's Skolem-function analysis is especially relevant where such constants or omitted `zo'e` depend on an enclosing bound variable. This is an unofficial but powerful explanation of ordinary readings such as every cat having its own parents, time, and place of birth.

### Abstractions

Abstractions are typed higher-order relation-forming operators, not one uniform cast:

- `ka` consumes a lambda/intension with one or more distinct `ce'u` parameters and produces a one-place property selbri whose x1 is that property;
- `du'u` packages propositional content into a selbri relating its x1 to that content/significance;
- `nu`, `mu'e`, `pu'u`, `za'i`, and `zu'o` produce event-kind selbri with distinctions that require theory;
- `jei`, `ni`, `li'i`, `si'o`, and `su'u` form truth-value, quantity, experience, concept, or generic abstraction selbri.

They may all be intrinsic higher-order roots in the same application graph, but they are not thereby semantically reduced to one another. `Nu(P) : Rel<[1:Ref<Event>]>`; `lo nu P` applies `Lo` to that x1-focused relation to obtain a `Ref<Event>`, while `nu P` by itself remains a selbri. Likewise `Ka(lambda x. P(x)) : Rel<[1:Ref<Property<Ref>>]>`, and `lo ka ...` describes a property referent rather than applying `Lo` directly to the property function. CLL itself says that the abstraction syntax is uniform while the semantics are rich and have few common features.

`me` is a sumti-to-selbri relation former, not a transparent cast from reified content back to the same content. CLL glosses it as “x1 is among the referents of the sumti,” while the current dictionary adds a second “specific in aspect” place; a concrete model must choose or preserve that provenance explicitly. Either reading changes semantic level. `me lo du'u P` can satisfy a syntactic selbri position, but it is not evidence that `P` and its reification are identical.

### Quotation, signs, and un-reification

Quotation is not one generic string constructor:

```
QuoteStruct(sequence) : Ref<Sign>
QuoteOpaque(text)     : Ref<Sign>
SignOf(referent)      : Ref<Sign>      // lu'e-like direction
Interpret(sign)       : Ref            // la'e-like direction
ReifyProp(p)          : Ref<Proposition>
ContentOf(r)          : Prop           // only for Ref<Proposition>
```

Structured `lu ... li'u` preserves nested acts/content and discourse accessibility; `zo`, `lo'u ... le'u`, and `zoi` produce opaque sign objects. `ContentOf` is the safety-critical named bridge used by any lexical axiom such as `zilvlina` that reasons about whether reified `du'u` contents are true. It is intensional and signature-controlled, not a generic cast. A precise `Du'u` theory can expose both content and sentence-sign places, keeping the distinction lexical rather than merely conventional.

### Tags/modals as ordered higher-order functions

The most compositional representation is an ordered, typed operator whose surface attachment determines its layer:

```
TagPred : ModalPayload x Pred -> Pred
TagProp : ModalPayload x Prop -> Prop
```

or, for a connection between two contents:

```
Tag2 : ModalPayload x Prop x Prop -> Prop
```

A modal payload is itself a partially filled `Pred`; `TagPred` or `TagProp` applies it to the host at the syntactically determined scope. These are typed overloads with the same graph/application shape, not two silent interpretations of one node. A lexical rule may lower `TagPred` to a relation over the host event; a proposition-scoped tag remains a scope operator. Operator order is semantically significant and must survive rendering. Act-level free modifiers/indicators are a separate `ActModifier` family, not evidence for `fi'o : Act -> Act`.

However, arbitrary `fi'o` is underdetermined. Standard syntax says its sumti fills x1 of the modal selbri, and the construction adds a modal place to the host relation. It does not supply a universal truth-conditional rule saying which remaining modal place receives the host bridi/event. BPFK material explicitly says the bridi-operator sense has to be defined for each modal selbri and may remain vague. Therefore:

- most BAI tokens can be mechanically expanded into `fi'o` plus their lexically associated, possibly converted source gismu (`do'e` is exceptional), but this is syntactic canonicalization rather than semantic reduction;
- a complex `fi'o` payload can be represented faithfully as a partially filled modal bridi/operator;
- turning every such payload into an event relation requires a lexical rule or a preserved underspecified attachment constraint, not an invented universal heuristic.

The BPFK `jai`-based paraphrases do not prove a universally lossless event attachment. Bare `jai` is itself deliberately vague about the promoted participant relation. Those paraphrases motivate a relationship between the modal payload and an event/content abstraction, while the exact attachment remains lexical or underspecified.

## Events and event properties

A neo-Davidsonian treatment fits eventive predications well:

```
lambda e. And(
  klama(Event=e),
  Agent(e, mi),
  Goal(e, zarci),
  Instrument(e, car)
)
```

or, retaining Lojban lexical places rather than replacing them all with thematic roles:

```
lambda e. klama(Event=e, 1=mi, 2=zarci, 5=car)
```

Additional event properties are ordinary bridi sharing `e`. This softens the hard argument/adjunct divide and gives many modals a natural attachment target. It does not require an event place on mathematical, classificatory, sign-level, or metalinguistic roots, and it does not force every modal to target an event.

But event introduction/closure has scope. `Not(ExistsEvent(lambda e. P(e)))` differs from `ExistsEvent(lambda e. Not(P(e)))`. Event closure therefore belongs in the explicit scoped semantics (or in a precisely specified `Close` operation), not as an invisible graph post-processing heuristic.

Lojban also does not guarantee that every modal is simply a property of a single event. Modal sentence connections can relate two abstract events or propositions; epistemic, evidential, causal, and discourse-level modifiers may target content or utterance rather than the event described. The event place should be available, not forced as the only semantic attachment point.

## Utterances

### Yes: facts about an utterance can be bridi

Let `u : Ref<Utterance>` be an utterance token, distinct from `a : Act`. Its properties can be represented by ordinary predications, but their status must be explicit:

```
Record(u, {
  Close(Utterance(u)),
  Close(RealizesAct(u, ReifyAct(a))),
  Close(Speaker(u, alice)),
  Close(Addressee(u, bob)),
  Close(HasSign(u, q : Ref<Sign>)),
  Close(HasContent(u, ReifyProp(p))),
  Close(Medium(u, speech)),
  Close(Time(u, t)),
  Close(FollowsAtLevel(u, previous_u, metalanguage_level))
})
```

Many PascalCase roots could be replaced by appropriately precise lowercase Lojban content roots where the dictionary relation actually matches. Intrinsics are needed where Lojban has no precise root or where the relation belongs to the semantic metalanguage.

This is a strong case for retaining utterance identity in the object model while storing most of its descriptive information as a graph of bridi. `Record(...) : TranscriptEntry` says these are transcript/semantic-model facts, not claims made by the speaker; `Assert(Record(...))` is a type error. If a speaker asserts one metadata proposition, that proposition receives its own `Assert`. The typed reification/interpretation bridges prevent token, sign, content, and act from being silently identified. CLL distinguishes an utterance text (`dei`) from its interpretation (`la'e dei`), and utterance back-reference also needs metalinguistic levels rather than one flat `Follows` chain.

### No: reporting an assertion is not performing it

```
Assert(Close(utters(alice, ReifyProp(p))))
```

is the current speaker's assertion that Alice utters `p`. It does not assert `p`. Likewise:

```
asserts(alice, ReifyProp(p))
```

is an inert content predication until some outer force applies to it.

If `Assert` were itself reduced to the truth-valued predicate `asserts(current_speaker, p)`, then using it would require an outer assertion to make that claim, producing either a regress or a silent reintroduction of a performative interpretation rule.

The clean model is:

```
u : Ref<Utterance>
a := Assert(p)
Record(u, {Close(RealizesAct(u, ReifyAct(a))), Close(Speaker(u, alice)), ...})
Perform(a)
```

with one explicit general effect boundary. `Assert(p)` always constructs the assertion act; it never conditionally performs it based on position. A document-level convention performs or merely records each listed top-level act. In particular, `Assert(Utters(x,y))` is the current assertion-act object whose content reports that x uttered y; it is not x's utterance of y.

### Assertion is not the only force needed for full Lojban

CLL supplies decisive counterexamples to an assertion-only discourse model:

- vocatives are legitimate Lojban sentences but not bridi and update address/reference;
- `ko` directs the listener to make a bridi true rather than asserting it;
- questions request an answer and can have propositional, alternative-set, or open-function content;
- a bare sumti, connective, number, relative clause, or other fragment can be a legal answer that completes prior open content without asserting a standalone bridi;
- pure emotion indicators make no claim and have no truth value;
- propositional attitudes can subordinate the apparent main bridi rather than assert it;
- discursives relate an utterance to discourse;
- performatives can make something true by being felicitously uttered.

Thus a complete model needs a typed `Act(force, content)` family even if declarative bridi use explicit `Assert` in human-readable output. The content type depends on force: assertions consume propositions, polar questions may consume propositions, wh-questions consume open functions/alternative sets, directives contain predications with every `ko` occurrence filled by the addressee, and bare fragments require `Mention` or context-dependent `Answer` force that applies them to a prior open question. Vocatives, indicators, and discursives may attach to an utterance mid-sentence and must not be forced into at-issue truth-conditional content.

Dynamic semantics gives the right architectural interpretation: content is inert until an act uses it as a context-update instruction. All descriptive facts about the act may remain bridi.

## What really desugars, and what does not

“Semantic-preserving” must be tested on at least five axes: (1) truth-conditional or force/content equivalence, (2) preservation of at-issue versus projective/use-conditional status, (3) preservation of anaphoric and discourse accessibility, (4) preservation of the original underspecification/reading set, and (5) preservation of surface sign identity wherever metalinguistic reference or quotation can target it. A rewrite that passes only the first axis is not a whole-utterance desugaring.

### Strong, rule-backed reductions

1. **FA**: normalize term-level place selection into an explicit lexical place label; the renderer may omit labels only for the ordinary canonical sequence. **SE** is separately a relation-level row permutation that changes which place is x1 for downstream descriptions, abstractions, and tanru composition.
2. **BE/BEI**: fill places on the attached brivla/selbri without asserting it. This directly supports persistent partial bridi construction.
3. **Omitted regular places**: represent as `Default`, with `zo'e` suppressed in the concise format.
4. **ZI'O**: mark a place `Absent`, creating a different relation rather than a contextual value.
5. **Most BAI surface tokens**: mechanically expand to `fi'o` plus their lexically specified, possibly SE-converted source gismu; this preserves syntax/lexical identity but does not determine the modal's attachment semantics, and `do'e` is exceptional.
6. **Logical sumti and bridi-tail connections**: expand into formula-level truth-function applications at their original scope, under all dominating binders/operators and without crossing abstraction/opacity boundaries. Tanru-internal connection is excluded; shared head/tail terms must be explicitly distributed while unrelated defaults remain distinct.
7. **Forethought/afterthought logical variants**: normalize to the same intrinsic truth function plus explicit operand order/scope.
8. **Explicit quantifiers**: normalize to typed generalized quantification with restriction, scope, distributivity, and any projective importing commitment preserved. Bare `PA selbri` and outer `PA sumti` require different restrictions under xorlo.
9. **Explicit `ce'u`**: normalize to canonical binder IDs and numbered lambda/intension arguments. Implicit `ce'u` placement remains policy-sensitive.
10. **`me`**: normalize to an explicitly provenance-chosen sumti-to-selbri relation; do not treat it as transparent dereification.
11. **`nu'a`/`na'u`**: normalize operator/selbri conversions only where their arity, typing, and lexical correspondence are defined.

### Reductions that require an explicit semantic policy

1. **Bare `lo`/`le` descriptions**: higher-order contextual reference, not automatic existential quantification. Dependency on enclosing binders may require Skolem-style reference functions.
2. **Ordinary omitted `zo'e` under quantifiers/negation**: represent an underspecified contextual term plus its possible binder-dependence set. A later policy may choose a rigid or Skolem-like dependency, but canonicalization must not choose prematurely; interaction with negation is also unsettled.
3. **Arbitrary `fi'o`**: preserve a modal operator/edge unless a lexical attachment rule specifies its truth conditions.
4. **Tenses and event properties**: event semantics is natural, but event closure and scope must be explicit.
5. **NU abstractors other than clear `ka` cases**: represent as typed higher-order roots until a defended reduction exists.
6. **Evidentials and propositional attitudes**: decide whether they change asserted content, force, commitment metadata, or some combination.
7. **Plural/mass readings**: a plural-reference or set/mereological policy is required; not all are first-order reducible.
8. **Anaphora, `go'i`, `nei`, `no'a`, and fragments**: require discourse graph/context, not sentence-local lambda reduction alone.
9. **Utterance pro-sumti**: resolution requires discourse identity and metalinguistic level; text/sign and interpretation remain distinct typed values.
10. **Discursives, evidentials, vocatives, and indicators**: they can often be represented as relations over utterance/discourse nodes, but expanding them into asserted bridi generally changes at-issue status and sometimes anaphoric behavior.
11. **Relation formation**: tanru, `zei`, `me`, MOI, `nu'a`, SE, and scalar NAhE can all use higher-order intrinsic relation constructors, but their lexical/compositional meanings are not thereby reduced.

### Known lossy or non-universal “reductions”

1. **`tu'a` and bare `jai`** deliberately suppress which abstraction/participant relation is intended. CLL explicitly calls the transformation information-losing.
2. **`do'e`, `co'e`, and many ellipses** preserve underspecification; resolving them by guessing would not be semantic-preserving.
3. **Tanru composition** is not generally truth-functional and has no universal expansion into conjunction.
4. **Tanru-internal jek** is the exception to the general logical-connection expansion rule.
5. **Non-logical connectives** construct pluralities, groups, sets, sequences, products, correspondence, and so on; they do not expand into truth functions.
6. **Indicators/free modifiers** cannot simply be deleted or turned into at-issue asserted reports. The wiki's “reduced logical form” explicitly deletes them and leaves several constructs unhandled, so it is a scope-normalization experiment, not a semantic-preserving normal form for all Lojban.
7. **A current utterance act** cannot be replaced by an asserted report that the act occurred without changing use to mention.

## Source mining results

### Brismu

Useful reductions/foundations found:

- logical basis and SKI/application account;
- explicit connective bootstrapping and acknowledgement that a basis remains primitive;
- first- and second-order quantifier axioms;
- `ka` as an internal-hom mechanism for treating relations as arguments;
- a typed distinction between open `ce'u` relations and fully applied bridi;
- abstractor classification by input and output kind;
- `jai`, `na'u`, and `nu'a` adjunction/cancellation ideas;
- signs (`la'e`, `lu'e`, `lu'a`, `lu'i`) expanded through `sinxa`;
- ellipsis and reference pushed into a discursive layer;
- BAI/TENSE equivalence families and a story-time event relation;
- explicit warning that second-order content is not always first-orderizable.

Limitations: brismu describes only a small fraction of the baseline as defined and a larger fraction as merely ontologized, treats the abstractors informally, and moves substantial conversational semantics into a discursive layer. Its published percentage/count wording is easy to conflate, so it should be cited by version rather than summarized as “161 defined.” It is a valuable mine of reductions and architecture, not a complete standard semantics.

### Lojban wiki snapshot

High-value pages found:

- **Expansion of logical connections**: full-bridi, bridi-tail, sumti, termset, and multiple-sumti expansion, with scope interactions; also proposes proposition predicates such as `vlinyje'u`.
- **lambda calculus**: `ka`/`ce'u` as function/binder, beta-style application through `ckaji`, multiple/nested variable discussion.
- **semantical equivalences**: useful historical list, but it labels its own claims as mixed-status and contains corrected false proposals; its old `lo` existential equivalence is pre-xorlo and unsuitable now.
- **reduced logical form**, steps 1-8: normalizes argument order, prenex scope, and logical connections, but removes indicators/free modifiers and explicitly leaves several constructs unhandled; not safe as a semantic-preserving whole-language reduction.
- **BPFK Abstractors**: proposed typed paraphrases and a detailed `ce'u` account, with acknowledged unsettled abstractors.
- **BPFK sumtcita Formants**: `fi'o` formal paraphrases, operator scope, and an explicit warning that arbitrary modal operator semantics are lexically/vaguely determined.
- **BPFK gadri** and the gadri commentary: descriptions as `zo'e` plus restrictions, no default outer quantification, plural constants, and Skolem-dependence issues.
- **BPFK Non-logical Connectives**: formal constructors for joint reference, groups, sets, sequences, union, intersection, products, and respectively.
- **BPFK Pro-bridi / Utterance Pro-sumti**: discourse-level bridi identity and explicit text-versus-interpretation distinction.
- **Tsani's Interpretations: Abstractors**: ambitious lambda reductions of properties and some abstractors; useful hypotheses but personal/unofficial and not reliable as a standard source.

## Stress tests

### Conditional

Surface: `ganai broda gi brode`

Core:

```
Assert(If(Close(broda), Close(brode)))
```

Neither component is independently asserted.

### Shared quantified term across a connective

A single surface quantified term shared by two connected bridi must dominate the connection:

```
Some(bind=x,
     restrict=R(x),
     body=And(Close(P(1=x)), Close(Q(1=x))))
```

It must not become `And(Some(x,P(x)), Some(y,Q(y)))`, which permits two witnesses and loses cross-conjunct identity. Shared unquantified referents may instead be filled into both branches using the same `Ref` identity; unrelated omitted places remain branch-local.

### Quantification with dependent omissions

Surface: `ro mlatu cu jbena`

Illustrative core sketch, conditional on a zo'e/dependency policy:

```
Assert(
  All(
    bind = x,
    restrict = ProjectiveNonempty(Close(mlatu(1=x))),
    body = Close(jbena(1=x))
  )
)
```

The omitted parent/time/place slots become distinct contextual terms whose dependency constraints say they may depend on `x`; they must not be printed as loud explicit placeholders in the human format. Resolving that possibility as actual Skolem dependence is guskant's unofficial analysis, not a settled consequence of the short official `zo'e` definition.

### Property

Surface abstraction: `ka ce'u prami mi`

Core:

```
Ka(lambda x. Close(prami(1=x, 2=mi)))
```

The lambda is the property intension; `Ka(...)` forms the one-place selbri whose x1 is that property. The full sumti `lo ka ce'u prami mi` is `Lo(Ka(...))` and therefore has `Ref<Property>` type.

### Description over partially filled content

Surface: `lo klama be mi`

Core:

```
Lo(AsSelbri(klama(2=mi)))
```

The description constructor consumes the x1-focused relation. Its explicit function view is `LoFn(lambda x. Close(klama(1=x,2=mi)))`.

### Event modification

Surface sketch: “I go to the market using the car.”

Core:

```
Assert(
  ExistsEvent(lambda e.
    And(
      Close(klama(Event=e, 1=mi, 2=zarci)),
      Close(Instrument(e, car))
    )
  )
)
```

If the exact Lojban modal only supplies an underspecified `fi'o` relationship, keep the modal operator rather than invent `Instrument`.

### Reported utterance

Surface/content: Alice says `P`.

```
Assert(Close(cusku(1=alice, 2=ReifyProp(P), 3=bob, 4=speech)))
```

This asserts the saying event, not `P`.

### Current assertoric utterance with metadata

```
u : Ref<Utterance>
a := Assert(P)
Record(u, {
  Close(RealizesAct(u, ReifyAct(a))),
  Close(Speaker(u, alice)),
  Close(Addressee(u, bob)),
  Close(Medium(u, speech))
})
Perform(a)
```

The graph facts describe `u` at the transcript metadata layer; `Assert(P)` constructs its force/content and `Perform` supplies the use-level boundary. The document convention decides whether top-level acts are performed or merely recorded.

### Question

```
Ask(lambda x. Close(klama(1=x, 2=zarci)))
```

or a set of alternative closed bridi. It is not `Assert(Question(...))`, which would report a question rather than ask it.

### Command

```
Direct(addressee, Close(P(ko_places=addressee)))
```

The exact directive content theory can vary, but each surface `ko` is a place-filler for the addressee and the utterance carries directive force; this is not assertion of `P`.

## Recommended conceptual kernel

The best current candidate is:

```
Atom
Start(Relation)
Fill(Predication, Place, Value)
Lambda(parameters, body)
Apply(function, arguments)
CloseΓ(context, predication)
Act(force, typed_content)
Perform(act)
Record(utterance_token, metadata_propositions) -> TranscriptEntry
QuoteStruct(sequence) / QuoteOpaque(text)
```

with graph identity/binders, literals, scope handles/constraints, argument-opacity marks, and typed level crossings as structural necessities. `CloseΓ` is semantically explicit wherever a predication becomes formula content, although a human renderer can normally suppress it. `Assert(content)` always means `Act(Assertion, content)`; top-level performance is a separate stated document convention.

Everything else can share this application graph:

- `And`, `Or`, `Not`, `ForAll`, `Exists`, `Exactly`;
- `Lo`, `Le`, `La`;
- `Ka`, `Du'u`, `Nu`, other abstractors;
- `TanruCompose`, `ZeiCompose`, `Me`, `Moi`, conversions and scalar relation operators;
- modal operators;
- question/directive/expressive forces;
- event, sign, utterance, and discourse relations.

This is small enough to enable generic graph processing, sharing, multiple renderers, and beta-reduction/structural equivalence in signature-marked extensional positions. Its semantic sorts, opacity marks, scope operators, and named coercions remain rich enough not to erase distinctions merely for graph uniformity.

## Open design questions

1. Does the top-level document conventionally denote performed acts or merely a descriptive record? The semantics must say; the distinction cannot be inferred from graph shape.
2. How should unresolved scope be represented: nested lambdas only, MRS-like handles/constraints, or both resolved and underspecified forms?
3. Which description/ellipsis dependencies should be explicit in the graph even when hidden in the human renderer?
4. Which NU and indicator analyses are normative enough to canonicalize, and which must remain intrinsic named operators?
5. What typed attachment alternatives must an unresolved `fi'o` retain: host predication, proposition, or a lexically constrained subset?
6. Which lexical roots are eventive, and when is eventification introduced? Universal event slots are not assumed.
7. After `zi'o` removes a place, do user-facing effective place indices renumber while origin-place identities remain as provenance? The graph must represent both rather than silently reuse the base row.
8. Should intrinsic logical roots be mapped to dictionary aliases in rendering, or should PascalCase always signal metalanguage and keep lexical predicates lowercase?
9. Which existing jbotci/XML rulings survive this calculus? They are a valuable falsification corpus, not axioms: each must be rejustified against sources and the preservation criteria above.
