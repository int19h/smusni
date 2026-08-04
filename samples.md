# Human-readable smusni S-expression samples

These samples exercise the version-0 rules in [the specification](spec.md).
They are design specimens, not golden renderer expectations. A block labelled
“fragment” is intended to appear inside a complete document; every other block
is a complete `Smusni` datum.

The English glosses explain the represented distinction and are not claimed as
word-for-word translations.

## 1. Predication, closure, and assertion

`mi klama` assembles predicate content, closes its remaining defaultable places,
and then explicitly constructs an assertion act:

```lisp
(Smusni 0
  (Assert
    (klama Speaker)))
```

The missing destination, origin, route, and means are distinct contextual
defaults. They are not printed as repeated `zo'e` nodes. The event is local and
unshared, so `Close` and the event binder are both omitted by the canonical
rules.

Filling every numbered place would still not assert:

```lisp
(Smusni 0
  (Mention
    (klama Speaker This Speaker This This)))
```

Here the saturated predicate term is mentioned as a value. It is not coerced to
`Content` because `Mention` is polymorphic.

## 2. Current places, computed `At`, and `zi'o`

A literal skip uses a keyword. The plain value after `:2` fills current x3:

```lisp
(Smusni 0
  (Assert
    (klama :2 This Yonder)))
```

An actual place question uses computed `At` and no later plain operand:

```lisp
(Smusni 0
  (Ask
    (OpenQ
      (λ (($p (PlaceOf klama (Referents Entity))))
        (klama :5 This (At $p This))))))
```

`zi'o` removes a current numbered place. Surviving labels keep their visible
numbers and plain traversal skips the hole:

```lisp
(Smusni 0
  (Assert
    ((DropPlace klama 3)
      Speaker
      This
      This
      This)))
```

## 3. Source place conversion is eliminated

An ordinary source `se klama` application prints the base `klama` root with
base places filled. There is no `Se` node:

```lisp
(Smusni 0
  (Assert
    (klama :2 Speaker :1 This)))
```

A converted property is an ordinary lambda over the permuted base fill:

```lisp
(Smusni 0
  (Let (($destination-property
          (Fn ((Referents Entity)) Content)
          (λ (($x (Referents Entity)))
            (klama :2 $x))))
    (Mention $destination-property)))
```

If the converted binary relation itself escapes into an ordered function place,
it eta-expands:

```lisp
(λ (($new-x1 (Referents Entity))
    ($new-x2 (Referents Entity)))
  (tavla :2 $new-x1 :1 $new-x2))
```

That last block is a fragment. A place expecting a labelled `PredTerm` rather
than the displayed `Fn` cannot consume it and uses typed fallback.

## 4. Modals are predicates joined by `Joi`

A `sepi'o` modal shares the event of the main clause with a `pilno` predication:

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($e Eventuality))
        (Joi
          (klama Speaker This :Eventuality $e)
          (pilno :2 This $e))))))
```

Direct `fi'o pilno` uses the place map represented by that tag rather than
assuming the `sepi'o` map:

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($e Eventuality))
        (Joi
          (klama Speaker This :Eventuality $e)
          (pilno Speaker This $e))))))
```

A compound, negated tag retains its connector and negation:

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($e Eventuality))
        (Joi
          (klama Speaker :Eventuality $e)
          (∨
            (¬ (pilno :2 This $e))
            (mukti Now $e)))))))
```

There is no modal-valued `At`; arguments inside each modal predicate are normal
predicate fills.

A tense uses the same ordinary-predicate-plus-`Joi` machinery. Here `pu`
reduces to the standard `fi'o se purci` analysis, so the event is x1 of
`purci` and the utterance time is x2:

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($e Eventuality))
        (Joi
          (citka Speaker :Eventuality $e)
          (purci $e Now))))))
```

`mo'i ri'u` is not a generic motion flag. Once the graph identifies the motion
event and mover, the axial reduction uses the transparent `MotionVector`
helper, whose definition projects `muvdu` by deleting only the unrepresented
route place:

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($e Eventuality))
        (Joi
          (cadzu Speaker :Eventuality $e)
          (MotionVector
            $e
            Speaker
            (λ (($to (Referents Entity))
                ($from (Referents Entity)))
              (pritu $to $from Speaker))))))))
```

This specimen represents the walking event itself as the motion and identifies
the walker as its mover. Neither follows mechanically from lexical x1: a
separate concurrent motion would have its own event plus `cabna`, and a
result-dependent reading would use the represented result relation. Other
`mo'i` directions retain and delete different lexical places, as specified by
their reduction rows.

Sticky `ki` is not a discourse-state node in the output. For source
`puki ... .i ...`, the resolved `pu` relation is simply repeated at each
inheriting event:

```lisp
(Smusni 0
  (Do
    (Assert
      (∃
        (λ (($first Eventuality))
          (Joi
            (klama Speaker This :Eventuality $first)
            (purci $first Now)))))
    (Assert
      (∃
        (λ (($second Eventuality))
          (Joi
            (batci This That :Eventuality $second)
            (purci $second Now)))))))
```

A later explicit tense composes onto the inherited path in source order, just
as an explicitly repeated tense would.

## 5. Explicit `Close` for shared predicate terms

An inline known-row predicate closes implicitly at `Assert`:

```lisp
(Smusni 0
  (Assert
    (melbi This)))
```

The same predicate term prints `Close` once it has identity of its own:

```lisp
(Smusni 0
  (Let (($description
          (PredTerm
            (Row
              (2 (Referents Entity))
              (3 (Referents Entity))
              (4 (Referents Entity))))
          (melbi This)))
    (Do
      (Mention $description)
      (Assert (Close $description)))))
```

A nondefaultable higher-order gap cannot be silently closed:

```lisp
(Smusni 0
  (Assert
    (Fallback Content "smusni.close.nondefaultable-place"
      (Object %1 "PredicateTerm"
        (Field "root" (RawAtom "higher-order-root"))))))
```

An elided value whose graph scope may depend on `$p` cannot disappear into
`Close`; its dependency set is explicit. This is a fragment inside the binder
for `$p`:

```lisp
(Bind (($destination (Referents Entity) (Context $p)))
  (Assert
    (klama Speaker $destination)))
```

## 6. Dynamic accessibility across connectives

A successful conjunction can introduce a reference for its right operand and
the later discourse:

```lisp
(Smusni 0
  (Bind (($cat (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              (mlatu $x)))))
    (Do
      (Assert
        (∧
          (jbena $cat)
          (blabi $cat)))
      (Assert
        (ciska $cat)))))
```

This specimen assumes the graph explicitly owns one cross-act identity. Its
`Bind` is at that legal common host, so lexical scope and dynamic accessibility
both include the two acts; ordinary default raising would stop at a force
boundary.

An ordinary xorlo reference is fixed for the force segment, so it scopes
outside visible negation:

```lisp
(Smusni 0
  (Bind (($cat (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              (mlatu $x)))))
    (Assert
      (¬
        (jbena $cat)))))
```

By contrast, the individual variable introduced inside this negated
quantifier is both lexically and dynamically local:

```lisp
(Smusni 0
  (Assert
    (¬
      (∃
        (λ (($x Entity))
          (∧
            (mlatu $x)
            (jbena $x)))))))
```

An implication passes the successful antecedent context to its consequent.
When the graph says both operands use the same identity, one lexical binder
must span both. This donkey-style normalization uses an explicit quantifier:

```lisp
(Smusni 0
  (Assert
    (∀
      (λ (($x Entity))
        (→
          (∧
            (mlatu $x)
            (jbena $x))
          (ciska $x))))))
```

This is not a same-type `Context` lookup. If the consequent instead contains a
genuinely new contextual choice, it receives its own `Bind`; if coreference is
required but the graph does not identify the antecedent, the affected
conditional uses typed fallback.

## 7. `lo`, `le`, and `la` are compositional references

`lo mlatu` uses the veridical property directly:

```lisp
(Smusni 0
  (Bind (($cat (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              (mlatu $x)))))
    (Assert
      (blabi $cat))))
```

There is no `Lo` constructor.

A `le` description composes the speaker-description relation rather than
asserting that the referent is extensionally a cat:

```lisp
(Smusni 0
  (Bind (($described (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              (skicu Speaker $x Audience
                (λ (($y (Referents Entity)))
                  (mlatu $y)))))))
    (Assert
      (blabi $described))))
```

A name description uses a sign and the graph's naming relation:

```lisp
(Smusni 0
  (Bind (($named (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              (Named "alis" $x)))))
    (Assert
      (klama $named))))
```

`Typical` is retained because typical reference is not ordinary unique or
indefinite selection:

```lisp
(Bind (($typical-cat (Referents Entity)
        (Typical
          (λ (($x (Referents Entity)))
            (mlatu $x)))))
  body)
```

The last block is a fragment.

## 8. Relative clauses are ordinary composition

A restrictive `poi` contributes its predicate inside the reference property:

```lisp
(Smusni 0
  (Bind (($white-cat (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              (∧
                (mlatu $x)
                (blabi $x))))))
    (Assert
      (jbena $white-cat))))
```

A descriptive `voi` selects a subreference of its host and uses the transparent
prelude helper `DescribedAs` rather than asserting the clause property. Its
normative definition removes `skicu` x3; no audience is fabricated:

```lisp
(Smusni 0
  (Bind (($base (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              (skicu Speaker $x Audience
                (λ (($y (Referents Entity)))
                  (gerku $y)))))))
    (Bind (($thing (Referents Entity)
            (Refer
              (λ (($x (Referents Entity)))
                (∧
                  (Among $x $base)
                  (DescribedAs Speaker $x
                    (λ (($y (Referents Entity)))
                      (blabi $y))))))))
      (Assert
        (jbena $thing)))))
```

A nonrestrictive `noi` is supplementary content:

```lisp
(Smusni 0
  (Bind (($dog (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              (gerku $x)))))
    (Assert
      (Supplement
        (melbi $dog)
        (blabi $dog)))))
```

Multiple clauses retain their connector rather than a list of `Relative`
records:

```lisp
(λ (($x (Referents Entity)))
  (∧
    (gerku $x)
    (∨
      (blabi $x)
      (bunre $x))
    (citka $x $food)))
```

A graph-owned `goi` alias becomes identity sharing:

```lisp
(Let (($friend (Referents Entity) $antecedent))
  (Assert
    (tavla Speaker $friend)))
```

The final two blocks are fragments.

## 9. Importing universal quantification

Source `ro` uses the importing `Every` constructor:

```lisp
(Smusni 0
  (Assert
    ((Every
       (λ (($x Entity))
         (mlatu $x)))
     (λ (($x Entity))
       (jbena $x)))))
```

Its effect-level expansion is:

```lisp
(Presuppose
  (∃
    (λ (($x Entity))
      (mlatu $x)))
  (∀
    (λ (($x Entity))
      (→
        (mlatu $x)
        (jbena $x)))))
```

The expansion is a fragment and shows why the nonemptiness commitment projects
through an outer negation. There is no `(Import Projective)` record and no
unstated import choice.

The mathematical nonimporting universal remains available directly:

```lisp
(Smusni 0
  (Assert
    (∀
      (λ (($x Entity))
        (→
          (mlatu $x)
          (jbena $x))))))
```

## 10. Sets, plurality, and exact cardinality

An outer exact count is ordinary cardinality of singular satisfiers:

```lisp
(Smusni 0
  (Assert
    (= 3
      (Card
        (SetOf
          (λ (($x Entity))
            (∧
              (gerku $x)
              (bajra $x))))))))
```

One fixed plural reference can instead be constrained through a singular-member
set without identifying the reference with that set:

```lisp
(Smusni 0
  (Bind (($dogs (Referents Entity)
          (Refer
            (λ (($r (Referents Entity)))
              (∧
                (gerku $r)
                (= 3
                  (Card
                    (SetOf
                      (λ (($x Entity))
                        (Among $x $r))))))))))
    (Assert
      (bajra $dogs))))
```

`Combine` is plural reference formation, not set union:

```lisp
(Assert
  (tavla Speaker
    (Combine $alis $bob)))
```

`ce'o` constructs an ordered list of reference values, so its element type is
explicit when the list is empty and inferred here:

```lisp
(List $alis $bob $carol)
```

The last two blocks are fragments.

## 11. Generalized quantifier witnesses

The `GQ`, its nuclear-scope function, and their application each have stable
identity. A witness is available only after that same application succeeds:

```lisp
(Smusni 0
  (Let (($gq (GQ Entity)
          (Exactly 3
            (λ (($x Entity))
              (gerku $x)))))
    (Let (($scope (Fn (Entity) Content)
            (λ (($x Entity))
              (bajra $x))))
      (Let (($run Content ($gq $scope)))
        (Do
          (Assert $run)
          (Bind (($dogs (Referents Entity)
                  (Witnesses $gq $scope)))
            (Assert
              (tatpi $dogs))))))))
```

This is not equivalent to counting members of `$dogs` after the fact. The full
quantifier function, scope function, and success identity remain explicit.

The following is deliberately invalid and therefore falls back:

```lisp
(Fallback (Referents Entity) "smusni.witness.before-success"
  (Object %1 "WitnessRequest"
    (Field "gq" (RawAtom "$gq"))
    (Field "scope" (RawAtom "$scope"))))
```

## 12. Simultaneous termsets

Two generalized quantifiers with one polyadic nuclear scope reduce to
mutually constrained, coordinate-exhaustive sets:

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($dogs (Set Entity))
          ($people (Set Entity)))
        (∧
          (= (Card $dogs) 3)
          (= (Card $people) 2)
          (∀
            (λ (($dog Entity))
              (↔
                (∈ $dog $dogs)
                (∧
                  (gerku $dog)
                  (∀
                    (λ (($person Entity))
                      (→
                        (∈ $person $people)
                        (nelci $dog $person))))))))
          (∀
            (λ (($person Entity))
              (↔
                (∈ $person $people)
                (∧
                  (prenu $person)
                  (∀
                    (λ (($dog Entity))
                      (→
                        (∈ $dog $dogs)
                        (nelci $dog $person)))))))))))))
```

Nesting `$dogs` around `$people` or vice versa would impose an order that can
change generalized-quantifier truth conditions. An input graph that has already
lost the coequal structure cannot be repaired heuristically:

```lisp
(Smusni 0
  (Assert
    (Fallback Content "smusni.termset.equal-scope-lost"
      (Object %1 "OrderedQuantifierNest"))))
```

## 13. Lambdas, abstractions, and event facets

A property abstraction needs only `λ`:

```lisp
(Smusni 0
  (Mention
    (λ (($x (Referents Entity)))
      (Close
        (melbi $x)))))
```

An event abstraction is a reference computation whose property shares the event
with all facets:

```lisp
(Smusni 0
  (Bind (($event (Referents Eventuality)
          (Refer
            (λ (($events (Referents Eventuality)))
              (∧
                (klama Speaker :Eventuality $events)
                (purci $events Now)
                (zvati $events Here))))))
    (Mention $event)))
```

The temporal and spatial facets are ordinary lowercase predicates of the same
event reference; no event-facet record or opaque PascalCase name is needed.

Reification is an explicit level crossing:

```lisp
(Smusni 0
  (Mention
    (Reify
      (klama Speaker))))
```

The inline predicate closes because `Reify` expects `Content`. An explicit
semantic scale fills the full-arity crossing:

```lisp
(Smusni 0
  (Mention
    (Measure
      (klama Speaker)
      DistanceScale)))
```

## 14. First-class acts and utterance facts

An act can be bound, targeted, and later performed:

```lisp
(Smusni 0
  (Let (($prior-act (Act Assertion)
          (Assert
            (melbi This))))
    (Let (($act (Act Assertion)
            (Assert
              (klama Speaker))))
      (Do
        (Express
          (Contrast :2 $act :3 $prior-act))
        (Perform $act)))))
```

There is no `TargetFocus`; the target is statically `Act<Assertion>`.

An utterance with metadata and two co-realized acts keeps its token:

```lisp
(Smusni 0
  (Let (($prior-act (Act Assertion)
          (Assert
            (melbi This))))
    (Let (($current-act (Act Assertion)
            (Assert
              (klama Speaker))))
      (Utterance (($u UtteranceToken))
        (SpeakerOf $u Speaker)
        (AudienceOf $u Audience)
        (Realizes $u $current-act)
        (Realizes $u
          (Express
            (Contrast :2 $current-act :3 $prior-act)))))))
```

The contrast targets the exact first-class act values. Facts about `$u` are
analyzer facts, not extra speaker assertions; if an indicator instead targets
the utterance token, the same `$u` can be passed to its registered relation.

An actual relation that Alice utters something can itself be asserted; this
fragment assumes both referents are bound by its surrounding transcript:

```lisp
(Assert
  (Utters $alis $utterance))
```

That reports an utterance relation; it does not perform `$utterance`.

## 15. Direct, embedded, and answered questions

A polar direct question:

```lisp
(Smusni 0
  (Ask
    (Polar
      (klama Speaker))))
```

An open argument question:

```lisp
(Smusni 0
  (Ask
    (OpenQ
      (λ (($x (Referents Entity)))
        (klama $x)))))
```

A relation question can bind an open-row predicate term when the answer's full
place structure is not yet known:

```lisp
(Smusni 0
  (Ask
    (OpenQ
      (λ (($relation
            (PredTerm
              (Row
                (1 (Referents Entity))
                Open))))
        ($relation This)))))
```

A two-variable question retains an ordered heterogeneous answer tuple:

```lisp
(Smusni 0
  (Ask
    (OpenQ
      (λ (($who (Referents Entity))
          ($where (Referents Location)))
        (klama $who $where)))))
```

An indirect question is an inert object:

```lisp
(Smusni 0
  (Mention
    (QuestionOf
      (OpenQ
        (λ (($x (Referents Entity)))
          (cortu $x))))))
```

Positive polar answer content says which answer was selected:

```lisp
(Smusni 0
  (Assert
    (Answer
      (Polar
        (klama Speaker))
      (PolarAnswer Yes))))
```

An embedded `kau`-style answerhood commitment without a graph-recorded tuple
uses an honest contextual profile:

```lisp
(Smusni 0
  (Assert
    (Answer
      (OpenQ
        (λ (($x (Referents Entity)))
          (cortu $x)))
      (ContextualAnswer Exhaustive))))
```

It does not claim the selected `$x` is present in the graph.

## 16. De-re, de-dicto, nested, and opaque reference

An extensional graph-owned host can place a reference outside negation:

```lisp
(Smusni 0
  (Bind (($book (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              (cukta $x)))))
    (Assert
      (¬
        (nelci Speaker $book)))))
```

Inside an intensional desire place, a de-dicto reference remains local:

```lisp
(Smusni 0
  (Assert
    (djica Speaker
      (Bind (($wanted (Referents Eventuality)
              (Refer
                (λ (($events (Referents Eventuality)))
                  (Bind (($car (Referents Entity)
                          (Refer
                            (λ (($x (Referents Entity)))
                              (karce $x)))))
                    (pilno Speaker $car :Eventuality $events))))))
        $wanted))))
```

An explicit legal de-re owner may move `$car` outside that boundary:

```lisp
(Smusni 0
  (Bind (($car (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              (karce $x)))))
    (Assert
      (djica Speaker
        (Bind (($wanted (Referents Eventuality)
                (Refer
                  (λ (($events (Referents Eventuality)))
                    (pilno Speaker $car :Eventuality $events)))))
          $wanted)))))
```

A nested description remains inside the outer description property unless its
own owner says otherwise:

```lisp
(Smusni 0
  (Bind (($driver (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              (Bind (($car (Referents Entity)
                      (Refer
                        (λ (($y (Referents Entity)))
                          (karce $y)))))
                (pilno $x $car))))))
    (Assert
      (klama $driver))))
```

An `Opaque` lexical edge cannot be raised; a contradictory escaping owner is a
typed local fallback rather than an assumed extensional reading.

## 17. Respectively, collections, and math

Respectively is tuple/list construction plus typed `ZipWith`:

```lisp
(Smusni 0
  (Assert
    (ZipWith
      (λ (($speaker (Referents Entity))
          ($listener (Referents Entity)))
        (tavla $speaker $listener))
      (List Speaker Audience)
      (List Audience Speaker))))
```

Set and interval operations use conventional mathematical notation:

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($x Entity))
        (∈ $x
          (∩
            (SetOf
              (λ (($y Entity))
                (gerku $y)))
            (SetOf
              (λ (($y Entity))
                (blabi $y)))))))))
```

```lisp
(Smusni 0
  (Mention
    (Interval 0 1 Closed Open)))
```

An unsupported questioned math operator remains typed fallback; it is not
printed as an arbitrary PascalCase atom.

## 18. Signs and quotation

Opaque quotation preserves text without interpreting it:

```lisp
(Smusni 0
  (Mention
    (OpaqueQuote "mi klama")))
```

A structured quotation can mention a complete transcript entry without
performing it:

```lisp
(Smusni 0
  (Let (($entry TranscriptEntry
          (Utterance (($u UtteranceToken))
            (SpeakerOf $u Speaker)
            (Realizes $u
              (Assert
                (klama Speaker))))))
    (Mention
      (StructuredQuote $entry))))
```

A sign token can have text and denotation facts without conflating either with
interpretation:

```lisp
(Smusni 0
  (Mention
    (Sign (($s (SignToken Sentence)))
      (TextOf $s "mi klama")
      (Denotes $s
        (Reify
          (klama Speaker))))))
```

When interpretation is represented, the result family is explicit:

```lisp
(InterpretContent $sentence-sign)
(InterpretAct $performative-sign)
```

Those two lines are fragments.

## 19. Recursion and identity

Mutually recursive inert functions use `LetRec`:

```lisp
(Smusni 0
  (LetRec
    (($even (Fn (Number) Content)
       (λ (($n Number))
         (∨
           (= $n 0)
           (∧
             (> $n 0)
             ($odd (− $n 1))))))
     ($odd (Fn (Number) Content)
       (λ (($n Number))
         (∧
           (> $n 0)
           ($even (− $n 1))))))
    (Assert
      ($even 4))))
```

The example demonstrates shape rather than a Lojban source sentence. Recursive
effectful initializers are not legal `LetRec` and use fallback.

## 20. Fallback and diagnostic separation

A local unsupported value preserves its type, reason, fields, identity, and
sharing:

```lisp
(Smusni 0
  (Assert
    (Fallback Content "smusni.unsupported.quantity-comparison"
      (Object %1 "QuantityComparison"
        (Field "left"
          (Object %2 "Quantity"
            (Field "kind" (RawAtom "Approximate"))))
        (Field "right" (Ref %2))))))
```

If the renderer cannot establish a typed performable root, it preserves the
whole graph structurally:

```lisp
(Smusni 0
  (TypedGraph "Performable"
    (Object %1 "SemanticGraph"
      (Field "root" (Ref %2))
      (Field "objects"
        (RawList
          (Object %2 "UnknownRoot"))))))
```

Neither document contains a `Warning` node. The corresponding stable diagnostic
code and human message are written to stderr in the normal `gentufa` diagnostic
format.

## 21. Word cards

Requested dictionary cards occupy the optional third document slot:

```lisp
(Smusni 0
  (Assert
    (klama Speaker))
  (Words
    (Word klama "x1 goes to x2 from x3 via x4 using x5")))
```

The cards neither scope over nor modify the semantic body.
