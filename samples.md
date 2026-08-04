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
    (pilno :2 This Now)))
```

An actual place question uses computed `At` and no later plain operand:

```lisp
(Smusni 0
  (Ask
    (OpenQ
      (λ (($p (PlaceOf klama (Referents Entity))))
        (klama (At $p This) :5 This)))))
```

`zi'o` removes a current numbered place. Surviving labels keep their visible
numbers and plain traversal skips the hole:

```lisp
(Smusni 0
  (Assert
    ((DropPlace klama 3)
      Speaker
      This
      :4 This
      :5 This)))
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
    (∃ (($e Eventuality))
      (Joi
        (klama Speaker :2 This :Eventuality $e)
        (pilno :2 This :3 $e)))))
```

Direct `fi'o pilno` uses the place map represented by that tag rather than
assuming the `sepi'o` map:

```lisp
(Smusni 0
  (Assert
    (∃ (($e Eventuality))
      (Joi
        (klama Speaker :2 This :Eventuality $e)
        (pilno Speaker :2 This :3 $e)))))
```

A compound, negated tag retains its connector and negation:

```lisp
(Smusni 0
  (Assert
    (∃ (($e Eventuality))
      (Joi
        (klama Speaker :Eventuality $e)
        (∨
          (¬ (pilno :2 This :3 $e))
          (mukti Now $e))))))
```

There is no modal-valued `At`; arguments inside each modal predicate are normal
predicate fills.

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
  (Let (($description (PredTerm (Row)) (melbi This)))
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

The `Bind` is at the least common legal host, so its lexical scope and its
dynamic accessibility both include the two acts.

Negation traps an ordinary introduction:

```lisp
(Smusni 0
  (Assert
    (¬
      (Bind (($cat (Referents Entity)
              (Refer
                (λ (($x (Referents Entity)))
                  (mlatu $x)))))
        (jbena $cat)))))
```

Using `$cat` after this act would be ill-scoped unless the graph supplied an
explicit fixed/de-re identity.

An implication passes the successful antecedent context to its consequent.
The consequent can therefore perform an ordinary contextual resolution, but
the resolved value does not escape the conditional:

```lisp
(Smusni 0
  (Assert
    (→
      (Bind (($x (Referents Entity)
              (Refer
                (λ (($r (Referents Entity)))
                  (mlatu $r)))))
        (jbena $x))
      (Bind (($x (Referents Entity) Context))
        (ciska $x)))))
```

`Context` in the consequent is evaluated against the antecedent's successful
output context. A graph-fixed reference whose lexical identity must span both
branches instead binds at a legal surrounding host.

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
              (skicu Speaker $x :4
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
              (cmene (NameSign "alis") $x)))))
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

A descriptive `voi` uses `skicu` with its audience place deleted. After
`DropPlace` removes current place 3, plain traversal fills original places 1,
2, and 4:

```lisp
(Smusni 0
  (Bind (($thing (Referents Entity)
          (Refer
            (λ (($x (Referents Entity)))
              ((DropPlace skicu 3) Speaker $x
                (λ (($y (Referents Entity)))
                  (blabi $y)))))))
    (Assert
      (jbena $thing))))
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
  (∃ (($x Entity))
    (mlatu $x))
  (∀ (($x Entity))
    (→
      (mlatu $x)
      (jbena $x))))
```

The expansion is a fragment and shows why the nonemptiness commitment projects
through an outer negation. There is no `(Import Projective)` record and no
unstated import choice.

The mathematical nonimporting universal remains available directly:

```lisp
(Smusni 0
  (Assert
    (∀ (($x Entity))
      (→
        (mlatu $x)
        (jbena $x)))))
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

The quantified content has a stable identity; its witness is available only
after that same content succeeds:

```lisp
(Smusni 0
  (Let (($q (QuantifiedContent Entity)
          ((Exactly 3
             (λ (($x Entity))
               (gerku $x)))
           (λ (($x Entity))
             (bajra $x)))))
    (Do
      (Assert $q)
      (Bind (($dogs (Referents Entity) (Witnesses $q)))
        (Assert
          (tatpi $dogs))))))
```

This is not equivalent to counting members of `$dogs` after the fact. The full
restrictor, scope, and success identity remain in `$q`.

The following is deliberately invalid and therefore falls back:

```lisp
(Fallback (Referents Entity) "smusni.witness.before-success"
  (Object %1 "WitnessRequest"
    (Field "quantifiedContent" (RawAtom "$q"))))
```

## 12. Simultaneous termsets

Two generalized quantifiers with one polyadic nuclear scope remain coequal:

```lisp
(Smusni 0
  (Let (($dogs (GQ Entity)
          (Exactly 3
            (λ (($x Entity))
              (gerku $x)))))
    (Let (($people (GQ Entity)
            (Exactly 2
              (λ (($y Entity))
                (prenu $y)))))
      (Assert
        (PolyQuant
          (Tuple $dogs $people)
          (λ (($dog Entity) ($person Entity))
            (nelci $dog $person)))))))
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
      (melbi $x))))
```

An event abstraction shares the event variable with all facets:

```lisp
(Smusni 0
  (Mention
    (λ (($e Eventuality))
      (∧
        (klama Speaker :Eventuality $e)
        (purci $e)
        (LongDuration $e)))))
```

`LongDuration` stands for a registered generated event-facet predicate, not an
open-ended PascalCase spelling.

Reification is an explicit level crossing:

```lisp
(Smusni 0
  (Mention
    (Reify
      (klama Speaker))))
```

The inline predicate closes because `Reify` expects `Content`. An abstraction
with an extra semantic scale place selects a fixed-arity operator:

```lisp
(Smusni 0
  (Mention
    (MeasureOn
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
          (Contrast $act $prior-act))
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
            (Contrast $current-act $prior-act)))))))
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

A two-variable question retains an ordered heterogeneous answer tuple:

```lisp
(Smusni 0
  (Ask
    (OpenQ
      (λ (($who (Referents Entity))
          ($where (Referents Place)))
        (klama $who :2 $where)))))
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
      (EventOf
        (Bind (($car (Referents Entity)
                (Refer
                  (λ (($x (Referents Entity)))
                    (karce $x)))))
          (pilno Speaker $car))))))
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
        (EventOf
          (pilno Speaker $car))))))
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
    (∃ (($x Entity))
      (∈ $x
        (∩
          (SetOf
            (λ (($y Entity))
              (gerku $y)))
          (SetOf
            (λ (($y Entity))
              (blabi $y))))))))
```

```lisp
(Smusni 0
  (Mention
    (Interval
      (Closed 0)
      (Open 1))))
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

A structured quotation can refer to a bound utterance token:

```lisp
(Smusni 0
  (Utterance (($u UtteranceToken))
    (SpeakerOf $u Speaker)
    (Realizes $u
      (Assert
        (klama Speaker)))
    (LocutionOf $u
      (StructuredQuote $u))))
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
    (($even (Fn (Natural) Content)
       (λ (($n Natural))
         (∨
           (= $n 0)
           (∧
             (> $n 0)
             ($odd (− $n 1))))))
     ($odd (Fn (Natural) Content)
       (λ (($n Natural))
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
