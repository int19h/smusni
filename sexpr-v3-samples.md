# Experimental smusni S-expression samples, draft 7

These are design probes, not output expectations. They exercise the reduced
tree shape before implementation. After implementation they will be replaced or
supplemented by renderer-generated examples and a corpus report.

## 1. Assertion is separate from predication

```lojban
mi klama
```

```lisp
(Smusni 0
  (Assert
    (klama Speaker)))
```

`klama`, `(klama Speaker)`, and the fully filled predicate term are inert.
`Assert` constructs the act; the top-level document performs it.
At this closure site the local, unshared, facetless event binder is implicit;
the exact elaboration is `(Assert (∃ (λ (($e Eventuality)) (klama Speaker
:Eventuality $e))))`.

## 2. Non-next and deleted places

```lojban
mi klama fu lo karce
```

```lisp
(Smusni 0
  (Assert
    (klama Speaker
      :5 (Refer karce))))
```

```lojban
mi dunda zi'o ti
```

```lisp
(Smusni 0
  (Assert
    ((DropPlace dunda 2) Speaker This)))
```

## 3. `sepi'o` is `.i joi`, not a modal record

```lojban
mi klama sepi'o lo karce
```

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($e Eventuality))
        (Joi
          (klama Speaker :Eventuality $e)
          (pilno :2 (Refer karce) $e))))))
```

The first hidden `pilno` place forces `:2`; after that, the plain `$e` fills
x3. The renderer did not infer that purpose link from `Joi`: the graph already
records the builder's closed, dictionary-grounded `pilno` x3 strengthening for
the BPFK unary bridi-operator reading.

## 4. Direct `fi'o pilno` has a different place map

```lojban
mi klama fi'o pilno lo karce
```

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($e Eventuality))
        (Joi
          (klama Speaker :Eventuality $e)
          (pilno (Refer karce) :3 $e))))))
```

The car fills x1. The hidden x2 forces the event fill to be labelled x3.

## 5. Elided and arbitrary modal payloads

```lojban
mi klama sepi'o
```

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($e Eventuality))
        (Joi
          (klama Speaker :Eventuality $e)
          (pilno :3 $e))))))
```

```lojban
mi klama fi'o broda lo karce
```

```lisp
(Smusni 0
  (Assert
    (Joi
      (klama Speaker)
      (broda (Refer karce)))))
```

The arbitrary case invents no event link. The binary BPFK paraphrase guarantees
only the inextricable, contextually unspecified `Joi` connection; a more
specific fill prints only when it is already recorded semantic data.

## 6. Restricted universal import is an explicit effect

```lojban
ro mlatu cu jbena
```

```lisp
(Smusni 0
  (Assert
    (Presuppose
      (∃
        (λ (($y Entity))
          (mlatu $y)))
      (∀
        (λ (($x Entity))
          (→
            (mlatu $x)
            (jbena $x)))))))
```

`∀` remains classical. The first operand of `Presuppose` is the projective
non-emptiness commitment; without `Presuppose`, no domain import is implied.

## 7. Shared contextual identity and higher-order dependence

```lojban
ganai broda gi brode .a brodi
```

```lisp
(Smusni 0
  (Let (($shared (Referents Entity) Context))
    (Assert
      (→
        broda
        (∨
          (brode $shared)
          (brodi $shared))))))
```

Semantic warnings are collected separately and do not occur in this datum.

A shared contextual value which may vary with `$x` has a function type:

```lisp
(Let (($z (Fn Entity (RefComp (Referents Entity))) Context))
  (∀
    (λ (($x Entity))
      (broda $x ($z $x)))))
```

## 8. A defective graph is not silently repaired

The grammatical Lojban `ganai da prenu gi da melbi` binds `da` over the whole
prenexless sentence and is **not** an example of this defect. If an imported or
partially built graph nevertheless retains a use outside its recorded binder,
the renderer emits a local `IllScoped`/`Unbound` marker when it can preserve the
surrounding tree and collects a semantic error. If not, it uses the typed
structural fallback. It does not move the quantifier or pretend the variable is
valid. The following is therefore a deliberately defective graph shape, not an
expected rendering of that Lojban sentence:

```lisp
(Smusni 0
  (Assert
    (→
      (∃
        (λ (($x Entity))
          (prenu $x)))
      (melbi (Unbound $x Entity)))))
```

## 9. Property abstractions are functions

```lojban
lo ka ce'u prami mi
```

```lisp
(Smusni 0
  (Mention
    (λ (($x (Referents Entity)))
      (prami $x Speaker))))
```

Two distinct `ce'u` occurrences would produce a two-argument lambda. No `Ka`
record or redundant `Refer` remains in the common value form.

## 10. Event abstractions are event properties

```lojban
mi djica lo nu mi cilre
```

```lisp
(Smusni 0
  (Assert
    (djica Speaker
      (Refer
        (λ (($e (Referents Eventuality)))
          (cilre Speaker
            :Eventuality $e))))))
```

The abstraction is inert because it is an argument value, not because a `Mode`
field says so. The required relation-place policy table assigns the `djica`
argument an `Intensional` boundary before this normal form is licensed, so the
inline `Refer` binds in that local argument computation unless the graph
explicitly marks it de re. Until that generated table is built and verified,
the current relation spelling alone is not evidence for the policy.

The extra abstraction places of `pu'u` and `zu'o` are not lost in an event-sort
annotation:

```lisp
(Measure (Close broda) $scale)
(ProcessOf (Close broda) $stages)
(ActivityOf (Close brode) $repeated-actions)
```

Here `$scale` has type `Referents<Scale>`, not a raw literal. The corresponding
second operands for `li'i`, `si'o`, and `su'u` are likewise preserved; all six
are omitted only when the source/model omits them.

## 11. `poi` is a veridical subreference restriction

```lojban
le gerku poi blabi cu melbi
```

```lisp
(Smusni 0
  (Let (($base (Referents Entity) Context))
    (Assert
      (Supplement
        (melbi
          (Refer
            (λ (($r (Referents Entity)))
              (∧
                (Among $r $base)
                (blabi $r)))))
        (skicu Speaker $base Audience
          (λ (($r (Referents Entity)))
            (gerku $r)))))))
```

`$base` is the contextual reference supplied by source `le`. Its
speaker-description is the `skicu` supplement. The ordinary `blabi` condition
commits the contextually supplied subreference to whiteness without forcing
individual distribution. It does not entail that the selected reference is the
maximal white subset. Because it is descriptive material inside `Refer`, it is backgrounded rather than
part of the containing `melbi` assertion's at-issue nucleus.

## 12. `voi` is a description predication

```lojban
le gerku voi blabi cu melbi
```

```lisp
(Smusni 0
  (Let (($base (Referents Entity) Context))
    (Assert
      (Supplement
        (melbi
          (Refer
            (λ (($r (Referents Entity)))
              (∧
                (Among $r $base)
                (DescribedAs Speaker $r
                  (λ (($s (Referents Entity)))
                    (blabi $s)))))))
        (skicu Speaker $base Audience
          (λ (($r (Referents Entity)))
            (gerku $r)))))))
```

Nothing asserts that `$r` is white. The asserted characterization is that the
speaker describes it by the white property. `DescribedAs` has the builder's
actual three-place order; no audience is invented. The separate four-place
`skicu` is the base dog-description supplement.

## 13. `noi` is supplementary content

```lojban
lo cukta noi mi nelci ke'a cu melbi
```

```lisp
(Smusni 0
  (Let (($book (Referents Entity) (Refer cukta)))
    (Assert
      (Supplement
        (melbi $book)
        (nelci Speaker $book)))))
```

The restrictive condition in sample 11 is conjoined inside a selecting
property. Here the description is bound first and the incidental predication is
a `Supplement` about that first-class referent. It stays at the narrowest scope
that contains `$book`; it is not a relative-clause or utterance-metadata record.

## 14. Tanru remain honestly vague

```lojban
ti blanu zdani
```

```lisp
(Smusni 0
  (Assert
    ((Tanru blanu zdani) This)))
```

`Tanru` preserves surface modifier/head order without asserting the `OfKind`
reading.

## 15. Event facets are predications

```lojban
mi pu klama lo zarci
```

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($e Eventuality))
        (∧
          (klama Speaker (Refer zarci)
            :Eventuality $e)
          (purci $e Now))))))
```

`purci` is used only after its lexical mapping and place order are verified. A
facet without an exact dictionary root is still an ordinary PascalCase
predicate over `$e`, not `(Facet ...)`.

## 16. Facets on described events stay inside the event property

```lojban
mi djica lo nu mi pu cilre
```

```lisp
(Smusni 0
  (Assert
    (∃
      (λ (($want Eventuality))
        (djica Speaker
          (Refer
            (λ (($learning (Referents Eventuality)))
              (∧
                (cilre Speaker
                  :Eventuality $learning)
                (purci $learning $want))))
          :Eventuality $want)))))
```

The explicit outer `$want` is required here because it is shared by the
`djica` event fill and the embedded `purci` anchor. In sample 10 the outer event
has no such visible property or external use, so ordinary closure may keep its
event binder implicit.

## 17. Cardinality is ordinary mathematics

```lojban
su'o ci mlatu cu jbena
```

```lisp
(Smusni 0
  (Assert
    (≥
      (Card
        (λ (($x Entity))
          (∧
            (mlatu $x)
            (jbena $x))))
      3)))
```

No `Cardinality`, `Quantity`, `Form`, `Scale`, or `ValueText` field node is
needed for this cardinal count-scale case.

### Inner count constrains one fixed reference

```lojban
lo ci gerku cu blabi
```

```lisp
(Smusni 0
  (Assert
    (blabi
      (Refer (Counted (Exactly 3) gerku)))))
```

`Counted` is inside `Refer`; it applies the `Exactly` cardinal generalized quantifier to
the reference's singular members and does not quantify the containing bridi.
Its fully reduced property is:

```lisp
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

By the `Refer` elaboration, both doghood and the inner count are descriptive
`Supplement` content about the fixed contextual reference; the host assertion
asks only whether that reference is white.

A non-exact inner quantifier has the same higher-order shape rather than a new
record:

```lisp
; lo su'o ci gerku
(Refer (Counted (AtLeast 3) gerku))
```

Universal inner quantification is maximal reference, not `Counted Every`:

```lisp
; lo ro gerku
(Refer
  (λ (($r (Referents Entity)))
    (∧
      (gerku $r)
      (∀ (λ (($x Entity))
        (→ (gerku $x) (Among $x $r)))))))
```

### Outer count is distributive cardinality

```lojban
re le gerku cu blabi
```

```lisp
(Smusni 0
  (Let (($dogs (Referents Entity)
          (Refer (skicu Speaker :3 Audience :4 gerku))))
    (Assert
      (=
        (Card
          (λ (($x Entity))
            (∧
              (Among $x $dogs)
              (blabi $x))))
        2))))
```

The selected `$dogs` are one fixed contextual reference; the outer `re`
counts singular members that individually satisfy the bridi.

### Exported witnesses retain their generalized quantifier

```lojban
ci da gerku .i re da blabi
```

```lisp
(Smusni 0
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
          2)))))
```

`Witnesses` preserves the quantifier application whose graph-owned discourse
referent escapes. The assertions still count the original satisfying
properties; they do not count the chosen witnesses and thereby make themselves
vacuous. An exact and an at-least quantifier therefore cannot collapse to the
same exported datum.

### Set and group descriptions are ordinary predications

```lisp
; lo'i prenu
(Let (($people (Referents Entity) (Refer prenu)))
  (Refer
    (selcmi :2 $people)))

; loi ci prenu
(Let (($people (Referents Entity) (Refer (Counted (Exactly 3) prenu))))
  (Refer
    (gunma :2 $people)))
```

The first refers number-neutrally to one or more set objects and the second to
one or more group objects; neither outer `Refer` forces a singleton. Plain
`(Refer prenu)` is neither kind of object: it is the number-neutral people
reference that can fill an ordinary people place directly.

The related nonlogical connections form different values:

```lisp
(Combine $alice $bob) ; jo'u: ordinary referents

(Refer ; joi: one group
  (Counted (Exactly 1)
    (gunma :2 (Combine $alice $bob))))

(Refer ; ce: one set
  (Counted (Exactly 1)
    (selcmi :2 (Combine $alice $bob))))

(Singleton (List $alice $bob)) ; ce'o: one sequence
```

And `lu'a` is visible in the containing predication rather than hidden in a
`Members` value:

```lisp
; lu'a $rat-set cu cmalu
(∀
  (λ (($x Entity))
    (→
      (cmima $x $rat-set)
      (cmalu $x))))
```

## 18. A genuinely equal-scope termset uses selected sets

```lojban
ci gerku ce'e re nanmu cu batci
```

```lisp
(Smusni 0
  (Assert
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
                  (→ (∈ $x $dogs) (batci $x $y)))))))))))))))
```

Ordinary nesting is not equivalent. Dog-wide nesting could choose two
different men for each dog; reversing it could choose three different dogs for
each man. The termset instead chooses one fixed three-dog set and one fixed
two-man set, requires all six Cartesian-product pairs, and makes each selected
set exhaustive relative to the other. Although the two set existentials are
printed in an order, their selectors deliberately depend on each other's sets;
their classical order is immaterial only because both existential binders
prefix the same conjunction and commute. Consequently, if four dogs all bite both
selected men, `(Exactly 3)` is false while `(AtLeast 3)` remains true; an
arbitrary three-dog subset is not a witness.

The current tersmu implementation's nested output is not a precedent: its own
documentation says that termset quantification was not implemented. The
semantic builder must retain the equal-scope relation needed for this lowering.
Unsupported downward-entailing polyadic quantifiers use typed fallback rather
than an unexplained `PolyQuant` atom or a vacuous empty witness set.

## 19. Respectively is tuple construction plus `ZipWith`

An ordered tuple value, where the receiving type explicitly admits it, is:

```lisp
(Tuple
  (Refer (cmene (NameSign "alis") :3 Speaker))
  (Refer (cmene (NameSign "bob") :3 Speaker)))
```

The ordinary respective predication is higher-order zipping rather than passing
a tuple into an entity place:

```lisp
(Assert
  (ZipWith
    (λ (($person (Referents Entity))
        ($destination (Referents Entity)))
      (klama $person $destination))
    (Tuple
      (Refer (cmene (NameSign "alis") :3 Speaker))
      (Refer (cmene (NameSign "bob") :3 Speaker)))
    (Tuple
      (Refer zarci)
      (Refer briju))))
```

## 20. Reported content is reified, not performed

```lisp
(Smusni 0
  (Let (($alice (Referents Entity)
          (Refer (cmene (NameSign "alis") :3 Speaker))))
    (Assert
      (xusra $alice
        (Reify
          (klama $alice (Refer zarci)))))))
```

Only the outer `Assert` is performed. `Reify` explicitly crosses from content
to a proposition referent.

## 21. Utterance facts are predications over a token

```lisp
(Smusni 0
  (Let (($alice (Referents Entity)
          (Refer (cmene (NameSign "alis") :3 Speaker))))
    (Let (($c Content (klama $alice (Refer zarci))))
      (Let (($a (Act Assertion) (Assert $c)))
        (Utterance $u
          (Realizes $u $a)
          (SpeakerOf $u $alice)
          (AudienceOf $u
            (Refer (cmene (NameSign "bob") :3 Speaker))))))))
```

The direct record performs `$a` by document convention. Embedded under a sign
or mention, it is inert transcript data.

```lisp
(Let (($alice (Referents Entity)
        (Refer (cmene (NameSign "alis") :3 Speaker)))
      ($utterance (Referents Utterance) Context))
  (Assert (Utters $alice $utterance)))
```

would instead be the current speaker's report about an uttering event.

## 22. Indicators target actual first-class values

The draft-2 `Displayed` sample becomes. `Let` is transparent on the performing
spine, so the `Utterance` entry below remains in the `Do` performing position
and both `Realizes` acts are executed:

```lisp
(Smusni 0
  (Do
    (Assert
      (klama Speaker (Refer zarci)))
    (Let (($c Content
            (¬
              (djica Speaker
                (Refer
                  (λ (($e (Referents Eventuality)))
                    (cilre Speaker
                      :Eventuality $e)))))))
      (Utterance $u2
        (Realizes $u2 (Assert $c))
        (Realizes $u2
          (Express
            (Contrast Speaker $c $u2)))))))
```

The relation's arguments are experiencer, real target, and anchor. Positive
polarity and unchanged host assertion are defaults. A non-default degree or
polarity transforms the relation, for example
`((Degree Strong Happiness) Speaker $c $u2)` or
`((Scalar Opposite Happiness) Speaker $c $u2)`.

## 23. Clause and predicate targets differ by type, not an enum

```lisp
(Let (($market (Referents Entity) (Refer zarci)))
  (Let (($p PredTerm (klama Speaker $market)))
    (Utterance $u
      (Realizes $u (Assert (Close $p)))
      (Realizes $u
        (Express
          (MetalinguisticNegation Speaker $p $u))))))
```

The target is `$p` itself. `Close` is visible because the same value is used at
both the predicate-term and content levels. The effectful market description is
bound at the enclosing dynamic site before it is captured by the inert
predicate term.

## 24. Questions are content/lambda queries with explicit level crossings

```lojban
ma klama lo zarci
```

```lisp
(Smusni 0
  (Let (($market (Referents Entity) (Refer zarci)))
    (Ask
      (OpenQ
        (λ (($x (Referents Entity)))
          (klama $x $market))))))
```

```lojban
ti mo
```

```lisp
(Smusni 0
  (Ask
    (OpenQ
      (λ (($p (OpenPredTerm (Referents Entity))))
        (Close ($p This))))))
```

```lojban
xu do klama
```

```lisp
(Smusni 0
  (Ask
    (Polar (klama Audience))))
```

An open indirect question crosses to its answer proposition rather than to a
polar-only wrapper:

```lojban
lo du'u makau cortu
```

```lisp
(Smusni 0
  (Mention
    (Reify
      (Answer
        (OpenQ
          (λ (($x (Referents Entity)))
            (cortu $x)))))))
```

If a question object itself is referenced, `QuestionOf` performs that crossing;
otherwise no `Question`, `Kind`, `Mode`, `Domain`, `Body`, or `Slot` record is
needed.

## 25. Discourse operators replace sequence records

```lisp
(Smusni 0
  (Do
    (Assert (klama Speaker))
    (NewTopic
      (Do
        (Assert (stali Audience))))))
```

An actual nonlogical connection is printed at the content/discourse locus; an
elided operand is `PriorDiscourse`. A `Sequence` token boundary is retained only
when some other object references the sequence identity.

The discourse overload is equally direct:

```lisp
(Smusni 0
  (Joi
    (Perform (Assert broda))
    (Perform (Ask (Polar brode)))))
```

## 26. Math uses mathematical syntax

```lojban
li re su'i ci du li mu
```

```lisp
(Smusni 0
  (Assert
    (= (+ 2 3) 5)))
```

## 27. Sign facts are predications

```lisp
(Let (($u (Referents Utterance) ...))
  (Sign $s
    (Quotes $s $u)
    (TextOf $s "...")
    (Denotes $s
      (Reify
        (klama Speaker (Refer zarci))))))
```

The common values are simply `(StructuredQuote $u)` and
`(OpaqueQuote "...")`. A `Sign` boundary appears only when its identity or
multiple properties matter.

## 28. Local fallback is visibly transitional

If a current graph surface cannot yet be lowered compositionally, the renderer
uses a local typed object expression and records the reason in corpus stats. A
whole-document `TypedGraph` remains the final totality mechanism only when local
scope/identity output would lie. Neither shape is intended normal form, and
neither carries diagnostics inside semantic stdout.

## 29. Fixed references bind across extensional negation

```lisp
(Smusni 0
  (Let (($dogs (Referents Entity) (Refer gerku)))
    (Assert
      (¬
        (melbi $dogs)))))
```

The concise `Refer` is not a pure value smuggled into a referent place. Because
xorlo makes it a fixed constant, its computed bind site is above extensional
negation. Crossing that visible scope-bearing operator makes the wide `Let`
explicit. It does not elaborate to the following narrower form:

```lisp
(Smusni 0
  (Assert
    (¬
      (Let (($dogs (Referents Entity) (Refer gerku)))
        (melbi $dogs)))))
```

That rejected form can turn contextual reference into a choice under negation.
Multiple reference computations at the same computed site bind in printed
operand order. Shared identity, dependency abstraction, or crossing a visible
scope-bearing operator prints the `Let` explicitly; a single-use reference may
remain inline beneath `Joi` or an administrative event shell.

## 30. Nested cardinalities retain ordinary lambda scope

```lisp
(Smusni 0
  (Assert
    (=
      (Card
        (λ (($x Entity))
          (∧
            (prenu $x)
            (=
              (Card
                (λ (($y Entity))
                  (∧
                    (gerku $y)
                    (prami $x $y))))
              3))))
      2)))
```

The inner cardinality remains inside the property used by the outer one; no
`Quantify` record or scope-free count node is introduced.
