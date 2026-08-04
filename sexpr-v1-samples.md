# Experimental smusni S-expression samples, draft 1

These are hand-audited semantic shape probes for the second design review. They
are not output expectations. After implementation they will be replaced in the
design record by renderer-generated examples.

## Ordinary assertion and implicit contextual places

```lojban
mi klama
```

```lisp
(Smusni 0
  (Assert
    (klama Speaker)))
```

The omitted x2–x5 and local event are the named contextual defaults. `Assert`
is never omitted.

## Out-of-order numbered fill

```lisp
(Smusni 0
  (Assert
    (klama Speaker
      (At 5 (Lo karce)))))
```

No implicit root-to-entity coercion is used: the car is `(Lo karce)`.

## Modal fill after full desugaring

Source:

```lojban
mi klama sepi'o lo karce
```

```lisp
(Smusni 0
  (Assert
    (∃ (($e Eventuality))
      (klama Speaker
        (At Eventuality $e)
        (At
          (λ (($tool Entity))
            (pilno (At 2 $tool) (At 3 $e)))
          (Lo karce))))))
```

The modal designator is a unary function over the tag argument. Its body is the
canonical `pilno` predicate term: x2 is the tool and x3 is the host event; x1
remains contextual. The modal does not become a guessed conjunction.

## Restricted universal with dependent contextual places

```lojban
ro mlatu cu jbena
```

```lisp
(Smusni 0
  (Assert
    (∀ (($x Entity))
      (Restrict
        (mlatu $x)
        (Import Projective))
      (jbena $x))))
```

The closure default says the omitted places of `jbena` may depend on every
accessible binder, including `$x`. If the graph records a narrower or fixed
dependency, the renderer prints that difference explicitly.

## Predicate-locus connective with shared omitted argument

Source:

```lojban
ganai broda gi brode .a brodi
```

```lisp
(Smusni 0
  (Assert
    (Let
      (($shared Entity Context))
      (→ broda
         (∨ (brode $shared)
            (brodi $shared))))))
```

The implication glyph is licensed only by the exact truth-table recognition.
The second-branch predicates share the same contextual x1, so it cannot be
silently closed once per branch.

## Property abstraction

```lojban
lo ka ce'u prami mi
```

```lisp
(Smusni 0
  (Mention
    (Lo
      (Ka
        (λ (($x Entity))
          (prami $x Speaker))))))
```

`ce'u` is a lambda variable; ordinary omitted later places remain contextual.

## Event abstraction

```lojban
mi djica lo nu mi cilre
```

```lisp
(Smusni 0
  (Assert
    (djica Speaker
      (Lo
        (Nu
          (cilre Speaker))))))
```

The `Nu` content is inert. `Lo` constructs the event referent; no inner
assertion occurs.

## Restrictive relative clause and numeral value

```lojban
le cukta poi mi nelci ke'a cu jdima li pasono
```

```lisp
(Smusni 0
  (Let
    (($book Entity
       (Le
         (λ (($x Entity))
           (∧ (cukta $x)
              (nelci Speaker $x))))))
    (Assert
      (jdima $book 190))))
```

`pasono` is 190. The description remains a reference constructor, not an
existential quantifier. The relative clause shares the described referent.

## Incidental relative clause versus transcript metadata

```lojban
lo cukta noi mi nelci ke'a cu melbi
```

```lisp
(Smusni 0
  (Let
    (($book Entity (Lo cukta)))
    (Utterance $u
      (Assert (melbi $book))
      (Incidental
        (nelci Speaker $book)))))
```

The `noi` content is a speaker commitment in a non-at-issue stratum. It is not
an analyzer fact such as `(Speaker $u Speaker)`.

## Tanru relation formation

```lojban
ti blanu zdani
```

```lisp
(Smusni 0
  (Assert
    ((OfKind zdani blanu) This)))
```

`OfKind` is printed only when the typed tanru projection recognizes this
relation formation; otherwise the full `TanruLink` fallback remains visible.

## Place deletion

```lojban
mi dunda zi'o ti
```

```lisp
(Smusni 0
  (Assert
    ((DropPlace dunda 2) Speaker This)))
```

The two plain operands fill original x1 and original x3. Original x2 is absent,
not contextual.

## Reported versus current assertion

```lisp
(Smusni 0
  (Let
    (($alice Entity (Named "Alice")))
    (Assert
      (xusra $alice
        (Lo
          (Du'u
            (klama $alice (Lo zarci))))))))
```

Only the outer `Assert` is the current utterance's force. `xusra` is an
ordinary lowercase content predicate describing Alice's assertion.

## Fill-in question and fragment response

```lisp
(Smusni 0
  (Ask
    (λ (($x Entity))
      (klama $x (Lo zarci)))))
```

```lisp
(Smusni 0
  (Mention Speaker))
```

The second form is a referential fragment. `Answer` is not invented as a force
when the graph records `Mention`.

## Termset / simultaneous quantification

```lisp
(Smusni 0
  (Assert
    (Quantify
      ((∃ (($x Entity)) (Restrict (broda $x)))
       (∀ (($y Entity))
          (Restrict (brode $y) (Import Projective))))
      (brodi $x $y))))
```

`Quantify` preserves one bundle; it does not choose a nested scope order.

## Respectively distribution

```lisp
(Smusni 0
  (Let
    (($alice Entity (Named "Alice"))
     ($bob Entity (Named "Bob")))
    (Assert
      (Respectively
        (Stream $alice $bob)
        (Stream (Lo zarci) (Lo briju))
        (λ (($person Entity) ($destination Entity))
          (klama $person $destination))))))
```

`Stream` prevents a member list from being mistaken for application.

## Event property and past tense

```lojban
mi pu klama lo zarci
```

```lisp
(Smusni 0
  (Assert
    (∃ (($e Eventuality))
      (∧
        (klama Speaker (Lo zarci) (At Eventuality $e))
        (Before $e Now)))))
```

The event becomes explicit because `pu` contributes a non-default facet.

## Corrected narrative probe

Source:

```lojban
mi pu klama lo zarci .i le nanmu poi mi viska ke'a cu dunda lo cukta mi .i mi jinvi lo du'u le cukta cu melbi .i ku'i mi na djica lo nu mi cilre
```

```lisp
(Smusni 0
  (Sequence SameTopic
    (Assert
      (∃ (($e Eventuality))
        (∧
          (klama Speaker (Lo zarci) (At Eventuality $e))
          (Before $e Now))))
    (Let
      (($man Entity
         (Le
           (λ (($x Entity))
             (∧ (nanmu $x)
                (viska Speaker $x))))))
      (Assert
        (dunda $man (Lo cukta) Speaker)))
    (Assert
      (jinvi Speaker
        (Lo
          (Du'u
            (melbi (Le cukta))))))
    (Utterance $u4
      (Assert
        (¬
          (djica Speaker
            (Lo
              (Nu
                (cilre Speaker))))))
      (Displayed
        (Discursive ku'i
          (Target Clause)
          (Anchor $u4))))))
```

This fixes the earlier draft's giver, restores the restrictive relative clause,
and makes `pu` visible. The exact `Displayed` form remains subject to the typed
field inventory; no field may be silently discarded.

## Accessibility probe

The semantic rule, not necessarily a literal output for one Lojban source:

```lisp
(Assert
  (→
    (∃ (($person Entity) ($animal Entity))
      (∧ (prenu $person)
         (danlu $animal)
         (ponse $person $animal)))
    (darxi $person $animal)))
```

The antecedent's referents are accessible inside the consequent. They are not
accessible after the implication. An ordinary state monad would not express
that pre/post distinction in its type; `𝒟<Γ,Δ,A>` does.
