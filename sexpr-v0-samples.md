# Experimental smusni S-expression samples, draft 0

These are hand-authored shape probes. They intentionally omit dictionary word
cards and most ordinary deictic-ground facts. They are not golden expectations.

## Small predication

Source:

```lojban
mi klama
```

```lisp
(Smusni 0
  (Assert
    (klama Speaker)))
```

## Numbered gap and modal place

Source sketch: “I go using the car,” with ordinary x2–x4 omitted.

```lisp
(Smusni 0
  (Assert
    (klama Speaker
      (At 5 (Lo karce)))))
```

If the source instead uses a modal whose designator is the relation `pilno`:

```lisp
(Smusni 0
  (Assert
    (klama Speaker
      (At pilno (Lo karce)))))
```

## Restricted universal with dependent contextual places

Source sketch:

```lojban
ro mlatu cu jbena
```

```lisp
(Smusni 0
  (Assert
    (∀ (x Entity)
      (Restrict
        (mlatu x)
        (Import Projective))
      (jbena x))))
```

The silent parent, time, and place arguments of `jbena` are distinct contextual
values. If the graph preserves possible dependence on `x`, the full renderer
must retain that constraint; the short notation above is acceptable only if
the document default explicitly says that contextual values may depend on all
enclosing binders.

## Complex connective

Source:

```lojban
ganai broda gi brode .a brodi
```

```lisp
(Smusni 0
  (Assert
    (→ broda
       (∨ brode brodi))))
```

The lowercase roots are zero-filled relations. The surrounding operators need
nullary content, so contextual closure occurs locally. Neither operand is
independently asserted.

## Property abstraction

Source:

```lojban
lo ka ce'u prami mi
```

```lisp
(Smusni 0
  (Mention
    (Lo
      (Ka
        (λ (x Entity)
          (prami x Speaker))))))
```

`ce'u` is the lambda variable; omitted later places remain contextual rather
than becoming more function arguments.

## Event abstraction

Source:

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

`Nu` forms an event-kind relation; `Lo` obtains a referent satisfying its x1
place. The inner content is inert and is not independently asserted.

## Restrictive relative clause

Source (the existing `numeral-price` sample):

```lojban
le cukta poi mi nelci ke'a cu jdima li pasono
```

```lisp
(Smusni 0
  (Let
    ((book Entity
       (Le
         (λ (x Entity)
           (∧ (cukta x)
              (nelci Speaker x))))))
    (Assert
      (jdima book 150))))
```

The description is not converted into an existential quantifier. The relative
clause shares the lambda-bound described referent.

## Incidental relative clause

Source sketch:

```lojban
lo cukta noi mi nelci ke'a cu melbi
```

```lisp
(Smusni 0
  (Let
    ((book Entity (Lo cukta)))
    (Utterance u1
      (Assert (melbi book))
      (Aside u1 (nelci Speaker book)))))
```

The incidental clause is recorded as projective/aside content, not folded into
the at-issue assertion or the restrictive description.

## Shared quantified term across a connective

```lisp
(Smusni 0
  (Assert
    (∃ (x Entity)
      (Restrict (broda x))
      (∧ (brode x)
         (brodi x)))))
```

The one binder scopes over the connective; duplicating `∃` into each branch
would permit different witnesses.

## Tanru predicate formation

Source:

```lojban
ti blanu zdani
```

```lisp
(Smusni 0
  (Assert
    ((OfKind zdani blanu) ti)))
```

`OfKind` returns a new relation whose place row comes from `zdani`. It does not
mean conjunction or ordinary mathematical function composition.

## Explicit place deletion

```lisp
(Smusni 0
  (Assert
    ((Without broda 2) ko'a ko'e)))
```

The second original place is absent, not filled by `zo'e`. The effective row is
used for the two ordinary applications; origin-place identities remain
available as provenance.

## Current versus reported assertion

```lisp
(Smusni 0
  (Assert
    (Asserts alis
      (Reify
        (klama alis zarci)))))
```

Only the outer `Assert` is performed. The inner `Asserts` is a descriptive
relation about Alice.

## Utterance facts as relations

```lisp
(Smusni 0
  (Let
    ((alis Entity (Named "Alice"))
     (bob Entity (Named "Bob"))
     (t1 Time (Now)))
    (Utterance u1
      (Assert (klama alis zarci))
      (Speaker u1 alis)
      (Audience u1 bob)
      (TimeOf u1 t1)
      (Medium u1 Speech))))
```

The metadata are relation terms under transcript `Record` semantics. They are
not conjuncts of what Alice asserted.

## Fill-in question and fragment answer

```lisp
(Smusni 0
  (Ask
    (λ (x Entity)
      (klama x zarci))))
```

```lisp
(Smusni 0
  (Answer mi))
```

The answer completes prior open content; it is not forced into an unrelated
standalone assertion.

## Termset / bundled quantification

Source sketch with two simultaneously introduced terms:

```lisp
(Smusni 0
  (Assert
    (Quantify
      ((∃ (x Entity) (Restrict (broda x)))
       (∀ (y Entity) (Restrict (brode y) (Import Projective))))
      (brodi x y))))
```

`Quantify` preserves a bundle when the graph says the binders are one termset
rather than inventing an arbitrary nesting order. A later notation may choose
a conventional simultaneous-binder symbol if one proves clearer.

## Respectively

```lisp
(Smusni 0
  (Assert
    (Respectively
      ((alice bob) (market office))
      (λ (person destination)
        (klama person destination)))))
```

This is a distribution operator, not `∧` and not a Cartesian product.

## Shared event with a licensed event property

```lisp
(Smusni 0
  (Assert
    (∃ (e Eventuality)
      (∧ (klama Speaker zarci (At Event e))
         (pilno karce e)))))
```

For an arbitrary `fi'o` whose host attachment is not lexically determined, the
modal relation stays a place designator:

```lisp
(Smusni 0
  (Assert
    (klama Speaker zarci
      (At (broda (At 2 ko'a)) ko'e))))
```

## Narrative with an aside and embedded proposition

Based on the existing `paragraph-narrative` sample:

```lisp
(Smusni 0
  (Sequence SameTopic
    (Assert
      (klama Speaker (Lo zarci)))
    (Assert
      (dunda Speaker (Lo cukta) Speaker))
    (Assert
      (jinvi Speaker
        (Lo
          (Du'u
            (melbi (Le cukta))))))
    (Utterance u4
      (Assert
        (¬ (djica Speaker
             (Lo
               (Nu
                 (cilre Speaker))))))
      (Aside u4 (ku'i u4)))))
```

This probe deliberately exposes unresolved design points: whether `jinvi`'s
proposition place should receive a reified `Du'u` referent exactly as the
dictionary signature requires; whether `ku'i` elaborates to a discourse
relation or remains a displayed-content intrinsic; and how repeated
speaker-described `cukta` references are scoped and shared. The renderer must
follow the graph rather than “improve” these by intuition.

