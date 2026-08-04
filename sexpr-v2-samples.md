# Experimental smusni S-expression samples, draft 2

These are design probes, not output expectations. They record the intended tree
shape after final Opus and Kimi convergence review. Once the renderer exists,
every sample is replaced or supplemented by renderer-generated output from its
actual graph.

## 1. Ordinary assertion and implicit closure

```lojban
mi klama
```

```lisp
(Smusni 0
  (Assert
    (klama Speaker)))
```

`Assert` is explicit. The document performs this top-level act. The local event
and unshared default `zo'e` places are silent.

## 2. A non-next original place

```lojban
mi klama fu lo karce
```

```lisp
(Smusni 0
  (Assert
    (klama Speaker
      (At 5 (Lo karce)))))
```

The car fills original x5. It is not a modal attachment.

## 3. A modal place is an assembled predicate term

```lojban
mi klama sepi'o lo karce
```

```lisp
(Smusni 0
  (Assert
    (∃ (($e Eventuality))
      (klama Speaker
        (At Eventuality $e)
        (Modal
          (pilno
            (At 2 (Lo karce))
            (At 3 $e)))))))
```

The graph's canonical `pilno` place map is printed directly: x2 is the tool and
x3 is the shared host event. Contextual x1 is silent.

## 4. Direct `fi'o pilno` is different

```lojban
mi klama fi'o pilno lo karce
```

```lisp
(Smusni 0
  (Assert
    (∃ (($e Eventuality))
      (klama Speaker
        (At Eventuality $e)
        (Modal
          (pilno
            (At 1 (Lo karce))
            (At 3 $e)))))))
```

Here the tag fills `pilno` x1, while the graph still records the host event at
x3. A bare-root modal shortcut would lose that shared identity and is therefore
not used.

## 5. An elided modal tag value

```lojban
mi klama sepi'o
```

```lisp
(Smusni 0
  (Assert
    (∃ (($e Eventuality))
      (klama Speaker
        (At Eventuality $e)
        (Modal
          (pilno (At 3 $e)))))))
```

The elided tool and user are ordinary contextual defaults. The shared event is
not.

## 6. Restricted universal and exact glyph recognition

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

`∀` captures the graph's universal operator plus its `All` quantity. The
omitted `jbena` places may depend on the one accessible binder, which is the
closure default.

## 7. Predicate-locus connection and shared contextual identity

```lojban
ganai broda gi brode .a brodi
```

```lisp
(Smusni 0
  (Assert
    (→ (WithWarnings broda
         (Warning
           (Severity Warning)
           (Message "relation place structure is unavailable")))
       (Let
         (($shared Entity Context))
         (∨ (WithWarnings (brode $shared)
              (Warning
                (Severity Warning)
                (Message "relation place structure is unavailable")))
            (WithWarnings (brodi $shared)
              (Warning
                (Severity Warning)
                (Message "relation place structure is unavailable"))))))))
```

The truth table and connector provenance license `→`. The shared contextual x1
is bound at the smallest scope dominating its two uses; `broda` has a different
contextual x1.

## 8. Binder failure uses a whole-document fallback

```lojban
ganai da prenu gi da melbi
```

The current graph places the existential binder below a negation while a sibling
consequent uses its variable. Compact output would contain a free variable, so
the renderer emits the mechanically complete shape:

```lisp
(Smusni 0
  (TypedGraph
    (Root @utterance_5)
    ...))
```

The real output contains every `Def` and field; the ellipsis here is editorial,
not literal output.

## 9. Property and event abstractions

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

```lojban
mi djica lo nu mi cilre
```

```lisp
(Smusni 0
  (Assert
    (djica Speaker
      (Lo
        (Nu (cilre Speaker))))))
```

Both abstractions are inert values. The typed `Ka` body position entails its
graph `Restrictive` mode, while the `Nu` event body entails `Inert`; neither
default needs a `Mode` wrapper. The standalone sumti fragment has `Mention`
force, not an invented answer act.

## 10. Relative-clause veridicality remains visible

```lojban
le gerku poi blabi cu melbi
```

```lisp
(Smusni 0
  (Assert
    (melbi
      (Le (($x Entity))
        (gerku $x)
        (Relative Restrictive Veridical
          (blabi $x))))))
```

For `le gerku voi blabi`, only the clause marker changes:

```lisp
(Relative Restrictive Nonveridical
  (blabi $x))
```

The base `le` description and the relative clause are not flattened into one
property, so `poi` and `voi` cannot collapse.

## 11. Incidental content keeps its attachment

```lojban
lo cukta noi mi nelci ke'a cu melbi
```

```lisp
(Smusni 0
  (Assert
    (melbi
      (Lo (($x Entity))
        (cukta $x)
        (Relative Incidental
          (nelci Speaker $x))))))
```

The `noi` content is a speaker-expressed non-at-issue stratum, not transcript
metadata, and it stays at the description scope where the graph attaches it.

## 12. Place deletion

```lojban
mi dunda zi'o ti
```

```lisp
(Smusni 0
  (Assert
    ((DropPlace dunda 2) Speaker This)))
```

The two plain operands fill original x1 and original x3.

## 13. Tanru projection

```lojban
ti blanu zdani
```

```lisp
(Smusni 0
  (Assert
    ((OfKind zdani blanu) This)))
```

This prints exactly when the typed recognition proof accounts for the underlying
tanru link, head conjunct, and absorbed modifier event. Otherwise the typed
`TanruLink` structure prints.

## 14. A facet on a generated matrix event

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

The event is explicit because `pu` contributes a non-default facet.

## 15. A facet on a described eventuality

```lojban
mi djica lo nu mi pu cilre
```

```lisp
(Smusni 0
  (Assert
    (∃ (($want Eventuality))
      (djica Speaker
        (Lo (($learning Eventuality))
          (Nu $learning (cilre Speaker))
          (Before $learning $want))
        (At Eventuality $want)))))
```

The `Before` predicate remains an attached property of the described learning
event and is anchored to the matrix event. It is not moved into an unrelated
matrix conjunction.

## 16. Cardinality is not automatically existential glyph sugar

```lisp
(Smusni 0
  (Assert
    (Cardinality (($x Entity))
      (AtLeast 3)
      (Restrict (mlatu $x))
      (jbena $x))))
```

`∃` is reserved for a graph existential operator or generated event binder.

## 17. Simultaneous termset binding

```lisp
(Smusni 0
  (Assert
    (Quantify
      (($x Entity
         (Cardinality
           (Quantity (Form AtLeast) (ValueText "su'o") (Scale Count)))
         (Restrict (broda $x)))
       ($y Entity
         Forall
         (Restrict (brode $y) (Import Projective))))
      (brodi $x $y))))
```

The one binder list scopes across every simultaneous binding specification and
the body. No nested form purports to bind a variable used by its sibling.

## 18. Two respectively surfaces

Argument-level `fa'u` produces composite referents:

```lisp
(Assert
  (klama
    (RespectivelyValue
      (La (Named "alis"))
      (La (Named "bob")))
    (RespectivelyValue
      (Lo zarci)
      (Lo briju))))
```

A graph `RespectivelyDistributionFormulaNode` instead prints streams and a
distribution body:

```lisp
(Respectively
  (Stream (La (Named "alis")) (La (Named "bob")))
  (Stream (Lo zarci) (Lo briju))
  (λ (($person Entity) ($destination Entity))
    (klama $person $destination)))
```

The two constructors are not conflated.

## 19. Reported assertion versus current performance

```lisp
(Smusni 0
  (Let
    (($alice Entity (La (Named "alis"))))
    (Assert
      (xusra $alice
        (Lo
          (Du'u
            (klama $alice (Lo zarci))))))))
```

Only the outer `Assert` is performed by this document. `xusra` is an ordinary
lowercase predicate reporting Alice's act.

## 20. Utterance token facts are records, not asserted content

```lisp
(Smusni 0
  (Let
    (($alice Entity (La (Named "alis"))))
    (Utterance $u
      (Act
        (Assert (klama $alice (Lo zarci))))
      (Speaker $u $alice)
      (Audience $u (La (Named "bob"))))))
```

As a direct document item, the record performs its `Act`; embedded under
`Mention` or `Quote`, the same record is inert. Its unreferenced default
locution, time, and place are suppressed under §3; the non-default audience is
why the record remains self-describing here. By contrast:

```lisp
(Assert (Utters $alice $u))
```

is the current speaker's assertion *about* an utterance event. It does not
perform the recorded act. This is illustrative-only in draft 2: no current graph
surface licenses `Utters`, so the first renderer never emits it.

## 21. Ordered discourse and displayed content

```lisp
(Smusni 0
  (Do
    (Assert
      (klama Speaker (Lo zarci)))
    (Utterance $u2
      (Act
        (Assert
          (¬ (djica Speaker
               (Lo (Nu (cilre Speaker)))))))
      (Displayed
        (Metalinguistic "ku'i"
          (Polarity Positive)
          (AssertionEffect None)
          (Experiencer Speaker)
          (Target ActContent)
          (TargetFocus Clause)
          (Anchor $u2))))))
```

The displayed-content family follows the current graph. The exact generated
form will preserve all graph fields and will replace this hand-written probe.
