# Samples

Worked specimens for [the specification](spec.md): Lojban sources, their
core terms, and — where a reading is contested territory — the pinned
reading in plain language and a nearby contrast. Each specimen's first
comment line is its Lojban source; specimens exercising a pin cite it.
These are design specimens: alpha-equivalent terms and transparent library
expansions are the same meaning, and no spelling here is "canonical".

Fragments (terms meant to appear inside a document) are marked; everything
else is a complete meaning, with `Assert`/`Ask` and closure written out
where they matter and elided (per spec §2 notation) where they don't.

## 1. Predication and closure

```lisp
; mi klama
(Assert
  (Close (klama Speaker)))
```

Fully expanded once, so the notation convention is grounded (spec §4.6) —
four contextual places and the event:

```lisp
; mi klama — Close expanded
(Assert
  (Bind (($to   (Referents Entity) (Context))
         ($from (Referents Entity) (Context))
         ($via  (Referents Entity) (Context))
         ($by   (Referents Entity) (Context)))
    (∃ (λ (($e (Referents Eventuality)))
      (klama Speaker $to $from $via $by :Eventuality $e)))))
```

Contrast: under negation the contextual places stay put — `mi na klama`
denies the going-to-the-contextual-place, and is not `¬∃destination…`
(pin P15; rationale §1.3).

```lisp
; klama fe ti tu — labelled fills, x1 left contextual
(Assert (Close (klama :2 This Yonder)))
```

```lisp
; mi klama ti zi'o ti ti — the origin role removed, not omitted
(Assert (Close ((DropPlace klama 3) Speaker This This This)))
```

```lisp
; ti se klama mi — conversion consumed by the mapping; no Se operator
(Assert (Close (klama Speaker This)))
```

```lisp
; lo ka se klama — a converted relation escaping as a function
(Mention
  (λ (($x (Referents Entity)))
    (Close (klama :2 $x))))
```

## 2. Events, tense, facets

Facet joining is dynamic conjunction over a shared event (the final
rulings' samples-consequences clause; the older idea of a dedicated
joining operator is retired):

```lisp
; mi pu citka
(Assert
  (∃ (λ (($e (Referents Eventuality)))
    (∧ (Close (citka Speaker :Eventuality $e))
       (purci $e Now)))))
```

```lisp
; mi pu pu citka — a tense path: past of a past reference point
(Assert
  (∃ (λ (($e (Referents Eventuality)) ($m (Referents Eventuality)))
    (∧ (Close (citka Speaker :Eventuality $e))
       (purci $m Now)
       (purci $e $m)))))
```

```lisp
; mi klama ti sepi'o ti — an instrumental facet, same event
(Assert
  (∃ (λ (($e (Referents Eventuality)))
    (∧ (Close (klama Speaker This :Eventuality $e))
       (Close (pilno :2 This :Eventuality $e))))))
```

Contrast (`nai` on the tag): `mi klama ti sepi'onai ti` negates only the
instrumental conjunct — `(∧ (klama …) (¬ (pilno …)))` — while bridi `na`
negates the whole conjunction. Both fall out of `∧` placement; nothing is
stipulated (rationale §1.13, the facet-decomposition entry).

```lisp
; mi ca'a citka — actuality as a facet
(Assert
  (∃ (λ (($e (Referents Eventuality)))
    (∧ (Close (citka Speaker :Eventuality $e))
       (fasnu $e)))))
```

Tenseless `mi citka` carries no temporal conjunct at all — absence, not a
default present (pin P8).

## 3. Reference and descriptions

```lisp
; lo mlatu cu blabi              [pin P1]
(Bind (($cat (Referents Entity)
        (Refer (λ (($x (Referents Entity))) (mlatu $x)))))
  (Assert (Close (blabi $cat))))
```

Pinned reading: a new referent — one or more real cats, number-neutral,
no quantifier. Contrast: `su'o mlatu cu blabi` quantifies and its witness
quantifies (though its selected witness stays referable — §5 below);
`lo` introduces with no quantificational force at all.

```lisp
; lo mlatu na jbena — the referent scopes outside negation
(Bind (($cat (Referents Entity)
        (Refer (λ (($x (Referents Entity))) (mlatu $x)))))
  (Assert (¬ (Close (jbena $cat)))))
```

```lisp
; le mlatu cu blabi              [pin P10]
(Bind (($it (Referents Entity)
        (Refer (λ (($x (Referents Entity)))
          (DescribedBy Speaker $x Audience
            (λ (($y (Referents Entity))) (mlatu $y)))))))
  (Assert (Close (blabi $it))))
```

Pinned reading: reference through the speaker's identifying description —
non-veridical (the "cat" may be a raccoon), speaker-specific. The
dedicated `DescribedBy` relation replaces older `skicu`-based spellings,
whose x4 is a medium of expression, not a property (rationale §2.6).

```lisp
; la .alis. klama
(Bind (($alis (Referents Entity)
        (Refer (λ (($x (Referents Entity))) (Named "alis" $x)))))
  (Assert (Close (klama $alis))))
```

```lisp
; lo'i gerku — a set object, via selcmi with plural x2   [pin P5]
(Bind (($base (Referents Entity)
        (MaxRefer (λ (($x Entity)) (gerku $x)))))   ; the maximal base:
                                                    ; THE dogs, not some
  (Bind (($sets (Referents (Set Entity))
          (Refer (λ (($s (Referents (Set Entity)))) (Close (selcmi $s $base)))))))
    (Mention $sets)))
```

`loi gerku` is the same shape through `gunma` at `Group`. Neither object
unwraps to its members implicitly.

```lisp
; lo'e mlatu cu cinri            [pin P11]
(Assert
  (Generic Typical
    (λ (($x Entity)) (mlatu $x))
    (λ (($x Entity)) (Close (cinri $x)))))
```

Pinned reading: a generic claim through a normality ordering — no
"typical cat" specimen exists in the term. `le'e` adds the Speaker as
stereotype-holder. Contrast (the witness that killed specimen theories):
`lo'e cinfo cu se kerfa lo clani` (maned — normal adult males) and
`lo'e cinfo cu se jbena lo cinfo` (bears young — normal adult females)
are both fine and generically true — supported by different normality
classes, which no single referent could verify (rationale §1.9).

## 4. Relative clauses and supplements

```lisp
; lo mlatu poi blabi cu jbena — restrictive: inside the property
(Bind (($cat (Referents Entity)
        (Refer (λ (($x (Referents Entity)))
          (∧ (mlatu $x) (blabi $x))))))
  (Assert (Close (jbena $cat))))
```

```lisp
; lo gerku noi blabi cu na melbi     [pin P7]
(Bind (($dog (Referents Entity)
        (Refer (λ (($x (Referents Entity))) (gerku $x)))))
  (Assert
    (Supplement $dog (blabi $dog)
      (¬ (Close (melbi $dog))))))
```

Pinned reading: whiteness is a projective side commitment — the negation
touches only the beauty claim. Contrast: `xu lo gerku noi blabi cu melbi`
questions beauty and still commits whiteness; and the restrictive
`poi`-variant above puts whiteness *inside* what `na` can reach through
the description.

```lisp
; mi tavla le pendo goi ko'a — aliasing is shared binding
(Bind (($friend (Referents Entity)
        (Refer (λ (($x (Referents Entity)))
          (DescribedBy Speaker $x Audience
            (λ (($y (Referents Entity))) (pendo $y)))))))
  (Assert (Close (tavla Speaker $friend))))
; later ko'a occurrences consume the same binding.  [pin P16]
```

Contrast (`ko'a` never assigned): a keyed contextual retrieval — one
value per key, so `ko'a du ko'a` is reflexively true.

## 5. Quantifiers, witnesses, anaphora

```lisp
; ci gerku cu bajra .i ri tatpi      [spec §5.6]
(Bind (($dogs (Referents Entity)
        (SelectExactly 3 (λ (($x Entity)) (gerku $x)))))
  (Do
    (Assert (Distrib (λ (($x Entity)) (Close (bajra $x))) $dogs))
    (Assert (Close (tatpi $dogs)))))
; the selection introduces and BINDS the witness; the anaphor is an
; ordinary bound occurrence — no free names, no retrieval operator.
```

The old formulation with an explicit run-retrieval operator is retired:
the exported witness *is* the three-dog reference the selection binds,
and nothing else was ever needed (rationale §1.6).

```lisp
; ro prenu cu ponse ci gerku .i ri tatpi — dependent witness
(Assert
  (Presuppose (∃ (λ (($x Entity)) (prenu $x)))
    (∀ (λ (($p Entity) ($d (Referents Entity)))
      (→ (∧ (prenu $p)
            (= (CardBasis $d (λ (($x Entity)) (gerku $x))) 3)
            (Close (ponse $p $d)))
         (Close (tatpi $d)))))))
```

Pinned reading: each person's three dogs are tired — the anaphor
normalizes into a joint locus with the governing quantifier. The
summed reading ("all the dogs together") requires explicit collection.

```lisp
; ro prenu poi ponse su'o xasli cu darxi ri — donkey   [pin P6]
(Assert
  (Presuppose (∃ (λ (($x Entity))
                (∧ (prenu $x)
                   (∃ (λ (($y Entity)) (∧ (xasli $y) (Close (ponse $x $y))))))))
    (∀ (λ (($p Entity) ($d (Referents Entity)))
      (→ (∧ (prenu $p) (xasli $d) (Close (ponse $p $d)))
         (Close (darxi $p $d)))))))
; $d at the plural type: the witness donkeys; the atomic-pair spelling
; is the distributive strengthening.
```

```lisp
; ro gerku cu blabi — importing universal   [pin P2]
(Assert
  (Presuppose
    (∃ (λ (($x Entity)) (gerku $x)))
    (∀ (λ (($x Entity)) (→ (gerku $x) (Close (blabi $x)))))))
```

Contrast: `naku ro gerku cu blabi` — the nonemptiness presupposition
projects; only the universal is negated. Bare-logic `ro da` carries no
presupposition.

```lisp
; ci gerku ce'e re prenu cu nelci    [pin P17]
(Assert
  (∃ (λ (($dogs (Set Entity)) ($people (Set Entity)))
    (∧ (= (Card $dogs) 3)
       (= (Card $people) 2)
       (∀ (λ (($d Entity))
         (→ (∈ $d $dogs)
            (∧ (gerku $d)
               (∀ (λ (($p Entity))
                 (→ (∈ $p $people)
                    (∧ (prenu $p) (Close (nelci $d $p)))))))))))))
```

Pinned reading (CLL ch. 16 §7's own gloss): two picked witness sets,
full product —
every one of the three dogs likes each of the two people. **No
maximality**: a fourth dog also liking them does not falsify this. The
coordinate-closed strengthening ("and they are exactly the participating
dogs/people") is a distinct, marked meaning — the earlier design that
made it the default is retired. Referential termsets (`le ci gerku ce'e
le re prenu`) need no termset semantics at all: fixed referents, product
predication.

```lisp
; so'i prenu cu klama — vague quantity    [spec §6.4]
(Bind (($n Natural
        (Vague (AdmissibleThreshold Many (λ (($x Entity)) (prenu $x))))))
  (Assert
    (AtLeast $n (λ (($x Entity)) (prenu $x))
                (λ (($x Entity)) (Close (klama $x))))))
```

No exact count hides here: the term denotes the family over admissible
thresholds, and `na so'i prenu cu klama` negates pointwise (spec §6.5).

## 6. Acts, questions, answers

```lisp
; xu mi klama
(Ask (Polar (Close (klama Speaker))))

; ma klama
(Ask (OpenQ (λ (($x (Referents Entity))) (Close (klama $x)))))

; ti mo — an open relation question
(Ask (OpenQ (λ (($r (PredTerm ⟨x1:(Referents Entity)⟩)))
  (Close ($r This)))))

; klama fi'a ti — a place question           [spec §4.7]
(Ask (OpenQ (λ (($p (Label klama)))
  (Close (At klama $p This)))))
```

```lisp
; mi cusku lu mi klama li'u — reported, not performed
(Assert
  (Close
    (cusku Speaker
      (StructuredQuote
        (Utterance (($u UtteranceToken))
          (SpeakerOf $u Speaker)
          (Realizes $u (Assert (Close (klama Speaker)))))))))
```

```lisp
; mi djuno lo du'u ma kau klama      [pin P9]
(Assert
  (Close
    (djuno Speaker
      (Reify
        (Answer
          (OpenQ (λ (($x (Referents Entity))) (Close (klama $x))))
          ContextualAnswer)))))
```

Pinned reading: answerhood committed; the exhaustivity slot is *absent* —
the weakest reading, with any completeness demand coming from `djuno`'s
own lexical presupposition, never from `kau`.

## 7. Indicators

```lisp
; .ui do klama — pure emotion: host asserted, joy displayed
(Let (($a (Act Assertion) (Assert (Close (klama Audience)))))
  (Do (Perform $a)
      (Express (Display (happiness Speaker Moderate) $a))))

; .au mi sipna — propositional attitude: host subordinated  [R6]
(Express (Close (desire Speaker (Reify (Close (sipna Speaker))))))
; no assertion of sleeping occurs — the host-force profile of .au.

; .uinai cai do klama — paired emotion, then degree   [spec §7.6]
(Let (($a (Act Assertion) (Assert (Close (klama Audience)))))
  (Do (Perform $a)
      (Express (Display (unhappiness Speaker Intense) $a))))
```

```lisp
; za'a do cadzu — evidential grounding the act        [R5]
(Let (($a (Act Assertion) (Assert (Close (cadzu Audience)))))
  (Do (Perform $a)
      (Express (Display (evidential-basis Speaker Observation) $a))))
; the display's target is the performed act's content, so the family
; force clause grounds the assertion (a mode of commitment);
; na za'a do cadzu negates the walking, never the basis.

; mi jinvi lo du'u ti'e do klama — evidential on embedded content
(Let (($c Content (Close (klama Audience))))
  (Assert
    (Close
      (jinvi Speaker
        (Reify
          (Supplement $c
            (Display (evidential-basis Speaker Hearsay) $c)
            $c))))))
; at content level Display reduces to an anchored Supplement, so the
; hearsay display rides the embedded claim projectively — the reason
; evidentials are targeted display, not an operand on assertion force.
; (ti'e placed after du'u, targeting the abstraction's content, per the
; CLL attachment rule.)
```

```lisp
; .i mi klama .i ku'i do stali — a discourse relation
(Do
  (Let (($a1 (Act Assertion) (Assert (Close (klama Speaker)))))
    (Do (Perform $a1)
        (Let (($a2 (Act Assertion) (Assert (Close (stali Audience)))))
          (Do (Perform $a2)
              (Express (Close (Contrast Speaker $a2 $a1))))))))
```

```lisp
; na'i — metalinguistic objection             [spec §7.3]
(Let (($prior (Act Assertion) …))          ; the objected act, bound
                                           ; earlier in the discourse
  (Bind (($defect DefectKind (Context)))
    (Express
      (Close (MetalinguisticallyDefective $prior $defect)))))
; the defect dimension is contextually recovered; nothing is negated
; and the objected content is not performed.
```

## 8. Vagueness

```lisp
; sutra klama — the tanru link is Vague       [spec §6.2]
(Assert
  (Close ((Tanru sutra klama) Speaker)))
; ≗ (Bind (($link (PredTerm ρ(klama))
;           (Vague (λ (($r (PredTerm ρ(klama))))
;                    (TanruAdmissible sutra klama $r)))))
;     … (∧ (klama …) ($link …)))
```

```lisp
; ti na'e melbi — scalar otherness            [spec §6.3]
(Assert (Close ((Scalar OtherThan melbi) This)))
; scale dimension: Context; region boundary: Vague.
; does NOT entail ¬(melbi ti) — that exclusion is implicature;
; to'e (Opposite) does entail it.
```

```lisp
; mi djica tu'a lo cukta                      [pin P14]
(Bind (($book (Referents Entity)
        (Refer (λ (($x (Referents Entity))) (cukta $x)))))
  (Bind (($a (Referents Eventuality)          ; sort from djica's x2
          (Vague (λ (($v (Referents Eventuality)))
            (∧ (∃ (λ (($c Content))
                 (= $v (EventOfContent $c)))) ; shape: an abstraction
               (Close (srana $v $book)))))))  ; ... about the book
    (Assert (Close (djica Speaker $a)))))
```

Pinned reading: some eventuality-sorted abstraction — its content
deliberately withheld — pertaining to the book, the sort fixed by the
host place (`djica` x2). The shape conjunct matters: aboutness alone
would admit nearly anything.

```lisp
; ta barda — gradable predication: Context scale, Vague cutoff  [spec §6.4]
(Bind (($s Scale (Context))                    ; which size-scale: recoverable
       ($reg (Region Scale)
         (Vague (λ (($r (Region Scale))) (AdmissibleCutoff $s $r)))))
  (Assert (Close ((Grade barda $s $reg) That))))

; du'e gerku cu klama — Vague threshold, Context purpose  [spec §6.4]
(Bind (($purpose (Referents Entity) (Context))  ; too many FOR WHAT: recoverable
       ($n Natural
         (Vague (AdmissibleThreshold TooMany
                  (λ (($x Entity)) (gerku $x)) $purpose))))
  (Assert
    (MoreThan $n (λ (($x Entity)) (gerku $x))
                 (λ (($x Entity)) (Close (klama $x))))))

; mi co'e do — elliptical selbri: Context, not Vague   [spec §6.1]
(Bind (($r (PredTerm ⟨x1:(Referents Entity), x2:(Referents Entity)⟩)
        (Context)))
  (Assert (Close ($r Speaker Audience))))
```

The recovery test draws this line: `co'e` expects the hearer to recover
*the* relation; `tu'a` waives recovery.

## 9. Abstractions

```lisp
; lo du'u mi klama cu se djuno do
(Bind (($p (Referents Proposition)
        (Refer (λ (($q (Referents Proposition)))
          (= $q (Reify (Close (klama Speaker))))))))
  (Assert (Close (djuno Audience $p))))
; (= here at the Proposition sort via the singleton lift; se du'u — the
; expressing sentence — goes through the derived DuhuRel x2, spec §9.2.)

; lo ni mi klama — an abstraction relation, reference outside  [R2]
(Bind (($a (Referents Amount)
        (Refer (λ (($x (Referents Amount)))
          (Close ((NiRel (Close (klama Speaker))) $x))))))
  (Mention $a))
; the omitted scale x2 closed contextually — the same rule as any
; omitted place; le ni …, quantified ni, relative clauses on
; abstractions: all inherited from ordinary reference.

; lo su'u mi klama kei be lo fasnu — explicit categorizer (CLL 11.9)
(Bind (($kind (Referents Entity)
        (Refer (λ (($k (Referents Entity))) (fasnu $k)))))
  (Bind (($a (Referents AbstractNature)
          (Refer (λ (($x (Referents AbstractNature)))
            (Close ((SuhuRel (Close (klama Speaker))) $x $kind))))))
    (Mention $a)))

; lo nu mi pu klama — event abstraction: Refer at the event sort
(Bind (($ev (Referents Eventuality)
        (Refer (λ (($e (Referents Eventuality)))
          (∧ (Close (klama Speaker :Eventuality $e))
             (purci $e Now))))))
  (Mention $ev))
```

## 10. Signs and mention

```lisp
; lu mi klama li'u
(Mention (StructuredQuote
  (Utterance (($u UtteranceToken))
    (Realizes $u (Assert (Close (klama Speaker)))))))

; lo'u mi klama le'u — text, uninterpreted
(Mention (OpaqueQuote "mi klama"))

; zo klama cu valsi
(Assert (Close (valsi (WordSign "klama"))))

; la'e lu mi klama li'u — a sign's content
(Mention
  (InterpretContent
    (StructuredQuote
      (Utterance (($u UtteranceToken))
        (Realizes $u (Assert (Close (klama Speaker))))))))

; li re te'a ci du li bi — MEX with te'a (library)
(Assert (= (te'a 2 3) 8))
; contrast: me'o re te'a ci mentions the EXPRESSION sign, not 8:
; (Mention (Sign (($s (SignToken MathExpression))) (TextOf $s "re te'a ci")))

; la .bab. goi by. cu klama .i by. prami — letteral-keyed binding
(Bind (($bob (Referents Entity)
        (Refer (λ (($x (Referents Entity))) (Named "bab" $x)))))
  (Do (Assert (Close (klama $bob)))
      (Assert (Close (prami $bob)))))
; the letteral by. is a binding KEY resolved at the mapping layer;
; both occurrences consume the one binding.
```

## 11. The spiral sentence, in full

```lisp
; lo ci gerku noi blabi cu na batci re prenu .i .uinai cai ri tatpi
(Bind (($dogs (Referents Entity)
        (Refer (λ (($r (Referents Entity)))
          (∧ (gerku $r)
             (= (CardBasis $r (λ (($x Entity)) (gerku $x))) 3))))))
  (Do
    (Let (($a1 (Act Assertion)
            (Assert
              (Supplement $dogs (Close (blabi $dogs))
                (¬ (Exactly 2 (λ (($x Entity)) (prenu $x))
                     (λ (($x Entity)) (Close (batci $dogs $x)))))))))
      (Perform $a1))
    (Let (($a2 (Act Assertion) (Assert (Close (tatpi $dogs)))))
      (Do (Perform $a2)
          (Express (Display (unhappiness Speaker Intense) $a2))))))
```

(The indicator sits sentence-initially — `.uinai cai ri tatpi` — so its
grammatical target is the whole second assertion, per the CLL attachment
rule the mapping annex carries; placed after `ri` it would instead
display unhappiness about the dogs.) Everything committed: three real
dogs, introduced; their whiteness, as a projective aside the negation
never touches; the denial that a two-person witness set exists whom they
bit; their tiredness; and the speaker's displayed intense unhappiness
about that last claim. Everything open, on purpose: when; jointly or
severally; and which precisification of nothing — because nothing else
here is vague.

## 12. Meanings without analyses

Gap-register illustrations (spec §14) — sentences the core deliberately
does not yet analyze, kept as obligations:

```text
da'i mi ricfu .i da'i mi citka lo nobli
  — hypothetical mood: scope, binding under the shift, scenario identity.
lo'e mlatu cu cinri .i ri se nelci mi
  — generic anaphora: what does ri reach?
mi za'o citka
  — ZAhO contours pending their lexical boundary rows.
```
