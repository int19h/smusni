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
A specimen displayed as a bare act denotes the one-act discourse
performing it (spec §7.1). Where a description's referent is never
referred back to, specimens abbreviate `lo du'u c` to its object former
`(Reify c)` directly; the full `Refer` lowering (§9 below) differs only
in exporting the unused referent. The capitalized indicator relations
(`Happiness`, `Unhappiness`, `Desire`, `EvidentialBasis`) are §16
placeholders — see-also the UI emotion gismu the audit adopts.
CLL and dictionary citations follow the editions listed in the
specification's References section.

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
(pin P15; rationale §1.2).

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

Facet joining is dynamic conjunction over a shared event — there is no
dedicated joining operator, because plain `∧` over the shared event
variable already says everything one would say:

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
       (Close (pilno :2 This :3 $e))))))
; the host event fills pilno x3 (purpose) — the tag row's licensed link
; per the official row: x1 uses x2 for purpose x3.
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

Tenseless `mi citka` is **reading-multiple** (pin P8), never a default
present. Its episodic reading carries a `Context`-anchored occasion —

```lisp
; mi citka — the episodic reading: at the contextually relevant occasion
(Assert
  (Bind (($occ Time (Context)))
    (∃ (λ (($e (Referents Eventuality)))
      (∧ (Close (citka Speaker :Eventuality $e))
         (cabna $e $occ))))))
```

— while the habitual/gnomic reading carries no temporal conjunct at
all. Which reading was meant is resolved upstream, like any ambiguity.

## 3. Reference and descriptions

```lisp
; lo mlatu cu blabi              [pin P1]
(Bind (($cat (Referents Entity)
        (Refer (λ (($x (Referents Entity))) (mlatu $x)))))
  (Assert (Close (blabi $cat))))
```

Pinned reading: a new referent — one or more real cats, number-neutral,
no quantifier. Contrast: `su'o mlatu cu blabi` quantifies (though its
selected witness stays referable — §5 below); `lo` introduces with no
quantificational force at all.

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
          (Close (skicu Speaker $x Audience
            (λ (($y (Referents Entity))) (mlatu $y))))))))
  (Assert (Close (blabi $it))))
```

Pinned reading: reference through the speaker's identifying description —
non-veridical (the "cat" may be a raccoon), speaker-specific — lowered
through `skicu` itself (official x4 is the description property;
guskant's own `le` expansion is this term in Lojban), with the describing
event anchored to this very utterance's locution by the mapping clause:
saying `le mlatu` *is* the describing. (`Close` above is the brief
spelling; the anchoring clause identifies the describing event with the
utterance token's locution, §7.4, rather than closing it
existentially.)

```lisp
; la .alis. klama
(Bind (($alis (Referents Entity)
        (Refer (λ (($x (Referents Entity))) (Named "alis" $x)))))
  (Assert (Close (klama $alis))))
```

```lisp
; lo'i gerku — a set object via selcmi (xorxes' lujvo: x2 = members) [P5]
(Bind (($base (Referents Entity)
        (MaxRefer (λ (($x Entity)) (gerku $x)))))   ; the maximal base:
                                                    ; THE dogs, not some
  (Bind (($sets (Referents (Set Entity))
          (Refer (λ (($s (Referents (Set Entity))))
            (Close (selcmi $s $base))))))
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
; le gerku voi blabi cu jbena — voi: non-veridical restriction  [pin P10]
(Bind (($dog (Referents Entity)
        (Refer (λ (($x (Referents Entity)))
          (∧ (Close (skicu Speaker $x Audience            ; the le-head:
               (λ (($y (Referents Entity))) (gerku $y)))) ; "my dog"
             (Close ((DropPlace skicu 3) Speaker $x       ; the voi
               (λ (($y (Referents Entity))) (blabi $y)))))))))   ; restriction
  (Assert (Close (jbena $dog))))
; the voi conjunct's audience place is DELETED, not omitted — a voi
; description has no audience role; the le-head keeps its audience.
; Three-way contrast: poi (veridical restriction, in the property),
; noi (projective supplement, below), voi (non-veridical restriction
; through the describer).
```

```lisp
; lo gerku noi blabi cu na melbi     [pin P7]
(Bind (($dog (Referents Entity)
        (Refer (λ (($x (Referents Entity))) (gerku $x)))))
  (Assert
    (Supplement $dog (Close (blabi $dog))
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
          (Close (skicu Speaker $x Audience
            (λ (($y (Referents Entity))) (pendo $y))))))))
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
    (Assert (Close (bajra $dogs)))
    (Assert (Close (tatpi $dogs)))))
; the selection introduces and BINDS the witness; the anaphor is an
; ordinary bound occurrence — no free names, no retrieval operator.
; the nuclear predication is NEUTRAL (P4): each-ran comes from bajra's
; lexicon row, not from the quantifier — contrast ci prenu cu jmaji,
; where the three gather TOGETHER, same shape.
```

There is no retrieval operator: the exported witness *is* the three-dog
reference the selection binds, and nothing else is needed
(rationale §1.6).

```lisp
; ro prenu cu ponse ci gerku .i ri tatpi — dependent witness
; (one content, abbreviating the two performed assertions)
(Assert
  (Presuppose (∃ (λ (($x Entity)) (prenu $x)))
    (∧
      ; sentence 1's own claim — the ownership, never erased:
      (∀ (λ (($p Entity))
        (→ (prenu $p)
           (∃ (λ (($d (Referents Entity)))
             (∧ (= (CardBasis $d (λ (($x Entity)) (gerku $x))) 3)
                (Close (ponse $p $d))))))))
      ; the anaphoric continuation at the joint locus (strong reading):
      (∀ (λ (($p Entity) ($d (Referents Entity)))
        (→ (∧ (prenu $p)
              (= (CardBasis $d (λ (($x Entity)) (gerku $x))) 3)
              (Close (ponse $p $d)))
           (Close (tatpi $d))))))))
```

Pinned reading: each person owns three dogs, and each person's dogs are
tired — the anaphor normalizes into a joint locus with the governing
quantifier, and the normalization keeps the first sentence's assertion
(a bare conditional would be vacuously true of a dogless person). The
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
; lo xo prenu cu jmaji — ... no — inner-no answer      [pin P22]
; the answer "no" is elliptical lo no prenu cu jmaji (guskant),
; which lowers through the zero-count special case, never Refer:
(Assert
  (No (λ (($x Entity)) (prenu $x))
      (λ (($w (Referents Entity))) (Close (jmaji $w)))))
; the nuclear scope is reference-typed (spec §12): "no people-witness
; gathers" — the collective reading a distributive quantifier could not
; state at all.
; answer substitution into the question's frame works; anaphora to
; the form is inaccessible (No exports nothing — nothing to refer to).
```

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
dogs/people") is a distinct, marked meaning, never the
default. Referential termsets (`le ci gerku ce'e
le re prenu`) need no termset semantics at all: constants take no part
in scope distinctions (CLL 16.7), so the members predicate neutrally —
the full product there needs explicit `ro…ro` (CLL Example 16.46).

```lisp
; ci jbopre cu simxu lo ka tavla — a reciprocal    [spec §12]
(Bind (($trio (Referents Entity)
        (SelectExactly 3 (λ (($x Entity)) (jbopre $x)))))
  (Assert
    (Reciprocate $trio
      (λ (($a (Referents Entity)) ($b (Referents Entity)))
        (Close (tavla $a $b))))))
; simxu's lexicon row consumes the library's Reciprocate schema:
; pairwise both ways among the witness.
```

```lisp
; so'i prenu cu klama — vague quantity    [spec §6.4]
(Bind (($n Natural
        (Vague (AdmissibleThreshold ManyK (λ (($x Entity)) (prenu $x))))))
  (Assert
    (AtLeast $n (λ (($x Entity)) (prenu $x))
                (λ (($w (Referents Entity))) (Close (klama $w))))))
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
      (Express (Close (Happiness Speaker $a Moderate)))))

; .au mi sipna — propositional attitude: host subordinated  [spec §7.6]
(Express (Close (Desire Speaker (Reify (Close (sipna Speaker))))))
; no assertion of sleeping occurs — the host-force profile of .au.

; .uinai cai do klama — paired emotion, then degree   [spec §7.6]
(Let (($a (Act Assertion) (Assert (Close (klama Audience)))))
  (Do (Perform $a)
      (Express (Close (Unhappiness Speaker $a Intense)))))
```

```lisp
; za'a do cadzu — evidential grounding the act        [spec §7.6]
(Let (($a (Act Assertion) (Assert (Close (cadzu Audience)))))
  (Do (Perform $a)
      (Express (Close (EvidentialBasis Speaker $a Observation)))))
; act-level display: an Express beside the bound host act; the family
; force clause grounds the assertion (a mode of commitment);
; na za'a do cadzu negates the walking, never the basis.

; mi jinvi lo du'u ti'e do klama — evidential on embedded content
(Assert
  (Close
    (jinvi Speaker
      (Reify
        (Let (($p Proposition (Reify (Close (klama Audience)))))
          (Supplement $p
            (Close (EvidentialBasis Speaker $p Hearsay))
            (Holds $p)))))))
; content-level display: the content occurs ONCE, under a pure Reify
; shared by Let; Holds evaluates that same proposition object, so the
; anchor, the displayed basis, and the evaluated body all carry one set
; of contextual sites. The hearsay rides the embedded claim projectively
; — the reason evidentials are targeted display, not an operand on
; assertion force. (ti'e placed after du'u, targeting the abstraction's
; content, per the CLL attachment rule.)
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
; ta na'e melbi — scalar otherness            [spec §6.3]
(Assert (Close ((Scalar OtherThan melbi) That)))
; scale dimension: Context; region boundary: Vague.
; DENIES beauty AND asserts an admissible alternative standing on the
; recovered scale (CLL 15.4: a selbri negation "remains an assertion of
; some specific truth") — stronger than na, not weaker; to'e asserts
; the antipode, no'e the midpoint.
```

```lisp
; mi djica tu'a lo cukta                      [pin P14]
(Bind (($book (Referents Entity)
        (Refer (λ (($x (Referents Entity))) (cukta $x)))))
  (Bind (($a (Referents Eventuality)          ; sort from djica's x2
          (Vague (λ (($v (Referents Eventuality)))
            (∧ (∃ (λ (($c Content))
                 (CoRef $v (EventOfContent $c)))) ; shape: an abstraction
               (Close (srana $v $book)))))))      ; ... about the book
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
         (Vague (AdmissibleThreshold TooManyK
                  (λ (($x Entity)) (gerku $x)) $purpose))))
  (Assert
    (MoreThan $n (λ (($x Entity)) (gerku $x))
                 (λ (($w (Referents Entity))) (Close (klama $w))))))

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
          (CoRef $q (Reify (Close (klama Speaker))))))))
  (Assert (Close (djuno Audience $p))))
; CoRef (library) is plural co-reference — mutual Among — since typed =
; stays first-order; Reify is pure and lifts to a singleton reference.

; lo se du'u mi klama — the sentence expressing it (CLL 11.7 x2)
(Let (($p Proposition (Reify (Close (klama Speaker)))))
  (Bind (($s (Referents (Sign Sentence))
          (Refer (λ (($x (Referents (Sign Sentence))))
            ((DuhuRel (Close (klama Speaker))) $p :2 $x)))))
    (Mention $s)))
; x1 is filled with the reified content itself — the relation
; identifies it, so leaving x1 to contextual closure would add a
; retrieval the Lojban does not contain.

; lo ni mi klama — an abstraction relation, reference outside  [spec §9.2]
(Bind (($a (Referents Amount)
        (Refer (λ (($x (Referents Amount)))
          (Close ((NiRel (Close (klama Speaker))) $x))))))
  (Mention $a))
; the omitted scale x2 closed contextually — the same rule as any
; omitted place; le ni …, quantified ni, relative clauses on
; abstractions: all inherited from ordinary reference.

; lo su'u mi klama kei be lo fasnu — explicit categorizer (CLL 11.9)
(Bind (($kind (Referents Eventuality)
        (Refer (λ (($k (Referents Eventuality))) (fasnu $k)))))
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
; defined because the realized act is an assertion: InterpretContent is
; the content projection on assertion-realizing entries (spec §7.5).

; li re te'a ci du li bi — MEX with te'a (library)
(Assert (= (te'a 2 3) 8))
; contrast: me'o re te'a ci mentions the EXPRESSION sign, not 8:
; (Mention (Sign (($s (SignToken MathExpression))) (TextOf $s "re te'a ci")))

; li pa vu'u mo'e lo ni mi klama — the numeric crossing (CLL 11.5)
(Bind (($scale (Referents Scale) (Context)))      ; ONE scale, hoisted:
  (Bind (($amt (Referents Amount)                 ; it fills NiRel's x2
          (Refer (λ (($a (Referents Amount)))     ; AND reads the value
            ((NiRel (Close (klama Speaker))) $a $scale)))))
    (Mention (− 1 (AmountValue $amt $scale)))))
; mo'e = AmountValue: the amount's numeric value on the SAME scale that
; defined it (distinct Context sites would allow a mismatch — pin P15).

; lo jei mi klama — fuzzy truth degree (CLL 11.6)
(Bind (($ep (Referents Epistemology) (Context)))
  (Bind (($tv (Referents TruthValue)
          (Refer (λ (($v (Referents TruthValue)))
            ((JeiRel (Close (klama Speaker))) $v $ep)))))
    (Mention (TruthValueDegree $tv))))   ; a Number in [0,1]

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
; (episodic readings: each sentence's occasion is Context-anchored, P8)
(Bind (($dogs (Referents Entity)
        (Refer (λ (($r (Referents Entity)))
          (∧ (gerku $r)
             (= (CardBasis $r (λ (($x Entity)) (gerku $x))) 3))))))
  (Do
    (Bind (($occ1 Time (Context)))       ; the biting's occasion — bound
      (Let (($a1 (Act Assertion)         ; OUTSIDE the negation, so na
              (Assert                    ; denies biting AT that occasion
                (Supplement $dogs (Close (blabi $dogs))
                  (¬ (Exactly 2 (λ (($x Entity)) (prenu $x))
                       (λ (($ppl (Referents Entity)))
                         (∃ (λ (($e (Referents Eventuality)))
                           (∧ (Close (batci $dogs $ppl :Eventuality $e))
                              (cabna $e $occ1)))))))))))
        (Perform $a1)))
    (Bind (($occ2 Time (Context)))
      (Let (($a2 (Act Assertion)
              (Assert
                (∃ (λ (($e (Referents Eventuality)))
                  (∧ (Close (tatpi $dogs :Eventuality $e))
                     (cabna $e $occ2)))))))
        (Do (Perform $a2)
            (Express (Close (Unhappiness Speaker $a2 Intense))))))))
```

(The indicator sits sentence-initially — `.uinai cai ri tatpi` — so its
grammatical target is the whole second assertion, per the CLL attachment
rule the mapping annex carries; placed after `ri` it would instead
display unhappiness about the dogs.) Everything committed: three real
dogs, introduced; their whiteness, as a projective aside the negation
never touches; the denial that any two-person witness was bitten at the
contextually relevant occasion — the occasion binder sits outside the
`¬`, which is exactly the tenseless-denial semantics of P8 ("I didn't
turn off the stove" denies one particular failure); their tiredness at
its own occasion; and the speaker's displayed intense unhappiness
about that last claim. Everything open, on purpose: whether the biting
denial and the tiredness hold of the dogs jointly or severally (P4);
and which precisification of nothing — because nothing else
here is vague. The occasions are not open but *recovered*: `Context`,
not absence — the habitual readings, which would drop the temporal
conjuncts entirely, are the other members of P8's reading family.

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
