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
placeholders — see-also the `-nmo` indicator-emotion family the
audit adopts (spec §16.5).
At a force boundary, a displayed complete eventless Content may use spec §2's
actual-reading shorthand for
`CloseClause(ActualClause(StateClause(content)))`; examples in which the
clause-event or CAhA choice matters expand it.
CLL and dictionary citations follow the editions listed in the
specification's References section.
Displays carry provisional row assumptions pending #12's official rows — a
specimen reads each predicate with the arity its display uses — and the
checker's fixture lexicon (`tools/smusni-redex/inventory/fixtures.sexp`)
mirrors those assumptions rather than authorizing them; a lexical
predicate written bare in a pure position — `{λ [$x :: Entity] (gerku $x)}`
— abbreviates L0.1's hoisted form for the assumed row (spec §11).

## 1. Predication and closure

```lisp
; mi klama
(Assert
  (Close (klama Speaker)))
; ≝ (Assert (CloseClause (ActualClause (DirectClause (klama Speaker)))))
; this specimen selects the actual missing-CAhA reading; Close names that
; core composition; not a default imposed on the surface.
```

Expanded once to the primitive closure boundary, so the notation convention
is grounded (spec §4.6) — four contextual places and the event:

```lisp
; mi klama — Close expanded
(Assert
  {Bind [$to :: Referents Entity] (Context)
         [$from :: Referents Entity] (Context)
         [$via :: Referents Entity] (Context)
         [$by :: Referents Entity] (Context)
    (CloseClause
      {λ [$e :: Referents Eventuality]
        (∧ (klama Speaker $to $from $via $by :Eventuality $e)
           (fasnu $e))})})
```

Replacing `CloseClause` here with bare `∃e` would preserve the run
projection but discard the fact that the same `$e` is this assertion's
clause eventuality; it is therefore not a full-Content expansion.

Contrast: under negation the contextual places stay put — `mi na klama`
denies the going-to-the-contextual-place, and is not `¬∃destination…`
(pin P15; rationale §1.2).

```lisp
; klama fe ti tu — labelled fills; place 1 left contextual
(Assert (Close (klama :2 This Yonder)))
```

```lisp
; mi klama ti zi'o ti ti — the origin role removed; not omitted
(Assert (Close ((DropPlace klama 3) Speaker This This This)))
```

```lisp
; ti se klama mi — conversion consumed by the mapping; no Se operator
(Assert (Close (klama Speaker This)))
```

```lisp
; lo ka se klama — a converted relation escaping as a function
(Mention
  {λ [$x :: Referents Entity]
    (Close (klama :2 $x))})
```

## 2. Events, tense, facets

Facet joining is dynamic conjunction over a shared event — there is no
dedicated joining operator, because plain `∧` over the shared event
variable already says everything one would say:

```lisp
; mi pu citka
(Assert
  (CloseClause
    (ActualClause
      {λ [$e :: Referents Eventuality]
        (∧ ((DirectClause (citka Speaker)) $e)
           (purci $e Now))})))
```

```lisp
; mi pu pu citka — a tense path: past of a past reference point
(Assert
  (CloseClause
    (ActualClause
      {λ [$e :: Referents Eventuality]
        (∃ {λ [$m :: Referents Eventuality]
          (∧ ((DirectClause (citka Speaker)) $e)
             (purci $m Now)
             (purci $e $m))})})))
```

```lisp
; mi klama ti sepi'o ti — an instrumental facet; same event
(Assert
  (CloseClause
    (ActualClause
      {λ [$e :: Referents Eventuality]
        (∧ ((DirectClause (klama Speaker This)) $e)
           (Close (pilno :2 This :3 $e)))})))
; the host event fills pilno place 3 (purpose) — the tag row's licensed link
; per the official row: place 1 uses place 2 for purpose place 3.
```

Contrast (`nai` on the tag): `mi klama ti sepi'onai ti` negates only the
instrumental conjunct — `(∧ (klama …) (¬ (pilno …)))` — while bridi `na`
negates the whole conjunction. Both fall out of `∧` placement; nothing is
stipulated (rationale §1.13, the facet-decomposition entry).

```lisp
; mi ca'a citka — actuality as a facet
(Assert
  (CloseClause
    (ActualClause (DirectClause (citka Speaker)))))
```

Tenseless `mi citka` is **reading-multiple** (pin P8), never a default
present. Its episodic reading carries a `Context`-anchored occasion —

```lisp
; mi citka — the episodic reading: at the contextually relevant occasion
(Assert
  {Bind [$occ :: Time] (Context)
    (CloseClause
      {λ [$e :: Referents Eventuality]
        (∧ ((ActualClause (DirectClause (citka Speaker))) $e)
           (cabna $e $occ))})})
```

— while the habitual/gnomic reading carries no temporal conjunct at
all. Which reading was meant is resolved upstream, like any ambiguity.

Missing CAhA is independently reading-multiple (P24, CLL 10.19): the
episodic specimen selected `ActualClause`; a capability reading selects
`CapableClause` instead. Explicit `ca'a` fixes the former.

```lisp
; ro datka cu flulimna — CLL 10.19's bare capability reading
(Assert
  (CloseClause
    (StateClause
      (Every {λ [$x :: Entity] (datka $x)}
        {λ [$duck :: Entity]
          (CloseClause
            (CapableClause (DirectClause (flulimna $duck))))}))))
; Every's nuclear scope is member-level (§12: Distrib over the maximal
; reference); each duck's capability clause closes locally; the outer State
; is the universal claim. No one event is shared by every duck.
```

```lisp
; ta pu du lo mi zdani — tense on eventless identity [spec §4.6]
(Assert
  (CloseClause
    (ActualClause
      {λ [$s :: Referents Eventuality]
        (∧ ((StateClause
               {Bind [$home :: Referents Entity]
                     (Refer {λ [$x :: Referents Entity]
                       (zdani $x Speaker)})
                 (CoRef That $home)}) $s)
           (purci $s Now))})))
; The home description is inside StateClause; so its property is evaluated in
; $s: That may have been the home then without being it now. Hoisting $home
; outside gives the rigid de re reading. du/CoRef itself retains ordinary arity.
```

```lisp
; fragment: a physical parameter has value $x now but not in a future state
; $alpha :: Referents Entity
; $valueOf :: Fn ((Referents Entity)) Number  (state-sensitive projection)
; $x :: Number
(CloseClause
  (ActualClause
    (ClauseAnd
      {λ [$s :: Referents Eventuality]
        (∧ ((StateClause (= ($valueOf $alpha) $x)) $s)
           (cabna $s Now))}
      {λ [$t :: Referents Eventuality]
        (∧ ((StateClause (¬ (= ($valueOf $alpha) $x))) $t)
           (balvi $t Now))})))
; The two applications of $valueOf are inside their StateClauses and may vary.
; Binding the resulting Number outside instead would give the rigid de re case.
```

```lisp
; li re su'i re ca'a du li vo — CAhA on mathematical identity
(Assert
  (CloseClause
    (ActualClause
      (StateClause (= (+ 2 2) 4)))))
```

```lisp
; mi na klama — the negative State is the clause eventuality
(Assert
  (CloseClause
    (ActualClause
      (ClauseNot (DirectClause (klama Speaker))))))
```

```lisp
; mi klama .ije do stali — joint State; one assertion
(Assert
  (CloseClause
    (ActualClause
      (ClauseAnd (DirectClause (klama Speaker))
                 (DirectClause (stali Audience))))))

; mi klama .ija do stali — branch-relative event; one assertion
(Assert
  (CloseClause
    (ActualClause
      (ClauseOr (DirectClause (klama Speaker))
                (DirectClause (stali Audience))))))
```

The constitution contribution underlying `mi sanga .i joi do dansu` is now
fully typed even though #6 still owns the compound act/transcript plan:

```lisp
; κ :: DecompositionBasis<Eventuality;Eventuality>; recovered for this joi
(JoiClause $κ
  (DirectClause (sanga Speaker))
  (DirectClause (dansu Audience)))
```

Applying this `ClauseContent` to `$j` evaluates the singing and dancing once,
requires `$j` to be their complete joint event at κ, and makes `$j` actual.
`CloseClause` would retain `$j` as the compound content's event; it would not
export either component event. This is deliberately not displayed as an
`Assert`: deciding the structured one-performance wrapper, component roles,
and UI/span targeting is the remaining `ConnectionPlan` gap, not part of
`JoiClause`.

## 3. Reference and descriptions

```lisp
; lo mlatu cu blabi              [pin P1]
{Bind [$cat :: Referents Entity]
        (Refer {λ [$x :: Referents Entity] (mlatu $x)})
  (Assert (Close (blabi $cat)))}
```

Pinned reading: a new referent — one or more real cats, number-neutral,
no quantifier. Contrast: `su'o mlatu cu blabi` quantifies (though its
selected witness stays referable — §5 below); `lo` introduces with no
quantificational force at all.

`lo R` remains literally `Refer R`; where R's resolved lexical mode declares
a unit profile, its plural extension already includes `CoveredBy`. The
atomless witness motivating that condition can be displayed directly. The
first conjunct says the bread is covered by cumulative bread units; the second
is guskant's Condition₁ — every subreference has a proper subreference, so no
atomic member basis is available:

```lisp
; atomless bread reference — CoveredBy succeeds without atomic members [P39]
{λ [[$bread :: Referents Entity]
    [$breadUnit :: Fn (Entity) Content]]
  (∧ (CoveredBy $breadUnit $bread)
     (∀ {λ [$r :: Referents Entity]
       (→ (Among $r $bread)
          (∃ {λ [$s :: Referents Entity]
            (∧ (Among $s $r) (¬ (Among $r $s)))}))}))}
```

An atomic count profile is the familiar special case: a selected dog witness
containing a cat or a pack object fails `CoveredBy(dogUnit, ·)`. A collective
predicate such as `jmaji` need not declare that profile and is not silently
distributed.

```lisp
; lo mlatu na jbena — the referent scopes outside negation
{Bind [$cat :: Referents Entity]
        (Refer {λ [$x :: Referents Entity] (mlatu $x)})
  (Assert
    (CloseClause (ClauseNot (DirectClause (jbena $cat)))))}
```

```lisp
; le mlatu cu blabi              [pin P10]
{Bind [$it :: Referents Entity]
        (Refer {λ [$x :: Referents Entity]
          (SpeakerDescribes $x
            {λ [$y :: Referents Entity] (mlatu $y)})})
  (Assert (Close (blabi $it)))}
```

Pinned reading: reference through the speaker's identifying description —
non-veridical (the "cat" may be a raccoon), speaker-specific — lowered
through `skicu` itself (official x4 is the description property;
guskant's own `le` expansion is this term in Lojban), with the describing
event anchored to this very utterance's locution by the mapping clause:
saying `le mlatu` *is* the describing. (`SpeakerDescribes` is §12's
defined form, displayed as itself: its definition identifies the
describing event with the utterance token's locution, §7.4, rather than
closing it existentially — #41.)

```lisp
; la .alis. klama
{Bind [$alis :: Referents Entity]
        (Refer {λ [$x :: Referents Entity] (Named "alis" $x)})
  (Assert (Close (klama $alis)))}
```

Composite personal pro-sumti are ordinary plural references (P40):

```lisp
; mi'o remna — one member-level-compatible predication [P40]
(Assert (Close (remna (Combine Speaker Audience))))
```

This is the carrier probe. No component-to-group inheritance would make a
constituted group human merely because the speaker and audience are humans.
For a collective relation, `mi'o` and explicit `jo'u` still give the same one
argument:

```lisp
; mi'o jmaji ≡ mi jo'u do jmaji — one neutral plural predication [P40]
(Assert (Close (jmaji (Combine Speaker Audience))))
```

Logical connection is structurally stronger, with two separately
instantiated clauses:

```lisp
; mi .e do jmaji — speaker gathers AND audience gathers [P40]
(Assert
  (CloseClause
    (ClauseAnd (DirectClause (jmaji Speaker))
               (DirectClause (jmaji Audience)))))
```

Constitution is a different typed result even before any group-level
predicate is chosen:

```lisp
; mi joi do — the distinct canonical Group<Entity> reading [P40]
{Bind [$κ :: DecompositionBasis (Group Entity) Entity]
      (Context (GroupBasisConstraint joi Entity) deps…)
  {Bind [$group :: Referents (Group Entity)]
        (JoiGroup $κ Speaker Audience)
    (Mention $group)}}
```

One composite argument does not duplicate its omitted places. This expansion
isolates x2: exactly one destination value is recovered for the one plural-x1
journey predication; the value may itself be plural, but there is no hidden
speaker-to-one/audience-to-another pairing:

```lisp
; mi'o klama — one place-1 value and one omitted place-2 Context site [P40]
{Bind [$to :: Referents Entity] (Context)
  (Assert
    (Close (klama (Combine Speaker Audience)
                  :2 $to :3 This :4 That :5 Yonder)))}
```

The sibling forms use named token-context projections whose §5.1 constraints
make the “others” genuinely other and enforce the exclusions:

```lisp
; mi'a / do'o / ma'a — their complete reference values [P40]
(Do
  (Mention (Combine Speaker MiAOthers))
  (Mention (Combine Audience DoOOthers))
  (Mention (Combine (Combine Speaker Audience) MaAOthers)))
```

Positive `mi'o … mei` remains #24: it cannot change any of these values into
a covert group.

```lisp
; lo'i gerku — a set object via selcmi (xorxes' lujvo: place 2 = members) [P5]
{Bind [$base :: Referents Entity]
        (Local (Refer {λ [$x :: Entity] (gerku $x)})) ; ordinary base via the
                                                        ; §5.3 member lift; not
                                                        ; a surface DR
  {Bind [$sets :: Referents (Set Entity)]
          (Refer {λ [$s :: Set Entity]
            (Close (selcmi $s $base))})
    (Mention $sets)}}
```

`loi gerku` uses the complete constitution layer, not free `gunma`'s
partial-friendly layer:

```lisp
; loi gerku — κ is the occurrence's resolved group basis
{Bind [$base :: Referents Entity]
      (Local (Refer {λ [$x :: Entity] (gerku $x)}))
  {Bind [$κ :: GroupBasis Entity]
         (Context (GroupBasisConstraint loi Entity) deps…)
    {Bind [$groups :: Referents (Group Entity)]
           (Refer {λ [$g :: Group Entity]
             (CompleteGunmaAt $κ $g $base)})
      (Mention $groups)}}}
; the outer restrictor is member-level: by the §5.3 lift the reference is
; CoveredBy that property — each qualifying group qualifies individually
```

Neither object unwraps to its members implicitly. A maximal all-dogs base is
available only when context or explicit `ro`/`MaxRefer` supplies it; bare
collection gadri do not force it. `CompleteGunmaAt` says there is no peer
component beyond `$base`; P39 separately makes a count-profile base
`CoveredBy` its declared units, while cumulative mass and other reference
modes keep their own exact lexical extension.
The `Local` boundary is independently observable: in CLL Example 6.52
`lo'i ratcu cu barda .i ku'i lu'a ri cmalu`, `ri` resolves to `$sets`, never
to the lowering-internal `$base`.

```lisp
; mi joi do bevri lo pipno — one constituted group carries
{Bind [$κ :: GroupBasis Entity]
      (Context (GroupBasisConstraint joi Entity) deps…)
  {Bind [$g :: Referents (Group Entity)]
         (JoiGroup $κ Speaker Audience)
    {Bind [$p :: Referents Entity]
           (Refer {λ [$r :: Referents Entity] (pipno $r)})
      (Close (bevri $g $p))}}}
```

The nearby `mi jo'u do bevri lo pipno` instead fills x1 with
`(Combine Speaker Audience)`: no group object and no covert
non-distributivity instruction.

The group result above is canonical manufacture: by definition
`(JoiGroup $κ Speaker Audience)` is
`(Massify $κ (Combine Speaker Audience))`. This does not identify every
same-member organization with that aggregate. In a scene with two distinct
same-roster committees, `lei ci prenu du le kamni` is true exactly when the
two descriptions select the same `Group<Entity>` object; the shared cover
does not force it. If one member later leaves, `ri` after `lei ci prenu`
continues to denote the originally selected object: a persistent committee's
`(components_κ ri)` may then be the remaining two, while a snapshot aggregate
of the original three retains that rigid cover.

Explicit `lu'o` canonicalizes: `lu'o le ci prenu` lowers, after resolving the
three-person reference and κ, to `(Massify κ people)`. Applied to a committee
it returns the canonical aggregate of the committee's current complete cover,
not automatically the committee. `lu'a` of one group uses the partial
`components_κ`; `lu'a` of one set uses its members; ordinary plural `lu'a`
marks `Distrib`. `lu'i` forms the exact set of units at a resolved covering
basis and is undefined without one (never an atomless-to-empty default).
`vu'i` forms an ordered `List`; an intended order is one `Context` site, while
a genuinely order-free use remains gap-registered.

The following fragment begins after `le kamni` has supplied its resolved group
reference and after κ has been resolved. It makes the contingency in the
preceding prose explicit: the `lei` description ranges over any group complete
over the three-person base, and identity with the independently selected
committee is asserted rather than derived from that cover.

```lisp
; lei ci prenu du le kamni — fragment after resolving le kamni and κ
{λ [[$κ :: DecompositionBasis (Group Entity) Entity]
    [$committee :: Referents (Group Entity)]]
  {Bind [$people :: Referents Entity]
        (Local (SelectExactly 3 {λ [$x :: Entity]
          (SpeakerDescribes $x
            {λ [$y :: Referents Entity] (prenu $y)})}))
    {Bind [$described :: Referents (Group Entity)]
          (Refer {λ [$g :: Group Entity]
                   (CompleteGunmaAt $κ $g $people)})
      (Assert (CoRef $described $committee))}}}
```

Canonical manufacture and the partial group-to-components crossing are
separate operations:

```lisp
; lu'o le ci prenu — canonical aggregate of the selected people
{Bind [$people :: Referents Entity]
      (Local (SelectExactly 3 {λ [$x :: Entity]
        (SpeakerDescribes $x
          {λ [$y :: Referents Entity] (prenu $y)})}))
  {Bind [$κ :: DecompositionBasis (Group Entity) Entity]
        (Context (GroupBasisConstraint lu'o Entity) deps…)
    {Bind [$aggregate :: Referents (Group Entity)] (Massify $κ $people)
      (Mention $aggregate)}}}
```

```lisp
; lu'a ri — fragment: components of the previously selected single group
{λ [[$κ :: DecompositionBasis (Group Entity) Entity]
    [$group :: Group Entity]]
  (Mention (components_κ $κ $group))}
; components_κ takes one Group<T> object (§12); ri's projective singular
; condition is what supplies that sole group and is elided here.
```

The bridge `lu'o mi'o cu remei ≡ mi'o remei` is still not claimed: P40 now
fixes `mi'o`'s plural side, while #24 still owns the missing positive
plural-`MeiRel` instance needed for the right-hand form.

```lisp
; lo'e mlatu cu cinri            [pin P11]
(Assert
  (Generic Typical
    {λ [$x :: Entity] (mlatu $x)}
    {λ [$x :: Entity] (Close (cinri $x))}))
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
{Bind [$cat :: Referents Entity]
        (Refer {λ [$x :: Referents Entity]
          (∧ (mlatu $x) (blabi $x))})
  (Assert (Close (jbena $cat)))}
```

```lisp
; le gerku voi blabi cu jbena — voi: non-veridical restriction  [pin P10]
{Bind [$dog :: Referents Entity]
        (Refer {λ [$x :: Referents Entity]
          (∧ (SpeakerDescribes $x            ; the le-head:
               {λ [$y :: Referents Entity] (gerku $y)}) ; "my dog"
             (SpeakerDescribesUnaddressed $x       ; the voi
               {λ [$y :: Referents Entity] (blabi $y)}))})   ; restriction
  (Assert (Close (jbena $dog)))}
; the voi conjunct's audience place is DELETED; not omitted — a voi
; description has no audience role; the le-head keeps its audience.
; Both anchor the describing event to this utterance's locution (#49).
; Three-way contrast: poi (veridical restriction; in the property);
; noi (projective supplement; below); voi (non-veridical restriction
; through the describer).
```

```lisp
; lo gerku noi blabi cu na melbi     [pin P7]
{Bind [$dog :: Referents Entity]
        (Refer {λ [$x :: Referents Entity] (gerku $x)})
  (Assert
    (Supplement $dog (Close (blabi $dog))
      (CloseClause (ClauseNot (DirectClause (melbi $dog))))))}
```

Pinned reading: whiteness is a projective side commitment — the negation
touches only the beauty claim. Contrast: `xu lo gerku noi blabi cu melbi`
questions beauty and still commits whiteness; and the restrictive
`poi`-variant above puts whiteness *inside* what `na` can reach through
the description.

```lisp
; mi tavla le pendo goi ko'a — aliasing is shared binding
{Bind [$friend :: Referents Entity]
        (Refer {λ [$x :: Referents Entity]
          (SpeakerDescribes $x
            {λ [$y :: Referents Entity] (Close (pendo $y))})})
  (Assert (Close (tavla Speaker $friend)))}
; the second place of pendo is omitted inside the description — one Context site (L1.6)
; later ko'a occurrences consume the same binding.  [pin P16]
```

Contrast (`ko'a` never assigned): a keyed contextual retrieval — one
value per key, so `ko'a du ko'a` is reflexively true.

## 5. Quantifiers, witnesses, anaphora

```lisp
; ci gerku cu bajra .i ri tatpi      [spec §5.6]
{Bind [$dogs :: Referents Entity]
        (SelectExactly 3 {λ [$x :: Entity] (gerku $x)})
  (Do
    (Assert (Close (bajra $dogs)))
    (Assert (Close (tatpi $dogs))))}
; the selection introduces and BINDS the witness; the anaphor is an
; ordinary bound occurrence — no free names; no retrieval operator.
; the nuclear predication is NEUTRAL (P4): each-ran comes from bajra's
; lexicon row; not from the quantifier — contrast ci prenu cu jmaji;
; where the three gather TOGETHER; same shape.
```

There is no retrieval operator: the exported witness *is* the three-dog
reference the selection binds, and nothing else is needed
(rationale §1.6).

```lisp
; ro prenu cu ponse ci gerku .i ri tatpi — dependent witness
; truth-conditional joint-locus artifact; the discourse keeps two Host acts
(Presuppose (∃ {λ [$x :: Entity] (prenu $x)})
  (∧
      ; sentence 1's own claim — the ownership; never erased:
      (∀ {λ [$p :: Entity]
        (→ (prenu $p)
           (∃ {λ [$d :: Referents Entity]
             (∧ (Distrib {λ [$x :: Entity] (gerku $x)} $d)
                (= (CardBasis $d {λ [$x :: Entity] (gerku $x)}) 3)
                (Close (ponse $p $d)))}))})
      ; the anaphoric continuation at the joint locus (strong reading):
      (∀ {λ [[$p :: Entity] [$d :: Referents Entity]]
        (→ (∧ (prenu $p)
              (Distrib {λ [$x :: Entity] (gerku $x)} $d)
              (= (CardBasis $d {λ [$x :: Entity] (gerku $x)}) 3)
              (Close (ponse $p $d)))
           (Close (tatpi $d)))})))
```

Pinned reading: each person owns three dogs, and each person's dogs are
tired — the resolver selects the strong joint-locus construal and the mapping
lowers that reading with the governing quantifier; the lowering keeps the
first sentence's assertion
(a bare conditional would be vacuously true of a dogless person). The
summed reading ("all the dogs together") requires explicit collection. This
is not an equivalent rewrite of the original selection computation: two
qualifying dog witnesses, only one tired, separate them. The present rule pays
with retroactive strengthening; plural-information states are the recorded
repair, while the weak selected-witness comparison is not a baseline Lojban
reading without a surface selector.

This displayed Content does not collapse the two written sentences into one
performance: the discourse mapping retains two `Host` occurrences and uses
the artifact to state the selected cross-sentence truth constraint.

```lisp
; ro prenu poi ponse su'o xasli cu darxi ri — donkey   [pin P6]
(Assert
  (Presuppose (∃ {λ [$x :: Entity]
                (∧ (prenu $x)
                   (∃ {λ [$y :: Entity] (∧ (xasli $y) (Close (ponse $x $y)))}))})
    (∀ {λ [[$p :: Entity] [$d :: Referents Entity]]
      (→ (∧ (prenu $p)
            (Distrib {λ [$z :: Entity] (xasli $z)} $d)
            (Close (ponse $p $d)))
         (Close (darxi $p $d)))})))
; $d at the plural type: the witness donkeys — the Distrib conjunct
; is the selection's own witness law; so the locus ranges over
; donkey-witness pluralities only; the atomic-pair spelling is the
; distributive strengthening.
```

```lisp
; ro gerku cu blabi — importing universal   [pin P2]
(Assert
  (Every {λ [$x :: Entity] (gerku $x)}
         {λ [$x :: Entity] (Close (blabi $x))}))
; ≝ {Bind [$w :: Referents Entity] (MaxRefer gerku-property)
;      (Distrib blabi-property $w)} per spec §12: MaxRefer's own Presuppose
; carries the import and the maximal witness $w is exported for later
; anaphora. The bare Presuppose(∃ gerku)(∀ x. gerku x → blabi x) has the
; same truth conditions but exports nothing — it is the truth-condition
; artifact of spec §5.6 rather than the lowering.
```

Contrast: `naku ro gerku cu blabi` — the nonemptiness presupposition
projects; only the universal is negated. Bare-logic `ro da` carries no
presupposition.

```lisp
; lo xo prenu cu jmaji — ... no — inner-no answer      [pin P22]
; the answer "no" is elliptical lo no prenu cu jmaji (guskant);
; which lowers through the zero-count special case; never Refer:
(Assert
  (No {λ [$x :: Entity] (prenu $x)}
      {λ [$w :: Referents Entity] (Close (jmaji $w))}))
; the nuclear scope is reference-typed (spec §12): "no people-witness
; gathers" — the collective reading a distributive quantifier could not
; state at all.
; answer substitution into the question's frame works; anaphora to
; the form is inaccessible (No exports nothing — nothing to refer to).
```

```lisp
; ci gerku ce'e re prenu cu nelci    [pin P17]
{Bind [$dogs :: Referents Entity]
        (SelectExactly 3 {λ [$x :: Entity] (gerku $x)})
        [$people :: Referents Entity]
        (SelectExactly 2 {λ [$x :: Entity] (prenu $x)})
  (Assert
    (Distrib {λ [$d :: Entity]
      (Distrib {λ [$p :: Entity]
         (Close (nelci $d $p))} $people)} $dogs))}
; co-selected plural witnesses (the selections commute — one joint
; locus; P25's referential discipline); the member-wise Distrib nest
; is the full product
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
{Bind [$trio :: Referents Entity]
        (SelectExactly 3 {λ [$x :: Entity] (jbopre $x)})
  (Assert
    (Reciprocate $trio
      {λ [$a $b :: Referents Entity]
        (Close (tavla $a $b))}))}
; simxu's lexicon row consumes the library's Reciprocate schema:
; pairwise both ways among the witness.
```

```lisp
; so'i prenu cu klama — vague quantity    [spec §6.4]
{Bind [$n :: Natural]
        (Vague (AdmissibleThreshold ManyK {λ [$x :: Entity] (prenu $x)}))
  (Assert
    (AtLeast $n {λ [$x :: Entity] (prenu $x)}
                {λ [$w :: Referents Entity] (Close (klama $w))}))}
```

No exact count hides here: the term denotes the family over admissible
thresholds, and `na so'i prenu cu klama` negates pointwise (spec §6.5).

## 6. Acts, questions, answers

```lisp
; xu mi klama
(Ask (Polar (Close (klama Speaker))))

; ma klama
(Ask (OpenQ {λ [$x :: Referents Entity] (Close (klama $x))}))

; ti mo — an open relation question
(Ask (OpenQ {λ [$r :: PredTerm (Row (1 (Referents Entity)))]
  (Close ($r This))}))

; klama fi'a ti — a place question           [spec §4.7]
(Ask (OpenQ {λ [$p :: CompatibleLabel (RowOf klama) (Referents Entity)]
  (Close (At klama $p This))}))
; the computed-label domain is the compatible refinement (§4.7): the
; event place and any sort-incompatible place contribute no branch
```

```lisp
; mi cusku lu mi klama li'u — reported; not performed
(Assert
  (Close
    (cusku Speaker
      (StructuredQuote
        (Utterance {$u :: UtteranceToken}
          {(∧ (SpeakerOf $u Speaker)
          (Realizes $u (Assert (Close (klama Speaker)))))})))))
```

The `Realizes` fact above describes a raw act package inside quotation; it
does not create a performance occurrence. Contrast the performance boundary:

```lisp
; one reusable package; two performance occurrences
{Let [$a :: Act Assertion] (Assert (Close (klama Speaker)))
  (Do (Perform $a) (Perform $a))}
```

The two `Perform` nodes create distinct `ActOccurrence`s even if this
fixture's contexts agree. In two transcript entries with different speakers,
grounds, or `Context` answers, `(ActContent $a)` remains the same raw package
while `RealizedContent(u₁)` and `RealizedContent(u₂)` may differ.

```text
E₁.ctx.speaker = Alice, E₂.ctx.speaker = Bob, oᵢ ∈ run(Perform_Eᵢ(a))
o₁ = ⟨a,u₁,Host,capture(E₁)⟩ ≠ o₂ = ⟨a,u₂,Host,capture(E₂)⟩
ActContent(a) is one raw value;
RealizedContent(u₁) = content(a) closed under capture(E₁)
RealizedContent(u₂) = content(a) closed under capture(E₂)
```

The lowercase operations in this display are model notation, not term-level
inspectors; core terms receive only the opaque `$oᵢ` handles.

```lisp
; la'e do'i — proposition reading of a salient performed assertion
{Bind [$u :: Referents UtteranceToken] (Context)
  (Mention (Reify (RealizedContent $u)))}
```

`RealizedContent` is partial and inert: `$u` must select one eligible
performed, context-resolved host assertion occurrence; its attached
UI acts do not compete. Cross-performance default whole-assertion `go'i` reuses
that occurrence content. `go'i ra'o` instead starts from raw
`(ActContent (RealizedAct<Assertion> $u))` as its source template, selectively
reinterprets the marked pro-assign sites in the new utterance
context/`ShiftedGround`, and retains every unrelated captured `Context` site.
If an override widens a captured site's governor and reaches a dependency
tuple absent from the antecedent run, it consults the original capture's
full-domain partial resolver: reuse gets that original-context value when
defined and projective undefinedness otherwise, never fresh caller resolution.

```lisp
; mi djuno lo du'u ma kau klama      [pin P9]
(Assert
  (Close
    (djuno Speaker
      (Reify
        (Answer
          (OpenQ {λ [$x :: Referents Entity] (Close (klama $x))})
          ContextualAnswer)))))
```

Pinned reading: answerhood committed; the exhaustivity slot is *absent* —
the weakest reading, with any completeness demand coming from `djuno`'s
own lexical presupposition, never from `kau`.

## 7. Indicators

```lisp
; .ui do klama — pure emotion: host asserted; joy displayed
{Let [$a :: Act Assertion] (Assert (Close (klama Audience)))
  {Bind [$o :: ActOccurrence Assertion] (Perform Host $a)
    (Do (Perform AttachedDisplay
      (Express (Close (Happiness Speaker $o Moderate)))))}}

; .au mi sipna — propositional attitude: host subordinated  [spec §7.6]
(Express (Close (Desire Speaker (Reify (Close (sipna Speaker))))))
; no assertion of sleeping occurs — the host-force profile of .au.

; .uinai cai do klama — paired emotion; then degree   [spec §7.6]
{Let [$a :: Act Assertion] (Assert (Close (klama Audience)))
  {Bind [$o :: ActOccurrence Assertion] (Perform Host $a)
    (Do (Perform AttachedDisplay
      (Express (Close (Unhappiness Speaker $o Intense)))))}}
```

```lisp
; za'a do cadzu — evidential grounding the act        [spec §7.6]
{Let [$a :: Act Assertion] (Assert (Close (cadzu Audience)))
  {Bind [$o :: ActOccurrence Assertion] (Perform Host $a)
    (Do (Perform AttachedDisplay
      (Express (Close (EvidentialBasis Speaker $o Observation)))))}}
; act-level display: Perform returns the bound occurrence handle; the family
; force clause grounds THIS occurrence (a mode of commitment);
; a later Perform $a returns a different; ungrounded occurrence;
; na za'a do cadzu negates the walking; never the basis.

; mi jinvi lo du'u ti'e do klama — evidential on embedded content
(Assert
  (Close
    (jinvi Speaker
      (Reify
        {Let [$p :: Proposition] (Reify (Close (klama Audience)))
          (Supplement $p
            (Close (EvidentialBasis Speaker $p Hearsay))
            (Holds $p))}))))
; content-level display: the content occurs ONCE; under a pure Reify
; shared by Let; Holds evaluates that same proposition object; so the
; anchor; the displayed basis; and the evaluated body all carry one set
; of contextual sites. The hearsay rides the embedded claim projectively
; — the reason evidentials are targeted display; not an operand on
; assertion force. (ti'e placed after du'u; targeting the abstraction's
; content; per the CLL attachment rule.)
```

```lisp
; .i mi klama .i ku'i do stali — a discourse relation
{Let [$a1 :: Act Assertion] (Assert (Close (klama Speaker)))
  {Bind [$o1 :: ActOccurrence Assertion] (Perform Host $a1)
    {Let [$a2 :: Act Assertion] (Assert (Close (stali Audience)))
      {Bind [$o2 :: ActOccurrence Assertion] (Perform Host $a2)
        (Do (Perform AttachedDisplay
          (Express (Close (Contrast $o2 $o1)))))}}}}
```

```lisp
; do klama .i na'i — metalinguistic objection         [spec §7.3]
{Let [$prior :: Act Assertion] (Assert (Close (klama Audience)))
  {Bind [$prioro :: ActOccurrence Assertion] (Perform Host $prior)
    {Bind [$defect :: DefectKind] (Context)
      (Express
        (Close (MetalinguisticallyDefective $prioro $defect)))}}}
; the defect dimension is contextually recovered; nothing is negated;
; and the objection itself performs nothing beyond the display.
```

## 8. Intended underspecification and soritical vagueness

```lisp
; mi sutra klama — one intended link recovered at this occurrence [spec §6.2]
(Assert
  (Close ((Tanru sutra klama) Speaker)))
; ≗ {Bind [$link :: PredTerm (RowOf klama)]
;         (Context {λ [$r :: PredTerm (RowOf klama)]
;                    (TanruAdmissible sutra klama $r)})
;     … (∧ (klama …) ($link …))}
; no governor dependencies in this reading. `na sutra klama` retrieves
; one intended admissible link at that occurrence's site and negates that claim;
; it does not quantify over every possible tanru link.
```

```lisp
; ta na'e melbi — scalar otherness            [spec §6.3]
{Bind [$d :: ContrastDomain (RowOf melbi)] (Context)
  (Assert (Close ((Scalar OtherThan $d melbi) That)))}
; contrast domain: visible Context site; any soritical boundary: Vague.
; DENIES beauty AND directly asserts membership in the complement of
; beauty's region in the recovered domain (CLL 15.4: selbri negation
; "remains an assertion of some specific truth"). No finer alternative is
; selected; to'e uses the domain's antipode; no'e its between-region.
```

```lisp
; mi djica tu'a lo cukta                      [pin P14]
{Bind [$book :: Referents Entity]
        (Refer {λ [$x :: Referents Entity] (cukta $x)})
  {Bind [$a :: Referents Eventuality]          ; sort from djica's place 2
          (Context {λ [$v :: Referents Eventuality]
            (∧ (∃ {λ [$p :: Proposition]
                 (CoRef $v (EventOfContent (Holds $p)))}) ; clause-event shape
               (Close (srana $v $book)))}
            $book)                               ; depends on this book
    (Assert (Close (djica Speaker $a)))}}
```

Pinned reading: the occurrence-specifically intended eventuality-sorted
abstraction pertaining to the book, its sort fixed by the host place
(`djica` x2). The speaker declines to spell it out; the hearer need only
recover it closely enough for the discourse. The shape conjunct matters:
aboutness alone would admit nearly anything, and negation must target this
one intended abstraction rather than every book-related event.

The positive/negative pattern is uniform for tanru links, `tu'a`
abstractions, bare-`jai` roles, and topic resolutions (with `C` the at-issue
content built from the recovered value):

```lisp
; positive                                  ; negative
{Bind [$v :: T] (Context P deps…)           {Bind [$v :: T] (Context P deps…)
  (C $v)}                                     (¬ (C $v))}
```

Within either resolved reading, the occurrence site produces one `$v`; the
logical operator consumes a claim containing that value. There is no positive
existential search for a truth-making alternative and no negative universal
denial of all admissible alternatives.

```lisp
; mi jai rinka lo nu do morsi — a typed bare-jai role site [spec §12]
{Bind [$death :: Referents Eventuality]
      (Refer {λ [$e :: Referents Eventuality]
        (Close (morsi :1 Audience :Eventuality $e))})
  {Bind [$role :: Fn ((Referents Entity) (Referents Eventuality)) Content]
        (Context
          {λ [$k :: Fn ((Referents Entity) (Referents Eventuality)) Content]
            (JaiRoleAdmissible rinka $k)})
    (Assert
      (Close ((JaiRaise rinka $role) :1 Speaker :2 $death)))}}
; T = Entity and A = Eventuality in this reading. The unfilled fai place
; retrieves the hidden cause event; the intended role relates Speaker to it.
```

```lisp
; ta barda — gradable predication: Context scale; Vague cutoff  [spec §6.4]
{Bind [$s :: Scale] (Context)                    ; which size-scale: recoverable
       [$reg :: Region Scale]
         (Vague {λ [$r :: Region Scale] (AdmissibleCutoff $s $r)})
  (Assert (Close ((Grade barda $s $reg) That)))}

; du'e gerku cu klama — Vague threshold; Context purpose  [spec §6.4]
{Bind [$purpose :: Referents Entity] (Context)  ; too many FOR WHAT: recoverable
       [$n :: Natural]
         (Vague (AdmissibleThreshold TooManyK
                  {λ [$x :: Entity] (gerku $x)} $purpose))
  (Assert
    (MoreThan $n {λ [$x :: Entity] (gerku $x)}
                 {λ [$w :: Referents Entity] (Close (klama $w))}))}

; mi co'e do — elliptical selbri: Context; not Vague   [spec §6.1]
{Bind [$r :: PredTerm
              (Row (1 (Referents Entity)) (2 (Referents Entity)))]
        (Context)
  (Assert (Close ($r Speaker Audience)))}
```

Both `co'e` and `tu'a` pass the intended-value recovery test. `co'e`
retrieves the intended relation at relation type; `tu'a` retrieves a
host-sorted abstraction under shape/aboutness and dependency constraints.
Neither has a baseline no-particular-value reading. `Vague` begins only where
there is no intended soritical boundary, as in the cutoff examples above.

## 9. Abstractions

```lisp
; lo du'u mi klama cu se djuno do
{Bind [$p :: Referents Proposition]
        (Refer {λ [$q :: Referents Proposition]
          (CoRef $q (Reify (Close (klama Speaker))))})
  (Assert (Close (djuno Audience $p)))}
; CoRef (library) is plural co-reference — mutual Among — since typed =
; stays first-order; Reify is pure and lifts to a singleton reference.

; lo se du'u mi klama — the sentence expressing it (CLL 11.7 place 2)
{Let [$p :: Proposition] (Reify (Close (klama Speaker)))
  {Bind [$s :: Referents (Sign Sentence)]
          (Refer {λ [$x :: Referents (Sign Sentence)]
            ((DuhuRel (Close (klama Speaker))) $p :2 $x)})
    (Mention $s)}}
; place 1 is filled with the reified content itself — the relation
; identifies it; so leaving place 1 to contextual closure would add a
; retrieval the Lojban does not contain.

; lo ni mi klama — an abstraction relation; reference outside  [spec §9.2]
{Bind [$a :: Referents Amount]
        (Refer {λ [$x :: Referents Amount]
          (Close ((NiRel (Close (klama Speaker))) $x))})
  (Mention $a)}
; the omitted scale place 2 closed contextually — the same rule as any
; omitted place; le ni …; quantified ni; relative clauses on
; abstractions: all inherited from ordinary reference.

; lo su'u mi klama kei be lo fasnu — explicit categorizer (CLL 11.9)
{Bind [$kind :: Referents Eventuality]
        (Refer {λ [$k :: Referents Eventuality] (fasnu $k)})
  {Bind [$a :: Referents AbstractNature]
          (Refer {λ [$x :: Referents AbstractNature]
            (Close ((SuhuRel (Close (klama Speaker))) $x $kind))})
    (Mention $a)}}

; lo nu mi pu klama — event abstraction: Refer at the event sort
{Bind [$ev :: Referents Eventuality]
      (Refer
        (ActualClause
          {λ [$e :: Referents Eventuality]
            (∧ ((DirectClause (klama Speaker)) $e)
               (purci $e Now))}))
  (Mention $ev)}
; The omitted-place Context sites remain inside the event property with their
; ordinary site identity; Refer sequences them rather than pretending purity.
```

```lisp
; lo nu ta du lo mi zdani — event abstraction over eventless identity
{Bind [$home :: Referents Entity]
      (Refer {λ [$x :: Referents Entity] (zdani $x Speaker)})
  {Bind [$state :: Referents Eventuality]
        (Refer (StateClause (CoRef That $home)))
    (Mention $state)}}
; StateClause is already the event property nu needs; no event place is
; added to CoRef/du and EventOfContent selects this same holding state.
```

## 10. Signs and mention

```lisp
; lu mi klama li'u
(Mention (StructuredQuote
  (Utterance {$u :: UtteranceToken}
    {(Realizes $u (Assert (Close (klama Speaker))))})))

; lo'u mi klama le'u — text; uninterpreted
(Mention (OpaqueQuote "mi klama"))

; zo klama cu valsi
(Assert (Close (valsi (WordSign "klama"))))

; la'e lu mi klama li'u — a sign's content
(Mention
  (InterpretContent
    (StructuredQuote
      (Utterance {$u :: UtteranceToken}
        {(Realizes $u (Assert (Close (klama Speaker))))}))))
; defined because the realized act is an assertion: InterpretContent is
; the RAW ActContent projection on assertion-realizing entries (spec §7.5).
; quotation supplies no ActOccurrence and therefore no RealizedContent; but
; the represented token's own intended context still interprets its deictics.

; li re te'a ci du li bi — MEX with te'a (library)
(Assert (= (te'a 2 3) 8))
; contrast: me'o re te'a ci mentions the EXPRESSION sign; not 8:
; (Mention (Sign {$s :: SignToken MathExpression} {(TextOf $s "re te'a ci")}))

; li pa vu'u mo'e lo ni mi klama — the numeric crossing (CLL 11.5)
{Bind [$scale :: Referents Scale] (Context)      ; ONE scale; hoisted:
  {Bind [$amt :: Referents Amount]                 ; it fills NiRel's place 2
          (Refer {λ [$a :: Referents Amount]     ; AND reads the value
            ((NiRel (Close (klama Speaker))) $a $scale)})
    (Mention (− 1 (AmountValue $amt $scale)))}}
; mo'e = AmountValue: the amount's numeric value on the SAME scale that
; defined it (distinct Context sites would allow a mismatch — pin P15).

; lo jei mi klama — epistemology-relative truth-value object (P38)
{Bind [$ep :: Referents Epistemology] (Context)
  {Bind [$tv :: Referents TruthValue]
          (Refer {λ [$v :: Referents TruthValue]
            ((JeiRel (Close (klama Speaker))) $v $ep)})
    (Mention $tv)}}
; The proposed numeric [0;1] crossing is gap-registered; not silently
; available as an alternative reading of this same surface form.

; la .bab. goi by. cu klama .i by. prami — letteral-keyed binding
{Bind [$bob :: Referents Entity]
        (Refer {λ [$x :: Referents Entity] (Named "bab" $x)})
  (Do (Assert (Close (klama $bob)))
      (Assert (Close (prami $bob))))}
; the letteral by. is a binding KEY resolved at the mapping layer;
; both occurrences consume the one binding.
```

## 11. The spiral sentence, in full

```lisp
; lo ci gerku noi blabi cu na batci re prenu .i .uinai cai ri tatpi
; (episodic readings: each sentence's occasion is Context-anchored; P8)
{Bind [$dogs :: Referents Entity]
      (Refer {λ [$r :: Referents Entity]
        (∧ (gerku $r)
            (= (CardBasis $r {λ [$x :: Entity] (gerku $x)}) 3))})
  (Do
    {Bind [$occ1 :: Time] (Context)          ; the biting's occasion — bound
      {Let [$a1 :: Act Assertion]         ; OUTSIDE the negation; so na
            (Assert                       ; denies biting AT that occasion
              (Supplement $dogs (Close (blabi $dogs))
                (¬ (Exactly 2 {λ [$x :: Entity] (prenu $x)}
                     {λ [$ppl :: Referents Entity]
                       (CloseClause (ActualClause
                         {λ [$e :: Referents Eventuality]
                           (∧ ((DirectClause (batci $dogs $ppl)) $e)
                              (cabna $e $occ1))}))}))))
        (Perform $a1)}}
    {Bind [$occ2 :: Time] (Context)
      {Let [$a2 :: Act Assertion]
            (Assert
              (CloseClause (ActualClause
                {λ [$e :: Referents Eventuality]
                  (∧ (Close (tatpi $dogs :Eventuality $e)) ; the prior direct-event
                     (cabna $e $occ2))})))         ; fill is kept: tatpi's mode is #12's
        {Bind [$o2 :: ActOccurrence Assertion] (Perform Host $a2)
          (Do (Perform AttachedDisplay
            (Express (Close (Unhappiness Speaker $o2 Intense)))))}}})}
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

## 12. Direct binding notation

The three binder forms are part of the core syntax. By spec §2's
convention a binder form is written `{…}` with its telescope in `[…]` and
a bare body; the delimiters show scope and do not quote core code.

```lisp
; lo ka se klama — direct function abstraction
{λ [$x :: Referents Entity]
  (Close (klama :2 $x))}
```

```lisp
; lo mlatu cu blabi .i ri jbena — effectful binding across a discourse
{Bind [$cat :: Referents Entity]
      (Refer {λ [$x :: Referents Entity] (mlatu $x)})
  (Do (Assert (Close (blabi $cat)))
       (Assert (Close (jbena $cat))))}
```

```lisp
; one act value; performed and then targeted by a display
{Let [$a :: Act Assertion] (Assert (Close (klama Speaker)))
  {Bind [$o :: ActOccurrence Assertion] (Perform Host $a)
    (Do (Perform AttachedDisplay
      (Express (Close (Happiness Speaker $o Moderate)))))}}
```

`λ` binds pure or effectful function bodies according to their type;
`Let` shares a value without running a computation; `Bind` runs one
value-returning computation — reference/contextual or performance — and
sequences its effects before the body. The
linguistic quotation `lu mi klama li'u` remains a sign (§7.5); there is
no baseline constructor for quoted core notation.

## 13. Meanings without analyses

Gap-register illustrations (spec §14) — sentences the core deliberately
does not yet analyze, kept as obligations:

```text
da'i mi ricfu .i da'i mi citka lo nobli
  — hypothetical mood: scope, binding under the shift, scenario identity.
lo'e mlatu cu cinri .i ri se nelci mi
  — generic anaphora: what does ri reach?
mi za'o citka
  — ZAhO contours pending their lexical boundary rows.
ti cinfo joi tigra
  — core shape available through JoiPred, but baseline lexicon still owes the
    common-row constitutive-origin ContributionBasis for this hybrid reading;
    it must not demand lion-only and tiger-only material parts.
ti blanu joi xunre bolci
  — JoiTanru fixes the structural shape (bolci once; only the two intended
    head-relative color links mixed), while the color row still owes its
    curated spatial-contribution basis in #12.
mi ce'e bau la .lojban. pe'e joi do ce'e bau la .glibau. casnu
  — pe'e-joi termset: paired term/tag bundles still lack a typed dispatch.
mi sanga .i joi do dansu
  — JoiClause supplies the compound event/content; #6 still owes the one
    performance's component roles, targeting, spans, and accessibility.
mi joi nai do cu remei
  — CLL's “some other connection” does not identify which alternative or its
    scope; no hidden existential-choice fallback.
li pa joi re du li ci
  — joik-connected mekso operands parse, but no number/operator/collection
    denotation has been established for this locus.
```
