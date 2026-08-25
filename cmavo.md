# Cmavo index

The cmavo-centric view of the mapping annex (spec §11): one entry per
cmavo the baseline treats, each with a Lojban example, its core term,
and links into the specification. The spec is normative; this index
orients. Entries are grouped in the mapping annex's order (spec §11);
grep for the cmavo you want. Families whose members lower uniformly
(digits, BAI, UI, BY, VUhU) get one entry with representatives.
Cmavo sequences that form a single grammatical unit — a unit at one
level of the EBNF grammar, not a composition of its parts (`.i je` is
not `.i` + `je`) — are indexed in §14. Cmavo that contribute pure
structure and no term constructor (terminators, grouping) are listed
once in §13. The documented no-mappings and open adjacencies the
cmavo-centric view makes visible are collected in §15.

In the examples, the first comment line is the Lojban source, and
every example is a **complete term** — no elision, and no comment ever
substitutes for term structure. Where completeness makes an example
larger than its point, the salient part is bracketed 👉 like this 👈 —
a formatting convention of this index only, **never** part of the
notation itself. Three kinds of names are not omissions: values bound
by earlier discourse or by ⊳ text-to-reading resolution (letteral and
KOhA assignments, transcript tokens, deictic values (directions, demonstrative
referents) — written as
plain names like `jan`, `dihu`, with their resolution noted, since
their binders live outside any single term by nature); lexicon-
supplied constants (relation names like `coi-greeting`, tag-supplied
labels like `gau-role`); and type metavariables (`T`, `ρ`), which §2
licenses as inferable-type elision.

## 1. Predication and places

### fa / fe / fi / fo / fu (FA)

Place tags: explicit labelled fills, freeing surface order (spec §4.2;
fills at distinct labels commute).

```lisp
; klama fa mi fi la .paris.
(Bind {$p :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(Named "paris" $r)}))
  {(Close (klama 👉:1 Speaker :3 $p👈))})
```

**See.** [Spec §4.1–4.2, §11](spec.md).

### fai (FA)

The fill tag for the place `jai` demotes the old x1 into.

```lisp
; mi jai gau rinka lo nu do klama kei fai lo nu mi darxi lo bitmu
(Bind {$eff :: Referents Eventuality}
      (Refer (λ {$e :: Referents Eventuality}
        {(Close (klama :1 Audience :Eventuality $e))}))
  {(Bind {$w :: Referents Entity}
        (Refer (λ {$r :: Referents Entity} {(bitmu $r)}))
    {(Bind {$cause :: Referents Eventuality}
          (Refer (λ {$e :: Referents Eventuality}
            {(Close (darxi :1 Speaker :2 $w :Eventuality $e))}))
      {(Close ((JaiPromote rinka gau-role)
               :1 Speaker :2 $eff 👉:fai $cause👈))})})})
; gau-role: the agent label gau's tag reduction supplies
```

**See.** [Spec §12, §11](spec.md); [catalog 2.20](catalog.md).

### se / te / ve / xe (SE)

Conversion: row relabeling — x1 exchanged with x2/x3/x4/x5. Pure
label routing; no separate operator survives lowering.

```lisp
; mi se klama
(Close (klama :2 Speaker))
```

**See.** [Spec §4.2](spec.md).

### zi'o (KOhA)

Place deletion: `DropPlace` removes the place from the row — a new
relation, not a vague fill (contrast `zo'e`).

```lisp
; zi'o zdani ti
(Close ((DropPlace zdani 1) :2 This))
```

**See.** [Spec §4.3](spec.md); [catalog 1.16](catalog.md).

### zo'e (KOhA)

Explicit ellipsis: identical to omission — a per-site `Context`
computation retrieving the contextually relevant value (P15). Distinct
sites retrieve independently.

```lisp
; mi klama zo'e
(Bind {$dest :: Referents Entity} (Context)
  {(Close (klama Speaker $dest))})
```

**See.** [Spec §5.3, §11](spec.md), pin P15.

### zu'i (KOhA)

`zo'e` plus typicality: the retrieved value is constrained to the
typical filler for the place.

```lisp
; mi klama zu'i
(Bind {$dest :: Referents Entity} 👉(Context)👈
  {(Close (klama Speaker $dest))})
```

The typicality is an **admissibility condition on the retrieval** —
only the place's typical filler is an admissible recovery (P15; part
of the site's key, §5.3), not a
term-level conjunct: the term is identical to `zo'e`'s, the key
differs.

**See.** [Spec §5.3, §11](spec.md), pin P15.

### co'e (GOhA), do'e (BAI)

The relation-level and tag-level ellipses: `Context` at relation type /
tag type (P14).

```lisp
; ko'a co'e ko'e — unassigned KOhA are keyed retrievals (P16)
(Bind {$a :: Referents Entity} (Context)
  {(Bind {$b :: Referents Entity} (Context)
    {(Bind {$r :: PredTerm ρ} 👉(Context)👈
      {(Close ($r $a $b))})})})
```

**See.** [Spec §5.3, §11](spec.md), pin P14.

### si / sa / su (SI/SA/SU)

Erasure: consumed before reading resolution (⊳ text-to-reading); no
term survives. Inside quotation the erased text is preserved as sign
material.

**See.** [Spec §11 ¶1, §7.5](spec.md).

## 2. Descriptions and names

### lo (LE)

Veridical description: `Refer` over the description property —
introduces a new discourse referent, nonempty and number-neutral by
type; no default quantifier (P1, xorlo).

```lisp
; lo gerku cu bajra
(Bind {$dogs :: Referents Entity}
      👉(Refer (λ {$r :: Referents Entity} {(gerku $r)}))👈
  {(Close (bajra $dogs))})
```

**See.** [Spec §5.3, §11](spec.md), pin P1; [primer ch. 3](primer.md).

### le (LE)

Speaker-described, non-veridical: `Refer` through
`skicu(Speaker, ·, Audience, P)` with the utterance-locution anchoring
clause — the describing event is this very utterance (P10).

```lisp
; le gerku cu bajra
(Bind {$x :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {👉(Close (skicu Speaker $r Audience
             (λ {$y :: Referents Entity} {(gerku $y)})))👈}))
  {(Close (bajra $x))})
```

`Close` here is the **licensed display abbreviation** of the fully
anchored term — the reference property conjoining
`(LocutionOf $e u₀)` at the utterance's own token, printed in full at
the spec's §11 `le` row — saying `le gerku` *is* the describing
(P10). An abbreviation of a real term, not a reinterpretation of
`Close`.

**See.** [Spec §11](spec.md), pin P10; [rationale §2.6](rationale.md).

### la (LA)

Names: `Refer` via the naming relation (`Named`/`NameSign`) — the
referent bears the name-sign.

```lisp
; la .alis. cu bajra
(Bind {$x :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(Named "alis" $r)}))
  {(Close (bajra $x))})
```

**See.** [Spec §7.5, §11](spec.md).

### lo'e / le'e (LE)

Typical/stereotypical generics: the axiomatic `Generic` operator at
the predication — mode `Typical` or `Stereotypical` (with the speaker
as holder for `le'e`); no prototype individual (P11).

```lisp
; lo'e gerku cu batci
(👉Generic Typical👈 (λ {$x :: Entity} {(gerku $x)})
  (λ {$x :: Entity} {(Close (batci $x))}))
```

**See.** [Spec §5.8, §11](spec.md), pin P11.

### loi / lo'i (LE)

Group and set objects: `Refer` to the `gunma`/`selcmi` object whose
components/members are the **maximal** plurality of the description
(P5); inner PA counts the base, outer PA counts groups/sets.

```lisp
; loi gerku cu sruri lo zdani — the maximal base bound first
(Bind {$base :: Referents Entity}
      👉(MaxRefer (λ {$x :: Entity} {(gerku $x)}))👈
  {(Bind {$g :: Referents (Group Entity)}
        👉(Refer (λ {$r :: Referents (Group Entity)} {(gunma $r $base)}))👈
    {(Bind {$z :: Referents Entity}
          (Refer (λ {$r :: Referents Entity} {(zdani $r)}))
      {(Close (sruri $g $z))})})})
```

**See.** [Spec §4.8–4.9, §11](spec.md), pin P5; [rationale §2.8](rationale.md).

### lei / le'i / lai / la'i (LE/LA)

The speaker-description and name counterparts of `loi`/`lo'i`: the
P10 `skicu` (or naming) base bound first, then `Refer` to the
`gunma` group / `selcmi` set object over it; inner PA constrains the
base, outer PA counts the objects.

**See.** [Spec §11](spec.md), pins P5, P10.

### Inner PA (`lo ci gerku`)

Unit count of the selected base under a counting basis:
`CardBasis` (P1; the basis answers "three *what*").

```lisp
; lo ci gerku cu bajra
(Bind {$d :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(∧ (gerku $r)
           👉(= (CardBasis $r (λ {$y :: Entity}
                               {(gerku $y)})) 3)👈)}))
  {(Close (bajra $d))})
```

**See.** [Spec §4.10, §11](spec.md), pin P1.

### Inner `no` (`lo no broda`)

Never `Refer` (plural references are nonempty by type): the zero-count
schema `No`, relativized to the bridi frame (P22).

```lisp
; lo no gerku cu bajra
(No (λ {$x :: Entity} {(gerku $x)})
    (λ {$w :: Referents Entity} {(Close (bajra $w))}))
```

**See.** [Spec §12](spec.md), pin P22.

### la'e / lu'e (LAhE)

The interpretation and sign-of crossings: `la'e X` the thing the sign
X refers to; `lu'e X` a sign for X.

```lisp
; mi djuno la'e by — by ⊳-bound to a sentence-sign referent
(Close (djuno Speaker (Reify 👉(InterpretContent by)👈)))
; la'e di'u at performed assertion content crosses directly through:
; (RealizedContent dihu), then the host-sorted crossing (P28)
```

**See.** [Spec §7.5, §11](spec.md).

### lu'a (LAhE)

Member-distribution marker: `lu'a r` ≝ distribution over the
members — `Distrib` at the use site (the explicit each-reading; spec
§12's plurality library).

```lisp
; lu'a le prenu cu bevri — each of them carries
(Bind {$p :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(Close (skicu Speaker $r Audience
           (λ {$y :: Referents Entity} {(prenu $y)})))}))
  {👉(Distrib (λ {$x :: Entity} {(Close (bevri $x))}) $p)👈})
```

**See.** [Spec §4.8, §12, §11](spec.md).

### ku (elidable terminator)

Structure only — see §13.

## 3. Relative clauses

### poi (NOI)

Restrictive clause: a conjunct inside the reference property; with
quantifiers, the restrictor (P20: the only domain restriction on `da`).

```lisp
; lo gerku poi blabi cu bajra
(Bind {$d :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(∧ (gerku $r) (blabi $r))}))
  {(Close (bajra $d))})
```

**See.** [Spec §5.3, §11](spec.md), pin P20.

### noi (NOI)

Projective supplement anchored at the referent: an aside committed
beside the at-issue claim; negation and questioning never touch it
(P7). Dependent supplements commit per instantiation.

```lisp
; lo gerku noi blabi cu bajra
(Bind {$d :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(gerku $r)}))
  {👉(Supplement $d (Close (blabi $d))
     (Close (bajra $d)))👈})
```

**See.** [Spec §5.5, §11](spec.md), pin P7; [primer ch. 5](primer.md).

### voi (NOI)

Restrictive speaker-description: the audience-deleted `skicu`
(`(DropPlace skicu 3)`) as a restrictive conjunct (P10).

**See.** [Spec §11](spec.md), pin P10.

### ke'a (KOhA)

The relative clause's parameter — the bound variable of the clause
property; inside `poi` it is the restricted referent.

**See.** [Spec §5.3, §11](spec.md).

### goi (GOI)

Discourse-scoped binding: assigns the referent to a KOhA key for the
rest of the discourse (P16).

```lisp
; lo gerku goi ko'a cu blabi .i ko'a bajra — ko'a ⊳-assigned to $d
(Bind {$d :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(gerku $r)}))
  {(Do (Assert (Close (blabi $d)))
       (Assert (Close (bajra 👉$d👈))))})
```

**See.** [Spec §5.6, §11](spec.md), pin P16.

### pe / ne / po / po'e / po'u / no'u (GOI)

The associator family, by CLL 8.3's own expansions (nested as CLL
nests them): `pe` → restrictive `srana` conjunct; `ne` → the
incidental (`Supplement`) counterpart; `po` → restrictive
`se steci srana`; `po'e` → restrictive `jinzi ke se steci srana`;
`po'u` → restrictive P23 identity; `no'u` → incidental identity. The
associated sumti is bound before the pure restriction forms.

```lisp
; le stizu pe mi cu blanu — CLL Example 8.18
(Bind {$s :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(∧ (Close (skicu Speaker $r Audience
             (λ {$y :: Referents Entity} {(stizu $y)})))
           👉(Close (srana $r Speaker))👈)}))
  {(Close (blanu $s))})
```

**See.** [Spec §11](spec.md); CLL 8.3.

### zi'e (ZIhE)

Relative-clause joining: restrictives conjoin in the reference
property, incidentals stack as separate `Supplement`s; mixed kinds
compose — order-insensitive truth-conditionally, with bindings and
supplements keeping source order at the effect level.

```lisp
; le gerku poi blabi zi'e noi le mi pendo cu ponse ke'a cu klama
; — CLL Example 8.39
(Bind {$d :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(∧ (Close (skicu Speaker $r Audience
             (λ {$y :: Referents Entity} {(gerku $y)})))
           👉(blabi $r)👈)}))
  {👉(Supplement $d
     (Bind {$p :: Referents Entity}
           (Refer (λ {$r :: Referents Entity}
             {(∧ (Close (skicu Speaker $r Audience
                  (λ {$y :: Referents Entity} {(pendo $y)})))
                (Close (srana $r Speaker)))}))   ; le MI pendo (CLL 8.7)
       {(Close (ponse $p $d))})
     (Close (klama $d)))👈})
```

**See.** [Spec §11](spec.md); CLL 8.4.

### vu'o (VUhO)

Attaches the relative clause to the whole connected sumti (P34): an
incidental clause anchors at the joint unit and predicates **once of
each immediate connectee**; a restrictive clause restricts each
operand under the connective's structure; a group-forming joik takes
the clause on the resultant object.

**See.** [Spec §11](spec.md), pin P34.

## 4. Quantifiers, numbers, termsets

### ro (PA)

Over descriptions: importing `Every` — `Presuppose` nonemptiness plus
distributive `∀` (P2; `ro` is *each*). Bare `ro da`: mathematical `∀`,
no import.

```lisp
; ro gerku cu bajra
(Presuppose (∃ (λ {$x :: Entity} {(gerku $x)}))
  (∀ (λ {$x :: Entity} {(→ (gerku $x) (Close (bajra $x)))})))
```

**See.** [Spec §4.5, §5.6, §11](spec.md), pin P2.

### su'o (PA)

At-least-one selection: the weakest member of the selection family
(`SelectSome ≝ SelectAtLeast 1`); exports its witness.

```lisp
; su'o gerku cu bajra
(Bind {$w :: Referents Entity}
      👉(SelectSome (λ {$x :: Entity} {(gerku $x)}))👈
  {(Close (bajra $w))})
```

**See.** [Spec §5.6, §4.10](spec.md); [catalog 2.22](catalog.md).

### Digits: pa re ci vo mu xa ze bi so no (PA)

Outer numeric quantifiers select witness sets of that cardinality
under a counting basis — neutral witness-set selection, not
distributive and not global (P17's documented divergence; the
CLL-literal readings are `GlobalExactly` and `Distrib`). Outer `no`
is not a selection: it lowers through the zero-count test `No`, which
exports nothing (spec §12's zero floor; P22).

```lisp
; re prenu cu bevri lo pipno
(Bind {$w :: Referents Entity}
      👉(SelectExactly 2 (λ {$x :: Entity} {(prenu $x)}))👈
  {(Bind {$p :: Referents Entity}
        (Refer (λ {$r :: Referents Entity} {(pipno $r)}))
    {(Close (bevri $w $p))})})
```

**See.** [Spec §4.10, §5.6](spec.md), pin P17.

### su'e / za'u / me'i (PA)

At-most / more-than / fewer-than: `za'u n` is the exporting
`MoreThan` (an `AtLeast n+1` selection, same witness-set discipline);
`su'e n` and `me'i n` are the bounded *tests* `AtMost`/`FewerThan`
(spec §12) — negations of selections, which select nothing and export
nothing.

**See.** [Spec §4.10, §5.6](spec.md).

### so'a / so'e / so'i / so'o / so'u (PA)

The vague-magnitude series: selections whose cardinality condition is
a `Vague`-parameterized region on the count scale.

**See.** [Spec §6.4–6.5](spec.md).

### ji'i (PA)

Approximation, position-indexed (P37): both positions denote
`Number`-valued `Vague` families — prefix/medial over the
`AdmissibleTolerance` region, suffix over the `AdmissibleRounding`
preimage (stated digits exact by construction), directionally under
`ma'u`/`ni'u`.

**See.** [Spec §4.10, §6.4, §12](spec.md), pin P37.

### du'e / rau / mo'a (PA)

Threshold quantifiers: `ThresholdKind` (TooManyK / EnoughK / TooFewK)
over the count scale — contextual threshold, explicit kind.

```lisp
; du'e gerku cu bajra
(👉TooMany👈 (λ {$x :: Entity} {(gerku $x)})
  (λ {$w :: Referents Entity} {(Close (bajra $w))}))
; TooMany is defined (catalog 2.13): a Context standard and a Vague
; admissible threshold, then MoreThan — the comment explains, the
; term above is already complete
```

**See.** [Spec §6.4](spec.md); [catalog](catalog.md).

### da / de / di (KOhA)

Unrestricted first-order variables: `∀`/`∃` over the top sort, domain
restricted only by `poi` (P20).

```lisp
; da gerku
(∃ (λ {$x :: Entity} {(gerku $x)}))
```

The prenexed spelling `da zo'u da gerku` denotes the same term;
prenex order is scope order (P26).

**See.** [Spec §4.5, §11](spec.md), pin P20.

### zo'u (ZOhU)

Prenex and topic separator (P26). Quantifier prenex: prenexed terms
lower to the quantifier/selection prefix in surface order — prenex
order is scope order. Topic use: the topic binds, and constrained `Context`
retrieves one intended `TopicResolution`: an admissible place of a single open
bridi or coarse `srana`-aboutness to the closed comment. CLL 19.4's fish has
distinct eater/eaten `Context` resolutions; `tu'e…tu'u` may extend a topic
over a sequence, but cross-clausal place-linking is gap-registered.

```lisp
; ro da poi prenu ku'o su'o de zo'u de patfu da — CLL Example 19.8
(Presuppose (∃ (λ {$x :: Entity} {(prenu $x)}))
  👉(∀ (λ {$x :: Entity} {(→ (prenu $x)
     (∃ (λ {$y :: Entity} {(Close (patfu $y $x))})))}))👈)
; prenex order = scope order: ro da outscopes su'o de
```

**See.** [Spec §11, §12](spec.md), pin P26; [catalog 1.51](catalog.md).

### da'a (PA)

All-but-n (default one): the `SelectAllBut` selection — a neutral
witness set whose remainder counts exactly n; the omitted
individuals are not a parameter and may vary under distributive
scope.

**See.** [Spec §12, §11](spec.md); [catalog 1.27](catalog.md).

### xo'e (experimental PA)

Elliptical number: `Context` at `Number` — P15's analogue, referenced
per the experimental-cmavo policy.

**See.** [Spec §11](spec.md), pin P15.

### bu'a / bu'e / bu'i (GOhA), cei + broda-series

Relation variables: **typed quantification at `PredTerm<ρ>`** (P30) —
predicate-typed variables, no reified objects; bare `bu'a` carries
implicit `su'o`, other quantifiers are prenex-only; the row is fixed
across occurrences; only pure higher-order restrictions type.
`cei`/`broda`-series: ⊳ **bridi-template** binding — fills, tense,
and negation stored, later fills override (the `go'i` machinery);
unassigned brodV are CLL's schematic sample predicates.

```lisp
; su'o bu'a zo'u la .djim. bu'a la .djan. — CLL Example 16.105
(Bind {$j :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(Named "djim" $r)}))
  {(Bind {$n :: Referents Entity}
        (Refer (λ {$r :: Referents Entity} {(Named "djan" $r)}))
    {👉(∃ (λ {$F :: PredTerm ρ} {(Close ($F $j $n))}))👈})})
```

**See.** [Spec §11](spec.md), pin P30.

### ce'e (CEhE), nu'i / nu'u (NUhI/NUhU)

Termsets: co-selected witness sets at one joint multi-parameter locus,
full product, no coordinate maximality (P17).

```lisp
; ci gerku ce'e re prenu cu batci — co-selected witnesses, full
; product (P17)
(Bind 👉{$dogs :: Referents Entity}
        (SelectExactly 3 (λ {$x :: Entity} {(gerku $x)}))
        {$people :: Referents Entity}
        (SelectExactly 2 (λ {$x :: Entity} {(prenu $x)}))👈
  {(Distrib (λ {$d :: Entity}
     {(Distrib (λ {$p :: Entity}
        {(Close (batci $d $p))}) $people)}) $dogs)})
; the selections commute (one joint locus); the member-wise Distrib
; nest is CLL's full product — every dog bites each person — with the
; plural witnesses exported and no coordinate maximality
```

**See.** [Spec §4.10, §11](spec.md), pin P17; [samples §5](samples.md).

### boi (elidable terminator)

Structure only — see §13.

## 5. Connectives

### .a / .e / .o / .u (A) — sumti connectives

Logical connection at the term locus: `∨ ∧ ↔ ∨`-of-left ("whether or
not") over the joint predication, with surface grammar fixing
structure and each connective carrying its accessibility row (P18).
The rest of the bridi is **shared, not copied**: a description
elsewhere in the sentence is introduced once, scoping over the
connective, and elided places keep one shared `Context` site across
both expansions (§5.3's site identity — `mi .e ti klama` names one
shared destination, not two).

```lisp
; mi .e do nelci lo gerku — one dog referent, both conjuncts see it
(Bind {$d :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(gerku $r)}))
  {👉(CloseClause
      (ClauseAnd (DirectClause (nelci Speaker $d))
                 (DirectClause (nelci Audience $d))))👈})
```

```lisp
; mi .a do klama lo zarci — ∨ instead; the store is still introduced
; once, outside the disjunction
(Bind {$z :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(zarci $r)}))
  {👉(CloseClause
      (ClauseOr (DirectClause (klama Speaker $z))
                (DirectClause (klama Audience $z))))👈})
```

**See.** [Spec §4.5, §5.3–5.4, §11](spec.md), pin P18. Compounds
(`na.a`, `se.u`, `.anai`): §14.

### ja / je / jo / ju (JA) — tanru-internal and general connectives

Same logical operators at their locus. At the *tag* locus: the
operator over the tag conjuncts (§11's facet joining). At the
*tanru-unit* locus: `TanruLinkConnect` (P33) — shared head asserted
once, one constrained-`Context` intended link per conjunct, connective over
the link applications; distinct-head units connect as whole predications.

```lisp
; ta blabi ja cmalu zdani — one house; the modification link is
; white-flavored or small-flavored
(Close (👉(TanruLinkConnect ∨ blabi cmalu zdani)👈 That))
```

**See.** [Spec §6.2, §12, §11](spec.md), pin P33;
[catalog 2.31](catalog.md).

### gi'a / gi'e / gi'o / gi'u (GIhA) — bridi-tail connectives

Logical connection of bridi tails: the shared head terms scope over
the connective (they are one introduction, one selection), each tail
closes separately, and tail-terms after the last tail are shared by
all tails.

```lisp
; mi nelci lo gerku gi'e bajra — Speaker shared, dog in one tail only
(Bind {$d :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(gerku $r)}))
  {👉(CloseClause
      (ClauseAnd (DirectClause (nelci Speaker $d))
                 (DirectClause (bajra Speaker))))👈})
```

```lisp
; mi dunda le cukta gi'e lebna lo jdini vau do — CLL Example 14.54:
; the tail-term do applies to both tails (dunda x3 and lebna x3)
(Bind {$b :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(Close (skicu Speaker $r Audience
           (λ {$y :: Referents Entity} {(cukta $y)})))}))
  {(Bind {$m :: Referents Entity}
        (Refer (λ {$r :: Referents Entity} {(jdini $r)}))
    {(CloseClause
      (ClauseAnd (DirectClause (dunda Speaker $b 👉Audience👈))
                 (DirectClause (lebna Speaker $m 👉Audience👈))))})})
```

Elided places in *different* tails stay distinct sites (CLL 14.58's
route argument: two goers' unspecified routes are not one route) —
contrast the sumti-connective case above, where one shared tail keeps
one site.

**See.** [Spec §4.5, §5.4, §11](spec.md); CLL 14.9.

### ga … gi …, gu'a … gi … (GA/GUhA) — forethought

Forethought spellings of the same operators (selbri-level for GUhA);
no separate semantics — structure resolved by surface grammar, with
the same tail-sharing discipline as the afterthought forms.

```lisp
; ga mi gi do citka lo plise — forethought ∨, apple introduced once
(Bind {$p :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(plise $r)}))
  {👉(CloseClause
      (ClauseOr (DirectClause (citka Speaker $p))
                (DirectClause (citka Audience $p))))👈})
```

**See.** [Spec §4.5, §5.3, §11](spec.md); §14 for the gek/guhek units.

### na (NA)

Bridi negation: `¬` at the left edge — `na` ≡ left-edge `naku`, with
CLL ch. 16's flip rules governing movement past quantifiers (P18).

```lisp
; mi na klama
(CloseClause (ClauseNot (DirectClause (klama Speaker))))
```

**See.** [Spec §4.5, §11](spec.md), pin P18.

### naku

`¬` at its surface position: quantifier scope read off the surface
order; movement flips per ch. 16.

**See.** [Spec §4.5, §11](spec.md), pin P18; §14 (`na ku` unit).

### joi (JOI)

Exact tag/facet `joi` that merely conjoins predications over an already shared
event lowers to `∧`. Constitution-bearing sumti, tanru/property, and
sentence/event uses are **gap-registered**: the prior `Vague` mixture/connecting
relation and `.i joi = Do` fallbacks are rejected, while the adopted indexed
`gunma` constitution and compound-performance laws are still being specified.

**See.** [Spec §4.8, §11](spec.md).

### ju'e (JOI)

Officially “vague non-logical connective: analogous to plain `.i`.” This is a
**registered gap**, not an invocation of `Vague`: neither CLL nor the dictionary
states whether one use has an intended connection, succeeds through any
admissible connection, merely sequences discourse, or varies by grammatical
locus. Attested uses make it a real candidate for the gap-level
`SomeAdmissible` analysis, but its negation, scope, accessibility, and
cross-locus behavior require a separate pin before any baseline term is
assigned.

**See.** [Spec §14](spec.md); GitHub issue
[#21](https://github.com/int19h/smusni/issues/21).

### jo'u (JOI)

Plural join, nothing more: `Combine` — associative, commutative,
idempotent; no group object formed.

```lisp
; mi jo'u do casnu
(Close (casnu (Combine Speaker Audience)))
```

**See.** [Spec §4.8](spec.md); [catalog 1.21](catalog.md).

### ce / ce'o (JOI)

Set former and list former: the connected terms as a `Set` object /
`List` object (order carried by `ce'o`).

**See.** [Spec §4.9, §11](spec.md).

### fa'u (JOI)

Respectively-pairing: `ZipWith` over the paired lists.

```lisp
; mi fa'u do tavla do fa'u mi
(ZipWith (λ {$s $l :: Referents Entity}
           {(Close (tavla $s $l))})
  (List Speaker Audience) (List Audience Speaker))
```

**See.** [Spec §11](spec.md); [samples](samples.md).

### ku'a / jo'e / pi'u (JOI)

Set operators: `∩` / `∪` / `×` on set objects.

**See.** [Spec §4.9, §11](spec.md).

### bi'i / bi'o / mi'i (BIhI), ga'o / ke'i (GAhO)

Intervals and regions: `bi'o` → the ordered `Interval` (a Set
object); `bi'i` → ⊳ symmetrization of the same at ordered domains,
and the `SpanRegion` betweenness span at metric domains; `mi'i` →
`MetricBall`
(center-radius, Context metric — no endpoint arithmetic); `bi'o nai`
→ `RegionComplement` in a Context universe; the region object fills
the host place. At tanru and sentence loci BIhI has **no standard
resolved mapping** (CLL 14.16: no meanings found) — a documented
no-mapping.

```lisp
; li pa ga'o bi'i ga'o li mu — endpoints explicitly included
(Interval 1 5 👉ga'o-kind ga'o-kind👈)
; ga'o-kind/ke'i-kind: the inclusive/exclusive endpoint kinds GAhO
; supplies (unmarked BIhI leaves them CLL-ambiguous)
```

**See.** [Spec §11, §12](spec.md); [catalog 2.32](catalog.md).

## 6. Tense, aspect, modals

### pu / ca / ba (PU)

Temporal facets as ordinary event predicates: precedence/overlap
conjuncts on the event, anchored at the utterance (or the chain's
anchor); chains (`pu pu`) compose as anchor paths.

```lisp
; mi pu klama
(CloseClause
  (λ {$e :: Referents Eventuality}
    {(∧ ((DirectClause (klama Speaker)) $e)
       (purci $e Now))}))
```

**See.** [Spec §11 tense block](spec.md), pin P8/P24.

### zi / za / zu (ZI), ze'i / ze'a / ze'u (ZEhA)

Temporal distance and duration magnitudes: `Vague`-parameterized
regions on the time scale conjoined to the tense facet.

**See.** [Spec §6.4, §11](spec.md).

### ki (KI)

Tense stickiness: ⊳ text-to-reading — propagates the resolved tense
by source order; no term constructor (P8).

**See.** [Spec §11](spec.md), pin P8.

### va / vi / vu (VA), FAhA, ve'i/ve'a/ve'u, vi'i/vi'a/vi'u, mo'i, fe'e

Spatial facets: location, direction, extent, dimensionality, and
motion conjuncts on the event — `MotionVector` carries `mo'i` (the
event bears the mover's `muvdu` motion in the `farna` direction);
`fe'e` routes an interval property to space.

```lisp
; le verba mo'i ri'u cadzu — rightward: the ri'u direction value,
; ⊳-resolved against the ground
  (Bind {$v :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(Close (skicu Speaker $r Audience
           (λ {$y :: Referents Entity} {(verba $y)})))}))
  {(CloseClause
    (λ {$e :: Referents Eventuality}
      {(∧ ((DirectClause (cadzu $v)) $e)
         👉(MotionVector $e $v rightward)👈)}))})
```

**See.** [Spec §11](spec.md); [catalog 1.50](catalog.md).

### roi (ROI)

Occurrence count: `n roi` **replaces** the single-event existential
closure with `RoiClause`: the set of distinct component eventualities
satisfying the host `ClauseContent` within the reference interval has
cardinality n, and `StateClause` supplies the event of that count claim
holding (P35). `roi nai` negates the count before the state lift; subjective
counts use the threshold GQs; the default interval is a Context anchor with
Vague extent.

**See.** [Spec §11](spec.md), pin P35.

### ta'e / ru'i / di'i / na'o (TAhE)

Habitual/regularity contours: **gap-registered** pending their lexicon
rows (P24 discipline applies).

**See.** [Spec §14](spec.md).

### pu'o / ca'o / ba'o / co'a / co'u / mo'u / za'o (ZAhO)

Aspectual contours: pinned as boundary-relation shape, contours filled
lexically — **gap-registered** until the rows land (P24).

**See.** [Spec §11, §14](spec.md), pin P24.

### ca'a / ka'e / nu'o / pu'i (CAhA)

Actuality and capability over `C : ClauseContent`: `ca'a` →
`ActualClause C`; `ka'e` → `CapableClause C`; `nu'o` →
`UnrealizedClause C`; `pu'i` → `DemonstratedClause C`. Missing CAhA is
reading-multiple among those four modes with no default (P24, CLL 10.19).

```lisp
; mi ka'e limna
(CloseClause
  (CapableClause (DirectClause (limna Speaker))))
```

**See.** [Spec §12, §11](spec.md); [catalog 1.50, 2.21](catalog.md).

### BAI family (bai, gau, ri'a, mu'i, ki'u, ta'i, pi'o, ka'a, …)

Modal tags: clause-event-predicate conjuncts per the lexicon's tag
reductions — each BAI names its gismu's relation between the tagged
sumti and the current clause event, joined by `∧` at the tag locus. `se`/`te`
conversions apply to the underlying row (§14 sequences).

```lisp
; mi klama bai do
(CloseClause
  (λ {$e :: Referents Eventuality}
    {(∧ ((DirectClause (klama Speaker)) $e)
       (Close (bapli :1 Audience :2 $e)))}))
```

**See.** [Spec §11](spec.md); [lexicon interface §10](spec.md).

### fi'o … fe'u (FIhO)

Ad-hoc tag: any predicate as tag, with the lexicon's host-event link.

**See.** [Spec §11](spec.md).

### cu'e (CUhE)

Tense/modal question: `OpenQ` over the tag domain.

**See.** [Spec §8, §11](spec.md).

## 7. Anaphora and pro-sumti

### mi / do / mi'o / mi'a / ma'a / do'o (KOhA)

Deictics from the utterance context: `Speaker`, `Audience`, and their
`Combine`-built combinations (`mi'o` = speaker⊕audience, `mi'a` =
speaker⊕others, …).

```lisp
; mi'o klama
(Close (klama (Combine Speaker Audience)))
```

**See.** [Spec §5.1](spec.md).

### ko (KOhA)

Imperative `do` (P27): fills its place with the **active addressee**
(the `doi`-updated `do`, falling back to the utterance's Audience)
and ⊳ marks the nearest **performed** clause as the command force —
no force extrusion through `Reify` or quotation (`lo nu ko klama`
constructs content, commands nothing).

```lisp
; ko klama
(Command Audience (Close (klama Audience)))
; Audience here = the fallback; after doi X the active addressee X
; fills both positions (see the doi entry)
```

**See.** [Spec §11, §7.1](spec.md), pin P27.

### ti / ta / tu (KOhA)

Demonstratives: `Deictic` at proximal/medial/distal against the
current ground.

```lisp
; ti gerku
(Close (gerku This))     ; This ≝ (Deictic Proximal g), g the ctx ground
```

**See.** [Spec §5.1, §6.1](spec.md).

### ri / ra / ru (KOhA)

Recency anaphora: ⊳ resolved by CLL ch. 7 counting over accessible
referents before the calculus; the term sees the binding, never a
search (P16). Source order of fills feeds the counting.

**See.** [Spec §5.6, §11](spec.md), pin P16.

### ko'a … fo'u (KOhA)

Assignable pro-sumti: assigned (by `goi`) → the bound variable;
unassigned → keyed `Context` — one value per key, so `ko'a du ko'a` is
reflexively true (P16).

**See.** [Spec §5.3, §11](spec.md), pin P16.

### vo'a / vo'e / vo'i / vo'o / vo'u (KOhA)

Bridi-place reflexives: bindings to the current bridi's fills.

**See.** [Spec §11](spec.md), pin P16.

### go'i family (go'i, go'e, go'a, go'o, nei, no'a) (GOhA)

Bridi anaphora: ⊳ cross-performance `go'i`/`go'e`/`go'a`/`go'o`
expansion uses the antecedent's **resolved occurrence capture** —
utterance-context projections and closure sites keep their values. Whole
assertion-content reuse is `RealizedContent u`; template overrides operate on
the same captured expansion. `nei`/`no'a`, and uses inside unperformed
material, instead reuse the already resolved current/outer template
environment: no occurrence is required. `go'i` as an answer is `Answer` with
polar selection.

**See.** [Spec §11, §8](spec.md), pin P16.

### ra'o (RAhO)

Selective re-resolution: take the raw package/template (`ActContent
(RealizedAct u)` at assertion force) as the source, but reopen only the
antecedent pro-sumti/pro-bridi sites marked by `ra'o`. Interpret those in this
new performance under the current `InContext`/`ShiftedGround`; omitted places,
tanru links, and other unmarked `Context` sites retain the antecedent capture.
This follows CLL 7.6's stated pro-assign update rather than treating `ra'o` as
a wholesale raw-package replay.

**See.** [Spec §5.1, §11](spec.md).

### di'u / de'u / da'u / di'e / de'e / da'e / dei / do'i (KOhA)

Utterance anaphora at `Referents<UtteranceToken>`: ⊳ recency over the
transcript at three distances, past and future; `dei` = the current
entry's own bound `CurrentToken`; `do'i` = `Context` at the salient token/span
(P28). `la'e` on these uses partial `(RealizedContent u)` when performed assertion content is demanded
(spec §7.4) — into the host-sorted crossing; an act-demanding host still
uses `RealizedAct<F>`. No universal coercion.

```lisp
; di'u jitfa jufra — dihu ⊳-bound by transcript recency
(Close ((Tanru jitfa jufra) 👉dihu👈))
```

**See.** [Spec §11, §7.4](spec.md), pin P28.

### da'o (DAhO)

Assignment cancellation: ⊳ clears all resolver stores (KOhA,
letteral, pro-bridi); `ni'o` levels imply it per depth — the
assignment-clearing level (`ni'o` spoken / `ni'o ni'o` written), with
the drastic level (one more) also resetting tenses and indicators,
and `no'i` resuming what its `ni'o` dropped (spec §7.2).

**See.** [Spec §11, §7.2](spec.md).

### ce'u (KOhA)

The abstraction parameter: λ's bound variable at the surface. Implicit
`ce'u` in `ka`: exactly one, first unfilled place (P12); explicit
`ce'u` in any `ce'u`-capable abstractor extracts λ (§11). The
experimental lambda-prenex `ce'ai` names binder order where multiple
readings arise.

```lisp
; lo ka ce'u tavla mi
(λ {$x :: Referents Entity} {(Close (tavla $x Speaker))})
```

**See.** [Spec §9.2, §11](spec.md), pin P12.

## 8. Abstractors

### nu (NU) — with mu'e / za'i as sort refinements

Event abstraction: `Refer` directly over the inner `ClauseContent` — the
lexical event for a direct episode, or the holding/joint/negative State of an
eventless or composed bridi. The eventuality sort may be refined by the
abstractor (Achievement `mu'e`, State `za'i`).
`pu'u` and `zu'o`, which keep real x2 places, live in the
abstraction-relation family instead (next entry; spec §9.2).

```lisp
; lo nu mi klama cu nandu
(Bind {$ev :: Referents Eventuality}
      (Refer 👉(ActualClause (DirectClause (klama Speaker)))👈)
  {(Close (nandu $ev))})
```

**See.** [Spec §9, §11](spec.md); [primer ch. 6](primer.md).

### du'u (NU)

Proposition abstraction: `Reify` — content held still as a first-order
`Proposition` object, with `Holds` the sole way back (round-trip
axiom). The inner `ClauseContent` is first closed once with `CloseClause`;
with explicit `ce'u`, `du'u` instead extracts λ exactly as `ka` (§11's arity
theorem: n **distinct** extracted variables = n-adic; bare `du'u` is
the 0-adic case). `se du'u`
= the sentence place of the derived `DuhuRel` (defined only for the
0-adic case — spec §9.2).

```lisp
; mi djuno lo du'u la .frank. cu bebna
(Bind {$f :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(Named "frank" $r)}))
  {(Close (djuno Speaker 👉(Reify (Close (bebna $f)))👈))})
```

**See.** [Spec §9.1–9.2, §11](spec.md); [catalog 1.31, 2.18](catalog.md);
[rationale §2.10](rationale.md).

### ka (NU)

Property abstraction: λ — with `ce'u` the parameter; consumed by
application at property places. Lowers directly (no discourse
referent — the reified-property family is a §9.1 reservation).

```lisp
; lo ka se klama
(λ {$x :: Referents Entity} {(Close (klama :2 $x))})
```

**See.** [Spec §4.4, §9.2, §11](spec.md), pin P12.

### ni / jei / li'i / si'o / su'u / pu'u / zu'o (NU)

The abstraction-relation family: named relations with labelled rows
(`NiRel`, `JeiRel`, `LihiRel`, `SihoRel`, `SuhuRel`, `PuhuRel`,
`ZuhoRel`), parameterized by the abstracted content, with reference
applying outside — so `lo`/`le`, quantification, and relative clauses
work on abstractions for free; omitted x2s close into `Context`.

```lisp
; lo ni mi klama
(Refer (λ {$a :: Referents Amount}
  {(Close (👉(NiRel (Close (klama :1 Speaker)))👈 $a))}))
; the outer Close handles NiRel's unfilled scale place (x2)
```

**See.** [Spec §9.2, §11](spec.md).

### kei (elidable terminator)

Structure only — see §13.

### tu'a (LAhE)

Intended abstraction retrieved through constrained `Context`: shape conjunct +
`srana`-aboutness, sort selected by the host place, dependency profile declared
by the resolved reading (P14). The speaker leaves the abstraction unspoken but
does not assert that any X-related abstraction will do.

```lisp
; mi troci tu'a lo vorme — an event-sorted abstraction (the host
; place selects the sort), shape conjunct + srana-aboutness (P14)
(Bind {$door :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(vorme $r)}))
  {(Bind {$a :: Referents Eventuality}
        👉(Context (λ {$v :: Referents Eventuality}
          {(∧ (∃ (λ {$p :: Proposition}
                {(CoRef $v (EventOfContent (Holds $p)))}))
              (Close (srana $v $door)))}) $door)👈
    {(Close (troci Speaker $a))})})
```

**See.** [Spec §11](spec.md), pin P14.

### jai (JAI)

With tag: explicit role promotion — the tagged role to x1, old x1 to
the fillable `fai` place (`JaiPromote`). Bare: participant raising out
of the abstraction-x1 with one intended admissible role retrieved by
constrained `Context` (P14). In a resolved bare reading, raised sort T and
old-x1 sort A fix the role type
`Fn<(Referents<T>, Referents<A>), Content>`; `JaiRaise` conjoins the role
between the new x1 and the old abstraction at `fai`.

```lisp
; mi jai gau rinka lo nu do klama
(Bind {$eff :: Referents Eventuality}
      (Refer (λ {$e :: Referents Eventuality}
        {(Close (klama :1 Audience :Eventuality $e))}))
  {(Close (👉(JaiPromote rinka gau-role)👈 :1 Speaker :2 $eff))})
; the unfilled fai place closes contextually; gau-role is the label
; gau's tag reduction supplies
```

```lisp
; mi jai rinka lo nu do morsi — bare jai, common agent-role resolution
(Bind {$death :: Referents Eventuality}
      (Refer (λ {$e :: Referents Eventuality}
        {(Close (morsi :1 Audience :Eventuality $e))}))
  {(Bind {$role :: Fn<(Referents<Entity>, Referents<Eventuality>), Content>}
        (Context
          (λ {$k :: Fn<(Referents<Entity>, Referents<Eventuality>), Content>}
            {(JaiRoleAdmissible rinka $k)}))
    {(Close ((JaiRaise rinka $role) :1 Speaker :2 $death))})})
; Close recovers the old rinka x1 at fai; $role relates Speaker to it.
```

**See.** [Spec §11, §12](spec.md); [catalog 2.20](catalog.md).

### kau (UI)

Indirect-question marker: `ContextualAnswer` — the answerhood object,
exhaustivity **absent** (weakest truth conditions; strengthenings
lexical/pragmatic/explicit; P9).

```lisp
; mi djuno lo du'u ma kau klama
(Close (djuno Speaker
  (Reify 👉(Answer (OpenQ (λ {$x :: Referents Entity}
                            {(Close (klama $x))}))
                   ContextualAnswer)👈)))
```

**See.** [Spec §8.2, §11](spec.md), pin P9.

### me'au / me'ei (experimental)

Referenced, not baseline: use an abstract-predicate sumti as selbri /
form such a sumti. At the propositional case `me'au` is `Holds` in
selbri position under §9.1's singleton condition — the `Meau0`
schema, singularity projective; no plural baseline reading. Above
arity 0 the reified-predicate family is a §9.1 reservation (§14 gap).

```lisp
; me'au .abu gi'a me'au by. — A or B, as claims; abu/by ⊳-bound to
; prior lo-du'u referents
(∨ 👉(Meau0 abu)👈 👉(Meau0 by)👈)
; Meau0 (spec §9.1): presupposes a sole member and holds it
```

**See.** [Spec §9.1, §14, §16.5](spec.md); [rationale §2.10](rationale.md).

## 9. Questions

### xu (UI)

Polar question: `Polar` over the content; as `xu kau`, the polar
answerhood object.

```lisp
; xu do klama
(Ask (Polar (Close (klama Audience))))
```

**See.** [Spec §8.1](spec.md).

### ma / mo / xo / ji / cu'e / pei / fi'a

Open questions at their typed domains: `OpenQ` over entities (`ma`),
relations (`mo`), numbers (`xo`), connectives (`ji`), tags (`cu'e`),
attitudes (`pei`; compound basis questions like `ju'apei`, spec
§8.1), place labels (`fi'a`). ⊳ Bare interrogatives take
utterance-level scope even from embedded positions.

```lisp
; ma klama
(Ask (OpenQ (λ {$x :: Referents Entity} {(Close (klama $x))})))
```

**See.** [Spec §8.1–8.3, §11](spec.md).

## 10. Indicators, discourse, vocatives

### UI attitudinals (ui, .oi, .au, .a'o, .ei, .ii, …; performatives ca'e and kin)

Displayed-content relations per lexicon entries with host-force
profiles: an `Express` act (act-level targets) or in-content display
(constituent targets), the relation being the indicator's
emotion/attitude relation (§16.5 maps the placeholders to the `-nmo`
family). ⊳ Target selection by grammatical attachment (P19).

```lisp
; .uinai mi klama — the display targets the bound host occurrence; degree
; Moderate is the unmarked region (cai would make it Intense)
(Let {$a :: Act Assertion} (Assert (Close (klama Speaker)))
  {(Bind {$o :: ActOccurrence Assertion} (Perform $a)
    {(Express (Close (Unhappiness Speaker $o Moderate)))})})
```

The occurrence handle makes the host-force/display target explicit after
lowering; performing `$a` again returns a distinct handle that the earlier UI
does not modify. A relation about the raw package may still target `$a`.

**See.** [Spec §7.6, §11](spec.md), pin P19; [samples §7](samples.md).

### Evidentials (za'a, ti'e, ka'u, ba'a, su'a, pe'i, ju'a, se'o, …) (UI)

The family force clause: `GroundedBy` — display, beside the performed
act, the speaker's basis (experiencer × target × `BasisKind`);
negation never touches the basis.

```lisp
; za'a do cadzu
(GroundedBy Observation (Assert (Close (cadzu Audience))))
```

**See.** [Spec §7.6](spec.md); [catalog 2.24](catalog.md).

### nai (NAI), cu'i (CAI)

Polarity and neutrality on indicators: lexical pairing — `nai` selects
the paired opposite relation, `cu'i` the scale midpoint (P19; the
`-nmo` derivation extends to both poles).

**See.** [Spec §7.6, §11](spec.md).

### cai / sai / ru'e (CAI)

Intensity: regions on the indicator's intensity scale (Intense /
Strong / Weak).

**See.** [Spec §6.4, §7.6](spec.md).

### dai (UI)

Experiencer shift: the displayed relation's experiencer moves from the
speaker to the contextually attributed party.

**See.** [Spec §7.6, §11](spec.md).

### ba'e (BAhE)

Sign-level focus: marks the focused sign token (P23); focus-sensitive
derivations (`po'o`-class) consume it.

**See.** [Spec §7.6, §11](spec.md), pin P23.

### fu'e / fu'o (FUhE/FUhO)

Indicator scope extension: ⊳ widens the grammatical attachment target
(P19); no term constructor of its own.

**See.** [Spec §11](spec.md), pin P19.

### na'i (UI)

Metalinguistic objection: the `NahiObjection` act — express, of a
bound prior target, defectiveness in a contextually recovered
dimension; performs nothing, negates nothing.

```lisp
; do klama .i na'i — the objected act Let-bound (§7.2: no
; discourse constants); its performance occurrence Bind-bound
(Let {$a :: Act Assertion} (Assert (Close (klama Audience)))
  {(Bind {$o :: ActOccurrence Assertion} (Perform $a)
    {👉(NahiObjection $o)👈})})
```

**See.** [Spec §7.3, §12](spec.md); [catalog 2.23](catalog.md).

### da'i (UI)

Hypothetical mood: **gap-registered** with a bounded design space —
a member of the `Shift` operator family over the evaluation world,
with scope, dynamic binding under the shift, and scenario identity
the three things a treatment must define (spec §14's entry).

**See.** [Spec §14, §5.1](spec.md).

### Discursives (ku'i, ji'a, si'a, mi'u, ta'o, va'i, …) (UI)

Library discourse relations between performed occurrence handles (`Contrast`,
`Addition`, `Parallel`, `Elaboration`, …), displayed beside the host
occurrence. Raw act values remain explicit metalinguistic alternatives.
Constituent `ji'a` and `po'o` are focus derivations
(`Additive`/`Only`).

```lisp
; .i mi klama .i ku'i do stali — no prior/following-discourse
; constants exist (§7.2): raw acts are Let-bound, occurrences Bind-bound
(Let {$a1 :: Act Assertion} (Assert (Close (klama Speaker)))
  {(Bind {$o1 :: ActOccurrence Assertion} (Perform $a1)
    {(Let {$a2 :: Act Assertion} (Assert (Close (stali Audience)))
      {(Bind {$o2 :: ActOccurrence Assertion} (Perform $a2)
        {(Express (Close (Contrast $o2 $o1)))})})})})
```

**See.** [Spec §7.2, §11](spec.md); [catalog 2.25](catalog.md).

### .i (I)

Discourse sequencing: `Do` — performance one after the other,
threading the information state (referents stay accessible per the
table).

**See.** [Spec §5.4, §7.1, §11](spec.md). Connected forms (`.i je`,
`.i ba bo`): §14.

### ni'o / no'i (NIhO)

Topic structure: `NewTopic` / `Resume` — push/pop against the
suspended-topic stack in the information state.

**See.** [Spec §5.1, §7.2, §11](spec.md).

### COI family (coi, co'o, ki'e, fi'i, je'e, …)

Performative expressives: `Express` of the COI lexical relation with
the performative host-force profile — the greeting *is* the act.

```lisp
; coi do
(COIExpress coi-greeting Audience)
```

**See.** [Spec §7.6, §11](spec.md); [catalog 2.26](catalog.md).

### doi (DOI)

Vocative address: the `Vocative` act beside the host, **plus** ⊳
binding of the active `do` (P27) — `do` and `ko` consult the active
binding before falling back to the utterance's Audience, which is
never mutated.

```lisp
; doi .djan. ko klama — the vocative act, then the command to John
(Bind {$j :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(Named "djan" $r)}))
  {(Do 👉(Vocative $j)👈
       (Command 👉$j👈 (Close (klama $j))))})
; the ⊳ active-do binding makes ko and do resolve to $j (P27)
```

**See.** [Spec §11, §7.1](spec.md), pin P27.

### mi'e (COI)

Performative self-naming: the act that makes the speaker bear the
name.

**See.** [Spec §11](spec.md).

### mai / mo'o (MAI)

Enumeration ordinals: `EnumerationOrdinal` display facts at the
**attachment-selected** constituent (CLL 19.7 numbers sumti inside
one bridi), item and section level; sequence key Context-recovered;
no temporal order implied.

**See.** [Spec §11, §12](spec.md); [catalog 1.54](catalog.md).

### sei … se'u (SEI)

Metalinguistic comment: projective supplement beside the host —
non-restrictive material landing on the supplement channel (§5.5).

**See.** [Spec §5.5](spec.md).

### to … toi (TO)

Parenthetical text: supplement-channel discourse beside the host, the
enclosed text performed as an aside.

**See.** [Spec §5.5](spec.md).

### soi (SOI)

Reciprocity ("vice versa"): the `Reciprocate` schema via the lexicon
rows it consumes.

**See.** [Spec §12, §11 ¶2](spec.md); [catalog](catalog.md).

## 11. Quotation, signs, MEX

### lu … li'u (LU/LIhU)

Structured quotation: `StructuredQuote` over the transcript entry —
a pure token-description property (`Utterance` entry notation);
quoted material introduces no discourse referents. Its `Realizes` fact names
a raw act package, not a performance occurrence, so `InterpretContent` uses
`ActContent` and no `RealizedContent` is available merely from quotation.

```lisp
; mi cusku lu mi klama li'u
(Close (cusku Speaker
  (StructuredQuote (Utterance {$u :: UtteranceToken}
    {(Realizes $u (Assert (Close (klama Speaker))))}))))
```

**See.** [Spec §7.4–7.5, §11](spec.md); [catalog 1.38, 2.27](catalog.md).

### lo'u … le'u (LOhU/LEhU), zoi (ZOI)

Opaque quotation: `OpaqueQuote` — text too broken to parse, or
non-Lojban text; pure sign material.

**See.** [Spec §7.5, §11](spec.md).

### zo (ZO)

Single-word quotation: `WordSign`.

```lisp
; zo klama
(WordSign "klama")
```

**See.** [Spec §7.5, §11](spec.md).

### BY letterals (.abu, by, cy, …), bu (BU)

Letteral signs: `LetteralSign`; ⊳ letteral anaphora keys bindings to
the referent whose name/description the letteral abbreviates. `bu`
forms a letteral from any word.

**See.** [Spec §7.5, §11](spec.md), pin P16.

### me'o (LI)

Mention of a math-expression sign (the expression itself, unevaluated
as a sign); contrast `li`.

**See.** [Spec §4.9, §7.5, §11](spec.md).

### li (LI)

The value: the number/expression's denotation as a first-order
object.

```lisp
; li re su'i re du li vo
(CloseClause (StateClause (= (+ 2 2) 4)))
```

**See.** [Spec §4.9, §11](spec.md).

### du (GOhA)

Identity: `=` between first-order individuals; `CoRef` (mutual
`Among`) between plural sumti (P23). At the declarative layer the resulting
eventless Content goes through `StateClause`, so tense, CAhA, ROI, ZAhO, and
`nu` have a state to consume. `du` itself remains rigid; a description or
physical value scoped inside the StateClause may vary with that state, while
an outside binding gives the de re reading.

```lisp
; ko'a du ko'e — unassigned KOhA are keyed retrievals (P16)
(Bind {$a :: Referents Entity} (Context)
  {(Bind {$b :: Referents Entity} (Context)
    {👉(CloseClause (StateClause (CoRef $a $b)))👈})})
```

**See.** [Spec §4.5, §11](spec.md), pin P23.

### VUhU operators (su'i, vu'u, pi'i, fe'i, …), pi, ni'u / ma'u

The MEX fragment: operators as typed functions over `Number`;
`pi` the radix point, `ni'u`/`ma'u` sign. Beyond the library fragment
(non-decimal bases, arrays, indefinite operators): gap-registered.

**See.** [Spec §4.9, §12, §14](spec.md).

### Numeral punctuation: fi'u, pi'e, ki'o, ra'e, ce'i (PA)

⊳ numeral syntax producing `Number` constants: fractions (`fi'u`),
mixed radix with base data (`pi'e`), digit grouping with zero-padding
(`ki'o`), repeating digits (`ra'e`), percent (`ce'i`); with `pi`,
`ni'u`/`ma'u` (above) they are the numeral grammar, not term-level
operators.

**See.** [Spec §11](spec.md).

### te'a / gei, xi (VUhU/XI)

Exponentiation and order-of-magnitude by metalanguage recursion;
`xi` subscripting as list indexing (undefined past the end — a
projective definedness condition).

**See.** [Spec §12](spec.md); [catalog 2.29](catalog.md).

### mo'e (MOhE)

The numeric crossing: a sumti's value as an operand
(`AmountValue`).

**See.** [Spec §9.2, §11](spec.md).

### me … me'u (ME/MEhU)

Sumti to selbri: the Among-property `MePred` — x1 is among the
referents (CLL 5.10; the ratified gadri definitions expand `lo PA
sumti` through it).

```lisp
; la .baltazar. cu me le ci nolraitru — bindings in source order
(Bind {$b :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(Named "baltazar" $r)}))
  {(Bind {$k :: Referents Entity}
        (Refer (λ {$r :: Referents Entity}
          {(∧ (Close (skicu Speaker $r Audience
               (λ {$y :: Referents Entity} {(nolraitru $y)})))
             (= (CardBasis $r (λ {$y :: Entity}
                                {(nolraitru $y)})) 3))}))
    {(Close (👉(MePred $k)👈 $b))})})
```

**See.** [Spec §12, §11](spec.md); [catalog 2.30](catalog.md).

### mei / moi / si'e / cu'o / va'e (MOI)

Number selbri: the MOI relation families — `MeiRel` (group from an
n-membered set), `MoiRel` (n-th under a Context-recovered pure
ordering), `SiheRel` (portion), `CuhoRel` (opaque probability,
0 ≤ n ≤ 1, no probability calculus — P29), `VaheRel` (scale
position). `me X me'u MOI` composes.

```lisp
; lei mi ratcu cu cimei — CLL Example 18.81; le MI ratcu = the
; pe-associator restriction (CLL 8.7); unfilled MeiRel places close
; contextually
(Bind {$base :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(∧ (Close (skicu Speaker $r Audience
             (λ {$y :: Referents Entity} {(ratcu $y)})))
           (Close (srana $r Speaker)))}))
  {(Bind {$g :: Referents (Group Entity)}
        (Refer (λ {$r :: Referents (Group Entity)} {(gunma $r $base)}))
    {(Close (👉(MeiRel 3)👈 :1 $g))})})
```

**See.** [Spec §12, §11](spec.md), pin P29; [catalog 1.52](catalog.md).

### na'u / nu'a / ma'o / ni'e / te'u (MEX conversions)

The §12 partial interfaces: relation→operator (`na'u`, where
functional), operator→relation (`nu'a`, total), operand→operator
(`ma'o`, the function a `Context` recovery — P36), the
amount-operand crossing (`ni'e`); `te'u` structural; `se` on
operators permutes.

**See.** [Spec §12, §11](spec.md), pin P36; [catalog 1.53](catalog.md).

### la'o (ZOI), zo'oi (experimental)

Foreign names: the ordinary naming route at the opaque text payload —
`(NameSign t)` and `Named` unchanged (the payload's being non-Lojban
is a fact about the text, not a type); `zo'oi` quotes one non-Lojban
word as a word-level opaque sign.

**See.** [Spec §12, §11, §7.5](spec.md).

## 12. Scalar and tanru operators

### na'e / no'e / to'e (NAhE)

Scalar negation: bind the intended `ContrastDomain` through `Context`, then
apply `(Scalar k D P)` with k = OtherThan / Neutral / Opposite — the
na'e-family contraries, not `¬` (P18 handles `na`).

```lisp
; mi na'e klama
(Bind {$d :: ContrastDomain ρ(klama)} (Context)
  {(Close ((Scalar OtherThan $d klama) :1 Speaker))})
```

**See.** [Spec §6.3, §11](spec.md); [catalog](catalog.md).

### je'a (NAhE), ja'a (NA)

Affirmers: transparent identities at their loci (`na je'a broda` ≡
`na broda`) that ⊳ **override inherited negation** in pro-bridi
expansions — `ja'a go'i` over a negative template removes the `na`
(P31). No fourth `Scalar` kind; emphasis is absence or `ba'e` focus.

**See.** [Spec §11](spec.md), pin P31.

### bo (tanru), ke / ke'e (KE/KEhE), co (CO)

Tanru grouping and inversion: ⊳ text-to-reading structure — they fix
which `Tanru M H` applications form, and contribute no constructor.
`co`: `A co B` ≡ `ke B ke'e A`, trailing sumti routed to the seltau's
places as `be`-fills (hence invisible to `vo'a`/`go'i`); multiple
`co` right-group (spec §6.2; CLL 5.8).

**See.** [Spec §6.2, §11](spec.md).

### be / bei / be'o (BE/BEI/BEhO)

Tanru-internal fills: linked sumti fill places of the tanru unit they
attach to — ordinary labelled fills routed inside the unit (the
categorizer's `be` in `lo su'u … kei be lo fasnu` likewise).

```lisp
; ta blanu zdani be mi — the be-fill rides inside the head unit
(Close ((Tanru blanu 👉(At zdani x2 Speaker)👈) That))
```

**See.** [Spec §6.2, §4.2](spec.md).

### zei (ZEI)

Compound-word formation: morphology/lexicon level — the compound is a
dictionary relation like any other; no term-level operator.

**See.** [Spec §10](spec.md).

## 13. Structure-only cmavo

These contribute grammatical structure and no term constructor; the
calculus never sees them (⊳ resolved before lowering): `cu` (selbri
separator); the elidable terminators `ku`, `kei`, `vau`, `be'o`,
`boi`, `ke'e`, `ge'u`, `ku'o`, `li'u`, `le'u`, `lo'o`, `me'u`,
`se'u`, `toi`, `fe'u`, `nu'u`, `ku'e`, `ve'o`, `do'u`; grouping `bo`
(connective/tense grouping), `ke`/`ke'e` at their non-tanru loci;
`tu'e`/`tu'u` (text grouping — scope width for connectives and for a
`zo'u` topic over sentence sequences); `fa'o` (end of text); `y`
(hesitation — morphology-level noise, no sign). (`zo'u` itself is
meaningful — see its entry in §4.)

**See.** [Spec §11 ¶1](spec.md).

## 14. Multi-cmavo units (single-level EBNF sequences)

Sequences that are single units at one level of the EBNF grammar.
Some are algebraically derivable from their members (the
`na`/`se`/`nai` decorations); some are irreducibly their own thing
(`.i je` is not `.i` + `je`). Either way the *unit*, not the parts,
is what the mapping addresses.

### ek: [na] [se] A [nai] — na.a, se.u, .anai, na.enai, …

One connective token: the four-place truth-functional selection —
`na`/`nai` flip the left/right operands, `se` swaps them. `na.a` =
only-if (→ flipped), `.anai` = if (←), `.enai` = and-not, `na.enai` =
neither (↓). Lowered as the corresponding `¬`-decorated operator with
the accessibility row of the base connective.

```lisp
; mi na.enai do klama — neither I nor you
(CloseClause
  (ClauseAnd (ClauseNot (DirectClause (klama Speaker)))
             (ClauseNot (DirectClause (klama Audience)))))
```

**See.** [Spec §4.5, §5.4, §11](spec.md), pin P18.

### jek / gihek / joik with na / se / nai

The same decoration pattern at the other loci: `na ja`, `se gi'a`,
`joi nai`, `se joi` — one unit per EBNF `jek`/`gihek`/`joik`
production; `se` on a non-logical connective swaps the (ordered)
operands; `nai` on a joik is per-locus: truth-table for logical
loci and `RegionComplement` for BIhI. Constitution-bearing `joi`/`joi nai`
loci remain gap-registered; `nai` creates no hidden discrete-choice fallback.

**See.** [Spec §4.5, §4.8, §11](spec.md).

### .i je / .i ja … — I + jek

Sentence-level logical connection as one unit — NOT `.i` followed by
an independent `je`: **one performance of the connected ClauseContent**
(P32 — forced by `.i ja`, where no pair of assertions exists), the
host's single force shared by the connection (content-taking forces;
an interrogative host queries the connected content), with `∧`'s
accessibility row shared with `Do`'s (spec §5.4). Constitution-bearing
`.i joi` and non-logical ijoiks are gap-registered pending their event and
compound-performance laws.

```lisp
; mi klama .i je do stali — one act asserting the conjunction
(Assert
  (CloseClause
    (ClauseAnd (DirectClause (klama Speaker))
               (DirectClause (stali Audience)))))
```

**See.** [Spec §11, §5.4, §7.1](spec.md), pin P32.

### .i ba bo / .i pu bo … — I + stag + BO

One performance with the tag relating the two events — both event
binders exposed, the tag conjunct inside (P32):

```lisp
; mi klama .i ba bo mi citka
(Assert
  (CloseClause
    (StateClause
      (∃ (λ {$e1 :: Referents Eventuality}
        {(∧ ((DirectClause (klama Speaker)) $e1)
           (∃ (λ {$e2 :: Referents Eventuality}
             {(∧ ((DirectClause (citka Speaker)) $e2)
                (balvi $e2 $e1))})))})))))
```

**See.** [Spec §11](spec.md), pin P32.

### ge … gi …, gu'e … gi (gek/guhek units)

Forethought connection as one unit — `[se] GA [nai] … gik`
(discontinuous, unlike the contiguous decorations above); the gik
(`gi [nai]`) carries the right-operand polarity. The gek production
also admits `joik GI` (forethought non-logical connection) and
`stag gik` (forethought tag connection) arms.

**See.** [Spec §4.5, §11](spec.md).

### Connective + BO / KE grouping (ek/jek/joik/gihek + bo, + ke…ke'e)

Grouping-decorated connectives (`.e bo`, `.i je bo` aside, `ja ke …
ke'e`, …), including the EBNF variants with an intervening simple tag
(`ek/jek/joik/gihek + stag + BO/KE`, e.g. `.e ba bo`): the BO/KE part
is ⊳ text-to-reading grouping — it fixes
association tightness and contributes no constructor; the semantics
is the base connective's, with an intervening tag adding its relation
per the I+stag+BO pattern (P32).

**See.** [Spec §11 ¶1, §4.5](spec.md).

### na ku

Surface-position negation as a quantifier-scope unit: `¬` exactly
where it stands, flip rules on movement (P18) — not `na` + a
description terminator.

**See.** [Spec §4.5, §11](spec.md), pin P18.

### SE + BAI (se bai, te gau, …)

One tag token: the conversion applies to the BAI's underlying row
before the tag reduction.

**See.** [Spec §11](spec.md).

### NAhE + BO (na'e bo)

Scalar variant of a sumti/tag as one unit: `Scalar` over the
associated relation.

**See.** [Spec §6.3, §11](spec.md).

### number + ROI (re roi, so'i roi …)

Occurrence-count tense as one unit: the counted instantiation-set
schema (P35) — see the `roi` entry in §6.

**See.** [Spec §11](spec.md), pin P35.

### number + MOI (moi/mei/si'e/cu'o/va'e)

Ordinal/cardinal/portion/probability/scale selbri from a number — a
single selbri former: the MOI relation families (see the MOI entry in
§11; [catalog 1.52](catalog.md)).

## 15. Documented no-mappings and open adjacencies

Every cmavo the baseline treats carries an entry above; what remains
is exactly what the specification itself marks open:

- **Documented no-mapping**: BIhI at tanru and sentence loci — CLL
  14.16 records that no meanings have been found; the mapping states
  no row and implementations must not invent one.
- **Registered gaps** (spec §14): ordinary first-order restrictive
  clauses on `bu'a`-variables; explicit-`ce'u` in the non-`ka`/`du'u`
  abstractors; the non-numeric `me … me'u MOI` composite;
  constitution-bearing sumti/property/event `joi` and compound ijoiks;
  the explicit vague connective `ju'e`; cross-clausal topic place-linking.
