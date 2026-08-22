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
once in §13. The record of the ledger of coverage holes this index
originally exposed — resolved in the round-14 cycle — is §15.

In the examples, the first comment line is the Lojban source; `…`
elides material irrelevant to the entry; some lowerings are shown in
the abbreviated style the samples book uses (e.g. `(Refer gerku-prop)`
for the full property spelled out).

## 1. Predication and places

### fa / fe / fi / fo / fu (FA)

Place tags: explicit labelled fills, freeing surface order (spec §4.2;
fills at distinct labels commute).

```lisp
; klama fa mi fi la paris
(Close (klama :1 Speaker :3 paris-ref))
```

**See.** [Spec §4.1–4.2, §11](spec.md).

### fai (FA)

The fill tag for the place `jai` demotes the old x1 into.

```lisp
; mi jai gau rinka … fai lo nu …
(Close ((JaiPromote rinka gau-role) :1 Speaker :fai event-ref))
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
(Bind {$dest :: Referents Entity} (Context) ; typical-for-place constraint
  {(Close (klama Speaker $dest))})
```

**See.** [Spec §5.3, §11](spec.md), pin P15.

### co'e (GOhA), do'e (BAI)

The relation-level and tag-level ellipses: `Context` at relation type /
tag type (P14).

```lisp
; ko'a co'e ko'e
(Bind {$r :: PredTerm ρ} (Context)
  {(Close ($r ko'a-ref ko'e-ref))})
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
(Bind {$dogs :: Referents Entity} (Refer gerku-prop)
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
        {(∃ (λ {$e :: Referents Locution}
          {(skicu :1 Speaker :2 $r :3 Audience :4 gerku-prop
                  :Eventuality $e)}))}))
  {(Close (bajra $x))})
```

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
(Generic Typical gerku-prop (λ {$x :: Referents Entity}
  {(Close (batci $x))}))
```

**See.** [Spec §5.8, §11](spec.md), pin P11.

### loi / lo'i (LE)

Group and set objects: `Refer` to the `gunma`/`selcmi` object whose
components/members are the **maximal** plurality of the description
(P5); inner PA counts the base, outer PA counts groups/sets.

```lisp
; loi gerku cu sruri lo zdani — the maximal base bound first
(Bind {$base :: Referents Entity} (MaxRefer gerku-prop)
  {(Bind {$g :: Referents Entity}
        (Refer (λ {$r :: Referents Entity} {(gunma $r $base)}))
    {(Close (sruri $g zdani-ref))})})
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
           (= (CardBasis $r gerku-prop) 3))}))
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
; mi djuno la'e by — by bound to a sentence-sign referent
(Close (djuno Speaker (Reify (InterpretContent by-sign))))
; la'e di'u crosses through the token's realized act instead:
; Realizes + InterpretAct, host-sorted (P28)
```

**See.** [Spec §7.5, §11](spec.md).

### lu'a (LAhE)

Member-distribution marker: `lu'a r` ≝ distribution over the
members — `Distrib` at the use site (the explicit each-reading; spec
§12's plurality library).

```lisp
; lu'a le prenu cu bevri — each of them carries
(Distrib (λ {$x :: Entity} {(Close (bevri $x))}) prenu-ref)
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
(Bind {$d :: Referents Entity} (Refer gerku-prop)
  {(Supplement $d (Close (blabi $d))
     (Close (bajra $d)))})
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
; lo gerku goi ko'a … .i ko'a bajra
(Bind {$d :: Referents Entity} (Refer gerku-prop)   ; ko'a ↦ $d
  {(Do (Assert …) (Assert (Close (bajra $d))))})
```

**See.** [Spec §5.6, §11](spec.md), pin P16.

### vu'o (VUhO)

### pe / ne / po / po'e / po'u / no'u (GOI)

The associator family, by CLL 8.3's own expansions (nested as CLL
nests them): `pe` → restrictive `srana` conjunct; `ne` → the
incidental (`Supplement`) counterpart; `po` → restrictive
`se steci srana`; `po'e` → restrictive `jinzi ke se steci srana`;
`po'u` → restrictive P23 identity; `no'u` → incidental identity. The
associated sumti is bound before the pure restriction forms.

```lisp
; le stizu pe mi cu blanu — CLL 8.18
(Bind {$s :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(∧ (le-stizu-base $r) (srana $r Speaker))}))
  {(Close (blanu $s))})
```

**See.** [Spec §11](spec.md); CLL 8.3.

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
(Bind {$w :: Referents Entity} (SelectSome gerku-prop)
  {(Close (bajra $w))})
```

**See.** [Spec §5.6, §4.10](spec.md); [catalog 2.22](catalog.md).

### Digits: pa re ci vo mu xa ze bi so no (PA)

Outer numeric quantifiers select witness sets of that cardinality
under a counting basis — neutral witness-set selection, not
distributive and not global (P17's documented divergence; the
CLL-literal readings are `GlobalExactly` and `Distrib`).

```lisp
; re prenu cu bevri lo pipno
(Bind {$w :: Referents Entity} (SelectExactly 2 prenu-prop)
  {(Close (bevri $w pipno-ref))})
```

**See.** [Spec §4.10, §5.6](spec.md), pin P17.

### su'e / za'u / me'i (PA)

At-most / more-than / fewer-than selections — the bounded members of
the selection family, same witness-set discipline.

**See.** [Spec §4.10, §5.6](spec.md).

### so'a / so'e / so'i / so'o / so'u (PA)

The vague-magnitude series: selections whose cardinality condition is
a `Vague`-parameterized region on the count scale.

**See.** [Spec §6.4–6.5](spec.md).

### ji'i (PA)

Approximation, position-indexed (P37): prefix/medial `ji'i`
approximate through `AdmissibleTolerance` (`Vague`, nonempty by VC1);
suffix `ji'i` rounds (a definedness condition on the numeral),
directionally under `ma'u`/`ni'u`.

**See.** [Spec §4.10, §6.4, §12](spec.md), pin P37.

### du'e / rau / mo'a (PA)

Threshold quantifiers: `ThresholdKind` (TooManyK / EnoughK / TooFewK)
over the count scale — contextual threshold, explicit kind.

```lisp
; du'e gerku cu bajra
(TooMany gerku-prop (λ {$w :: Referents Entity}
  {(Close (bajra $w))}))
; ≝ Bind a Context standard and a Vague admissible threshold,
;   then MoreThan (catalog 2.13)
```

**See.** [Spec §6.4](spec.md); [catalog](catalog.md).

### da / de / di (KOhA)

Unrestricted first-order variables: `∀`/`∃` over the top sort, domain
restricted only by `poi` (P20).

```lisp
; da gerku
(∃ (λ {$x :: Entity} {(gerku $x)}))
; da zo'u da gerku — the prenexed spelling; prenex order is scope
; order (P26)
```

**See.** [Spec §4.5, §11](spec.md), pin P20.

### zo'u (ZOhU)

Prenex and topic separator (P26). Quantifier prenex: prenexed terms
lower to the quantifier/selection prefix in surface order — prenex
order is scope order. Topic use: the topic binds, and a `Vague`
`TopicResolution` fills an admissible place of the open comment frame
or bears `srana`-aboutness to the closed comment (CLL 19.4's fish =
the place choice); `tu'e…tu'u` extends one topic over a sequence.

```lisp
; ro da poi prenu ku'o su'o de zo'u de patfu da — CLL 19.8
(Presuppose (∃ prenu-prop)
  (∀ (λ {$x :: Entity} {(→ (prenu $x)
     (∃ (λ {$y :: Entity} {(Close (patfu $y $x))})))})))
```

**See.** [Spec §11, §12](spec.md), pin P26; [catalog 1.51](catalog.md).

### da'a (PA)

All-but-n (default one): the `SelectAllBut` selection — a neutral
witness set whose remainder counts exactly n; the omitted
individuals are not a parameter and may vary under distributive
scope.

**See.** [Spec §12, §11](spec.md); [catalog 2.31](catalog.md).

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
; su'o bu'a zo'u la .djim. bu'a la .djan. — CLL 16.105
(∃ (λ {$F :: PredTerm ρ} {(Close ($F jim-ref jan-ref))}))
```

**See.** [Spec §11](spec.md), pin P30.

### ce'e (CEhE), nu'i / nu'u (NUhI/NUhU)

Termsets: co-selected witness sets at one joint multi-parameter locus,
full product, no coordinate maximality (P17).

```lisp
; ci gerku ce'e re prenu cu batci
(∃ (λ {$dogs $people :: Set Entity}
  {(∧ (= (Card $dogs) 3) (= (Card $people) 2) …)}))
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
; mi .e do nelci lo gerku — one dog-referent, both conjuncts see it
(Bind {$d :: Referents Entity} (Refer gerku-prop)
  {(∧ (Close (nelci Speaker $d))
     (Close (nelci Audience $d)))})
```

```lisp
; mi .a do klama lo zarci — ∨ instead; the store is still introduced
; once, outside the disjunction
(Bind {$z :: Referents Entity} (Refer zarci-prop)
  {(∨ (Close (klama Speaker $z))
     (Close (klama Audience $z)))})
```

**See.** [Spec §4.5, §5.3–5.4, §11](spec.md), pin P18. Compounds
(`na.a`, `se.u`, `.anai`): §14.

### ja / je / jo / ju (JA) — tanru-internal and general connectives

Same logical operators at their locus. At the *tag* locus: the
operator over the tag conjuncts (§11's facet joining). At the
*tanru-unit* locus: `TanruLinkConnect` (P33) — shared head asserted
once, one `Vague` link per conjunct, connective over the link
applications; distinct-head units connect as whole predications.

```lisp
; ta blabi ja cmalu zdani — one house; the modification link is
; white-flavored or small-flavored
(Close ((TanruLinkConnect ∨ blabi cmalu zdani) ta-ref))
```

**See.** [Spec §6.2, §12, §11](spec.md), pin P33;
[catalog 2.32](catalog.md).

### gi'a / gi'e / gi'o / gi'u (GIhA) — bridi-tail connectives

Logical connection of bridi tails: the shared head terms scope over
the connective (they are one introduction, one selection), each tail
closes separately, and tail-terms after the last tail are shared by
all tails.

```lisp
; mi nelci lo gerku gi'e bajra — Speaker shared, dog in one tail only
(Bind {$d :: Referents Entity} (Refer gerku-prop)
  {(∧ (Close (nelci Speaker $d)) (Close (bajra Speaker)))})
```

```lisp
; mi dunda le cukta gi'e lebna lo jdini vau do — CLL 14.54: the
; tail-term do applies to both tails (dunda x3 and lebna x3)
(Bind {$b :: Referents Entity} (Refer le-cukta-prop)
  {(Bind {$m :: Referents Entity} (Refer jdini-prop)
    {(∧ (Close (dunda Speaker $b Audience))
       (Close (lebna Speaker $m Audience)))})})
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
(Bind {$p :: Referents Entity} (Refer plise-prop)
  {(∨ (Close (citka Speaker $p))
     (Close (citka Audience $p)))})
```

**See.** [Spec §4.5, §5.3, §11](spec.md); §14 for the gek/guhek units.

### na (NA)

Bridi negation: `¬` at the left edge — `na` ≡ left-edge `naku`, with
CLL ch. 16's flip rules governing movement past quantifiers (P18).

```lisp
; mi na klama
(¬ (Close (klama Speaker)))
```

**See.** [Spec §4.5, §11](spec.md), pin P18.

### naku

`¬` at its surface position: quantifier scope read off the surface
order; movement flips per ch. 16.

**See.** [Spec §4.5, §11](spec.md), pin P18; §14 (`na ku` unit).

### joi (JOI)

By syntactic position (the one non-logical connective with split
lowering): sumti `joi` → group formation with `Vague` mixture kind;
tag/facet joining → `∧`; discourse joining → `Do`; residual
genuinely-unspecified connection → `Vague` over the connecting
relation.

```lisp
; mi joi do bevri lo pipno
(Bind {$g :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(gunma $r (Combine Speaker Audience))}))  ; mixture kind Vague
  {(Close (bevri $g pipno-ref))})
```

**See.** [Spec §4.8, §11](spec.md).

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
object); `bi'i` → ⊳ symmetrization of the same (endpoint order
normalized with the GAhO kinds); `mi'i` → `MetricBall`
(center-radius, Context metric — no endpoint arithmetic); `bi'o nai`
→ `RegionComplement` in a Context universe; the region object fills
the host place. At tanru and sentence loci BIhI has **no standard
resolved mapping** (CLL 14.16: no meanings found) — a documented
no-mapping.

```lisp
; li pa bi'i li mu
(Interval 1 5 k₁ k₂)   ; endpoint kinds k₁ k₂ chosen by ga'o/ke'i
```

**See.** [Spec §11, §12](spec.md); [catalog 2.33](catalog.md).

## 6. Tense, aspect, modals

### pu / ca / ba (PU)

Temporal facets as ordinary event predicates: precedence/overlap
conjuncts on the event, anchored at the utterance (or the chain's
anchor); chains (`pu pu`) compose as anchor paths.

```lisp
; mi pu klama
(∃ (λ {$e :: Referents Eventuality}
  {(∧ (Close (klama :1 Speaker :Eventuality $e))
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
; le verba mo'i ri'u cadzu
(∃ (λ {$e :: Referents Eventuality}
  {(∧ (Close (cadzu :1 verba-ref :Eventuality $e))
     (MotionVector $e verba-ref rightward-ref))}))
```

**See.** [Spec §11](spec.md); [catalog 1.50](catalog.md).

### roi (ROI)

Occurrence count: `n roi` **replaces** the single-event existential
closure with the counted instantiation-set schema — the set of
distinct eventualities satisfying the host event property within the
reference interval has cardinality n (P35); `roi nai` negates the
count; subjective counts use the threshold GQs; the default interval
is a Context anchor with Vague extent.

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

Actuality and capability: `ca'a` → `fasnu` actuality conjunct; `ka'e`
→ the capability schema over the primitive `InnatelyCapable`; `nu'o` =
capable and unrealized; `pu'i` = capable and demonstrated.

```lisp
; mi ka'e limna
(InnatelyCapable Speaker (λ {{$b :: Referents Entity}
                             {$e :: Referents Eventuality}}
  {(Close (limna :1 $b :Eventuality $e))}))
```

**See.** [Spec §12, §11](spec.md); [catalog 1.50, 2.21](catalog.md).

### BAI family (bai, gau, ri'a, mu'i, ki'u, ta'i, pi'o, ka'a, …)

Modal tags: event-predicate conjuncts per the lexicon's tag
reductions — each BAI names its gismu's relation between the tagged
sumti and the host event, joined by `∧` at the tag locus. `se`/`te`
conversions apply to the underlying row (§14 sequences).

```lisp
; mi klama bai do
(∃ (λ {$e :: Referents Eventuality}
  {(∧ (Close (klama :1 Speaker :Eventuality $e))
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

Bridi anaphora: ⊳ expansion with the antecedent's **resolved**
context — closure sites keep their values; `go'i` as an answer is
`Answer` with polar selection.

**See.** [Spec §11, §8](spec.md), pin P16.

### ra'o (RAhO)

Re-resolution: the expanded bridi's deictics re-resolve under the
current `InContext`/`ShiftedGround`.

**See.** [Spec §5.1, §11](spec.md).

### di'u / de'u / da'u / di'e / de'e / da'e / dei / do'i (KOhA)

Utterance anaphora at `Referents<UtteranceToken>`: ⊳ recency over the
transcript at three distances, past and future; `dei` = the current
entry's own bound token; `do'i` = `Context` at the salient token/span
(P28). `la'e` on these crosses through the token's realized act
(`Realizes` + `InterpretAct`) into the host-sorted crossing — no
universal coercion.

```lisp
; di'u jitfa jufra — the previous utterance is a false sentence
(Close (jitfa-jufra dihu-token))   ; dihu-token ⊳ bound by recency
```

**See.** [Spec §11, §7.4](spec.md), pin P28.

### da'o (DAhO)

Assignment cancellation: ⊳ clears all resolver stores (KOhA,
letteral, pro-bridi); `ni'o` levels imply it per depth — single
(spoken) / double (written) clear assignments, triple also resets
tense and indicator stickiness, `no'i` resumes (spec §7.1).

**See.** [Spec §11, §7.1](spec.md).

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

Event abstraction: `Refer` over event properties — the eventuality
sort refined by the abstractor (Achievement `mu'e`, State `za'i`).
`pu'u` and `zu'o`, which keep real x2 places, live in the
abstraction-relation family instead (next entry; spec §9.2).

```lisp
; lo nu mi klama cu nandu
(Bind {$ev :: Referents Eventuality}
      (Refer (λ {$e :: Referents Eventuality}
        {(klama :1 Speaker :Eventuality $e)}))
  {(Close (nandu $ev))})
```

**See.** [Spec §9, §11](spec.md); [primer ch. 6](primer.md).

### du'u (NU)

Proposition abstraction: `Reify` — content held still as a first-order
`Proposition` object, with `Holds` the sole way back (round-trip
axiom). With explicit `ce'u`, extracts λ exactly as `ka` (§11's arity
theorem: n **distinct** extracted variables = n-adic; bare `du'u` is
the 0-adic case). `se du'u`
= the sentence place of the derived `DuhuRel` (defined only for the
0-adic case — spec §9.2).

```lisp
; mi djuno lo du'u la frank cu bebna
(Close (djuno Speaker (Reify (Close (bebna frank-ref)))))
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
(Refer (λ {$a :: Referents Amount} {(Close ((NiRel …) $a))}))
```

**See.** [Spec §9.2, §11](spec.md).

### kei (elidable terminator)

Structure only — see §13.

### tu'a (LAhE)

Vague abstraction: shape conjunct + `srana`-aboutness, sort selected
by the host place (P14) — the deliberately underspecified "something
about X".

```lisp
; mi troci tu'a lo vorme
(Bind {$a :: Referents Eventuality}
      (Vague tuha-abstraction-of-vorme)  ; shape conjunct + srana-aboutness
  {(Close (troci Speaker $a))})
```

**See.** [Spec §11](spec.md), pin P14.

### jai (JAI)

With tag: explicit role promotion — the tagged role to x1, old x1 to
the fillable `fai` place (`JaiPromote`). Bare: participant raising out
of the abstraction-x1 with the role `Vague`.

```lisp
; mi jai gau rinka lo nu …
(Close ((JaiPromote rinka gau-role) :1 Speaker …))
```

**See.** [Spec §11, §12](spec.md); [catalog 2.20](catalog.md).

### kau (UI)

Indirect-question marker: `ContextualAnswer` — the answerhood object,
exhaustivity **absent** (weakest truth conditions; strengthenings
lexical/pragmatic/explicit; P9).

```lisp
; mi djuno lo du'u ma kau klama
(Close (djuno Speaker (Reify (Answer klama-question ContextualAnswer))))
```

**See.** [Spec §8.2, §11](spec.md), pin P9.

### me'au / me'ei (experimental)

Referenced, not baseline: use an abstract-predicate sumti as selbri /
form such a sumti. At the propositional case `me'au` is `Holds` in
selbri position under §9.1's singleton condition — the `Meau0`
schema, singularity projective; no plural baseline reading. Above
arity 0 the reified-predicate family is a §9.1 reservation (§14 gap).

```lisp
; me'au .abu gi'a me'au by.  — A or B, as claims
(∨ (Meau0 abu-ref) (Meau0 by-ref))  ; Meau0 (spec §9.1): presupposes
                                    ; a sole member and holds it
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
; .uinai mi klama — the display targets the bound host act; degree
; Moderate is the unmarked region (cai would make it Intense)
(Let {$a :: Act Assertion} (Assert (Close (klama Speaker)))
  {(Do (Perform $a)
      (Express (Close (Unhappiness Speaker $a Moderate))))})
```

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
; na'i (objecting to the previous utterance)
(NahiObjection prior-target)
```

**See.** [Spec §7.3, §12](spec.md); [catalog 2.23](catalog.md).

### da'i (UI)

Hypothetical mood: **gap-registered** with a bounded design space —
a member of the `Shift` operator family over the evaluation world,
with scope, dynamic binding under the shift, and scenario identity
the three things a treatment must define (spec §14's entry).

**See.** [Spec §14, §5.1](spec.md).

### Discursives (ku'i, ji'a, si'a, mi'u, ta'o, va'i, …) (UI)

Library discourse relations between act values (`Contrast`,
`Addition`, `Parallel`, `Elaboration`, …), displayed beside the host
act. Constituent `ji'a` and `po'o` are focus derivations
(`Additive`/`Only`).

```lisp
; .i mi klama .i ku'i do stali — no prior/following-discourse
; constants exist (§7.2): both acts are Let-bound values
(Do (Let {$a1 :: Act Assertion} (Assert (Close (klama Speaker)))
  {(Do (Perform $a1)
      (Let {$a2 :: Act Assertion} (Assert (Close (stali Audience)))
        {(Do (Perform $a2)
            (Express (Close (Contrast $a2 $a1))))}))}))
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
(Do (Vocative jan-ref)
    (Command jan-ref (Close (klama jan-ref))))
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

**See.** [Spec §11, §12](spec.md); [catalog 2.34](catalog.md).

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
quoted material introduces no discourse referents.

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
(= (+ 2 2) 4)
```

**See.** [Spec §4.9, §11](spec.md).

### du (GOhA)

Identity: `=` between first-order individuals; `CoRef` (mutual
`Among`) between plural sumti (P23).

```lisp
; ko'a du ko'e
(CoRef koha-ref kohe-ref)
```

**See.** [Spec §4.5, §11](spec.md), pin P23.

### VUhU operators (su'i, vu'u, pi'i, fe'i, …), pi, ni'u / ma'u

The MEX fragment: operators as typed functions over `Number`;
`pi` the radix point, `ni'u`/`ma'u` sign. Beyond the library fragment
(non-decimal bases, arrays, indefinite operators): gap-registered.

**See.** [Spec §4.9, §12, §14](spec.md).

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
; la .baltazar. cu me le ci nolraitru
(Close ((MePred le-ci-nolraitru-ref) baltazar-ref))
```

**See.** [Spec §12, §11](spec.md); [catalog 2.30](catalog.md).

### mei / moi / si'e / cu'o / va'e (MOI)

Number selbri: the MOI relation families — `MeiRel` (group from an
n-membered set), `MoiRel` (n-th under a Context-recovered pure
ordering), `SiheRel` (portion), `CuhoRel` (opaque probability,
0 ≤ n ≤ 1, no probability calculus — P29), `VaheRel` (scale
position). `me X me'u MOI` composes.

```lisp
; lei mi ratcu cu cimei — CLL 18.81
(Close ((MeiRel 3) ratcu-group set-ref members-ref))
```

**See.** [Spec §12, §11](spec.md), pin P29; [catalog 1.52](catalog.md).

### na'u / nu'a / ma'o / ni'e / te'u (MEX conversions)

The §12 partial interfaces: relation→operator (`na'u`, where
functional), operator→relation (`nu'a`, total), operand→operator
(`ma'o`, the function a `Context` recovery — P36), the
amount-operand crossing (`ni'e`); `te'u` structural; `se` on
operators permutes.

**See.** [Spec §12, §11](spec.md), pin P36; [catalog 2.35](catalog.md).

### la'o (ZOI), zo'oi (experimental)

Foreign names: naming through `(ForeignName t)` over the opaque
payload; `zo'oi` quotes one non-Lojban word as a word-level opaque
sign.

**See.** [Spec §12, §11](spec.md); [catalog 2.36](catalog.md).

## 12. Scalar and tanru operators

### na'e / no'e / to'e (NAhE)

Scalar negation: `(Scalar k P)` with k = OtherThan / Neutral /
Opposite — the na'e-family contraries, not `¬` (P18 handles `na`).

```lisp
; mi na'e klama
(Close ((Scalar OtherThan klama) :1 Speaker))
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
; ta blanu zdani be mi
(Close ((Tanru blanu (λ … {(zdani :2 Speaker)})) ta-ref))
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
(∧ (¬ (Close (klama Speaker))) (¬ (Close (klama Audience))))
```

**See.** [Spec §4.5, §5.4, §11](spec.md), pin P18.

### jek / gihek / joik with na / se / nai

The same decoration pattern at the other loci: `na ja`, `se gi'a`,
`joi nai`, `se joi` — one unit per EBNF `jek`/`gihek`/`joik`
production; `se` on a non-logical connective swaps the (ordered)
operands; `nai` on a joik is per-locus: truth-table for logical
loci, `RegionComplement` for BIhI, and for mixture joiks the `Vague`
mixture kind constrained to admissible alternatives other than the
named one (§11).

**See.** [Spec §4.5, §4.8, §11](spec.md).

### .i je / .i ja / .i joi … — I + jek/joik

Sentence-level connection as one unit — NOT `.i` followed by an
independent `je`: **one performance of the connected content** (P32 —
forced by `.i ja`, where no pair of assertions exists), the host's
single force shared by the connection, with `∧`'s accessibility row
shared with `Do`'s (spec §5.4).

```lisp
; mi klama .i je do stali — one act asserting the conjunction
(Assert (∧ (Close (klama Speaker)) (Close (stali Audience))))
```

**See.** [Spec §11, §5.4, §7.1](spec.md), pin P32.

### .i ba bo / .i pu bo … — I + stag + BO

One performance with the tag relating the two events — both event
binders exposed, the tag conjunct inside (P32):

```lisp
; mi klama .i ba bo mi citka
(Assert (∃ (λ {$e1 :: Referents Eventuality}
  {(∧ (Close (klama :1 Speaker :Eventuality $e1))
     (∃ (λ {$e2 :: Referents Eventuality}
       {(∧ (Close (citka :1 Speaker :Eventuality $e2))
          (balvi $e2 $e1))})))})))
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

## 15. Ledger record

The nineteen coverage holes this index originally exposed (H1–H19:
`zo'u`, `ko`, the GOI associators, `me`/MOI, `lei`/`le'i`/`lai`/
`la'i`, the `di'u` series, `zi'e`, `je'a`, `bu'a`/`cei`, `da'o`, the
MEX conversions, `co`, ROI, BIhI, the connective residue, MAI,
`vu'o`, `doi`, and the number-notation/quote residue) were resolved
by the round-14 design cycle: mapping rows in spec §11 (with §6.2 and
§7.1 additions), library forms in §12, and pins P26–P37 in §13. Each
former hole's cmavo now carries a real entry above. Two records
survive the ledger:

- **Documented no-mapping**: BIhI at tanru and sentence loci — CLL
  14.16 records that no meanings have been found; the mapping states
  no row and implementations must not invent one.
- **Reserved-family adjacencies** (spec §14, unchanged): ordinary
  first-order restrictive clauses on `bu'a`-variables, and
  explicit-`ce'u` in the non-`ka`/`du'u` abstractors, remain
  registered gaps.
