# Reference pluralities with a set-theoretic counting layer

Status: convergence candidate, folded into `sexpr-v3-draft.md` draft 7. This supersedes the concrete
`Referents<K> = Set⁺<Individual<K>>` recommendation in
`plurality-sets-design.md`.

## 1. Conclusion

Make number-neutral plural reference explicit, but do **not** identify every
ordinary sumti value with an object-language set or require every such value to
be atomically decomposable.

Use an abstract `Referents<K>` value for what an ordinary sumti refers to. A root
predicate place accepts `Referents<K>` directly. In the discrete, countable fragment,
`Referents<K>` has the familiar nonempty-set model. Exact quantification is then
higher-order cardinality predication on a derived extension of singular
members. Set objects
(`lo'i`) and group objects (`loi`/`gunma`) remain ordinary referents described by
ordinary predications.

This keeps the attractive part of the Brismu proposal while avoiding the false
equation “the people who walked = the abstract set of people which walked”.

## 2. Why the literal nonempty-set alias is too strong

The first pass proposed:

```text
Referents<K> = Set⁺<Individual<K>>
```

That is a useful model, but an overcommitted public definition.

First, ratified xorlo permits generic reference. Guskant's explicitly
unofficial plural-logic account goes further: `me` is a reflexive, transitive,
antisymmetric “among” relation and `jo'u` is an idempotent commutative
combination. It explicitly permits a referent which is neither one individual
nor a plurality of atomic individuals, with material reference as the example.
The notation permits that extension without claiming it as normative. The free
set model is one model of that algebra, not its only model.

Second, a set is already an object-language kind in Lojban. `lo'i prenu` is an
abstract referent with membership and cardinality. If the semantic value of
plain `lo prenu` is printed as the same `Set` type, the notation invites exactly
the invalid inference that the abstract set walked or ate.

Third, reference selection is dynamic. A pure set constructor does not by
itself express contextual selection, fixed identity, projection, or anaphoric
accessibility.

## 3. Revised value types

```text
K                     one singular semantic kind, such as Entity or Eventuality
Referents<K>               a nonempty, number-neutral referential value of kind K
Set<K>                an extensional set of singular K-values; may be empty
PredTerm<{p:Referents<K>} + ρ>
RefComp<Γ, Δ, A; E>   a dynamic computation returning reference value A
```

`Referents<K>` includes the singleton and multiple-referent cases without making
them different types. It may also admit a non-atomic or kind-level referent when
the source and discourse ontology do. The printed name says only that this is
what a reference expression supplies to a place.

A singular variable of kind `K` singleton-lifts when it fills a `Referents<K>`
place. The coercion normally remains implicit:

```text
Singleton : K -> Referents<K>
```

The ordinary plural operations are relations/functions on `Referents<K>`:

```text
Among   : K x Referents<K> -> PredTerm<empty>
Among   : Referents<K> x Referents<K> -> PredTerm<empty>
Combine : Referents<K> x Referents<K> -> Referents<K>
```

`Among` is the semantic reduction of the relevant `me` relation. `Combine` is
the number-neutral, commutative, idempotent `jo'u` operation. Whether the final
surface uses `Among`/`Combine`, lowercase source-backed predications, or
conventional order/join glyphs remains a notation decision.

The singular-member property `λx. Among(x,r)` supplies an ordinary mathematical
extension only when the source explicitly requests an inner count or outer
quantifier. Those singular values are the values substitutable for the source's
ordinary bound variable, not metaphysical atoms. A generic or material
reference is never silently assigned the empty extension and cardinality zero.
If the graph cannot recover a source-licensed counting basis, projection uses
typed fallback plus a collected diagnostic.

## 4. Predicate places are number-neutral

Every ordinary root place takes `Referents<K>`. The root itself is a primitive
relation over such arguments:

```lisp
(bevri (Refer (Counted (Exactly 3) prenu)) (Refer pipno))
```

No hidden `Each`, `Group`, `Cover`, or `PluralFill` is inserted. This is not an
incomplete reduction any more than leaving `bevri` itself as a lexical root is
incomplete. The extension of `bevri` over number-neutral arguments is part of
the lexical/contextual interpretation. Lojban deliberately leaves the plain
sentence neutral between distributive, collective, and contextually supplied
cover readings.

No distributivity, cover, or cumulative-closure law is supplied by the
notation. When the source explicitly contributes distributivity, group formation, a
portion, or another reading, the corresponding higher-order operation or
referent is printed. A downstream theorem-proving profile may additionally
axiomatize cumulative closure or covers, but the human-readable projection must
not choose one without source/model evidence.

## 5. `Refer` consumes a property of a reference value

The first pass made the reference operator consume a property of one individual and silently
required every selected member to satisfy it. That needlessly imposed atomic
distribution. The better type is:

```text
Refer : Fn<Referents<K>, Content>
        -> RefComp<Γ, Δ, Referents<K>; E>
```

Thus `(Refer gerku)` uses the existing property eta-coercion over x1, and means a
contextually selected, fixed reference value with a projecting `gerku`
description. Ratified xorlo defines it as `zo'e noi ke'a gerku`: doghood is
backgrounded descriptive content, not part of the containing assertion,
denial, or question's at-issue nucleus. It is not an existential quantifier and
not necessarily the full extension of `gerku`.

Source `le` supplies `Refer` with a partially filled `skicu` property, such as
`(Refer (skicu Speaker :3 Audience :4 gerku))`. Source `la` supplies a lowercase
`cmene` property, such as `(Refer (cmene (NameSign "alis") :3 Speaker))`.
Neither needs its own semantic reference operator. The next effective open
place—x2 in both examples—is eta-expanded as the referred value.

Ordinary reference computations are nonempty. A literal zero inner count is a
special negated-existence construction or a referential failure; it is not an
empty `Referents<K>` silently passed to a lexical place.

## 6. Inner count is a constraint inside reference selection

`lo ci gerku` counts the referents of one constant. It does not quantify the
containing bridi. A fully reduced property is:

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

The concise, conventional contraction is:

```lisp
(Refer (Counted (Exactly 3) gerku))
```

`Exactly 3` is a first-class cardinal generalized quantifier. `Counted` applies it to
the reference's source-licensed singular member property while preserving the
base description; it is not an outer quantifier. The long form shows that no
special cardinality record is necessary. Non-exact inner quantifiers use the
same form, for example `(Refer (Counted (AtLeast 3) gerku))`. `Every` is not in
the `CardGQ` input family: `lo ro gerku` separately lowers to a dog reference
which contains every singular dog, rather than a reference containing every
entity in the universe.

The constraint must remain inside the reference computation. Binding an
unconstrained `(Refer gerku)` and then separately asserting `Card = 3` has the
wrong force and projects incorrectly through negation, questions, and
attitudes. A generic post-selection `WhereRef` is therefore rejected.

## 7. Outer count is cardinality of singular satisfiers

Given a fixed description referent `$dogs`, “exactly two of those dogs are
white” is:

```lisp
(Let (($dogs (Referents Entity) (Refer gerku)))
  (Assert
    (=
      (Card
        (λ (($x Entity))
          (∧
            (Among $x $dogs)
            (blabi $x))))
      2)))
```

This reuses the existing higher-order `Card : Property<T> -> Number`. Its
property extension is the derived set on which cardinality is computed; no
printed `Filter` node is required.

The common outer quantifiers reduce similarly:

```text
ro r P       = for every singular x, Among(x,r) -> P(x)
su'o r P     = Card(x => Among(x,r) and P(x)) >= 1
no r P       = Card(x => Among(x,r) and P(x)) = 0
re r P       = Card(x => Among(x,r) and P(x)) = 2
su'o ci r P  = Card(x => Among(x,r) and P(x)) >= 3
```

This reduction is for an outer quantifier applied to an existing reference
expression, such as `re le gerku`. It must not be confused with bare
`PA broda`, whose ratified xorlo expansion is `PA da poi broda` and therefore
uses a domain binder plus restriction. The current `∀`/`∃` forms remain for
that case and for unrestricted quantification.

The three surface forms are therefore deliberately distinct:

```text
PA broda       domain quantification
PA lo broda    outer quantification over a fixed reference
lo PA broda    one fixed reference with an inner count
```

When the selected witnesses are subsequently referred to, truth-conditional
`Card` alone is insufficient. The graph-owned witness reference must also be
bound using
`Witnesses : GQ<T> x Property<T> -> RefComp<Γ,Δ,Referents<T>;E>`.
The first operand retains the originating generalized quantifier, including
its restriction; the second is its nuclear scope. The reference is whatever
witness identity the graph exports from that successful dynamic application,
not a hard-coded maximal extension or arbitrary subset. The original
restriction/scope truth condition still prints independently, so exact and
lower-bounded quantifiers cannot become identical or vacuous. A zero-witness
quantifier cannot export the nonempty `Referents<T>` type. The binding form is
mechanically selected exactly when the graph records a later-accessible
selection source; otherwise only the concise cardinality/∀ form prints.

Positive equal-scope termsets reduce one step further. For restrictions `Pi`,
sets `Si`, and nuclear relation `R`, each selected set is the full coordinate
extension relative to the other selected sets:

```text
Ei(xi; S-i) = Pi(xi) ∧
  ∀x-i. (∧j≠i xj ∈ Sj) → R(x1,...,xn)

∃S1...Sn.
  ∧i (Restrict Qi Pi)(λxi. xi ∈ Si)
  ∧i ∀xi. xi ∈ Si ↔ Ei(xi; S-i)
```

The right-to-left biconditional direction is essential. Merely requiring a
qualifying Cartesian subset would make `Exactly 3` indistinguishable from
`AtLeast 3`, because an arbitrary three-member subset could always be selected
from four qualifying individuals. Coordinate-wise exhaustivity preserves the
distinction while avoiding an ordered individual-quantifier nest. Quantifier
dependencies, intensional scope, unsupported downward-entailing polyadic lifts,
and generalized non-cardinal scales remain higher-order or use typed fallback
rather than inheriting current tersmu's work-in-progress nesting.

## 8. `poi` is not necessarily an individual set filter

The first set pass treated every restrictive relative clause as memberwise
`Filter`. That again forces distributivity. The established expansion is a
property conjunction over a reference value:

```lisp
; a restrictive description based on $base
(Refer
  (λ (($r (Referents Entity)))
    (∧
      (Among $r $base)
      (blabi $r))))
```

In the ordinary white-dogs case this commits the contextually supplied
subreference to being among the base and white.
The same form remains valid when the relative predicate is collective or the
referent is non-atomic. There is no `Relative` record and no forced
individual-level `Filter`. It entails no maximality. Because the conjunction is
descriptive material under `Refer`, it projects rather than becoming part of the
host assertion or question's at-issue nucleus.

`voi` replaces the veridical relative predication with `DescribedAs`. `noi` is
structurally different: bind the description first, then place a `Supplement`
about that first-class reference outside the selecting property. Thus ordinary
conjunction plus the effect connector encode the restrictive/incidental split;
sets do not collapse these different commitments.

## 9. `lo'i` and `loi` need no primitive constructors

The source-backed expansions already use ordinary predications and bind their
shared base once:

```lisp
; lo'i prenu
(Let (($people (Referents Entity) (Refer prenu)))
  (Refer (selcmi :2 $people)))

; loi prenu
(Let (($people (Referents Entity) (Refer prenu)))
  (Refer (gunma :2 $people)))
```

The first returns a number-neutral reference to one or more set objects; the
second returns a number-neutral reference to one or more group objects. They
may have refined result kinds such as `Set<Entity>` and `Group<Entity>`, but
neither requires `SetOf` or `GroupOf` in the normal printed form.

Set extensionality determines the first object by its members. `gunma` relates
a group to its members, but the group is not identical to their set. Mereology
can likewise be expressed through `pagbu` predications. This is the precise
sense in which groups and material structure can be built *over* set-theoretic
foundations without treating the set itself as the walking or carrying agent.

The related operations stay distinct:

| source | reduction | result |
|---|---|---|
| `X jo'u Y` | `(Combine X Y)` | ordinary reference |
| `X joi Y` | `(Refer (Counted (Exactly 1) (gunma :2 (Combine X Y))))` | one group |
| `X ce Y` | `(Refer (Counted (Exactly 1) (selcmi :2 (Combine X Y))))` | one set |
| `X ce'o Y` | `(Singleton (List X Y))` | one ordered sequence |

`lu'i S` and `lu'o S` use the same singleton-counted `selcmi` and `gunma`
shapes with `S` in x2. `vu'i S` forms the set of `S`, then selects one `porsi`
with that set in x3 only when the operand is unordered; its elided ordering rule
then remains contextual. An already ordered operand or graph-recorded ordering
rule is preserved rather than discarded and re-chosen. `lu'a` lowers at its containing
predication to ordinary universal quantification over `cmima`/`Among`, because
merely returning a member reference would lose its explicit distributivity.
For example, `lu'a $rat-set cu cmalu` becomes
`∀x.(cmima(x,$rat-set) -> cmalu(x))`. An anaphorically live member reference may
also be bound through `(Refer (cmima :2 $rat-set))`.

Thus no `SetOf`, `GroupOf`, `SeqOf`, `Members`, or generic `Mass` intrinsic is
needed. Empty-set `lu'a` cannot produce an ordinary nonempty reference and uses
typed fallback plus a collected semantic diagnostic.

## 10. Scope and effects are unchanged by the counting model

An unquantified xorlo description is a constant. Its computed fixed reference
binding is semantically wider than extensional `¬`, `∨`, and `→`; those operators
do not turn it into a fresh existential choice. Crossing one of those visible
scope-bearing operators makes the wide `Let` explicit. `Joi` and administrative
event-closure shells remain transparent inside the already selected host.
Binding respects the closed `Extensional | Intensional | Opaque` policy for
every dynamic relation place or constructor input and any graph-recorded de-re
owner; the renderer never guesses an “intensional handler” from root spelling.

Consequently the old sample which placed `(Refer gerku)` freshly inside `¬` is
wrong. The correct shape is:

```lisp
(Smusni 0
  (Let (($dogs (Referents Entity) (Refer gerku)))
    (Assert
      (¬
        (melbi $dogs)))))
```

Set/cardinality reduction does not replace the indexed discourse computation,
`BindRef`, `Presuppose`, `Supplement`, or first-class witness identity. It only
gives ordinary mathematical reductions for the countable parts of their
content.

## 11. What is and is not adopted from Brismu

Adopt:

- ordinary set theory for extensions, singular-member domains, filtering, and
  cardinality;
- first-class set values and set relations where Lojban explicitly speaks of
  sets;
- ordinary predicational expansions of group, set, sign, and other apparent
  special forms;
- a discursive/dynamic layer for contextual `lo`/`le` reference.

Do not infer:

- that every plural constant is publicly identical to a mathematical set;
- that a set of people can fill an ordinary people-place *as the set object*;
- that membership alone supplies collective agency, genericity, material
  parthood, reference effects, or distributivity;
- that cardinality eliminates higher-order binders or discourse witness state.

The implementation may use a set representation for the free, discrete model
of `Referents<K>`. The notation and type laws should expose only the weaker
commitment that every source construct actually warrants.

In particular, “sets, not masses” does **not** mean that the set of some people
itself walks. It means that extensional membership, extensions, and cardinality
are available for free in the metalogic and as explicit object-language set
objects. A mass/group can then be an ordinary object related to its components
by `gunma`, and material structure can be axiomatized with `pagbu`; those
relations can themselves be studied through sets of satisfying individuals.
This builds group/mereological theories *over* set-theoretic foundations rather
than identifying groups with sets.

Nor does first-class `Set<K>` eliminate plural/dynamic reference. Xorlo's plain
constants remain number-neutral and quantification is singular/distributive
only where the source says so. Exact quantification can be reduced to `Card` of
a derived property extension, but the binder, its restriction and scope,
projective description effects, and any exported discourse witness remain
higher-order/dynamic structure. Making plurality explicit is therefore useful;
making every sumti an object-language set would be a category error.

## 12. Research anchors

- [Brismu: Sets, not Masses](https://brismu.systems/sets-not-masses.html) gives
  the free-set motivation and explicitly places plural/discursive logic above
  that foundation rather than equating every discourse referent with a set.
- [Gadri: an unofficial commentary from a logical point of
  view](https://mw.lojban.org/papri/gadri:_an_unofficial_commentary_from_a_logical_point_of_view)
  supplies the explicitly unofficial plural `me`/`jo'u` algebra, Skolem-style
  dependence, and predicational `selcmi`/`gunma` reductions.
- [How to use xorlo](https://mw.lojban.org/papri/How_to_use_xorlo) and ratified
  CLL 25.2/16 establish the constant versus quantified split, inner/outer
  numerals, and singular distributive quantification only where explicit.
- [BPFK sumtcita
  formants](https://mw.lojban.org/papri/BPFK_Section%3A_sumtcita_Formants)
  gives both the `.i joi` paraphrase and the unary higher-order bridi-operator
  account used for tags.
- Robaldo, Szymanik, and Meijering's [witness-set
  analysis](https://dare.uva.nl/search?metis.record.id=438841) is the reason the
  notation retains the originating generalized quantifier and does not bake
  one global maximalization policy into `Witnesses`.
- Westerståhl's [Decomposing Generalized
  Quantifiers](https://www.cambridge.org/core/journals/review-of-symbolic-logic/article/abs/decomposing-generalized-quantifiers/FCDDEF372B3571751CAE4C7D64A6ADBC)
  cautions that a generalized quantifier decomposes into a quantifier plus a
  set only under stated conditions; this supports keeping `GQ`, restriction,
  and dynamic export explicit.
- Sher's [Ways of Branching
  Quantifiers](https://philosophyfaculty.ucsd.edu/faculty/gsher/ways-of-branching-quantifiers.pdf)
  supplies the maximal each-all condition needed when a branching quantifier
  is non-monotone. The coordinate biconditionals above are its extensional
  spelling and prevent exact counts from collapsing to lower bounds.
- Uegaki's [semantics of question-embedding
  predicates](https://semanticsarchive.net/Archive/DQ3MDgwN/paper.pdf) surveys
  the conventional question-to-proposition/answerhood crossing represented by
  `Answer` in the main draft.

## 13. Decision

The main draft adopts `Referents<K>` as the number-neutral argument type, but
defines it abstractly rather than as `Set⁺<Individual<K>>`. Predicate roots are
primitive relations over `Referents<K>`. Ordinary set theory supplies
extensions and cardinality only at explicit counting sites. `lo'i` and `loi`
expand through `selcmi` and `gunma`; nonlogical connections and LAhE crossings
use their distinct source-backed reductions. Dynamic reference binding,
projecting descriptor content, and higher-order quantification remain wherever
identity, effects, scope, distributivity, or unsupported polyadic dependencies
make a pure cardinality formula insufficient. Positive CLL equal-scope termsets
use selected mathematical sets only inside their truth conditions; those sets
are not identified with ordinary plural referents.
