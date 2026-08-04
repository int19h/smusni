# Plural reference over sets: design pass

Status: design candidate for discussion and adversarial review. This note does
not yet amend draft 3, and implementation remains paused.

## 1. The proposal, with one necessary distinction

Brismu's “sets, not masses” claim supports using ordinary set-theoretic
foundations for plural semantics. It does **not** entail that an object-language
set is the agent in every plural predication. Three levels must remain distinct:

1. A **plural denotation** is the semantic value of an ordinary sumti such as
   `lo ci prenu`: one or more individuals considered as the fillers of a bridi
   place.
2. A **set referent** is the abstract object denoted by `lo'i prenu`. It has
   membership and cardinality, but the set itself does not walk or weigh what
   its members weigh.
3. A **group referent** is the first-class `gunma` denoted by `loi prenu`. It is
   one individual whose properties may arise collectively from its members.

Sets can underlie all three without identifying them. The first is a
metalanguage denotation type. The second and third are individuals in the
object-language universe, related to their members by different constructors
or predications.

That distinction reconciles the Brismu foundation with CLL/xorlo:

- an unquantified `lo`/`le`/`la` sumti is a constant, not a hidden quantifier;
- it may refer to one or several things, with no default distributive reading;
- an explicit outer quantifier ranges distributively over individual referents;
- `lo'i` denotes a set, while `loi` denotes a group (`gunma`).

## 2. Recommended semantic types

Use a nonempty set as the denotation of every ordinary reference expression:

```text
Individual<K>       one object of semantic kind K
Refs<K>             = Set⁺<Individual<K>>
Set<K>              an extensional set value; it may be empty
Group<K>            a group individual with K-members

PredTerm<{p:Refs<K>} + ρ>
RefComp<Γ, Δ, K; E> = dynamic computation returning Refs<K>
```

`Set⁺` is the familiar nonempty-powerset construction. `Refs`, rather than
`Plural`, is the proposed human-facing name because the singleton and the
many-member cases are not different semantic families. The existing
`Ref<Plural<T>>` distinction disappears.

All ordinary predicate places take `Refs<K>`. A singular constant or bound
individual is injected as a singleton; this coercion can normally remain
implicit:

```text
↑ : Individual<K> -> Refs<K>
```

Thus root predication itself stays uniform:

```lisp
(klama Speaker (Lo zarci))
(mlatu $x)                    ; $x is singleton-lifted when singular
```

The lexical relation is interpreted over plural arguments. That preserves the
source's neutral reading: applying `bevri` to three people does not silently
choose “each separately” or “one group object”. It says that those people, as
the plural argument, stand in the carrying relation. An explicit distributive
operator is used only when Lojban explicitly contributes one.

This is preferable to a generic `(PluralFill ...)` node: plurality belongs to
the argument type and the relation's extension, while `Fill` remains the one
operation for filling a place.

## 3. Set referents and group referents

The plural-denotation wrapper is not itself an object-language set. The level
crossings are explicit and typed:

```text
SetOf   : Refs<K> -> Individual<Set<K>>
Members : Individual<Set<K>> -> Set<K>
GroupOf : Refs<K> -> Individual<Group<K>>
Members : Individual<Group<K>> -> Set<K>
```

The exact names remain open. The invariant is more important than the spelling:

- `(Lo'i prenu)` returns a singleton `Refs<Set<Entity>>`; this abstract set may
  fill a set-valued place such as the population place of `fadni`.
- `(Loi prenu)` returns a singleton `Refs<Group<Entity>>`; that group may bear a
  collective property.
- `(Lo prenu)` returns `Refs<Entity>` directly and may contain one or several
  people.

The concise forms may elaborate through ordinary content-word predications:

```text
lo'i prenu  = lo selcmi be lo prenu
loi prenu   = lo gunma be lo prenu
```

`SetOf` and `GroupOf` are therefore candidates for typed elaboration functions,
not necessarily permanent printed intrinsics. Even if both are implemented
with sets internally, `GroupOf(S)` is not equal to `SetOf(S)`.

## 4. `lo`, `le`, and contextual selection

For an individual property `P`, `Lo(P)` dynamically obtains a fixed nonempty
reference set `S` whose members satisfy `P`:

```text
Lo : Property<Individual<K>> -> RefComp<Γ, Δ, K; E>

Lo(P) chooses S : Refs<K>
       subject to every x in S satisfying P(↑x)
```

It does not denote the full extension `{x | P(x)}` and it does not existentially
quantify the containing bridi. It is a contextually determined plural constant.

`Le(P)` similarly obtains a fixed nonempty `S`, but contributes the speaker's
description of `S` by `P`, rather than a veridical member restriction. `La`
constrains the selected referents by naming. Their dynamic/effectful status is
unchanged by the use of sets.

The nonemptiness is intentional. Ordinary xorlo descriptions refer to one or
more things; an empty set remains available as an explicit set value, but it is
not the default denotation of an unquantified ordinary sumti.

The fixed selected set scopes like an unquantified xorlo constant: extensional
`¬`, `∨`, `→`, and `Joi` do not by themselves force reselection. An intensional
handler such as an attitude, quotation, or a locally handled presupposition may
delimit it. Set semantics clarifies what is selected, but does not remove
dynamic scope or accessibility.

## 5. Inner numerals are predicates of the selected set

The inner numeral in `lo ci gerku` reports the cardinality of the description's
referents. It can therefore lower to an ordinary constraint on the selected
reference set:

```lisp
(Let (($dogs (Refs Entity) (Lo gerku)))
  (WhereRef $dogs
    (λ (($S (Refs Entity)))
      (= (Card $S) 3))))
```

`WhereRef` is only a provisional spelling for an effect-preserving constraint
on a reference computation. It should be eliminated if the existing reference
effect calculus can express the constraint without a new primitive. A concise
surface candidate is:

```lisp
(Lo gerku (Exactly 3))
```

whose elaboration is the cardinality predication above. `Exactly` here is not a
quantifier and does not scope over the containing bridi.

## 6. Outer quantifiers reduce to set selection and cardinality

An explicit outer quantifier is different: it applies the containing
predication distributively to individual members of a restriction set. Given
`S : Refs<K>` and `P : Individual<K> -> Content`, define:

```text
Matches(S, P) = { x in S | P(↑x) }
```

Then the common unary generalized quantifiers reduce to set relations:

```text
ro S P       = Matches(S, P) = S
su'o S P     = Matches(S, P) != empty
no S P       = Matches(S, P) = empty
re S P       = Card(Matches(S, P)) = 2
su'o ci S P  = Card(Matches(S, P)) >= 3
```

For example, “exactly two of the dogs are white” is:

```lisp
(=
  (Card
    (Filter $dogs
      (λ (($x Individual<Entity>))
        (blabi $x))))
  2)
```

This is a genuine simplification: exact quantification is cardinality
predication on a derived set, and universal/existential quantification is an
equality/nonemptiness test on that set.

It does not justify deleting every binder or higher-order quantifier:

- unrestricted quantification still needs a domain or a classical binder;
- dependencies between several quantified places still require nested or
  polyadic higher-order structure;
- a termset may intentionally leave relative scope unordered;
- modal and intensional operators still determine accessibility and scope;
- collective predication on a bare plural argument is not the same operation as
  distributively filtering its members.

The likely result is that most surface count quantifiers lower to `Filter`,
`Card`, equality, and set inclusion, while `∀`, `∃`, and `PolyQuant` remain in
the small logical vocabulary for irreducible cases.

## 7. Relative clauses become particularly direct

With `Refs<K>` as the ordinary description value, restrictive relative clauses
are set filtering rather than a new relative-clause object:

```lisp
; lo gerku poi blabi
(Filter (Lo gerku)
  (λ (($x Individual<Entity>))
    (blabi $x)))
```

The result is still a reference computation, not a pure extensional set; the
filter must sequence the base reference effects and preserve fixed identity.
`noi` remains a supplement anchored to each relevant individual or to the
plural referent as licensed by the source. `voi` remains a `DescribedAs`
predication. Sets simplify the restrictive subset operation but do not collapse
the distinct commitments of `poi`, `voi`, and `noi`.

## 8. Consequences for the existing draft

If adopted, this design requires more than changing a type name:

1. Replace `Ref<K>`/`Plural<K>` with `Individual<K>`/`Refs<K>` and state that
   ordinary predicate places consume `Refs<K>`.
2. Change `Lo`, `Le`, and `La` to return `Refs<K>` computations.
3. Rewrite relative-clause examples as effect-preserving set filters.
4. Separate plural denotations from the object-level `Set` and `Mass`/group
   constructors already listed in the intrinsic registry.
5. Recast inner counts as constraints on a selected reference set and outer
   counts as cardinalities of member filters.
6. Correct reference binding so fixed xorlo constants bind across extensional
   connectives and stop only at the relevant intensional handler.
7. Audit all lexical place types and higher-order properties for the singleton
   injection, rather than inserting ad hoc plural coercions in individual
   examples.

## 9. Questions for review

1. Is interpreting every lexical relation directly over `Refs<K>` adequate for
   Lojban's deliberately unspecified distributive/collective readings, or is a
   cover/cumulative relation operator semantically indispensable?
2. Should the visible type be `Refs<K>`, `Referents<K>`, `Set⁺<K>`, or another
   established term? `Refs` is concise; `Set⁺` makes the mathematics clearest.
3. Can inner-cardinality constraints be expressed entirely by existing dynamic
   bind plus ordinary predication, avoiding `WhereRef`?
4. Should `lo'i` and `loi` print as `SetOf`/`GroupOf`, or always elaborate to
   `selcmi`/`gunma` predications?
5. Which quantifier forms truly require `∀`, `∃`, generalized quantifiers, or
   `PolyQuant` after the set reduction?
6. Does filtering a dynamic plural reference preserve the right maximality,
   nonemptiness, projection, and fixed-reference behavior for every `poi` host?

## 10. Provisional recommendation

Adopt sets as the foundation of plural **denotations**, and make plurality
explicit in the type of every ordinary predicate place. Do not identify a
plural denotation with an object-language set or group. Reduce inner counts and
ordinary outer counts to cardinality and filtering wherever the source licenses
that reduction. Retain higher-order binders, dynamic reference effects, and an
explicit distinction between neutral plural predication, distributive member
quantification, set objects, and group objects.

This gives the desired “bridi and lambdas all the way down” shape a more uniform
argument model: a bridi place is filled once, with a number-neutral reference
set. Singularity, plurality, exact cardinality, distributivity, set reification,
and grouping are orthogonal operations around that fill rather than different
kinds of place filling.
