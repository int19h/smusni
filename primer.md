# The Lojban semantic core: a primer

This is a guide to Smusni for readers who know Lojban. No background in
linguistics, logic, or programming is assumed. The examples explain how
Smusni represents meaning; you do not need to learn its formal notation
to follow them.

[The specification](spec.md) gives the precise rules. This primer explains
the main ideas and points out important limits. Smusni does not yet cover
every Lojban construction.

## 0. Why a semantic core?

Consider:

```lojban
lo ci gerku cu batci re prenu
```

We recognize dogs, biting, and people. But to say exactly what this means,
we also need to answer questions such as:

- Does `ci` count the dogs being referred to, or all dogs that bite?
- Does `re` mean exactly two people, or at least two?
- Must each dog bite separately?
- Which people and which occasion are relevant?
- What changes if we insert `na`?

A semantic core is a notation for spelling out such distinctions. It
represents a reading of a sentence using a small collection of building
blocks: referring to things, applying predicates, counting, denying,
asking, and so on. Their meanings and rules for combination are explicit.

A sentence can also introduce something to refer back to or add an aside
that survives denial. Smusni represents these discourse contributions as
part of meaning, alongside the objects and claims being discussed.

The core is not a replacement for spoken Lojban. Nor does it eliminate
context. If you say `mi klama`, knowing the grammar does not tell the
listener where you are going. The representation must leave room for the
intended destination without confusing it with a claim that any destination
will do.

Sometimes the same Lojban text permits different readings. Smusni represents
a resolved reading: one in which the relevant interpretation has been
selected. That does not mean every fact is known. A question can remain
unanswered, a description can fail to find anything, and a claim can be false.

We will build up to this example:

```lojban
lo ci gerku noi blabi ku'o goi ko'a cu na batci re prenu .i .uinai cai ko'a tatpi
```

“The three dogs, which are white, did not bite exactly two people.
Ugh—they are tired.”

The main denial concerns the exact count of bitten people. The whiteness
is a separate aside, `ko'a` keeps the dog reference available, and
`.uinai cai` expresses strong unhappiness about the second claim.
The chapters below explain these contributions separately.

## 1. Saying things: predication

Start with:

```lojban
mi klama
```

On an ordinary going-on-a-particular-occasion reading, this says that the
speaker goes. The word `klama` supplies a relation between a goer,
destination, origin, route, and means. `mi` fills the goer place.

The corresponding Smusni expression is:

```lisp
; mi klama — on a reading about actual going
(Assert                    ; make the declarative assertion
  (Close                   ; fill omissions and close the going clause
    (klama Speaker)))      ; klama with mi in its first place
```

Inside parentheses, the first item names an operation or predicate and
the remaining items are its arguments. Read this example from the inside
out: apply `klama` to `Speaker`, complete the clause with `Close`, then
make an assertion with `Assert`. `Speaker` is the reference supplied by
`mi`. A semicolon begins a comment, which explains the term but is not
part of its meaning.

`Close` fills omitted places and retains the going as the clause's event.
Here it also selects actual occurrence. This is shorthand for the reading
shown, not a rule that every tenseless bridi asserts actual occurrence.
`Assert` makes an assertion package; a standalone act snippet abbreviates
performing that act. Chapter 6 explains why that distinction matters.

A predicate is a relation used to say something about its arguments.
Applying `klama` to the speaker is predication. Lojban's familiar place
structures make this part of the model relatively direct.

The four unspoken places have not disappeared. They receive values from
context. Suppose we have been discussing a trip to the shop. `mi klama`
can concern that destination without naming it again.

We can make the destination retrieval visible:

```lisp
; mi klama — the understood destination shown explicitly
(Assert
  {Bind [$destination :: Referents Entity]
        (Context)                         ; omitted destination, like zo'e
    (Close (klama Speaker $destination))}) ; mi klama [that destination]
```

`Context` supplies the contextual retrieval step. `Bind` combines that step
with its body, the final `Close` expression, using the returned value as
`$destination`. The retrieval itself introduces no descriptive reference.
Chapter 4 explains [how a result and discourse effects are carried forward](#let-and-bind-naming-and-sequencing).
The dollar sign marks a variable. `:: Referents Entity` says what kind
of value it holds: a reference to one or more entities. Square brackets
group that declaration; braces show the binding and its scope. They do
not quote text. Origin, route, and means are still filled by `Close`.

There are three different ways to leave something unspecified:

- Omission or `zo'e`: use the value intended in this context. The listener
  need not recover every detail, but must recover enough for the conversation.
- `zi'o`: remove a place from the relation. `mi klama ti zi'o` uses
  a relation with no origin place, not a relation whose origin is unknown.
- `da`: use a variable under a quantifier. With its ordinary implicit
  `su'o`, this claims that at least one value satisfies the predication.

These distinctions matter under negation. If the intended destination is
the shop, `mi na klama` denies that going. It need not deny going anywhere
at all. Negating the claim does not replace the intended destination with
a search for other destinations.

Referring to the speaker, the current time, or an indicated object is
called deixis. The reference depends on the particular utterance.
Two uses of `ti` can indicate the same thing or different things:
each use must be associated with its own indication.

Finally, distinguish a claim from an assertion of that claim. We can ask
whether someone goes, command them to go, or discuss their going without
asserting that they go. Chapter 6 explains this distinction.

## 2. Events: when and how

```lojban
mi pu klama
```

On the ordinary episodic reading, there is a going by the speaker, and that
going is earlier than the utterance. Smusni keeps the going event as part
of the meaning so that tense, location, manner, and other descriptions can
concern the same event.

Once that going event is available as `$going`, the tense contribution is:

```lisp
; pu in mi pu klama — fragment, with $going already bound to the event
(purci $going Now)          ; pu: that going is earlier than this utterance
```

`purci` is the earlier-than relation. `$going` denotes the event described
by the clause, and `Now` supplies the utterance time. This fragment adds
the time relation; it does not by itself assert that anyone goes.

`pu` relates it to an earlier time, `ba` to a later time, and `ca` to
a simultaneous time. Spatial tenses locate it. A tag such as `sepi'o`
adds an instrument relation. In a sequence such as `pu pu`, one temporal
reference point can be earlier than another, rather than both being
independently measured from now.

“Event” here includes states, not just actions. Compare:

```lojban
mi pu klama
ta pu du lo mi zdani
```

The first concerns a going. The second can concern a state in which that
building was my home. It need not still be my home now. The description
can be understood relative to that earlier state. A reading which fixes
the home reference independently of the earlier state is different.

The technical umbrella term is eventuality: an action, happening, or state
that a clause describes. An identity claim, a negative claim, or a general
claim can have a state of affairs without becoming a physical action.
A mathematical identity does not have to occur for a brief interval.

A tenseless bridi does not automatically mean “now.” It can concern a
particular occasion, a habit, or something timeless. On a particular-occasion
reading, the relevant time can be understood from context just as the
destination can. “I didn't turn off the stove,” for example, normally
concerns a particular occasion, not every occasion in my life. This
comparison comes from Partee's discussion of English tense; the source
and its application to Lojban are given in [the specification's
References](spec.md#references).

Likewise, leaving out CAhA does not always mean `ca'a`:

- `ca'a` requires actual occurrence.
- `ka'e` concerns innate capability.
- `nu'o` and `pu'i` relate capability to whether it is realized.

Thus `ro datka cu flulimna` can describe what ducks are capable of,
without saying that every duck is swimming now. The reading of the
unmarked sentence determines which of these claims is intended.

The specification uses the clause's eventuality to connect these meanings
with `nu` abstractions. Some tense and aspect combinations still need
a complete analysis; the existence of this common idea does not supply
every such rule.

## 3. Things: reference

```lojban
lo ci gerku
```

This refers to three dogs. It does not say that there are only three dogs
in the world, or even only three dogs in the conversation. The inner
number counts the dog units in this particular reference.

Without a number, `lo gerku` can refer to one dog or several. It requires
dogs, but not a unique dog or all relevant dogs. Once a reference has been
introduced, reusing it means referring to those same things, not choosing
a fresh set of suitable dogs.

The reference-producing part of `lo gerku` is:

```lisp
; lo gerku — reference expression, not a complete assertion
(Refer                          ; lo: introduce a reference
  {λ [$r :: Referents Entity]
    (gerku $r)})                ; gerku: the description it must satisfy
```

`λ`, read “lambda,” makes an expression with a parameter. Here `$r` is
a possible reference and `(gerku $r)` tests the dog description of it.
`Refer` uses that condition to introduce a nonempty reference satisfying
the description. It need not include all dogs. `gerku` also has a breed place.
Its value can be understood from context, just as the destination can in
`mi klama`; leaving it unwritten here does not delete it.

A plural reference can contain one or more things referred to together. It does not
automatically create a new object called their group or set:

| Expression | What it refers to |
|---|---|
| `lo re prenu` | Two people together |
| `loi re prenu` | A group constituted by two people |
| `lo'i re prenu` | A set whose members are two people |

This matters when we apply predicates. A group might weigh 150 kg
without either member weighing 150 kg. We cannot freely replace the group
with its members, or the members with the group.

### Together and separately

```lojban
lo ci nanmu cu bevri lo pipno
```

This predicates carrying of the three men. It does not silently expand
into three claims that each man carries the piano alone. Nor does it add
a hidden choice between a “together” meaning and a “separately” meaning.
Which arrangements count as carrying depends on the predicate.

When we explicitly distribute a predication, we apply it to the members
separately. `lu'a` provides this memberwise treatment. Ordinary plural
predication does not insert it automatically.

Compare:

- `mi jo'u do bevri lo pipno`: carrying is predicated of you and me
  as an ordinary plurality.
- `mi joi do bevri lo pipno`: carrying is predicated of a group
  constituted by you and me.
- `mi .e do bevri lo pipno`: the connective joins separate predications
  about me and about you.

Smusni treats `mi'o` as the ordinary plural reference `mi jo'u do`.
For example, `mi'o remna` concerns the speaker and listener, without
requiring an additional group object to be human.

### Other descriptions

`le gerku` refers through the speaker's description as dogs, even if
that description is inaccurate. It does not simply mean “some things
which happen to be dogs.” `la` instead refers through a name.
Neither guarantees that a later independent use will pick the same
referents; an anaphor such as `ri` has the specific job of retaining
the earlier reference.

`loi gerku` and `lo'i gerku` construct their group or set from a
selected dog reference. That base need not include every dog.
The base is not also introduced as a second, separately available sumti.
If `ri` refers back to the set, it refers to the set; `lu'a ri`
explicitly turns attention to its members.

`lo'e` and `le'e` express generalizations, not reference to one
representative specimen. In talk about lions, a claim about manes can
concern a different normal case from a claim about giving birth.
One supposedly typical individual need not exemplify both.
`le'e` makes the speaker's stereotype relevant. Neither construction
is simply “all” or “at least one.”

### What counts as a unit?

Three dogs, three teams, and three portions of water use different units.
Smusni therefore distinguishes referring to things from counting them.
It does not require every possible reference to decompose into universal,
indivisible atoms.

The relation between a whole and its components also needs a basis.
A team has members; an event has phases; a mixture has contributions.
`joi` uses a complete component base at the intended level, whereas
ordinary `gunma` can mention only some components. A blue/red mixture
need not consist of two separate objects, one wholly blue and one wholly
red. The analysis must specify how the contributions combine; the word
“mixture” alone does not determine it.

## 4. What later sentences can see

In the running example, `goi ko'a` assigns the dog reference to
`ko'a`. The second sentence then predicates tiredness of those same
dogs. It does not choose whichever dogs happen to be tired.

Anaphora is reference back to something already introduced. The central
question is not just how far back an expression occurs, but whether its
reference is available at the later position. This is called accessibility.

Some common patterns are:

| Construction | What can be reused? |
|---|---|
| A and B | B can use references introduced by A; eligible references can remain available afterwards. |
| A implies B | B can use references introduced by A, but those local references do not escape the whole conditional. |
| A or B; either A or B but not both (exclusive-or) | References introduced only inside either alternative do not escape it. |
| Not A | References introduced inside A do not escape the negation. |
| One assertion, then another | Eligible references can continue into the next assertion. |

Conjunction joins contents into one claim. A sentence sequence performs
successive assertions, which can have different truth values. They are
different operations even though both can pass references from left to right.

All these rules respect enclosing scopes. A connective inside a quantifier
does not make the quantifier's local references available everywhere.
Equally, using an already available reference inside a negative claim does
not erase that reference.

For a simple positive sequence:

```lojban
lo gerku cu sipna .i ri cu xunre
```

The second sentence concerns the same dog or dogs as the first. The two
claims must fit one shared reference; one sleeping dog and a different red
dog do not suffice.

To see what sharing a reference means, suppose `$dogs` is the reference
already assigned by `goi ko'a` in the running example. Its later use is:

```lisp
; ko'a tatpi — content fragment, with $dogs already bound
(Close (tatpi $dogs))           ; tatpi applied to ko'a's existing reference
```

There is no new `Refer` here. `$dogs` uses the value supplied by its
surrounding binding. `Close` completes the tiredness clause, but does
not choose another dog reference. The full term must put this expression
within the binding's scope.

### Let and Bind: naming and sequencing

Both forms give a value a name within a body. `Let` names a supplied
value. When a `Bind` term is evaluated, its source computation runs and
supplies the returned value to the body. The additional operation is
sequencing, not a different kind of naming.

`Let` is immediate lambda application. For example:

```lisp
; pure arithmetic: name 2 and use that value twice
{Let [$n :: Number] 2
  (+ $n $n)}
```

This means the same as applying `{λ [$n :: Number] (+ $n $n)}` to
`2`, and returns `4`. A lambda is a function with a named parameter;
applying it substitutes the supplied value into its body.

#### What sequencing carries

The model's discourse state records possible reference assignments and
their scopes, alongside possibilities about the world. Effects change what
later parts of the discourse can use or contribute additional commitments:

- `Refer` obtains a reference and introduces it for possible later anaphora.
- `Context` retrieves an understood value without introducing a new
  descriptive antecedent.
- A condition such as sleeping filters the possibilities that satisfy it.
- A `noi` aside contributes a side commitment, handled at its proper scope.

`Bind` passes the returned value to its body **in the resulting state**,
retaining the associated side commitments. It does not extract the value and
restore the old state. If reference selection has several admissible results,
each stays paired with its own state and commitments.

The body describes how to continue with that result. If the source returns
no value, ordinary `Bind` cannot enter its body. This is distinct from
continuing after a false assertion, which chapter 6 explains.

This is monadic sequencing: pass the ordinary result onward while carrying
the accompanying effects. The state is explicit in the model's definition
but is not an ordinary argument in a Smusni term. This semantic state is not
a computer's memory or everything a listener believes.

Naming a returned value does not itself introduce an anaphoric source.
The source operation and scope rules determine that. For example, `Local`
can keep the dogs needed to construct `lo'i gerku` available inside the
term while hiding their temporary introduction from later anaphora; the
set is the surface antecedent.

#### One computation, one or two runs

The next fragments start with supplied inputs. `$source` is an ordinary
dog-reference computation, independent of earlier results. `$sleep` and
`$red` test whether every dog in their argument is asleep or red, without
introducing references or side claims. These are illustrative Content
fragments, not complete translations of Lojban utterances.

```lisp
; select dogs once; those same dogs must sleep and be red
{Let [$select :: RefComp (Referents Entity)] $source ; name the computation
  {Bind [$dogs :: Referents Entity] $select          ; run it once
    (∧ ($sleep $dogs)                               ; these dogs sleep
       ($red $dogs))}}                             ; these dogs are red
```

`RefComp (Referents Entity)` is the type of a computation returning an
entity reference. Naming that computation does not run it. When the whole
Content is evaluated, `Bind` runs it and supplies the returned reference
as `$dogs`. The conjunction `∧` tests both claims about that reference.

```lisp
; run the same source twice; the two references may differ
{Let [$select :: RefComp (Referents Entity)] $source
  {Bind [$dogs1 :: Referents Entity] $select         ; first introduction
        [$dogs2 :: Referents Entity] $select         ; second, in the resulting state
    (∧ ($sleep $dogs1)                              ; the first dogs sleep
       ($red $dogs2))}}                            ; the second dogs are red
```

Suppose dog A sleeps but is not red, and dog B is red but does not sleep.
The available references are A, B, and both together. No one reference
passes both memberwise tests, so the first fragment cannot succeed.
The second can introduce A and then B. Two runs may also return the same
dogs; sharing a computation does not mean sharing one run's result.
Shared `Context` and `Vague` sites retain their identities. The two runs
here make separate reference introductions, not new copies of those sites.

The type of `$dogs` is the returned reference type. The body and the whole
`Bind` in the first fragment have type `Content`; the enclosing `Let`
does too. A successful Content run returns the single trivial value of type
`Unit`, together with state and commitments. That value is not a truth
value. Content also retains its clause-event meaning.

With a performance body, `Bind` instead remains at the performance level.
In chapter 11, binding the handle `$o2` and then performing the attached
display forms a `Discourse`: running it performs the assertion and display.
A performance cannot be hidden inside Content by discarding its return value.

### Dependent references

Now consider a reference that depends on another:

```lojban
ro prenu poi ponse su'o xasli cu ctigau ri
```

Here `ctigau` means feeding, with the food left understood; its dictionary
place structure is cited in [the specification's References](spec.md#references).
On the supported reading, each person feeds every donkey that person owns.
For every qualifying person–donkey pair, the feeding claim holds.
The donkey reference is used within the sentence where its owner is
being considered. This kind of construction is often called donkey
anaphora.

It does not follow that a later sentence can recover a new combined
collection of all those dependent donkeys. The universal's scope has
ended. Likewise, “every person has three dogs; they are tired” is not
automatically given a reading where “they” retrieves each person's dogs
from inside the earlier quantification.

Accessibility is determined from the structure, not by first discovering
whether the speaker is right. A reference can be in scope yet fail to have
a value in a particular situation. That differs from a reference that is
out of scope in the first place. Finding a suitable object somewhere in
the world does not repair an out-of-scope reference.

The specification calls the study of these changes through a conversation
dynamic semantics. Its rules cover the distinctions above, but not every
possible anaphoric construction. Questions, quotations, and combinations
of several failed descriptions still have unfinished parts.

## 5. How many

The position of a number matters:

```lojban
ci gerku cu sipna
lo ci gerku cu sipna
```

The first counts dogs that sleep: exactly three relevant dogs sleep.
The second refers to three dogs and predicates sleeping of that reference.
It does not exclude other sleeping dogs.

In the first sentence, `ci` is an outer quantifier. It counts individuals
satisfying the whole condition. In the second, it is an inner number in
the description. It counts units within the reference.

Suppose four equally relevant dogs are asleep:

| Claim | Result |
|---|---|
| `ci gerku cu sipna` | False: four is not exactly three. |
| `su'o ci gerku cu sipna` | True: at least three sleep. |
| `su'o re gerku cu sipna` | True: at least two sleep. |
| `lo ci gerku cu sipna` | Can be true of a reference to three of them. |

“Relevant” is fixed by the conversation and the reading, not narrowed
afterwards to make a count come out right. We are not counting every dog
in the universe, but we cannot discard a fourth qualifying dog merely to
make `ci` true.

For a finite set of relevant sleeping dogs, the exact-count test is:

```lisp
; counting part of ci gerku cu sipna
; fragment: $sleepingDogs is the already formed set of qualifying individuals
(= (Card $sleepingDogs) 3)      ; ci: that set has exactly three members
```

`Card` counts the members of a mathematical set, and `=` tests equality
with the number `3`. `$sleepingDogs` contains all dogs meeting the resolved
sleeping condition, not a chosen triple. Forming that set supplies the
`gerku` and `sipna` conditions; the fragment above shows only the count.
Using a set for counting does not make the Lojban sumti refer to that set.

### Bounds and zero

For ordinary finite individual counts:

- `su'o re`: at least two.
- `su'e re`: at most two.
- `za'u re`: more than two.
- `me'i re`: fewer than two.
- `no`: zero.

Saying that zero dogs sleep counts dogs satisfying that condition;
it does not introduce a dog reference.

Bare `me'i`, without a following bound, means “not all”:

```lojban
me'i gerku cu sipna
```

At least one relevant dog does not sleep. This permits none of the dogs
to sleep; it does not mean “some but not all.” If there are no relevant
dogs, it is false. Explicit `me'i pa gerku cu sipna` instead says that
zero relevant dogs sleep, which is true when there are none.

Ordinary `su'o gerku` says that at least one individual dog satisfies
the predicate. It does not mean exactly one, and it is not a plural
reference with a chosen size.

### Every, and descriptions of all

```lojban
ro gerku cu sipna
ro lo gerku cu sipna
```

The first says that every relevant dog sleeps. If there are no relevant
dogs, there is no counterexample, and the universal is true. The technical
term is a non-importing universal: it does not itself claim existence.

The second first has a dog reference supplied by `lo gerku`, then
predicates sleeping of each of its members. That description must have
referents. Thus the two sentences differ when there are no dogs.

`lo ro gerku` is different again: it refers to all relevant dogs and
can supply a plural argument. Referring to all of them is not the same
operation as making a separate predication about every individual.

### Keeping a reference for later

An outer count does not create a new group for later `ri`. If
`su'o re gerku cu sipna` is followed by a `ri` intended to mean
“the group of at least two dogs introduced by that count,” the reference
is not available under these scope rules.

A description can supply the reference directly:

```lojban
lo su'o re gerku cu sipna .i ro ri cu xunre
```

On the ordinary reading where sleeping applies to the dogs individually,
we have one reference containing at least two dog units. The later
sentence says that every member of that same reference is red.
It cannot switch to a different selection of red dogs.

This is useful when a continuing plural reference is wanted. It does not
make descriptions and outer quantifiers interchangeable in every
construction. Negation, dependencies, and collective predicates can
distinguish them.

An ordinary positive existential can also support continuity; the scope
rule is not simply a ban on quantifiers or on references involving more
than one object.

### Reference requirements under negation

```lojban
lo mlatu na jbena
```

The description still requires cats. The main denial does not move the
description inside negation and turn a failure to find cats into success.
More generally, denying something about a reference does not reselect
the reference.

Some requirements and side claims survive a main-clause denial. This is
called projection. A presupposition is a requirement treated as background;
a supplement is a separate side commitment, such as a `noi` clause.
They are not the same as the content that `na` denies. The full example
in chapter 11 shows the supplement case.

The numerical rules above cover ordinary individual counts. Other numerical
domains and some combinations of quantifiers still need analysis.
Approximate quantities are discussed in chapter 9.

## 6. Doing things with words

Compare:

```lojban
do klama
xu do klama
ko klama
```

The first asserts going, the second asks about it, and the third directs
the listener to go. The going content and what the speaker does with
it are distinct. Assertion, question, and command are kinds of speech act;
the difference between them is called force.

The question and command use different core forms:

```lisp
; xu do klama — about actual going
(Ask                           ; ask, rather than assert
  (Polar                       ; xu: a yes/no question
    (Close (klama Audience)))) ; do klama: the content being asked about

; ko klama
(Command Audience              ; ko: direct the listener
  (Close (klama Audience)))     ; the going content being commanded
```

`Audience` is the listener reference supplied by `do` and addressed by
`ko`. `Polar` forms a yes/no question from content, and `Ask` makes the
question act. `Command` takes both its addressee and its content.
Putting actual-going content inside the command does not assert that
the listener has complied. As with `Assert`, these forms construct acts;
they are performed when used as standalone discourse acts.

Describing or quoting an act does not perform it:

```lojban
mi cusku lu ko klama li'u
```

Reporting the command does not itself issue that command. Similarly,
embedding a going description in a desire claim does not assert that
the going occurs.

### Occasions of speaking

The same words can be uttered more than once. Each utterance has its own
speaker, time, indicated objects, and understood omissions.

Suppose Alice says `mi klama`. A later `go'i` normally keeps the
resolved claim about Alice, not a freshly interpreted `mi` referring
to the new speaker. `ra'o` requests reinterpretation of the earlier
pronoun-like expressions it targets, such as `mi`, in the new context.
It does not reset every unrelated omitted
place or tanru link.

Smusni therefore distinguishes reusable content from a particular occasion
of saying it. An expression of feeling can concern that occasion, while
an embedded proposition can be discussed without being asserted again.

### Continuing after a false claim

Return to:

```lojban
lo gerku cu sipna .i ri cu xunre
```

If the dog reference succeeds but the dogs are awake, the first claim is
false. The reference has not changed into “whichever dogs sleep.”
The later sentence still concerns the original dogs.

If there are no dogs, the later `ri` still points to the same accessible
source, but that source has no dog value to supply. In this bounded
construction, the first assertion is false and the later use is undefined,
not out of scope. Smusni does not invent a dog or pretend the second utterance
was never made.

An independent continuation, such as “I am leaving,” can still be true
after a false first assertion. That does not make both assertions jointly
true. The detailed construction presently covers a limited description-
and-assertion pattern, not every combination of failed descriptions and
speech acts.

### Asking and answering

`ma klama` asks for a value that fills a place. `ma klama ma` asks
for a pair of values. `mo` asks for a relation, and `fi'a` asks
which compatible place is intended. These questions differ in what
counts as an answer, not in whether a reply has already been supplied.

Where a later anaphor can refer to a `ma` source, that source may remain
open until an answer is given. The later predication concerns the same
eventual answer; the model does not guess a value merely to fill the gap.
The complete rules for these question-to-continuation constructions
remain unfinished.

`kau` concerns an answer within another claim:

```lojban
mi djuno lo du'u ma kau klama
```

This concerns knowing who goes, not directly asking the listener who goes.
Bare `kau` does not itself say that the answer lists everyone.
An embedding word can require a stronger answer, but that requirement
must come from its meaning or from a separate claim, not from an invisible
“all answers” marker.

## 7. Feelings and evidence

```lojban
.ui do klama
.au mi sipna
```

The first asserts that you go and displays happiness about it.
The second expresses a desire to sleep; it does not assert that the speaker
sleeps. Not every indicator leaves its surrounding words as an assertion.

An indicator has a target: what the feeling, evidence, or comment concerns.
Position and attachment matter. In the running example:

```lojban
.i .uinai cai ko'a tatpi
```

The strong unhappiness concerns the claim that the dogs are tired.
Placing the indicator after `ko'a` instead would make the dogs its target.
Repeating the assertion later does not automatically repeat the earlier
display of unhappiness.

With `$occasion` already naming that second assertion's particular
performance, the accompanying display is packaged as:

```lisp
; .uinai cai attached to the ko'a tatpi assertion
; fragment: $occasion is the already performed assertion's occurrence
(Express                              ; display the attitude
  (Close (Unhappiness                  ; .uinai
           Speaker                    ; understood experiencer: the speaker
           $occasion                  ; sentence-initial attachment target
           Intense)))                 ; cai
```

`Express` constructs a display act, distinct from an assertion.
`Unhappiness` is the core's current relation name for the displayed
emotion, with experiencer, target, and intensity places. It is not an
automatic substitution of the gismu `badri`. `Intense` supplies the
intensity here. The enclosing discourse performs this display alongside
the assertion; this fragment does not repeat the assertion itself.

Here `nai` selects the paired emotion, unhappiness, and `cai`
intensifies it. This is not ordinary logical negation: “not happy” and
“unhappy” need not make the same claim.

An evidential gives a basis for a claim. In `za'a do cadzu`, observation
is presented as the basis for saying that you walk. Negating the walking
claim does not simply negate the evidence attribution. Evidentials can
also concern embedded content, as in
`mi jinvi lo du'u ti'e do klama`.

### Comments on the conversation

Discursives describe relations between contributions or their relevant
parts: `ku'i` marks a contrast, `ji'a` an addition, and `mi'u`
a sameness. The representation can express this relation without first
deciding whether the speaker is right about it.

“Also, I went to the shop” need not introduce a fact nobody has mentioned.
Repeating a true statement can be redundant without becoming false
merely because of `ji'a`. What counts as the same, parallel, or contrasting
contribution depends on the relevant comparison. The detailed definitions
of these comparisons are not all complete.

“Only us,” with `po'o` attached to `mi'o`, is different: it says both
that we satisfy the claim and that
relevant outsiders do not. Members of our own plurality are not outsiders
merely because they are less than the whole plurality. A group that also
contains an outsider can still be a competitor.

### Three kinds of rejection

- `na` denies the content within its scope.
- `na'e` puts something in the contrasting region of an intended domain.
  It says more than simple denial without naming one particular finer
  alternative.
- `na'i` objects to an utterance in some respect: for example, to its
  framing or applicability. It is not another truth-functional “not.”

The model keeps these contributions distinct. It does not translate
every negative-looking word into the same operation.

## 8. Ideas about ideas

Lojban lets us talk about a going, a claim about going, or the property
of going. These are different kinds of meaning:

```lojban
lo nu do klama
lo du'u do klama
lo ka ce'u klama
```

- `nu` concerns the event or state described by the clause.
- `du'u`, without extracted `ce'u` places, concerns a proposition:
  the clause's content represented as something we can refer to.
- `ka` concerns a property, with `ce'u` marking a place to be filled.
  Here it is the property of going.

A property can be understood as an expression with a blank. Fill the blank
with Alice and you get the claim that Alice goes; fill it with Bob and
you get the corresponding claim about Bob. The formal term is a function.
In an unmarked `ka`, Smusni uses the first unfilled place for the implicit
`ce'u`. Explicit `ce'u` extraction in `du'u` likewise produces
a function rather than a closed proposition.

The property example makes that open place visible:

```lisp
; ka ce'u klama — the property part of lo ka ce'u klama
{λ [$x :: Referents Entity]        ; ce'u: a place still to be supplied
  (Close (klama $x))}              ; klama with that value in its first place
```

As in the `Refer` example, `λ` supplies a parameter. Here filling `$x`
gives a going clause through `Close`. Merely forming the function does
not assert any of those clauses.

For a proposition, the core instead represents already formed content
as something that can be referred to:

```lisp
; du'u do klama — proposition-forming fragment
; $goingContent is the already formed Content for do klama
(Reify $goingContent)              ; represent that content as a Proposition
```

`Reify` does not assert or evaluate its argument. The surrounding `lo`
description also introduces a reference to the proposition; the snippet
shows the proposition-forming step, not that outer reference operation.

The technical term “type” tells us which kind of value an expression supplies
and which kind a place accepts. An event, a proposition, and a property
are not automatically interchangeable just because English can call each
of them “an idea.” Each lexical reading needs a compatible place structure.

Other abstractors add their own relations:

| Abstractor | What it concerns |
|---|---|
| `ni` | An amount on a scale |
| `jei` | A truth value under a standard of knowing, or epistemology |
| `li'i` | An experience, with an experiencer |
| `si'o` | A concept in a mind |
| `su'u` | An abstraction with a category |
| `pu'u` | A process with stages |
| `zu'o` | An activity with repeated actions |
| `mu'e`, `za'i` | An achievement or state, refining the event kind used by `nu` |

These still behave as Lojban relations. `lo ni …` and `le ni …`
differ in the ordinary way that `lo` and `le` do.
An omitted scale or experiencer can be understood from context.
`jei` does not automatically produce a number between zero and one.

### Leaving an abstraction unspoken

`tu'a X` leaves an intended X-related abstraction for the listener to
recover. The receiving predicate helps determine what kind is needed,
and context supplies the intended connection. It does not normally mean
that any arbitrary abstraction involving X will do.

An important distinction is whether a description picks something independently
or is understood within a desire, belief, or other attitude. Wanting to use
a car need not mean there is a particular actual car one wants to use.
The formal terms are de re for the independently fixed reference and
de dicto for the description understood within the attitude. Some such
attitude constructions still lack a complete mapping in Smusni;
the distinction alone is not a complete analysis of every example.

## 9. Intended values and vague boundaries

Not knowing the answer is different from there being no exact answer.

If `mi klama` concerns a trip to the shop, the intended destination can
be definite even when the listener fails to identify it. Clarification
can repair the misunderstanding.

With “many dogs,” there need not be one precise number secretly intended
as the dividing line between many and not many. This is vagueness:
clear cases can coexist with borderline cases.

Smusni distinguishes three situations:

| Situation | Example | Treatment |
|---|---|---|
| A value is intended but left unspoken | A destination, a tanru link, or the abstraction in `tu'a` | Recover it from context closely enough for the conversation. |
| A boundary is genuinely vague | How many counts as `so'i`, or how close counts as `ji'i` | Consider admissible precise versions of that same meaning. |
| No such additional claim is made | Bare `kau` does not say “all answers” | Do not insert a hidden choice or assertion. |

The precise versions of a vague meaning are called sharpenings.
For an unqualified claim to count as true, it must hold across the
admissible sharpenings; one favorable sharpening is not enough.
These are not unrelated alternative meanings. Uncertainty about which
destination the speaker meant is not turned into a vague family of
destinations.

### Tanru

```lojban
sutra klama
```

The head `klama` supplies the place structure. `sutra` modifies the
going in the way intended on this occasion. Being fast at going is a
natural conventional interpretation, but the words alone do not determine
every detail of their relation.

Smusni represents one intended link, constrained to modify the head
predication. It does not make the sentence mean that any imaginable link
is acceptable. The official `tanru` definition distinguishes meaning
from a particular usage or instance; see the source discussion in
[spec §6.2](spec.md#62-tanru). Conventional uses guide interpretation,
while a lujvo has its own lexical meaning.

```lisp
; sutra klama — a selbri expression, not an assertion
(Tanru sutra klama)             ; sutra modifies the head klama
```

`Tanru` combines the modifier and head using the occurrence's intended
link. The result is a predicate with `klama`'s places. No argument has
been filled and no assertion has been made merely by constructing it.

An intended value may depend on another part of the sentence. In talk
about each person's home, the home can vary with the person. “Understood
from context” does not mean “one constant for the entire conversation.”

### Approximation and neutral regions

`no'e` concerns a neutral region in an intended comparison.
That region need not have a fuzzy boundary: a stipulated numerical scale
can have an exact middle. Nor must the region always be a single point
or the arithmetic midpoint. The comparison determines the required
structure; genuine borderline cases receive the vagueness treatment.

For approximate quantities, the intended approach distinguishes the exact
value being discussed from the tolerance used to describe it.
Reusing one approximate quantity must preserve that same underlying value.
Two independent approximations need not have the same error, even if
they use the same tolerance.

An expression involving approximate values may remain unsimplified.
The model need not invent a conventional numerical answer where none is
established. The full rules for approximate arithmetic and equality still
need completion.

## 10. Words about words

Compare talking about going with talking about the word `klama`.
The latter is use of a sign: a word, quotation, name, or other expression.

- `zo klama` quotes one word.
- `lu mi klama li'u` represents a Lojban utterance.
- `lo'u … le'u` quotes text without requiring grammatical analysis.
- `me'o` refers to a mathematical expression; `li` uses a value.

```lisp
; zo klama — a word-sign expression
(WordSign "klama")              ; zo quotes the following word
```

`WordSign` constructs a sign for a word. The double quotes enclose literal
text. This expression denotes the word, not a going and not a claim that
someone goes.

Quoting something does not assert or perform it. A quotation can contain
a command without commanding the listener, or a false claim without
committing the quoting speaker to that claim.

`la'e` crosses from a sign to what it represents. `lu'e` goes in the
other direction, to a sign for something. These crossings must respect
what kind of thing is represented. Quoted words are not automatically
a proposition merely because they occur inside a sumti.

This is separate from anaphora into quoted material. Lojban permits an
outer anaphor to reach into a linguistic quotation; that does not make
the narrator assert everything in the quotation. A reference inside
the quote cannot instead reach out into the
narrator's surrounding discourse. Smusni still needs the complete formal
rule for this crossing.

## 11. The whole example

```lojban
lo ci gerku noi blabi ku'o goi ko'a cu na batci re prenu .i .uinai cai ko'a tatpi
```

Take a reading about particular occasions, with the omitted biting
details understood consistently across the people being counted.

1. `lo ci gerku` supplies a reference containing three dog units.
   It does not claim that only three dogs exist.
2. `noi blabi` contributes the separate claim that these dogs are white.
   The following `na` does not deny their whiteness.
3. `goi ko'a` assigns the dog reference to `ko'a`.
4. `batci re prenu` makes an exact count of people satisfying the
   biting condition. The dogs can participate together; the count of
   people does not split them into separate dog predications.
5. `na` denies that exact count. Any number of qualifying bitten people
   other than two makes the denial true. It does not mean that no pair of
   bitten people exists.
6. The second sentence uses `ko'a` for the same dogs and says they
   are tired, on its own relevant occasion.
7. Sentence-initial `.uinai cai` displays strong unhappiness about
   that second assertion.

Here is the complete term for this reading. It shows the path where the
dog reference and contextual values are successfully supplied. It does
not supply the general failed-description continuation discussed in
chapter 6.

```lisp
; lo ci gerku noi blabi ku'o goi ko'a cu na batci re prenu
; .i .uinai cai ko'a tatpi
{Bind [$dogs :: Referents Entity]       ; retain this reference as ko'a
      (Refer {λ [$r :: Referents Entity] ; lo: a described reference
        (∧ (gerku $r)                   ; gerku
           (= (CardBasis $r            ; ci: count dog units in $r
                {λ [$x :: Entity] (gerku $x)})
              3))})
  (Do                                  ; the two successive utterances
    {Bind [$occ1 :: Time] (Context)     ; first understood occasion
          [$biteLocus :: Referents Entity] (Context) ; omitted batci x3
          [$bitingTool :: Referents Entity] (Context) ; omitted batci x4
      {Let [$a1 :: Act Assertion]
            (Assert                    ; first assertion
              (Supplement $dogs
                (Close (blabi $dogs))   ; noi blabi: a separate side claim
                (¬                     ; na: deny the exact count
                  (GlobalExactly 2     ; re
                    {λ [$x :: Entity] (prenu $x)} ; prenu
                    {λ [$person :: Entity]
                      (CloseClause
                        (ActualClause
                          {λ [$e :: Referents Eventuality]
                            (∧
                              ((DirectClause
                                 (batci $dogs $person ; who bites whom
                                   $biteLocus $bitingTool))
                               $e)
                              (cabna $e $occ1))}))}))))
        (Perform Host $a1)}}           ; make the first assertion
    {Bind [$occ2 :: Time] (Context)     ; second understood occasion
      {Let [$a2 :: Act Assertion]
            (Assert                    ; ko'a tatpi
              (CloseClause
                (ActualClause
                  {λ [$e :: Referents Eventuality]
                    (∧
                      (Close (tatpi $dogs :Eventuality $e))
                      (cabna $e $occ2))})))
        {Bind [$o2 :: ActOccurrence Assertion]
              (Perform Host $a2)       ; perform it and retain this occurrence
          (Do
            (Perform AttachedDisplay  ; attached .uinai cai display
              (Express
                (Close
                  (Unhappiness Speaker $o2 Intense)))))}}})}
```

Read the outer structure first. The initial `Bind` obtains the dogs
once. Its scope contains both utterances, so every later `$dogs` is
the same reference. `Do` sequences the performances; it does not
combine everything into one assertion.

### Describing and counting

`Refer` uses the condition on `$r` to introduce the dogs. The symbol
`∧` means “and”: the reference satisfies the dog description and has
the specified count. `CardBasis` counts units within that reference
using the supplied dog condition. `Entity` is the type of a single
entity; `Referents Entity` is the type of a reference to one or more
entities.

`GlobalExactly` performs the outer count. In this finite example it
forms the set of individuals satisfying both conditions and tests its
size, the same `Card`/equality operation illustrated in chapter 5.
Here the conditions mean “is a relevant person” and “was bitten by these
dogs in the specified way.” They are simple tests: they make no new
discourse references, contextual choices, or side claims.

The symbol `¬` means “not.” It surrounds the exact count, not the
reference to the dogs. `Supplement` takes an anchor, a side claim,
and the main content. Here the anchor is `$dogs`, the side claim
is their whiteness, and only the main biting claim is negated.

### Completing the clauses

Each `Context` supplies an understood value. `$occ1` and
`$occ2` have type `Time`; the two sentences need not concern the
same occasion. The biting locus and tool fill `batci`'s third and
fourth places. Their bindings sit outside the person count, so the tests
for different people use the same values on this reading.

`DirectClause` leaves the lexical event place available to be filled.
Thus `((DirectClause (batci …)) $e)` supplies `$e` as the biting
event. The double parentheses show two applications: first form the
event-dependent clause, then apply it to an event reference.
`cabna` relates that event to the understood occasion.

`ActualClause` requires the event to occur; `CloseClause` closes
the event parameter while retaining its value as the clause's eventuality.
This is the explicit event structure that `Close` usually abbreviates.
In the tiredness clause, `:Eventuality $e` fills the same labelled event
place directly. That clause uses the tiredness eventuality assumed for
this worked lexical reading.

### Asserting and displaying

`Let` gives a name to an already constructed value. Here `$a1` and
`$a2`, each of type `Act Assertion`, name the two assertion packages.
Unlike `Bind`, `Let` does not run a computation to obtain a result;
see [the small comparison in chapter 4](#let-and-bind-naming-and-sequencing).

`Perform Host` performs a main discourse act. The second performance
returns an `ActOccurrence Assertion`, which `Bind` names `$o2`.
That is the particular assertion occurrence targeted by the indicator,
not the reusable assertion package `$a2`.

Finally, `Perform AttachedDisplay` performs the accompanying display.
`Express` packages the emotion content; `Unhappiness` takes the
speaker, the target occurrence, and `Intense` for `cai`, as in
chapter 7. Nothing here performs the tiredness assertion a second time.

The result contains a description, an aside, a denial, a continuing
reference, a second assertion, and a display of feeling. The core gives
each contribution its own place while specifying how they interact.
[Samples §11](samples.md#11-the-spiral-sentence-with-an-explicit-alias)
contains the same worked reading among the other formal examples.

## 12. Glossary and further reading

These terms provide a route from the examples to the specification.
The capitalized names are Smusni notation, not new Lojban vocabulary.

| Term | Meaning here | Where to look |
|---|---|---|
| Predicate | A relation applied to arguments, such as `klama` with its places filled | Spec §4.1 |
| Type | The kind of value an expression supplies or accepts | Spec §3 |
| Plural reference | One or more things referred to together, without a new group object | `Referents`, spec §3.2 |
| Reference introduction | Making a reference available for possible later use | `Refer`, spec §5.3 |
| Binding | Associating a value with a name for use within a scope | `Let` and `Bind`, spec §4.4 and §5.2 |
| Computation | A meaning interpreted with context and discourse state, potentially returning a value and contributing changes | Model interface and `RefComp`, spec §5.1–§5.2 |
| Monadic sequencing | Continuing with a result and its matching state and commitments | `Bind`, spec §5.1–§5.2 |
| Scope | The part of an expression governed by a binder or operator | Spec §4.4–§4.5 |
| Accessibility | Whether a reference is available at a later position | Spec §5.4–§5.6 |
| Dynamic semantics | How meaning includes changes in what later discourse can use | Spec §5 |
| Eventuality | An event or state that a clause describes | `ClauseContent`, spec §4.6 |
| Contextual resolution | Recovering an intended value sufficiently for the conversation | `Context`, spec §5.3 |
| Vagueness | A meaning with genuinely unsettled boundaries | `Vague`, spec §6 |
| Projection | A requirement or side claim survives a main denial or question | `Presuppose` and `Supplement`, spec §5.5 |
| Force | Assertion, question, command, or another kind of speech act | `Act`, spec §7.1 |
| Performance | Actually making an assertion, asking, commanding, or displaying | `Perform`, spec §7.1 |
| Act occurrence | One particular performance, with its utterance context | `ActOccurrence`, spec §7.4 |
| Proposition | Content represented as something that can be referred to | `Reify`, spec §9.1 |
| Property | An expression with places left open to be filled | Functions and `ka`, spec §4.4 and §9 |
| Sign | Words or other material representing something | Spec §7.5 |
| Gap | A reading or construction not yet given a complete analysis | Spec §14 |

For a first look at the formal notation, start with
[samples §1](samples.md#1-predication-and-closure), which expands
`mi klama` step by step. Use [the catalog](catalog.md) to look up core
forms and [the cmavo index](cmavo.md) to start from a Lojban word.

For Lojban background, consult the CLL, the
[xorlo introduction](https://mw.lojban.org/papri/How_to_use_xorlo), and
[jbovlaste](https://jbovlaste.lojban.org/).
[The specification's References](spec.md#references) identifies the
editions and sources used for particular claims.

For readers who want the theory behind these distinctions, useful topics
are compositional semantics, dynamic semantics, plural reference,
presupposition, and speech acts. The specification's References includes
the works explicitly used or compared. [The rationale](rationale.md)
explains the arguments for Smusni's choices; those arguments are separate
from learning how to read the model.
