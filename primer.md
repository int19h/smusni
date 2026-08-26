# The Lojban semantic core: a primer

*The same definition as [the specification](spec.md), explained for people
who speak Lojban rather than formal semantics.*

## 0. Why a semantic core?

You can learn, from CLL, what every Lojban construct does. What you cannot
get from CLL is a single precise answer to the question *what does this
sentence mean?* — precise enough that two people who disagree about an
inference can point at the exact place their readings differ. CLL explains
meaning in prose, and prose runs out exactly where the interesting
disagreements start: does `ro broda` claim that broda exist? What do the
unmarked places of `mi klama` commit you to? When three dogs bit two men,
who bit whom? What, exactly, does a tanru say?

The semantic core answers by giving Lojban a second notation: a small,
typed, Lisp-looking language of *meanings*. Every Lojban sentence, once you
settle its reading, translates into a term of this language, and the term
is the meaning — with all its semantic structure typed, defined, or
honestly registered as an open gap (a few constructs, like generic
sentences, are frankly axiomatic, and the spec says so on the spot). The
core is deliberately verbose: it is an assembly language for meaning, and
ordinary Lojban is the high-level language that compiles to it. You will
never speak the core. You consult it the way you consult a dictionary: when
you need to know exactly what was said.

Three promises the core makes, which this primer keeps returning to:

1. **It resolves what CLL left accidentally unsettled.** Where the text of
   CLL just never decided something, the core picks — openly, with the
   choice written down as a numbered "pin" and an argument for it.
2. **It distinguishes intended underspecification from genuine vagueness.** A
   tanru normally conveys one intended link without spelling it out; `zo'e`
   hands an intended value to context; “many” has a cutoff with no fact of the
   matter. A bare sentence carries no tense marker, and which of its several
   readings you meant is yours to have meant. The core says precisely *how*
   each dimension is left open instead of putting every case in one bucket.
3. **It never depends on any program.** The core is a definition on paper.
   It mentions no parser, no software, no error messages. Anyone can
   implement it; nobody has to.

One naming note: the CapitalizedWords you'll see in core terms are
provisional core names. The project's end state is that every
*predicate* is an ordinary Lojban content word — many already are
(`purci`, `gunma`, `skicu`), and the rest carry dictionary-style
definitions awaiting an existing word or a new coinage. Executing
operators and structural forms such as `Bind` keep their semantic role;
a Lojban predicate may describe their results, but cannot perform their
work merely by having a dictionary row. The spec's §16 tracks the
distinction.

**How to read this primer.** Each chapter takes Lojban you already know,
shows the core term for it, and introduces the few formal ideas involved —
each idea gets a plain-language explanation, a worked example, and (in a
"jargon box") the name a semanticist would use, so you can graduate to the
dense specification when you want to. One example sentence follows us
through the whole book:

```
lo ci gerku noi blabi cu na batci re prenu .i .uinai cai ri tatpi
```

"The three dogs, which are white, didn't bite two people. Ugh — they are
tired." By the end you will be able to write down everything this little
discourse commits its speaker to, and everything it leaves open. (Even
the word order teaches: the `.uinai cai` sits at the front of its
sentence so that the displayed feeling is about the whole claim — placed
after `ri` it would be a feeling about the dogs.)

## 1. Saying things: predication

Start smaller:

```
; mi klama
(Assert (Close (klama Speaker)))
```

Two moves happened. First, `klama` is a **predicate** — a relation with
five labelled places (goer, destination, origin, route, means) — and
`Speaker` (that's `mi`) fills its first place. Second, and separately,
`Assert` turns the filled-in content into a claim. Keep these apart:
Lojban embeds bridi inside other bridi all the time (`mi djica lo nu do
klama` doesn't claim you go), so *saying-that* must be a separate
ingredient from *the that*. The core makes it a visible one. (`Close`, the
third word, is the spec's name for "fill the omitted places from context
and close the clause" — the next paragraph and chapter 2 unpack it.)

**What about the four unfilled places?** `mi klama` doesn't mention a
destination, but it isn't about going *nowhere*; the destination is
"whatever we're obviously talking about." The core writes that down
explicitly. Each omitted place becomes a `Context` value — a typed slot
whose content the hearer is expected to recover from the situation:

```
(Assert
  (Bind {$destination :: Referents Entity} (Context)
    {(∃ (λ {$e :: Referents Eventuality}
      {(klama Speaker $destination … :Eventuality $e)}))}))
```

(Only the destination slot is shown — the origin, route, and means each
get their own `Context` binding exactly like it; the specification's
samples write all four out. There's also an event variable in there —
chapter 2. And where this primer writes `∃` over that event, the
specification writes `CloseClause`, which additionally records *which*
event was the clause's own; the primer keeps the simpler spelling
throughout.) Three different
"missing thing" markers get three different treatments, and the difference
matters:

> **Not the same as!**
> - *omitted place / `zo'e`* — context supplies the intended value; the
>   listener needs to recover it accurately enough for this conversation, not
>   read the speaker's mind exactly. If no discourse-sufficient value can be
>   recovered, clarification or repair is needed. (`mi klama` — to the place
>   we both know enough about.)
> - *`zi'o`* — the place is surgically removed from the relation. `mi
>   klama ti zi'o` isn't going-with-unknown-origin, it is a
>   four-place going that has no origin at all.
> - *`da`* — a genuine "there is something": a logical variable, with all
>   the argumentative weight that carries.

> **Jargon box.** The core's name for the slot-filled-by-context is a
> `Context` computation; semanticists talk about *deixis* and *contextual
> resolution*. The whole apparatus of typed places is a *sorted relational
> signature*; the rule that `mi klama` asserts a going-event exists is
> *existential closure* over a *Davidsonian event argument* (chapter 2).

## 2. Events: when and how

Why did an event variable appear in `mi klama`? Because Lojban tense works
by *talking about the event*. `mi pu klama` says two things: there's a
going by me, and that going is earlier than now:

```
; mi pu klama
(Assert
  (∃ (λ {$e :: Referents Eventuality}
    {(∧ (klama Speaker :Eventuality $e)
       (purci $e Now))})))
```

That's the whole theory of tense. `pu` is not a verb inflection; it is a
predicate (`purci`, "is earlier than") applied to the event. `ba` is
`balvi`, `ca` is `cabna`; spatial tenses locate the event; `sepi'o` adds a
`pilno` ("uses") predication about the same event; BAI modals are the same
trick with other predicates. Stacked tenses chain: `mi pu pu klama` says
the going is before some point which is itself before now.

But “the event” is not always a lexical action. Every declarative clause first
has a `ClauseContent` slot:

- an ordinary episode such as `mi klama` puts the going itself there;
- `ta du lo mi zdani` puts the state of that identity holding there;
- a negation has a negative state;
- conjunction has a joint state, while disjunction keeps whichever branch
  event makes it true;
- a quantified or generic claim has a state of the whole claim holding, not
  one impossible event shared by every quantified individual.

So `ta pu du lo mi zdani` is entirely ordinary: `pu` says that identity-state
is earlier than now. With the home-description evaluated inside that state,
the building may have been my home then but not now; hoist its referent outside
and strict identity gives the rigid de re reading. `lo nu ta du lo mi zdani`
refers to the same kind of state. The core
does not retype binary `du`; `StateClause`
lifts its complete equality content, and `CloseClause` closes the uniform
event slot only when assertion or another content-taking operation needs it.
Nothing says those states must be short or finite: a mathematical holding
state may span all time or space. And a physical quantity may have value X
now and Y later: evaluate its value-description inside each state. Bind the
value outside instead and you deliberately get the rigid, de re reading.
Binary identity and arithmetic stay ordinary; state sensitivity belongs to
the quantity/value expression being compared.

And a bare, tenseless bridi? **There is no default tense** — but CLL
(ch. 10) itself lists the readings: `mi klama` "can be understood as" I went, I'm
going, I will go, I continually go — "context resolves which is
correct." The core takes that literally: those are different *readings*.
On an episodic reading ("I went") the time is a contextual slot exactly
like the destination — think of "I didn't turn off the stove!", which
denies one particular relevant failure, not every stove-touching in
history. On a habitual or timeless reading, there is genuinely no time
claim at all. What never happens is the core inserting a tense you
didn't choose. (Pin P8.)

Actuality has the same explicit discipline. `ca'a` requires the clause event
to occur (`fasnu`); `ka'e`, `nu'o`, and `pu'i` make capability claims. CLL
10.19 says an omitted CAhA can be understood either way, so the resolved
reading chooses among those four modes with no default. Bare episodic `mi
citka` normally selects actual; bare `ro datka cu flulimna` can select innate
capability without claiming that every duck is swimming now.

## 3. Things: reference

Now the noun phrases. Under xorlo — the modern gadri baseline, which the
core adopts wholesale —

```
; lo ci gerku
(Refer (λ {$r :: Referents Entity}
  {(∧ (gerku $r) …exactly-three-units…)}))
```

`lo P` does one thing: it **introduces a referent** — one-or-more things
that really are P, brought into the conversation so that later sentences
can pick them up. It is not "some", not "the", not "all": no quantifier,
no uniqueness, no counting, unless you add one. The inner `ci` says the
referent is three dogs; it does *not* say how many dogs exist.

The core's referents are **plural** through and through: `Referents` is a
type of one-or-more-things-together, with just two built-in notions —
`Combine` (this plurality together with that one: `jo'u`) and `Among`
(these are some of those). Nothing else: no assumption that pluralities
reduce to individuals plus grouping, and — importantly — **no hidden
answer to "together or separately?"**. `lo ci nanmu cu bevri lo pipno`
says the three men carried the piano; whether they carried it jointly or
each carried it is simply not part of what was said. If you want it said,
Lojban gives you words (`lu'a` for each-of; `loi` groups), and the core
gives those words meanings. (Pin P4.)

The other gadri, briefly:

- `le P` — *the ones I'm describing as P*: reference through the
  speaker's description, which may be inaccurate ("that `le nanmu`
  turned out to be a woman"). The core spells this with `skicu` itself —
  "the one I describe to you as P," where the describing is the very act
  of saying `le P` — so you count on the speaker's ability to point, not
  on the description's truth.
- `la N` — reference through a name-sign.
- `loi P` / `lo'i P` — reference to a *group object* / a *set object*
  built from a contextually selected, not automatically maximal, reference to
  P-things. A crowd can surround a building though no person
  does; the group is a thing in its own right.
- `lo'e P` / `le'e P` — generic talk ("the typical P…") — not a
  reference to any particular P at all. The core gives these their own
  operator, `Generic`: a typicality claim through a normality ordering,
  with no "typical specimen" in the term. Why no specimen? Because
  `lo'e cinfo cu se kerfa lo clani` (maned — that's normal *males*) and
  `lo'e cinfo cu se jbena lo cinfo` (bears cubs — normal *females*) are
  both true, and no single lion, however typical, could verify both.
  `le'e` is the same with the speaker as the stereotype's holder. The
  operator is frankly axiomatic — genericity is an open problem in
  semantics at large, and the core says so rather than pretending
  (spec §5.8).

> **Not the same as!** plurality (`lo re prenu`, some two people) /
> group (`loi re prenu`, a twosome as a unit) / set (`lo'i re prenu`, an
> abstract set object with two members). Three types; predicates care
> which they get.

`joi` is the connective that constructs such a whole. Compare:

- `mi jo'u do bevri lo pipno`: the x1 is the ordinary plural “you and I”; the
  word `bevri` decides whether that plurality can satisfy carrying together,
  separately, or in some other configuration.
- `mi joi do bevri lo pipno`: `joi` introduces a group object completely
  constituted by you and me at the intended grouping basis, and the carrying
  is predicated of that group.

The composite pronouns side with the plain plural, not with `joi`: `mi'o`
is `mi jo'u do`, one neutral plurality of speaker and listener, so `mi'o
remna` says we are humans without building a group that would then have
to be human; `mi .e do remna` makes two separate claims; and only `mi joi
do` builds the group (pin P40).

This is not a magic rule that properties flow between members and wholes. A
group can weigh 150 kg without either member doing so, and a member can be
tired without the group being tired. The core instead has a typed
constitution relation. Ordinary `gunma` is allowed to mention only some
components (“I am part of my family”); the stronger relation used by `joi`
and `loi` says that the supplied base is complete at the chosen peer level.
The peer level matters: people in a team, phases of an event, and origins or
aspects of a mixed property are different kinds of contribution, not one
universal notion of physical part.

The same programme closes at the right result type. Two ordinary sumti form a
`Group`; two event descriptions in an event-demanding place can form one
joint event; compatible tanru properties can form one mixed property when the
lexicon declares how their row combines. That is why a blue/red ball need be
neither wholly blue nor wholly red, and why a lion/tiger hybrid need not have
pure-lion and pure-tiger body parts. If no contribution rule is declared, the
reading is a gap rather than “whatever mixture the model happens to like.”

One subtlety matters for later pronouns. In `loi gerku` the component-dog
reference is only a lowering step; the surface introduced the group. The
`Local` boundary keeps that hidden base usable while constructing the group
but does not add it to the anaphora stack. Thus in CLL's
`lo'i ratcu … .i ku'i lu'a ri …`, `ri` reaches the set, not a second invisible
rat reference. `Local` changes accessibility only: it does not make the base
maximal, erase its truth conditions, or hide the resulting collection.

## 4. What later sentences can see

Our running example continues `.i ri … tatpi` — "they are tired." What
does `ri` reach back to? This is where the core earns its keep, because
"reference that persists" is the thing classical logic is famously bad at.

The core's model: a conversation carries a growing stock of **discourse
referents**. `lo`-phrases add to the stock. So do successful quantifiers:
after `ci gerku cu bajra` ("three dogs ran"), *those three dogs* are
available, and `.i ri tatpi` says they are tired. Every connective has a
stated policy — the core calls it the accessibility table — for what
survives it:

- `.ije` (and), `.i` (next sentence): everything introduced on the left
  is visible on the right, and afterwards.
- `.ija` (or): what happens in a disjunct stays in the disjunct.
- `na` (not): nothing escapes a negation.
- `ganai…gi` (if…then): the consequent can see the antecedent's
  introductions — which is exactly what donkey sentences need:

```
; ro prenu poi ponse su'o xasli cu darxi ri
; "everyone who owns a donkey beats it"
(∀ (λ {{$p :: Entity} {$d :: Referents Entity}}
  {(→ (∧ (prenu $p) (xasli $d) (ponse $p $d))
     (darxi $p $d))}))
```

(The donkey variable is a *plural* one — if someone owns several donkeys,
`ri` reaches all of them; and the full form also carries the "there are
donkey-owners" presupposition that `ro` brings — the spec's version
spells both out.)

The pronoun inside the consequent covaries with the donkey inside the
relative clause — classical logic can't write that with separate
quantifiers, so the resolved strong reading *lowers* to one universal over
person–donkey pairs. This is a reading choice, not an equivalent rewrite of
the compositional selection. The same selected construal, one level up, handles "every person
has three dogs; they are tired" (each person's dogs are tired).

That choice has a cost: the later pronoun retroactively strengthens how the
first sentence is construed. A future plural-information-state model could
store the dependency when it first arises and remove that retroactivity. The
weaker "one selected witness" model is coherent, but no Lojban form has been
found that selects it, so it is not a second silent reading.

> **Jargon box.** This is *dynamic semantics*: meanings are instructions
> for updating the conversation, not just true/false conditions
> (semanticists: DRT, DPL, *donkey anaphora*, *discourse referents*).
> Toaq's Kuna implementation gets the same results with algebraic
> effects; Lojban's core states the policies as a table.

## 5. How many

Quantifiers sit *on top of* reference. Three shapes to keep apart:

```
; ci gerku cu bajra          — "three dogs ran"
;   pick three dogs; they ran.  (witness selection)
; ro gerku cu bajra          — "all dogs ran"
;   presupposes there are dogs; each ran.  (importing universal)
; ro da zo'u …               — "for absolutely everything…"
;   the mathematician's ∀; no presupposition.  (bare logic)
```

(One honesty note the spec records as a pin: the printed CLL (ch. 16)
glosses bare numbers globally — "exactly two things, no more or less" —
and distributively, each thing separately. The core sides
with modern usage on both counts: `ci gerku` picks its three and stays
silent about others, says nothing about together-or-separately — which
is how `su'o prenu cu jmaji`, "some people are gathering", can be true
at all, though no single person gathers — and the global "and no more"
reading is there when you mark it.)

Two pins worth knowing. First, `ro broda` **imports**: saying "every
broda" commits you to broda existing — and that commitment survives
negation ("it's not true that every dog ran" still grants dogs), which is
why the core represents it as a *presupposition*, a claim that projects
out of whatever you wrap around it. Second, termsets: `ci gerku ce'e re
prenu cu batci` picks out three dogs and two people with all six bitings
— and says nothing about whether a fourth dog also joined in. CLL's own
termset section (ch. 16) glosses it exactly so ("picks out two groups …
every one of the dogs bites each of the men") and stops there; the "and nobody
else" reading is available, but you have to say it.

Vague numbers get chapter 9's treatment. Two different shapes hide
here: `so'i` "many" has *no* exact threshold — not even a secret one
context knows — while `ji'i re no` "about twenty" states its number and
leaves the *tolerance* fuzzy.

One more thing quantifiers do: their picks stay referable. After `su'o
gerku cu bajra`, the next sentence's `ri` can be those very dogs — a
quantified claim and a lasting referent at once (the spec calls this
witness export).

## 6. Doing things with words

`Assert` from chapter 1 has siblings:

```
(Ask (Polar (Close (klama Speaker))))                          ; xu mi klama
(Ask (OpenQ (λ {$x :: Referents Entity} {(Close (klama $x))}))) ; ma klama
(Command Audience (Close (klama Audience)))                    ; ko klama
(Express …)                            ; .ui and friends — chapter 7
(Vocative Audience)                    ; doi (addressing the listener)
```

Acts are *values*: you can build one, quote one, talk about one — none of
which performs it. `mi cusku lu ko klama li'u` reports a command without
giving one; the quotation marks in the core are a hard boundary that
meaning does not leak through. Performing happens only on the discourse
**spine** — the document's top-level sequence of acts, the things
actually said (everything else is acts *talked about*).

One package can be performed more than once. Each performance is a distinct
**act occurrence**, tied to its utterance token and to the speaker, time,
deictic ground, and omitted-place resolutions of that occasion. The package
does not change: `ActContent` always returns its raw content.
`RealizedContent` instead starts from a performed assertion's token and
returns the content under that occurrence's captured context. This is why
cross-utterance `go'i` keeps what the previous speaker/context meant, while `ra'o`
asks for deliberate re-resolution of the antecedent pro-assigns now. It does
not reopen unrelated omitted places or tanru links: those remain captured.
A quoted `Realizes` fact has a package
but no performance occurrence, so quotation interpretation correctly gets
the raw content. The capture is semantic, not a replay log: truth evaluation,
reference choices, projective commitments, and vagueness still obey their
ordinary rules.
The captured resolver is a partial function over every legal dependency tuple
of each captured site, not a log of tuples the first run happened to visit.
If a later `go'i` override reaches a new tuple, that original captured
function supplies it or is projectively undefined; the new speaker does not
quietly choose a replacement. A standalone UI/COI/vocative is its own Host
occurrence; "attached" roles exist only when another Host is present.

Embedded questions: `mi djuno lo du'u ma kau klama` — "I know who came."
What `kau` contributes is *answerhood*: my knowledge settles the question.
Does it settle it exhaustively (I know of everyone whether they came)?
**Lojban does not say**, and the core writes exactly that: the answer's
exhaustivity slot is simply absent — another "absence means absence" case.
(A verb might add its own demands; that's the dictionary's business, not
`kau`'s. Pin P9.)

## 7. Feelings and evidence

Now the `.uinai cai` in our running example. Indicators are the core's
**displayed content**: things shown rather than claimed. Each attitudinal
is a little relation from the dictionary — an experiencer, a target, and
a degree on an intensity scale — displayed alongside its host:

```
; .i .uinai cai ri tatpi     (ri = the dogs, from the prior sentence)
(Let {$a :: Act Assertion} (Assert (Close (tatpi $dogs)))
  {(Bind {$o :: ActOccurrence Assertion} (Perform Host $a)
    {(Do (Perform AttachedDisplay
      (Express (Close (Unhappiness Speaker $o Intense)))))})})
```

The bound `$o` is the performance occurrence. If `$a` is performed again, the
new handle does not inherit the earlier indicator; a relation can still
mention reusable `$a` explicitly when that is what the speaker targets.

(`Unhappiness` is capitalized because it is one of the spec's
placeholder relations — §0's naming note — awaiting its Lojban content
word. The candidates are the dictionary's `-nmo` words — `uinmo`
"feels happy about", built as *indicator* + `cinmo`, a pattern that
extends to every indicator — with the emotion gismu like `badri` as
runners-up.)

Note the three moving parts, all decided by rulings you can look up:
`nai` did **not** logically negate anything — `.uinai` is the *paired
emotion*, unhappiness, a word of its own; `cai` intensified *that*
(intense unhappiness, not "intensely other-than-happy"); and the target —
what the feeling is about — is the whole assertion it opens. And one thing
that did *not* happen: pure-emotion indicators like `.ui` never change
what is claimed — `.ui do klama` claims you're going and displays joy
about it. (Whether an indicator's host stays claimed is exactly what
the host-force profile below decides, per word.)

Two special indicator families:

- **Propositional attitudes**: `.au mi sipna` — "would that I slept!" —
  does *not* assert that I sleep. Each indicator's dictionary entry says
  whether it leaves its host asserted (`.ui`) or subordinated (`.au`,
  `.a'o`, `.ai`); this "host-force profile" is looked up, never guessed.
- **Evidentials**: `za'a do cadzu` — "I see you're walking" — the `za'a`
  gives the *basis* of the claim (observation), and negating the sentence
  negates the walking, never the basis. Deeper embeddings work too:
  `mi jinvi lo du'u ti'e do klama` marks hearsay on the *embedded*
  content. That's why the core treats evidentials as targeted display
  rather than as a feature of assertion.

Discursives (`ku'i` "however", `ji'a` "also") relate the current performed
occurrence to a previous one; `na'i` objects to a prior utterance ("something's off about
saying that") without negating anything — which is why Lojban has three
negation-flavored words, and the core gives them three unrelated meanings:

> **Not the same as!** `na` (the claim is false, nothing more) / `na'e`
> (scalar: denies the stated point AND asserts something else on the
> scale — `na'e melbi` says not-beautiful-but-something-else, perhaps
> plain; it claims *more* than `na`, not less) / `na'i` (metalinguistic
> objection: the utterance itself was defective — no truth claim at all).

## 8. Ideas about ideas

Lojban's abstractors each make a different *kind* of thing, and predicates
select which kind they accept — you can know a `du'u` but not an event,
attend a `nu` but not a proposition:

- `nu` — the event or state of the clause as a whole: directly the lexical
  event when one survives, otherwise its holding/joint/negative state.
- `du'u` — a proposition: the reified content itself.
- `ka` — a property: a function, with `ce'u` marking the open slot
  (unmarked: the first unfilled place — pin P12).
- `ni` — an amount on a scale; `jei` — a truth value under an
  epistemology; `li'i` — an experience with an experiencer; `si'o` — a
  concept in a mind; `su'u` — the generic abstraction with a category.

`jei` does not silently turn that truth value into a number. CLL's old [0,1]
proposal never acquired conventions or established practice, so P38 keeps the
numeric crossing as a future gap proposal rather than an optional baseline
reading.

In the core these last five are ordinary *relations* — "a is the amount
of content c on scale s" — so all your gadri skills apply to them:
`lo ni…`, `le ni…`, quantified `ni`s, relative clauses on abstractions,
and an omitted scale is the usual contextual slot. Nothing new to learn:
that is the point.

`tu'a X` deserves its own line: “the abstraction about X that I mean, without
my spelling it out.” The speaker is being lazy or low-precision, not normally
asserting that any X-related event will do. The host predicate fixes the
abstraction's sort, its relation to X constrains recovery, and context supplies
one intended value closely enough for the discourse.

## 9. Intended values and vague boundaries

The core sorts every “unspecific” construct in Lojban with the **recovery
test**: *does this occurrence have an intended value, or is there genuinely no
fact fixing a soritical boundary?*

- Intended value → **`Context`**. Omitted places, `zo'e`, `co'e`, `zu'i`,
  the link meant by a tanru, the abstraction meant by `tu'a`, bare `jai`'s
  intended role, a topic's place/aboutness link, and the contrast domain for
  `na'e`. Recovery need only be relevance-equivalent; misunderstanding is
  possible and repairable. A site also says which enclosing variables it may
  depend on, so an intended value can either stay constant or covary.
- No fact fixes one soritical boundary → **`Vague`**. Where exactly “many”
  starts, how wide a neutral region is, or how far “about twenty” extends. The
  meaning is a family of sharpenings of *one concept*, and the core computes
  pointwise with that family. Unrelated alternative meanings never go here.
- There is no value to give because nothing was said → **absence**.
  Tenselessness, `kau`'s exhaustivity, together-or-separately.

The tanru, finally, in full honesty:

```
; sutra klama
(Tanru sutra klama)   ; places = klama's; the intended LINK is Context
```

A `sutra klama` is a goer, with `sutra` bearing on the going in the way meant
on this occasion—fast at going is the strong conventional prior, but a context
can support another link. CLL's alternatives and warning about
misunderstanding show that the surface does not determine the link; they do not
make every possible link part of one truth condition. The core retrieves one
link constrained to genuinely modify the head predication. A lujvo lexicalizes
a link that a tanru leaves for contextual recovery.

Pleasingly, Lojban already knew. The official dictionary entry for the
gismu `tanru` (jbovlaste) reads "x1 is a binary metaphor formed with x2
modifying x3, **giving meaning x4 in usage/instance x5**" — the
dictionary itself says a tanru has a meaning in an individual usage. That
supports occurrence-specific recovery; conventionality biases the resolver
without turning a bare tanru into a lexicalized expression.

## 10. Words about words

`lu mi klama li'u` is a *sign* — a quoted transcript, mentioning an
assertion nobody performed. `lo'u … le'u` quotes text too broken to parse;
`zo klama` quotes one word; letterals (`ly.`) are signs usable as
variables; `me'o` mentions a mathematical expression while `li` uses its
value; `la'e` crosses from a sign to what it expresses, `lu'e` crosses
back. Signs are opaque: nothing dynamic — no referent, no presupposition —
leaks through a quotation boundary. This entire family is what keeps
use/mention straight, and it is why the core can talk about Lojban in
Lojban without paradox.

> **Notation box: why the braces?** In `(λ {$x :: T} {body})`,
> `{$x :: T}` is the binder telescope — “introduce variable `$x` of
> type `T`” — and `{body}` marks its scope. `Let` and `Bind` use the
> same punctuation. These are direct binding forms, not functions that
> receive quoted source code, and the braces do not create signs. Lojban
> quotation remains the `lu`/`zoi`/`zo` family above. A staged extension
> for quoting the core's own notation was explored and set aside; nothing
> in the baseline depends on it.

## 11. The whole example

```
lo ci gerku noi blabi cu na batci re prenu .i .uinai cai ri tatpi
```

Everything at once now. `lo ci gerku` introduces a three-dog referent.
`noi blabi` commits, *aside*, that they're white — a supplement: the `na`
that follows will not touch it, and if this had been a `xu` question the
whiteness still wouldn't be questioned. `na batci re prenu`: the at-issue
claim, negated — within it, `re prenu` selects a two-person witness set;
the negation says no such biting configuration holds. `.i ri`: the dogs.
Notice what the negation *did* block: the two people are trapped inside
it, inaccessible to any later anaphor — which is exactly why `ri` skips
them and lands on the dogs, introduced outside. `tatpi` claims they're
tired; the sentence-initial `.uinai cai` displays the speaker's intense
unhappiness about that whole claim. The tenseless sentences are read
episodically here, so *when* is not open but handed to context — the
biting denial targets the contextually relevant occasion, like
chapter 2's stove. What was left open, on purpose: whether the dogs act
jointly or severally; and nothing else — everything other than that
was said.

And here is that story written down — the sentence's full core term, on
its episodic readings (each sentence's occasion contextually anchored,
the way chapter 2 anchored the stove):

```lisp
(Bind {$dogs :: Referents Entity}                       ; chapter 3: lo introduces…
      (Refer (λ {$r :: Referents Entity}
        {(∧ (gerku $r)
            (= (CardBasis $r (λ {$x :: Entity} {(gerku $x)})) 3))})) ; …three dogs
  {(Do
    (Bind {$occ1 :: Time} (Context)                       ; chapter 2: the occasion —
      {(Let {$a1 :: Act Assertion}                      ; outside the negation
            (Assert
              (Supplement $dogs (Close (blabi $dogs))  ; the noi aside, outside the ¬
                (¬ (Exactly 2 (λ {$x :: Entity} {(prenu $x)}) ; chapter 5: a two-person
                     (λ {$ppl :: Referents Entity}          ; witness
                       {(∃ (λ {$e :: Referents Eventuality}
                          {(∧ (Close (batci $dogs $ppl :Eventuality $e))
                              (cabna $e $occ1))}))})))))
        {(Perform $a1)})})                             ; chapter 6: …and say it
    (Bind {$occ2 :: Time} (Context)
      {(Let {$a2 :: Act Assertion}
            (Assert
              (∃ (λ {$e :: Referents Eventuality}       ; chapter 4: ri = $dogs
                {(∧ (Close (tatpi $dogs :Eventuality $e))
                    (cabna $e $occ2))})))
        {(Bind {$o2 :: ActOccurrence Assertion} (Perform Host $a2)
          {(Do (Perform AttachedDisplay
            (Express (Close (Unhappiness Speaker $o2 Intense)))))})})}))}) ; chapter 7
```

Three names appear here that earlier chapters only gestured at.
`CardBasis` is chapter 3's `…exactly-three-units…` made honest: it
counts a plural referent *by a unit predicate* — these, counted as
dogs, number three. (The count alone would tolerate a pack riding
along; what rules it out is `gerku`'s own plural meaning, which under a
count profile requires the referent to be *covered* by dog units — pin
P39 — so `lo ci gerku` is three dogs and nothing else.) `Exactly n P body` is chapter 5's witness
selection as one operator: pick an n-unit P witness and run the
body on it — on the witness *as a plurality*, which is why the body's
variable `$ppl` is reference-typed: whether the dogs bit the two
together or one by one is not part of what was said (chapter 3's
together-or-separately, again). And `Supplement` is `noi` itself: it attaches the aside
(the whiteness) to its anchor (`$dogs`) alongside the at-issue claim —
the aside is new information, committed by the speaker — but it
*projects* the way chapter 5's presuppositions do, sitting structurally
beside the `¬` rather than under it, where no negation or question can
reach. Everything else you have seen: the two
`Let`/`Perform` pairs are chapter 6's acts-as-values, built and then
said; and `Express` takes the bound occurrence `$o2` — this performance
of `$a2` — as the emotion's target: the displayed unhappiness is about
*that assertion as made here*, which only a language whose acts are values
and whose performances are handles can even write down.

If you can reconstruct the story from the sentence — or check it off
against the term, line by line — you have the core. The specification
is the same story with the definitions filled in.

## 12. Glossary and further reading

**Glossary** (core term ↔ plain language ↔ Lojban ↔ where):

| Core | Plain | Lojban | Spec |
|---|---|---|---|
| `PredTerm<ρ>` | the type of relations over place row ρ | a brivla's relation | §3.3 |
| row ρ | the labelled place structure itself | x1…xn | §3.3 |
| `RefComp` | a computation that refers/retrieves (what `Bind` runs) | — | §3.4 |
| `ClauseContent` | a clause with its event/state still open | tense, tags, `nu` | §3.4, §4.6 |
| `StateClause` / `CloseClause` | give eventless content a holding state / close the common event slot | `du`, negation, force | §4.6, §9.3 |
| `Close` | actual-mode shorthand: fill omitted places and close a clause | an actual resolved bridi | §4.6 |
| `Refer` | introduce things into the conversation | `lo`/`le`/`la` | §5.3 |
| `Context` | recover the occurrence's intended value closely enough | `zo'e`, omissions, `co'e`, tanru, `tu'a`, topic | §5.3, §6 |
| `Vague` | family of soritical sharpenings; no cutoff fact | `so'i`, gradable cutoffs, `ji'i` tolerance | §5.3, §6 |
| `Referents` / `Among` / `Combine` | one-or-more things; some-of; together-with | plural sumti, `jo'u` | §3.2, §4.8 |
| accessibility table | what later text can refer back to | `ri` across `.i`/`ja`/`naku` | §5.4 |
| `Presuppose` | claim that survives negation | `ro`-import | §5.5 |
| `Supplement` | aside, committed regardless | `noi`, `sei` | §5.5 |
| witness export | a quantifier's picks stay referable | `ci gerku … .i ri` | §5.6 |
| `Generic` | typical-talk without a specimen | `lo'e`/`le'e` | §5.8 |
| `Act` / `ActOccurrence` / `Perform` | reusable speech-act package / one contextualized performance / doing it | quoted vs spoken, `go'i`/`ra'o` | §7.1–7.4 |
| `ActContent` / `RealizedContent` | raw package content / a performed assertion's captured content | quotation vs `la'e di'u` | §7.4 |
| displayed content | shown, not claimed | UI family | §7.6 |
| host-force profile | does the indicator's host stay claimed? | `.ui` vs `.au` | §7.6 |
| `Reify` | content as a thing | `du'u` | §9.1 |
| abstraction relations | amount/experience/concept as relations | `ni`/`li'i`/`si'o`/`su'u` | §9.2 |
| sign | quoted material, opaque | `lu…li'u`, `zo` | §7.5 |
| pin | our documented ruling where CLL was silent | — | §13 |
| gap | honestly not yet analyzed | `da'i`, … | §14 |

**Further reading**, staged. Lojban side: CLL chapters 5–19, the xorlo
page (<https://mw.lojban.org/papri/How_to_use_xorlo>), the official
dictionary (jbovlaste, <https://jbovlaste.lojban.org/>), and guskant's
"gadri: an unofficial commentary from a logical point of view" — the
primer's claims cite them throughout, and the specification's References
section gives the full citations, including which CLL edition the
section numbers follow. First formal
steps: Heim & Kratzer, *Semantics in Generative Grammar* (λs, quantifiers);
Groenendijk & Stokhof's "Dynamic Predicate Logic" and Kamp's DRT for
chapter 4's ideas; Link's plural logic and Oliver & Smiley, *Plural Logic*
for chapter 3; Hamblin/Karttunen on questions; Potts, *The Logic of
Conventional Implicatures*, for supplements and expressives; Searle,
*Speech Acts*, for chapter 6. Comparative: Eberban's reference grammar
(<https://eberban.github.io/eberban/> — a loglang with a formal core and
a rebuilt vocabulary; the architecture
this project borrowed) and Toaq's refgram
(<https://toaq.net/refgram/introduction/>)
with the Kuna semantic
implementation (the same problems, solved with algebraic effects). Then
the [specification](spec.md), which you are now equipped to read — with
the [catalog](catalog.md) beside it as the per-name reference (every
operator: plain-language definition, formal definition where one
exists, example, and where the details live).
