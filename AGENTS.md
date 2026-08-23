# Charter: the Lojban semantic core

This repository defines a community-facing **definition of Lojban
semantics** in terms of a small typed semantic core — a "Lojban semantic
assembly language".

## Mission

Flip the usual direction of Lojban semantics work. Instead of deriving
meaning from syntax construct by construct, we ask: **what meanings should a
Lojban utterance be able to convey**, and **what minimal set of typed
building blocks suffices to express all of them** — however verbose the
result, since syntactic sugar can always be layered on later. Every Lojban
utterance, under a resolved reading, is to denote a term of this core —
the specification's adequacy chapter states how far that claim presently
reaches, with its gap register bounding the remainder; the core is
the definition, and Lojban surface syntax becomes one (privileged) way to
spell its terms.

This is a *definition*, not a description:

- Where CLL is **explicit** that meaning is vague (e.g. the tanru
  modification relation), the core must contain machinery for *explicit,
  typed* vagueness — the vagueness is represented, not ignored.
- Where CLL is merely **underspecified** — where vagueness is an accident of
  the text, not a design intent — we pin the most useful interpretation and
  record why. The pin list and its justifications are first-class
  deliverables.
- xorlo is baseline (<https://mw.lojban.org/papri/How_to_use_xorlo>); CLL's
  pre-xorlo gadri semantics is superseded where they conflict.
- Sources — CLL, the official dictionary, the xorlo page, guskant's gadri
  commentary, Brismu (<https://brismu.systems/>) — are *guides*, not
  authorities; the specification's
  doctrine chapter states how they are weighed, and the compatibility
  principle that governs departures: a practical speaker of CLL Lojban
  must never have the rug pulled without strong, recorded motivation.

## The documents

At the repository root:

1. **`spec.md`** — the dense, formally precise specification. Audience:
   readers comfortable with formal semantics (typed lambda calculi,
   generalized quantifiers, dynamic semantics, speech-act theory). Complete
   and normative: types, term formers, well-formedness, semantics
   (denotational where possible, dynamic/effectful where needed), and the
   principles mapping Lojban constructs to core terms. Focused strictly on
   the semantic core: how and why it is **necessary and sufficient** to
   cover Lojban.
2. **`primer.md`** — the same content for fluent Lojbanists and amateur
   conlangers who are *not* semanticians. Terminology is unpacked and
   motivated rather than dropped: each technical notion gets a plain-language
   explanation, worked Lojban examples, and pointers for further reading so a
   motivated reader can graduate to the dense version.
3. **`rationale.md`** — for every major construct: why it is primitive (what
   meaning cannot be expressed without it), and why it is shaped this way
   rather than the plausible-looking alternatives. Ties into concrete
   examples.
4. **`samples.md`** — worked specimens: Lojban sentences with their full
   core terms, organized to walk the specification's chapters.
5. **`catalog.md`** — one entry per named identifier: informal
   definition, formal definition where one exists, purpose with an
   example, and links — split into true primitives (defined only by
   prose and axioms) and the forms defined in terms of them.
6. **`cmavo.md`** — the cmavo-centric index: one entry per treated
   cmavo (and per multi-cmavo grammatical unit) with a Lojban
   example, its core term, and links into the specification; its
   final section collects the documented no-mappings and the open
   adjacencies the cmavo-centric view makes visible.

## Hard constraints

- **No implementation residue.** The core is a definition of meaning, not
  of any processor: no registries, no reduction rows, no error taxonomies,
  no canonical-output rules, no duties for a renderer. The reader must
  never need to know any implementation exists. Where a rule would exist
  only to serve an implementation, it is out; where a construct's shape
  could only be explained by an internal model detail, it is reshaped on
  semantic merits.
- **The S-expression notation** — `()` for function application and
  nothing else, `{…}` quoting the core's own notation (binder telescopes
  and bodies included, so binders are ordinary sign-consuming words),
  PascalCase operators, lowercase lexical predicates, `$variables`,
  `;` comments — is a vehicle,
  not the subject. It is kept because it is readable and avoids
  bikeshedding; the PascalCase operators are explicit placeholders under
  the specification's content-word program.
- **Core vs sugar.** The core may be verbose. Anything derivable stays out
  of the core (or is explicitly marked as a derived form with its
  definition). Necessity arguments belong in the rationale.
- **Self-contained.** A reader with CLL, the xorlo page, and standard
  formal-semantics literature must be able to evaluate every claim. Cite
  CLL chapters/sections and the literature where a construct follows or
  departs from an established treatment.

## Comparative inputs (explicitly citable)

Unlike CLL, the reference grammars of two younger loglangs already define
much of their semantics formally. Both are cited in the deliverables, and
both repay study even where their solutions do not transfer:

- **Eberban** (<https://github.com/eberban/eberban>; reference grammar at
  <https://eberban.github.io/eberban/>). Custom higher-order logic;
  three-valued (true/false/unknown); every predicate threads an implicit
  *context argument* used to implement tense and similar meaning without
  surface verbosity; particles have per-family compositional definitions;
  a set-typed dictionary with explicit per-place distributivity marking;
  and the "Eberban from scratch" chapter reconstructs the practical
  vocabulary from a deliberately minimal core (pairs, sets, lists, maps,
  time) — exactly the core-plus-sugar architecture this project wants.
  Relevant chapters: Logic framework, Chaining, Explicit binding,
  Sentences, Logical primitives, Predicate transformations, Default
  arguments, Dictionary conventions, Eberban from scratch.
- **Toaq** (Delta; <https://toaq.net/>, refgram
  <https://toaq.net/refgram/introduction/>) and its reference
  implementation **Kuna**
  (<https://github.com/toaq/kuna>). Kuna's semantics is a simply-typed
  λ-calculus with an inventory of *effect* type constructors composed
  algebraically: intension `Int`, scope-taking continuation `Cont`,
  plurality `Pl`, Heim-style indefinites `Indef`, questions `Qn`,
  supplement pairing `Pair` (appositives — compare our `Supplement`),
  discourse-binding export/consume `Bind`/`Ref` (compare our accessibility
  story), deixis `Dx`, and speech acts `Act`.

Questions worth asking against both: what do they get for free that we
build by hand (Eberban's context argument vs our explicit event/tense
predications; Kuna's effect rows vs our explicit binders and force
constructors)? What do they *fail* to cover that Lojban needs? Which of
their formal devices would make our core smaller or crisper without
smuggling in an implementation?

## Derived artifacts (future)

The documents are the definition; anything executable or machine-checked
is a **derived artifact**, never the authority. Two lines look
promising once the core stabilizes. A **Lean 4** mechanization: Lean
supplies a staged, typed syntax-elaboration-and-kernel-checking host,
and its extensible syntax means elaborator macros could plausibly
*interpret the core notation directly* — though a mechanization must
separately enforce the core's written-only, constructive-only
reflection discipline, which Lean's own syntax and `Expr` APIs
(inspection, antiquotation) do not impose. Even Lojban text could be
fed in, given an independently specified parsing and reading-resolution
layer in front (mere normalization — spaces between words, no dots or
commas — only makes the text lexable). The result would make sample
terms type-checked objects rather than prose. A **Metamath cross-check**
against Brismu's derivations would test the pin list from the opposite
direction. Both are future work items, started only on explicit
decision; neither may ever become a place where the definition lives.

## Coverage

The specification's adequacy chapter carries the full coverage matrix —
every CLL construct family mapped to its analysis or to an honest entry
in the gap register. In outline, the core covers: predication over typed
places with contextual defaulting; place conversion and deletion; event
semantics with tense/modal facets as ordinary predicates over events;
sorts (entities, eventualities and their subsorts, sets, groups, lists,
signs, acts, utterances, amounts, scales, …) and functions; lambdas;
inert `Let` vs effectful `Bind`; reference (descriptions, names,
generics) and the specificity triad; relative clauses; generalized
quantifiers with explicit import, witness export, and presupposition;
plural reference with subreference and join; cardinality under a
counting basis; termsets; logical and non-logical connectives with a
normative dynamic-accessibility table; abstraction relations and their
numeric crossings; questions and answerhood; de re / de dicto; quotation,
signs, and utterance tokens; speech acts and discourse structure;
indicators and evidentials; typed vagueness (the tanru former, scalar
operators, contextual computations, supplements); core reflection
(quotation of the core's own notation, with binders as sign-consuming
words — the basis of the language's self-description); and mex to the
extent Lojban ties it to meaning.

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
2. **It refuses to resolve what Lojban deliberately leaves open.** A tanru
   really is vague; `zo'e` really does hand the matter to context; a bare
   sentence really carries no tense marker, and which of its several
   readings you meant is yours to have meant. The core has machinery to
   *say precisely that something is left open, and in which way* — this
   may be its most unusual feature.
3. **It never depends on any program.** The core is a definition on paper.
   It mentions no parser, no software, no error messages. Anyone can
   implement it; nobody has to.

One naming note: the CapitalizedWords you'll see in core terms are
*placeholders*. The project's end state is that every predicate is an
ordinary Lojban content word — many already are (`purci`, `gunma`,
`skicu`), and the rest carry dictionary-style definitions awaiting an
existing word or a new coinage (the spec's §16 tracks each one).

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
(Assert (klama Speaker))
```

Two moves happened. First, `klama` is a **predicate** — a relation with
five labelled places (goer, destination, origin, route, means) — and
`Speaker` (that's `mi`) fills its first place. Second, and separately,
`Assert` turns the filled-in content into a claim. Keep these apart:
Lojban embeds bridi inside other bridi all the time (`mi djica lo nu do
klama` doesn't claim you go), so *saying-that* must be a separate
ingredient from *the that*. The core makes it a visible one.

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
chapter 2.) Three different
"missing thing" markers get three different treatments, and the difference
matters:

> **Not the same as!**
> - *omitted place / `zo'e`* — context supplies a specific value; if your
>   listener can't work out which, communication failed. (`mi klama` — to
>   the place we both know about.)
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
  built from P-things. A crowd can surround a building though no person
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
quantifiers, so the core *normalizes* the sentence to one universal over
person–donkey pairs. The same trick, one level up, handles "every person
has three dogs; they are tired" (each person's dogs are tired).

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
  {(Do (Perform $a)
      (Express (Close (Unhappiness Speaker $a Intense))))})
```

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
what the feeling is about — is the assertion it follows. And one thing
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

Discursives (`ku'i` "however", `ji'a` "also") relate the current act to a
previous one; `na'i` objects to a prior utterance ("something's off about
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

- `nu` — an event: refer to eventualities satisfying the clause.
- `du'u` — a proposition: the reified content itself.
- `ka` — a property: a function, with `ce'u` marking the open slot
  (unmarked: the first unfilled place — pin P12).
- `ni` — an amount on a scale; `jei` — a truth value under an
  epistemology; `li'i` — an experience with an experiencer; `si'o` — a
  concept in a mind; `su'u` — the generic abstraction with a category.

In the core these last five are ordinary *relations* — "a is the amount
of content c on scale s" — so all your gadri skills apply to them:
`lo ni…`, `le ni…`, quantified `ni`s, relative clauses on abstractions,
and an omitted scale is the usual contextual slot. Nothing new to learn:
that is the point.

`tu'a X` deserves its own line: "something about X," with the something
*deliberately withheld*. Not context-recoverable — withheld. It's our
first honest meeting with the core's third specificity category, and it
leads straight to:

## 9. Being vague on purpose

The core sorts every "unspecific" construct in Lojban with one question,
the **recovery test**: *is your listener supposed to work out the specific
value?*

- Yes → **`Context`**. Omitted places, `zo'e`, `co'e` (the elliptical
  selbri — "you know the relation I mean"), `zu'i`, which scale `na'e`
  negates on. Communication fails if recovery fails.
- No, and there is genuinely no fact of the matter → **`Vague`**. The
  tanru link; `tu'a`'s abstraction; where exactly "many" starts. The
  meaning itself is a *family* of admissible precisifications, and the
  core computes with the whole family (negate a `Vague` claim and you get
  the family of negations — nothing collapses).
- There is no value to give because nothing was said → **absence**.
  Tenselessness, `kau`'s exhaustivity, together-or-separately.

The tanru, finally, in full honesty:

```
; sutra klama
(Tanru sutra klama)   ; places = klama's; the LINK is Vague
```

A `sutra klama` is a goer, with `sutra` bearing on the going *somehow* —
fast at going, in the common precisification, but CLL (ch. 5) is explicit
that the relation is open (a fast-food courier? goes when fast things are
needed?).
The core keeps a constrained open slot: any link that makes the modifier
genuinely modify the head predication is admissible; naming one (there's a
library of named links: manner, material, purpose…) is what a lujvo does.

Pleasingly, Lojban already knew. The official dictionary entry for the
gismu `tanru` (jbovlaste) reads "x1 is a binary metaphor formed with x2
modifying x3, **giving meaning x4 in usage/instance x5**" — the
dictionary itself says a tanru's meaning is a per-occasion resolution,
which is exactly the analysis above stated as a place structure.

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

> **Advanced box: the core can quote itself.** Beside the Lojban
> quotes above, the core has braces — `{…}` — which quote *the core's
> own notation*, not Lojban text. A quoted piece of notation is held
> back, unevaluated, and special words operate on it: the λ you have
> seen everywhere is really such a word — `(λ {$x :: T} {body})` applies
> it to a quoted parameter (`$x :: T` reads "variable `$x` of type
> `T`") and a quoted body and *produces* the
> function, so the braces show at a glance which parts are held back
> and, in ordinary term syntax, parentheses only ever mean "apply". One rule keeps this safe:
> braces are only ever *written* — nothing running can be turned back
> into its own code. This is advanced, optional machinery (spec §7.7);
> its payoff is that the binder words become ordinary vocabulary —
> functions with places, like any other word, though a small bootstrap
> floor (quoting and interpreting themselves) always remains — which
> is how, one day, Lojban gets to describe Lojban's own semantics in
> Lojban.

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
        {(Do (Perform $a2)
             (Express (Close (Unhappiness Speaker $a2 Intense))))})}))}) ; chapter 7
```

Three names appear here that earlier chapters only gestured at.
`CardBasis` is chapter 3's `…exactly-three-units…` made honest: it
counts a plural referent *by a unit predicate* — these, counted as
dogs, number three (so a plurality can be three dogs and one pack
without contradiction). `Exactly n P body` is chapter 5's witness
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
said; and `Express` takes `$a2` itself as the emotion's target — the
displayed unhappiness is about *that assertion*, which only a language
whose acts are values can even write down.

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
| `Close` | fill remaining places from context, claim an event | unmarked bridi | §4.6 |
| `Refer` | introduce things into the conversation | `lo`/`le`/`la` | §5.3 |
| `Context` | context supplies the specific value | `zo'e`, omissions, `co'e` | §5.3 |
| `Vague` | admissible family, no fact of the matter | tanru link, `tu'a`, `so'i` | §5.3, §6 |
| `Referents` / `Among` / `Combine` | one-or-more things; some-of; together-with | plural sumti, `jo'u` | §3.2, §4.8 |
| accessibility table | what later text can refer back to | `ri` across `.i`/`ja`/`naku` | §5.4 |
| `Presuppose` | claim that survives negation | `ro`-import | §5.5 |
| `Supplement` | aside, committed regardless | `noi`, `sei` | §5.5 |
| witness export | a quantifier's picks stay referable | `ci gerku … .i ri` | §5.6 |
| `Generic` | typical-talk without a specimen | `lo'e`/`le'e` | §5.8 |
| `Act` / `Perform` | built speech act vs doing it | quoted vs spoken | §7.1 |
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

# The Lojban semantic core

*A definition of Lojban meaning in terms of a small typed semantic
language.*

This document defines a semantic core for Lojban: a typed language of
meanings such that every Lojban utterance, under a resolved reading,
denotes a term of the core — within the analyzed coverage §15 states,
the gap register (§14) bounding the remainder. It is a **definition**,
not a description: where
the Complete Lojban Language (CLL) is explicit that a meaning is vague, the
core represents that vagueness with typed machinery; where CLL is merely
underspecified — vague by accident rather than by design — this document
pins an interpretation and records the pin as a numbered ruling. The
baseline for gadri and quantification is xorlo
(<https://mw.lojban.org/papri/How_to_use_xorlo>) — which the
Contemporary Lojban Language edition of CLL ratifies in-text (CLL 6.2;
editions and all other sources are listed in the References section) —
and pre-xorlo gadri semantics is superseded where older texts conflict.

The intended audience of this document is a reader comfortable with formal
semantics: typed lambda calculi, generalized quantifiers, dynamic semantics,
multidimensional/projective meaning, and speech-act theory. A companion
[primer](primer.md) presents the same content for fluent Lojbanists who are
not semanticians; a [rationale](rationale.md) argues, construct by
construct, why the core is shaped as it is and not otherwise;
[samples](samples.md) gives worked specimens with their Lojban sources;
and the [catalog](catalog.md) carries one reference entry per named
form — primitives and defined forms, each with prose, formal
definition, example, and links.

Two other engineered languages have formally specified fragments of their
semantics and are cited as comparative anchors where instructive: Eberban
(higher-order logic base, an implicit threaded context argument, and a
"from scratch" chapter that rebuilds practical vocabulary over a minimal
core; <https://github.com/eberban/eberban>) and Toaq Delta with its
reference implementation Kuna (a simply-typed λ-calculus with algebraic
effect constructors for scope, plurality, indefinites, questions,
supplements, discourse binding, deixis, and speech acts;
<https://toaq.net/>, <https://github.com/toaq/kuna>). The rationale
discusses what this core adopts from each and what it deliberately
declines.

## 1. Doctrine and judgments

### 1.1 The direction of definition

The core is meaning-first. Rather than assigning a denotation to each
syntactic construct of Lojban and hoping the assignments compose, the core
fixes an inventory of expressible meanings — typed terms — and then states,
in the mapping annex (§11), how Lojban surface constructs spell those
terms. Surface Lojban is one privileged concrete syntax for the core;
nothing in the core's semantics depends on it. The core may be verbose:
anything derivable is defined in the library (§12) rather than added to
the kernel, and syntactic sugar over the core is always possible later.
This is the same architecture Eberban's "from scratch" chapter demonstrates:
a deliberately small logical core, with the practical vocabulary
reconstructed over it as definitions.

### 1.2 Sources, compatibility, and the two programs

**Guides, not authorities.** This specification is the normative
definition; its sources are interpretations that *guide* it. That
includes CLL itself — which has well-known internal inconsistencies —
the official dictionary, the xorlo baseline, guskant's gadri commentary
("gadri: an unofficial commentary from a logical point of view"), and
Brismu's relational interpretation. Where the guides conflict or fall
silent, this document decides, and records the decision as a pin.

**The compatibility principle.** A speaker who does not know or care
about formal semantics but already speaks CLL Lojban in practice must
not have the rug pulled from under them: this document defines *Lojban*,
not a successor language. Some backwards incompatibility is unavoidable —
no coherent definition can cover every interpretation in circulation —
but a deviation from established reading or practice is acceptable only
when strongly motivated: it resolves a contradiction, or it buys a
substantially simpler model where the alternative is convoluted for no
real gain. Gratuitous deviation is a defect. Every deviation is a pin
that names its motivation against this principle.

**The lexicon program.** The wider project includes a revision of the
official gismu list to give entries defined semantics. This
specification may therefore *propose* redefinitions of existing words —
marked as proposals with exact wording, decided by the project's human
committee, never silently applied — where an existing word is almost
right and a minor diff unlikely to affect real usage would make it
exactly right.

**The content-word program.** The end state has **only content words as
predicates**: every PascalCase operator in this document is a
placeholder for a future content word (an existing gismu/lujvo where one
fits, a proposed redefinition where one almost fits, a new coinage
otherwise), each carrying a predicate-style definition and a see-also
note explaining why nearby existing words do or do not serve. The
PascalCase convention persists in the notation as those placeholders.
The program's reach and discipline are specified in §16 — including how
far the reduction over first-class signs goes and where it provably
stops. One boundary governs the whole program: **only content words
denote object-language predicates; the structural judgments and
evaluator operations that give them meaning are not thereby required to
be content words.**

### 1.3 Resolved readings

The core denotes **resolved readings**. Processes that turn a text into a
reading — anaphora resolution (which antecedent `ri` takes), erasure
(`si`/`sa`/`su`), elliptical expansion (`go'i`, `no'a`), sticky-tense
propagation (`ki`), indicator target selection — are **text-to-reading
rules**. They are normative (the mapping annex states them; a conforming
reading of a Lojban text must obey them) but they contribute no term
constructors: the calculus sees their *results* — variable bindings, token
identities, expanded content — never the processes themselves. A
syntactically well-formed text whose resolution fails (an anaphor with no
accessible antecedent, an unassigned assignable with no discourse key) has
no resolved reading; that is a statement about the mapping, not an error
object in the semantics.

### 1.4 Three ways not to be specific

The single most load-bearing distinction in this document is between three
things a meaning can do short of full specificity. They are distinct term
formers with distinct semantics (§5.3), and confusing them is the
characteristic mistake this core is designed to prevent:

- **Reference** (`Refer`): introduce a discourse referent satisfying a
  descriptive condition. A referent is new, veridically described (for
  `lo`), and available to subsequent anaphora.
- **Contextual resolution** (`Context`): retrieve a contextually salient
  value. Nothing is asserted about it and no referent is introduced; the
  speaker expects a cooperative hearer to recover a *specific* value, and
  communication fails if they cannot. Omitted places, `zo'e`, `co'e`,
  `do'e`, deictic grounds, and salient scales are of this kind.
- **Deliberate vagueness** (`Vague`): a typed, constrained set of
  admissible precisifications with **no fact of the matter** as to which is
  meant. The term never chooses. The tanru modification link, `tu'a`'s
  withheld abstraction, and soritical thresholds are of this kind.

The operational test — the **recovery test** — is printed with the full
classification in §6.1.

A fourth possibility is **absence**: the meaning simply lacks a dimension.
A bare `kau` answerhood makes no
exhaustivity claim; unmarked plural predication makes no distributivity
claim; a tenseless bridi on its habitual/gnomic readings makes no
temporal claim (its episodic readings instead carry a `Context` time —
ruling P8). Absence is represented by absence — no hole, no parameter, no
covert operator. Where a dimension is absent, the truth conditions are
those of the weakest reading, and strengthenings enter only lexically,
pragmatically, or by explicit marking. (Rulings P8, P9, P4.)

### 1.5 Ambiguity is upstream

Grammatical ambiguity — a text with several parses, or a parse with several
resolutions — yields several resolved readings, each a distinct core term.
The core never encodes disjunctions of readings; it is downstream of
disambiguation. In particular, a construct is never classified `Vague`
merely because a text is ambiguous: `Vague` is a property of one reading's
meaning, not of the reader's uncertainty between readings. (Where a
construction's readings genuinely differ — e.g. implicit `ce'u` with
several unfilled places — the mapping annex says "distinct readings," never
"contextual vagueness"; ruling P12.)

### 1.6 Well-formedness, not failure

The core is defined by formation rules and typing judgments. An ill-typed
combination is not a term; a construction whose side conditions fail (e.g.
closure over a non-defaultable place, §4.6) is undefined at that point.
This document has no failure codes, no diagnostics, and no processing
model. Meanings this core deliberately does not analyze are listed in the
gap register (§14) with the reason no analysis is assigned; a gap is a
statement about this specification, not a runtime event.

### 1.7 Two truth values

At-issue content is two-valued. Partiality (undefined operations,
presupposition failure) is handled by the projective machinery (§5.5): a
partial operation carries a definedness condition that projects like any
presupposition. There is no third truth value; the phenomena a three-valued
logic would bundle — contextually unresolved values, question force,
presupposition failure — are kept apart by `Context`, the question types,
and `Presuppose` respectively. (Eberban's true/false/unknown is declined;
see the rationale.) Deliberate vagueness does not breach this: bivalence
holds **at every precisification** of a `Vague` parameter, and "supertruth"
over admissible precisifications (§5.3) is a metalogical consequence
notion, not an object-language truth value — borderline vagueness yields no
third value, only a family of bivalent readings.

## 2. Notation

Core terms are written as S-expressions:

- `(operator operand …)` — application and operator forms; PascalCase
  names are core operators and library forms; lowercase names are lexical
  predicates (dictionary words: `klama`, `gerku`); Greek λ introduces
  functions; a small set of mathematical glyphs (`¬ ∧ ∨ → ↔ ⊕ ∀ ∃ = ∈ ⊆
  ∪ ∩ ≤ < ⊤`) name the logical and mathematical operators (`⊤` is
  the trivially true content — the empty conjunction, `∧`'s unit).
- `$name` — variables, always introduced by a binder with an explicit
  type ascription: `(λ {$x :: Entity} {…})`, `(Let {$p :: T} v {…})`.
  `::` is the **type-ascription keyword** — a member of the keyword
  family below, marking that its operand is a type — and every form
  that requires a type annotation requires it. A compound type is a
  **generic instantiation** — a type constructor applied to indices of
  its declared kinds: sorts (`Referents Entity`), rows (`Record ρ`,
  `PredTerm ρ(H)`, and `Label klama` — the §4.7 abbreviation of the
  row-indexed `Label ρ(klama)`), forces (`Act Assertion`), sign kinds
  (`SignToken K`) — and after `::` the
  application spine is written flat: `{$r :: Referents Entity}`
  applies the `Referents` former to
  `Entity` (the type the metalanguage displays as `Referents<Entity>`),
  and parentheses appear only to group a *nested* instantiation
  (`{$sets :: Referents (Set Entity)}`). Row expressions — `ρ`,
  `ρ−ℓ`, `ρ(H)` — are stated metalanguage (a row name, a row minus a
  label, the row of a relation) and keep that spelling inside
  schematic ascriptions; they are not term-level parentheses. Thus `{$x :: Entity}` binds
  over single individuals while `{$r :: Referents Entity}` binds a
  plural reference (§3.2): different types, one notation. (Should a
  function type ever be needed in this position, an `Fn`/`EFn`
  instantiation takes its parameter sort-list as a single
  parenthesized operand.)
- `:label value` — a labelled place fill inside a predication (§4.2);
  `:2` names the second lexical place, `:Eventuality` the event place.
  `::` above is the same device one level up: a keyword marking the
  role of the operand that follows it as a type.
- `; text` — comments, to end of line; consumed as whitespace. By
  convention a specimen's first comment line is its Lojban source.
- `"…"` — `Text` literals (used by name signs, quoted text, and sign
  facts).
- `{…}` — **quotation of core notation** (§7.7): an `Expression` sign —
  elaborated, scoped, α-classed core syntax — or a **telescope**. A
  telescope is either one **group** — variables sharing one ascription,
  `{$x :: T}`, `{$x $y :: T}` — or a **concatenation** of telescopes,
  `{{$x :: T} {$y :: S}}`, ordered and left-scoping. A single group is
  always written flat: nesting appears exactly when there are two or
  more groups. Braces are reserved for these quotes; set-builder and
  record displays are metalanguage and use words or `⟨…⟩`. Parentheses
  *inside* braces are mentioned syntax, not application.
- The binder names are **aliases** of the reflection words (§7.7):
  `λ` *is* `MakeLambda`, and `(λ {$x :: T} {body})` is an ordinary
  application — `Let` and `Bind` likewise per their definitions — so
  `()` is function application and **nothing else** — in term syntax
  always parenthesized; in a type after `::` application is the flat
  spine just described, with parentheses grouping nested
  instantiations only (angle-bracket signature displays such as
  `Fn<(A), B>` are metalanguage, not this notation). A binder form is
  always a word applied to a telescope quote, its active operands, and
  a body quote: `(λ {$x :: T} {body})`; `(Let {$x :: T} v {body})`;
  `(Bind {$x :: T} c {body})`, variadic by alternation
  (`(Bind {$x :: T} c₁ {$y :: S} c₂ … {body})`, §5.2).

Notation conventions — elision of inferable types, the writing of `Close`
(§4.6), currying conventions, pretty-printing — are non-semantic: two
spellings that denote the same term per this document's rules are the same
meaning, and no unique canonical spelling is defined or required. This
chapter is the only place notation is normative, and only to the extent
that a reader must be able to parse the examples.

## 3. Types

### 3.1 Sorts of individuals

The domain of first-order individuals is sorted. `Entity` is the top
first-order sort. Beneath it:

```text
Entity
├─ Eventuality       events and states of affairs; subsorts:
│      Achievement, Process, Activity, State, Experience,
│      Locution (an uttering event)
├─ Location
├─ Time
├─ Amount            (positions on scales)
├─ Scale
├─ Epistemology
├─ TruthValue
├─ Concept
├─ AbstractNature
├─ Proposition       (reified content, §9)
├─ Question          (reified queries, §8)
├─ Number            with Natural <: Number and, embedded through the
│                    finite cardinalities, Cardinal <: Number
├─ Text              (uninterpreted character sequences)
├─ Set<T>  Group<T>  List<T>    (collection objects, §4.9)
├─ Sign<K>  SignToken<K>        (signs, §7.5; K a sign kind)
├─ UtteranceToken               (utterance tokens, §7.4)
└─ Ground            (deictic grounds, §5.1)
```

All sorts under `Entity` above are pairwise siblings except where a
subsort line says otherwise
(`Time` is not a `Location`, `Epistemology` is not a `Scale`,
`AbstractNature` not a `Concept`).
`Bool` is the two-element answer type for polar questions (§8.1), distinct
from the epistemology-relative `TruthValue` sort.

Subsorting is subset inclusion in every model; a term of a subsort may
stand wherever the supersort is required (covariantly, through `Referents`
as well), and never conversely. The sort hierarchy makes lexical selection
expressible — `barda` selects an `Amount`-bearing argument where `fasnu`
selects an `Eventuality` — and underwrites the no-coercion ruling (P13):
no implicit conversions exist between sorts; every crossing is an explicit
operator or lexical relation.

The hierarchy is open at the leaves in one deliberate way: `Entity` admits
kind-like referents where a model and the lexicon's kind-admitting places
allow them. There is no `Kind` sort and no automatic kind reading of any
description; see ruling P3. One further opening is **reserved**, not
present: §9.1's reified-predicate family would, if adopted, add an
indexed first-order sort family beside `Set<T>`/`Sign<K>`, each member
an ordinary first-order domain for equality, `Referents`,
descriptions, and typed quantifiers, with `Proposition` retrospectively
its row-⟨⟩ member; in the baseline only `Proposition` exists.

### 3.2 Plural reference

`Referents<T>` is the type of **plural references**: nonempty,
number-neutral pluralities of `T`s. It is not `Set<T>` (a set is a single
first-order object with membership; a plurality is not an object over and
above its members), not a mereological sum, and not a group. Its algebra
(§4.8) has exactly a join (`Combine`) and the induced subreference order
(`Among`); no atomicity, no distributivity, and no covers are assumed.
`Referents<T>` is covariant in `T`, and a single `T` lifts implicitly to a
singleton `Referents<T>` at referential positions (a typing rule, not an
operator).

Nonemptiness is part of the type: there is no empty plural reference.
(Consequences for `lo no broda` are drawn in ruling P22.)

### 3.3 Relations, functions, and rows

A **place row** ρ is a finite sequence of labelled, typed places, e.g. for
`klama`:

```text
ρ(klama) = ⟨ x1:Referents<Entity>, x2:Referents<Entity>,
             x3:Referents<Entity>, x4:Referents<Entity>,
             x5:Referents<Entity> ; ev:Referents<Eventuality> ⟩
```

The event place `ev` is distinguished: it is present exactly on
event-licensed lexical entries (§10) and is filled with `:Eventuality`.

- `PredTerm<ρ>` — the type of relations over row ρ. It is a **transparent
  alias** for the row-function type `Record ρ → Content`: partial filling
  is abstraction over the residual row, place selection is record
  projection, and two relations equal on all row records are the same
  relation. A relation over the exhausted row is its content:
  `PredTerm<⟨⟩>` applied at the empty record is `Content`, and the
  notation writes that final application invisibly. The alias is retained pervasively in signatures because
  labelled places are the load-bearing Lojban-specific structure (free
  place order, `zi'o`, conversion, place questions all speak in labels).
- `Fn<(A …), B>` — ordinary functions with positional parameters, the type
  of λ-abstractions. Properties are `Fn<(T), Content>`; generalized
  quantifiers are `Fn<(Fn<(T), Content>), Content>`.
- `Label<ρ>` — the finite type of ρ's place labels; the domain of place
  questions (§8.3).

Purity is tracked in the function space: `Fn` is the **pure** arrow — a
function whose body, *when its result is evaluated*, performs no dynamic
effects (§5): no introductions, no contextual retrievals, no projective
emissions — and `EFn` the effectful arrow. Positions that demand purity
are exactly **set comprehension (§4.9), quantifier and `Generic`
restrictors (§4.10, §5.8), and selection restrictors (§5.6)**; a body with
unhoisted effects simply fails to have the pure type. Nuclear scopes,
`OpenQ` bodies, and `Generic`'s nuclear operand are `EFn` — they may
close places contextually and introduce referents, with the accessibility
table governing what escapes. This is the whole of the purity discipline:
a typing fact, not an algorithm. `PredTerm<ρ>`, `Fn`, and `EFn` are types
and appear freely in variable annotations, λ parameter lists, and
`Context`/`Vague` type arguments.

### 3.4 Control types

```text
Content            evaluable (dynamic) propositional content
RefComp<T>         reference/contextual computations returning T
Act<F>             speech acts of force F ∈ ⟨Assertion, Question,
                   Directive, Expressive, Address⟩
Discourse          performed discourse (sequences of acts and transitions)
Query<A>           questions with answer domain A
```

`Content` is the type of what can be asserted, questioned, negated, and
embedded. Its denotation (§5.1) is a world-indexed context-change
potential; the world index never appears in the term language. `Act<F>`
values are first-class: constructing an act and performing it are
different things (§7.1), which is what keeps quotation and reported speech
from performing their contents. An act is a pure *value*, not a
computation: only `Perform` injects it into the dynamic carrier
(§5.1, §7.1).

### 3.5 Index and composite types

Beside the sorts and the function space, the type language carries a
small stock of **index and composite formers**, each already used by a
named construct and normative for exactly those uses:

- **Closed enumerations** — finite, equality-bearing index types,
  declared with their constructs: `Bool` (§3.1), `Proximity` (§5.1),
  the force index of `Act<F>`, the effect classes of §7.7,
  `ThresholdKind`, `Direction`, `BasisKind`, `DefectKind`,
  `EnumerationLevel`, the intensity regions (§7.6), and the
  place-label types `Label<ρ>`. `=` is available at every enumeration
  (§4.5); the eliminator is the finite equality-guarded disjunction —
  the §4.7 computed-label case split.
- **Closed unions** — finitely-tagged sums declared with their
  constructs: `TopicResolution<ρ,T>` (§12) and the indicator target
  type `Target` (§7.6). A union value is built by its named injection
  and consumed by the same finite equality-guarded disjunction.
  `Target` is fixed here once: a `Proposition`, an act value of
  *some* force (the force index existential and erased — recoverable
  only through the partial `InterpretAct<F>`/`RealizedAct<F>`
  family), a plural reference at *some* sort, or a sign of *some*
  kind. The same force-erasure reading types `Realizes u a` (§7.4):
  its act operand is force-existential. Sort-polymorphic fact
  relations (`Denotes`, §7.5) are metalanguage families — one
  relation per sort — not union-typed operators.
- **Tuples** — finite products: multi-parameter quantifier loci
  (§4.5), open-question answer domains (§8.1), `TupleAnswer`
  payloads (§8.2). Projection is positional and total.
- **List construction** — `(List a …)` builds `List<T>` values
  (§4.9); elimination is metalanguage recursion over list structure
  (§12's `ZipWith` and `xi`), never a term-level recursion former
  (§4.4).

Nothing else is composite: `Record ρ` stays the row-record theory of
§3.3, and set-builder or record displays remain metalanguage (§2).

## 4. The static core

### 4.1 Lexical predication

A lexical predicate applied to fills for its row yields `Content`:

```lisp
; mi klama ti
(klama Speaker This)
```

Fills are positional by default, following the row order; a labelled fill
`:n value` selects a place out of order, and subsequent positional fills
continue from the place after `n`:

```lisp
; klama fe ti tu        — x2 = ti, x3 = tu, x1 unfilled
(klama :2 This Yonder)
```

The event place is filled as `:Eventuality e`. Unfilled places do not
default silently; they are closed by `Close` (§4.6) into explicit
contextual computations, or abstracted by λ, or genuinely absent only
under `DropPlace`.

**All fill notation is sugar over one former.** The single-place fill
`(At R ℓ v)` with a literal label (§4.7) fills place ℓ and yields the
relation over the residual row; every multi-place fill desugars to
nested single fills, with the positional and `:n`-continuation rules
above merely computing which labels are used:

```lisp
(klama :2 This Yonder)
  ≝ (At (At klama x2 This) x3 Yonder)
(klama Speaker This)
  ≝ (At (At klama x1 Speaker) x2 This)
```

Fills are values — effectful arguments are bound by `Bind` before they
reach a fill position — so distinct-label fills **commute**
(definitionally: `(At (At R ℓ₁ v₁) ℓ₂ v₂) ≡ (At (At R ℓ₂ v₂) ℓ₁ v₁)`
— a metatheoretic equation, since object-language `=` does not apply
at row-function types). That commutation
is the semantic fact beneath Lojban's free surface order: FA
reordering and `se`-conversion are notation precisely because the
order of *fills* never was part of the meaning. Two things surface
order still governs, upstream of the term: effectful argument
computations `Bind` in source order before any fill forms, and the
⊳ anaphora-resolution rules (`ri`'s recency counting, CLL ch. 7) read
the *text's* sumti order — so reordering a sentence can change which
term the mapping produces, while never changing what any one term
means. And `At` itself is no
new primitive: with `PredTerm` a transparent alias (§3.3), the literal
fill is partial application of the row function —
`(At R ℓ v) ≝ (λ {$rest :: Record ρ−ℓ} {(R ⟨$rest extended with
ℓ = v⟩)})` — so the
whole fill apparatus bottoms out in λ and labelled records.

### 4.2 Place conversion

`se`/`te`/`ve`/`xe` and FA tags are consumed by the mapping: a converted
predication is the base predication with fills routed to their base
places. A converted relation escaping into a function position is the
λ-abstraction over the permuted row:

```lisp
; se tavla, as a first-class binary relation
(λ {$new-x1 $new-x2 :: Referents Entity}
  {(tavla $new-x2 $new-x1)})
```

No `Se` operator exists in the core.

### 4.3 Place deletion

`(DropPlace R n) : PredTerm<ρ − n>` is the relation ρ with place `n`
removed — the meaning of `zi'o`. Deletion is semantic surgery on the
relation, not omission of a fill: `mi klama ti zi'o ti ti` predicates a
relation that *has no origin role*, which neither `zo'e` nor closure can
express. A lexical entry states which deletions are meaningful (§10).

### 4.4 Functions and binding

`(λ {$x :: T} {body})` forms functions — the telescope may be any §2
telescope: a shared-run group (`{$x $y :: T}`) or a concatenation
(`{{$x :: T} {$y :: S}}`) — and application is juxtaposition.
`(Let {$x :: T} v {body})` is inert sharing — definable as immediate
application, retained for legibility and for expressing identity of one
value used twice (`goi` aliasing). `Let` bodies may not smuggle effects
into shared positions: an effectful computation is shared by `Bind`
(§5.2), never by `Let`. There is no recursion former in the term language;
recursive definitions occur only in the library's metalanguage (§12).

### 4.5 Connectives and quantifiers

The logical operators are `¬ ∧ ∨ → ↔ ⊕` over `Content` and the
quantifiers `∀ ∃` over typed λ-bodies, with (multi-parameter) joint loci:

```lisp
(∀ (λ {$x $y :: Entity} {…}))
```

Statically they have classical truth conditions. Dynamically each carries
an accessibility row (§5.4) that is part of its meaning; `↔` and `⊕` are
primitive precisely because their classical rewrites duplicate operands,
and duplication re-runs dynamic effects. Multi-parameter loci are the
normal form of donkey configurations (§5.6) and simultaneous termsets
(ruling P17).

Equality `=` is primitive at every first-order sort **except the
constructive-only syntax kinds** (`Expression`/`Telescope` signs —
no code equality, §7.7's discipline) and at the
discrete index types (`Bool`, place labels, the closed enumerations);
it is never available at the plural reference type, where `CoRef`
(mutual `Among`) is the equivalence. `du` maps to `=` between
first-order individuals and to `CoRef` between plural sumti.

### 4.6 Closure

`Close` turns an open predication into `Content`: it existentially closes
the event place (when the row licenses one and no explicit event fill or
abstraction consumes it) and introduces one `Context` computation per
remaining defaultable place. It is a **normatively defined derived
operation** — schema, for a row with unfilled defaultable places p₁…pₖ and
an event place:

```lisp
(Close P)  ≝
(Bind {$v1 :: T1} (Context) … {$vk :: Tk} (Context)
  {(∃ (λ {$e :: Referents Eventuality}
    {(P :p1 $v1 … :pk $vk :Eventuality $e)}))})
```

Each omitted place is a *distinct* contextual computation (ruling P15),
and the site/key identity rule of §5.3 applies: when a λ-abstracted
predication containing closure sites is applied more than once within one
performance, the closure sites keep their identity — `mi .e ti klama`
shares one contextual destination across both conjuncts unless the reading
expresses otherwise. `Close` is undefined at a row whose remaining places
are not defaultable; such content must fill or abstract them explicitly.
The surface convention that `Close` is implicit at force boundaries is
notation (§2), not semantics.

### 4.7 Place questions

`Label<ρ>` (§3.3) types questions over places. `At` is the
single-place fill former: with a **literal** label, `(At R ℓ v)` is
partial application of the row function at field ℓ (§4.1 — every fill
notation desugars to it). With a **computed** label —
`$p : CompatibleLabel<ρ,T>` for a fill `v : T`, the `fi'a` case —
`(At R $p v)` abbreviates the finite case split over the compatible
labels, each branch a literal fill:

```lisp
(∨ (∧ (= $p ℓ₁) C[(At R ℓ₁ v)]) … (∧ (= $p ℓₙ) C[(At R ℓₙ v)]))
```

(`C[·]` the containing predication through its closure — the
computed-label form is licensed exactly where that closed context
exists, so every branch is `Content`). The domain is the
**compatible-label refinement** `CompatibleLabel<ρ,T>` (declared with
the topic interface, §12): the labels whose place sort accepts the
fill — a heterogeneous row contributes no ill-typed branch — and the
event place is excluded (no FA tag reaches it; surface place
questions ask over the lexical x-places). When **two or more**
computed fills occur in one predication, the case split ranges over
the assignments in which the computed labels are **pairwise
distinct** (two fills never answer one place); a single computed
fill — the ordinary `fi'a` — carries no such condition. `(Label R)`
abbreviates `Label<ρ(R)>`, and a computed-fill domain
`(CompatibleLabel R T)` likewise. `fi'a` maps to an open question
over its compatible-label domain (§8.3); an open relation question
(`mo`) binds a `PredTerm`-typed variable directly and needs no
special row machinery.

### 4.8 The plural algebra

`Combine : Referents<T> × Referents<T> → Referents<T>` is plural join
(associative, commutative, idempotent — `jo'u`), and
`Among : Referents<T> × Referents<T> → Content` is the subreference
order. Both are primitive at the plural type and axiomatized together
(`Among x y` holds exactly when `Combine x y` and `y` co-refer — the
library's `CoRef`, §12; typed
equality `=` itself stays at the first-order sorts, so the axiom is
stated as co-reference, not object equality). Singular `T`s lift to
singleton references at referential positions.

The bridge from pluralities to collection objects is **basis
extraction**: for a pure `P : Fn<(T), Content>`,

```text
(UnitSet P r) : Set<T>   —  the set of P-satisfying units among r:
                             x ∈ (UnitSet P r)  iff  P(x) ∧ Among(x, r)
(CardBasis r P) ≝ (Card (UnitSet P r))
```

`CardBasis` is how inner cardinality is stated: counting is always
counting units *under a description* within a reference (pin P1's
source-licensed unit basis).

That is the whole plural kernel. No atoms are assumed (nothing requires
that references bottom out in singletons), no distributivity operator is
covert, and no cover parameter attaches to predication: a lexical
predicate applied to a plural reference holds or fails of that plurality,
and which configurations verify it is the predicate's lexical business
(the lexicon may declare per-place plurality behavior, §10). Marked
readings are explicit: the library's `Distrib` (from `∀`/`Among`) for
each-reading, group objects (§4.9) for collective packaging, and `lu'a`
(§12) when a resolved reading commits to structure.
(Rulings P4; the design follows plural logic — Boolos, Oliver & Smiley —
rather than covert-operator theories.)

**Representation note (non-normative).** Under the discipline **D** —
nonempty, atomistically generated, singleton-separated, singleton-prime
(a unit below a join is below one of the operands) pluralities with
extensional identity by units (discourse-introduction identity carried
outside the extension), every nonempty unit set represented (with the
infinite joins that requires), natural under subsorts — the quotient
`Referents<T>/CoRef` is isomorphic to the nonempty sets over `T`:
`Combine` is union, `Among` is subset, the singleton lift sends each
individual to its singleton set. A set-backed implementation of that fragment is therefore
legitimate, and set-typed lexicons (Eberban's nonempty `tce` places)
are intertranslatable with this one inside D. The specification does
not adopt D: atomistic generation is exactly what the no-atoms clause
declines, and representation sets must in any case stay distinct from
the first-order `Set<T>` objects of §4.9 (ruling P25; the full
argument, including why the re-spec was declined, is the rationale's
sets essay).

### 4.9 Collections and mathematics

Collection *objects* are first-order individuals distinct from plural
references:

- `(SetOf P) : Set<T>` for pure `P : Fn<(T), Content>` — extensional
  comprehension; `∈` is membership; `Card : Set<T> ⇀ Cardinal` is
  defined at the finite sets, its definedness projective (§5.5) — the
  comparisons built on it (`Most`, `GlobalExactly`, the ROI schema)
  inherit the finiteness condition.
  (`CardBasis`, §4.8, is the corresponding operation for plural
  references: it counts units under a description within a reference.)
- `Group<T>` objects are related to their components by the lexical
  relation `gunma` (x2 plural — ruling P5); `Set<T>` objects by `selcmi`.
  `loi`/`lo'i` descriptions refer to such objects (§11); neither unwraps
  implicitly to its members.
- `List<T>` objects carry order (`ce'o`); indexing and `ZipWith` (the
  `fa'u` analysis) are library forms over list recursion (§12).
- `Number` and its subsorts carry the arithmetic operators
  `+ − × ÷ < ≤` (with `a > b ≝ b < a` and `≥` likewise); partial
  operations (division, non-total roots) carry
  projective definedness conditions (§5.5). Intervals are comprehensions
  with endpoint conditions; further mathematics (exponentiation, bases,
  arrays) is library and gap-register material.

### 4.10 Cardinal quantification

Bare-PA terms denote **witness-set selection** (rulings P1, P17): `ci
gerku cu bajra` selects a three-unit witness reference of dogs and
predicates running of it —

```lisp
; ci gerku cu bajra — the default (witness-set) reading
(Bind {$w :: Referents Entity}
        (SelectExactly 3 (λ {$x :: Entity} {(gerku $x)}))
  {(Close (bajra $w))})
```

— the shape the library's `Exactly n` (§12) realizes. Two things about
this reading. **Exactness attaches to the selected witness**: its units
number exactly three under the `gerku` basis (`CardBasis`, §4.8), and
nothing is said about dogs outside it, so a fourth runner does not
falsify the sentence. **The nuclear predication is neutral** (P4): the
claim is of the witness plurality, and how the dogs satisfy `bajra` —
severally here, since running is lexically distributive-capable, but
jointly for `ci prenu cu jmaji`, where only the three *together*
gather — is the predicate's lexical business; the each-reading is the
marked `Distrib`/`lu'a` form, never an operator smuggled in by the
quantifier. The **global** exact reading — "the dog-runners number
exactly three, and no others" —

```lisp
; the marked global strengthening (not the bare-PA default)
(= (Card (SetOf (λ {$x :: Entity} {(∧ (gerku $x) (bajra $x))}))) 3)
```

is a distinct, stronger meaning, named `GlobalExactly` in the library and
available where a reading commits to it. CLL ch. 16 §6's own account of
bare numeric quantification is both global ("exactly two things, no more
or less", Example 16.34) and singular-variable — "`PA broda` … is
shorthand for `PA da poi broda`" (16.6), which distributes; pin P17
records, as one documented divergence with its argument, that this
specification takes neutral witness-set selection as the default — the
reading dominant in xorlo-era usage, the one that composes with witness
export (§5.6) and termsets, and the only one under which collective
predicates remain expressible beneath quantifiers at all (`su'o prenu cu
jmaji`).

## 5. Dynamics

### 5.1 Model theory

A model supplies a set of worlds W, sorted domains, world-indexed lexical
interpretations, and **information states**: sets of world–assignment
pairs. The dynamic layer is one algebraic computation type. Its carrier:

```text
Comp<A>    =  InformationState → P( InformationState × A × Obligations )
Content    =  Comp<Unit>          RefComp<T> = Comp<T>
Discourse  =  Comp<Unit> at the performance level (its effect
              vocabulary adds commitment/performance operations);
              Act<F> is NOT a computation — it is the pure
              force-tagged package of §7.1, entering this carrier
              only through Perform
bind       :  Comp<A> × (A → Comp<B>) → Comp<B>   (the carrier's
              sequencing operation — the surface `Bind` word, §5.2/§7.7,
              is its telescope-spelled face)
```

where `Obligations` collects the pending projective commitments
(presupposition conditions, supplement sides with their anchors and
handlers) accumulated but not yet discharged, and information states
additionally carry the discourse-segment structure (the current
segment and the suspended-topic stack) that keyed retrieval (§5.3)
and the §7.2 transitions consult. A computation, run on a
state, yields the possible output states (nondeterminism carries plural
and witness selection — success of *some* branch is success), each with
a returned value and its obligations; lexical truth at a world filters
states; assignment extension is referent introduction; `bind` sequences,
threading state and unioning obligations. `Vague` parameters are **not**
this nondeterminism: a term with `Vague` parameters denotes the *family*
of computations indexed by admissible precisification profiles (§6.5,
VC2–VC3) — formally, the denotation function is profile-indexed,
⟦t⟧π : Comp, with π assigning one admissible precisification to each
`Vague` site (VC3's consistency), and the unindexed ⟦t⟧ abbreviating
the π-family — and truth simpliciter, where invoked, is supertruth
over the family — existential collapse of precisifications into branches would
make one admissible reading's success suffice, which VC1 forbids. Each named operation of this chapter (`Refer`,
`Context`, `Vague`, `Presuppose`, `Supplement`, the selections of §5.6,
the connectives' state-passing) is an operation of this algebra, and its
clause consists of two parts with two homes: **what escapes and what is
accessible is stated once, in the accessibility table (§5.4)** — nothing
elsewhere may restate it — while return values, truth filtering, and
obligation discharge are fixed by the carrier above and the operation's
own paragraph.

The world index supports the intensional facts of §5.7 (de re/de dicto,
opacity) and the subordinated contents of §7.6; **no world variable or
world type appears in the term language**. Counterfactual and hypothetical
mood (`da'i`) is a registered gap (§14) whose future treatment will live
in this index.

**The utterance context** is a typed record:

```text
ctx = ⟨ speaker  : Referents<Entity>,   audience : Referents<Entity>,
        time     : Time,                place    : Location,
        ground   : Ground ⟩

Speaker, Audience : ctx → Referents<Entity>
Now : ctx → Time            Here : ctx → Location
Proximity          = Proximal | Medial | Distal   (a closed type)
GroundDescription  : the sort of ground specifications (an orientation
                     center with its perspective facts; `Ground` values
                     are constructed from them)
Deictic       : Proximity × Ground → Referents<Entity>
ShiftedGround : GroundDescription → Ground        (constructs — §6.1)
InContext     : Content × Ground → Content
```

Demonstratives (`This`/`That`/`Yonder`, i.e. `ti`/`ta`/`tu`) are
`Deictic` at the three proximities against the context's ground:
`This ≝ (Deictic Proximal g)`, `That ≝ (Deictic Medial g)`,
`Yonder ≝ (Deictic Distal g)`, with `g` the `ctx` record's ground.
`ShiftedGround` **constructs** a ground (never a contextual resolution),
and `InContext` evaluates content with deictic projections taken from the
given ground — the explicit form of context shift (`ra'o`; §11).
`InContext` shifts the *utterance* context only; shifting the *evaluation
world* (hypothetical mood) would be a sibling index-shift operator —
`InContext` is currently the sole member of that family — and awaits the
`da'i` gap entry (§14).

### 5.2 Effectful binding

`(Bind {$x :: T} comp {body})` runs the computation `comp : RefComp<T>` and
binds its result for `body`, sequencing effects left to right. (As a
word, `Bind` is the alias of `MakeBind`, §7.7, which expands to the
carrier operation `bind` of §5.1 over `MakeLambda`; this section states
the semantics that expansion delivers.) The sequencing is
the eliminator for `RefComp` and cannot be β-reduced away: the computation
may introduce referents, consult context, or project obligations. `Let`
(§4.4) is its pure degenerate case. A multi-binding
`(Bind {$x₁ :: T₁} c₁ {$x₂ :: T₂} c₂ … {body})` is left-to-right nesting —
`(Bind {$x₁ :: T₁} c₁ {(Bind {$x₂ :: T₂} c₂ {…})})` — so later computations
may consume earlier results. The honest gloss: `Bind` is
function application under mandatory call-by-value at computation
types, made visible — the λ-fragment stays pure so that β-equality
holds unconditionally, and every effect-sequencing point is a `Bind`
node the accessibility table can see (rationale §1.14).

`Bind` is **uniform across the computation categories**: `Discourse`
denotes in the same carrier as `Content` (§5.1 — its effects include
performance and commitment), so `body` may be `Content`, a reference
computation, or a discourse, and the binding scopes the referent over
the whole body either way. An act is a pure *value* (§7.1), not a
computation: a bare act written as a `Bind` body stands, by §7.1's
display coercion, for the one-act discourse performing it, and a
computation that returns an act package as a value is typed
`RefComp<Act F>` like any other value-returning computation. This is
what lets a description or
selection introduced before an act sequence remain bound across it
(`(Bind {$x :: Referents T} (Refer P) {(Do a₁ a₂)})` — the ordinary
spelling of
cross-sentence reference).

### 5.3 The specificity triad

Three primitive computations answer §1.4:

- `(Refer P) : RefComp<Referents<T>>`, for `P` a property of references —
  introduces a **new discourse referent**: a nonempty, number-neutral
  plurality satisfying `P` veridically, fixed for its force segment, and
  accessible to later anaphora per §5.4. This is the xorlo semantics of
  descriptions (ruling P1): no implicit outer quantifier, no uniqueness,
  no default cardinality.
- `(Context deps…) : RefComp<T>` — retrieves a contextually salient value
  of type `T`, constrained by an optional property and by its declared
  dependencies (binders the choice may covary with). It asserts nothing
  and introduces nothing. **Site/key identity:** each syntactic occurrence
  is one site; a site retrieves once per performance, so re-applications
  of a shared λ reuse the site's value; keyed uses (unassigned KOhA,
  ruling P16) retrieve once per key per discourse segment, every
  occurrence of the key consuming the same value.
- `(Vague P) : RefComp<T>` — denotes the nonempty set of **admissible
  precisifications** of type `T` satisfying the constraint `P`, with no
  fact of the matter selecting one. Composition law: precisification sets
  lift pointwise through all operators, and a complete interpretation
  chooses one precisification per parameter per binding site,
  consistently; truth simpliciter, where needed, is supertruth over
  admissible choices. The term never chooses.

### 5.4 The accessibility table

The table below is normative: it states, per operator, what each operand's
computation may see and what survives the whole. "Introductions" are
discourse referents from `Refer`, quantifier witnesses (§5.6), and token
binders (§7.4).

| Form | Dynamic rule |
|---|---|
| `∧`, `Do` | Left to right; each operand sees all preceding successful introductions; introductions of both survive. Facet conjunctions over a shared event (tense/modal joining, §11) are ordinary `∧`. |
| `∨` | Operands each see the incoming state; branch-local introductions do not escape the disjunction. |
| `¬` | Operand sees the incoming state; nothing escapes. |
| `→` | Antecedent sees the incoming state; consequent sees the antecedent's successful introductions; nothing escapes the conditional. Donkey normalization (§5.6) applies when a consequent anaphor binds an antecedent introduction. |
| `↔`, `⊕` | Each operand evaluated exactly once against the incoming state; nothing escapes. (Hence primitive: rewrites would duplicate evaluation.) |
| `∃`, `∀`, GQs | The restrictor is pure (`Fn`); body introductions are local to each instantiation. **Witness export:** a successful evaluation of an exporting quantifier introduces its witness referent(s) — see §5.6, including the dependent case. |
| `Refer` | Introduces its referent into the current force segment; fixed there (no re-selection under `¬` or across facets). |
| `Presuppose` | See §5.5: the condition projects to the nearest legal commitment boundary; the at-issue operand sees the incoming state. Introductions inside the condition are local to the condition check; nothing escapes from it. |
| `Supplement` | See §5.5: side content is committed once at its handler, projectively; the at-issue operand's value passes through. |
| Force constructors, `Perform` | Act boundaries close force segments: referents introduced inside a constructed-but-unperformed act are not accessible outside it; performed acts in `Do` chain normally. |
| Quotation, `Reify` | Opaque at construction: nothing crosses a sign boundary, and `Reify` runs nothing — no introduction, retrieval, or obligation occurs at the reification site. `Holds` (§9.1) evaluates the represented content at its own occurrence site, and what escapes *that* evaluation is governed by the operators around the `Holds`, exactly as for any content — never retroactively by the `Reify` site. |

### 5.5 Projective content

`(Presuppose π body)` imposes `π` as a projective condition: it must hold
at the nearest boundary that can commit it (accommodating contexts may add
it), and it survives `¬`, `∨`, `→`, and question force. Its type is
polymorphic over the computation categories —
`Presuppose : Content × Comp<A> → Comp<A>`: the condition is content,
the body any computation (§12's `MaxRefer` uses it at a reference
computation). It is the mechanism of quantifier import (ruling P2), definedness of partial
operations (§1.7), and lexically triggered presuppositions.

`(Supplement anchor side body)` contributes `side` as a **non-at-issue
commitment about `anchor`** while the at-issue value is `body`'s. The side
commitment projects: under negation only `body` is negated, under question
force only `body` is questioned. A supplement whose `side` depends on a
quantifier-bound variable attaches at a handler inside that binder —
committed per instantiation, projective to that scope's top (ruling P7).
`noi`, parentheticals (`sei`, `to…toi`), and non-restrictive material
generally land here. Presuppositions may be satisfied or accommodated;
supplements are always new commitments — the two are not interchangeable.

### 5.6 Quantifier witnesses, donkey configurations, anaphora

**Selections and witness export.** Quantified terms whose witnesses can
be referred back to are built from **selection computations** — the
quantifier-strength members of the `Refer` family:

```text
SelectExactly n P : RefComp<Referents<T>>   ; an n-unit witness set of P
SelectAtLeast n P : RefComp<Referents<T>>   ; ditto, at least n
SelectSome P      ≝ SelectAtLeast 1 P       ; ≥ 1 (su'o) — defined
```

(restrictor `P` pure). The witness laws: a selection's witness `w`
satisfies `(Distrib P w)` and `(= (CardBasis w P) n)` (`SelectExactly`)
or `(≤ n (CardBasis w P))` (`SelectAtLeast`); and the **dependence
law**: under governing binders, a selection introduces one witness per
value of the governors (where `Refer` introduces a single
governor-invariant constant — the §5.6 boundary note below). A
selection introduces its witness reference —
explicitly bound by `Bind`, like every computation — and the nuclear
content then predicates of it:

```lisp
; ci gerku cu bajra .i ri tatpi
(Bind {$dogs :: Referents Entity}
        (SelectExactly 3 (λ {$x :: Entity} {(gerku $x)}))
  {(Do (Assert (Close (bajra $dogs)))
      (Assert (Close (tatpi $dogs))))})
```

The library's GQ forms (`Exactly`, `AtLeast`, `Some`, … — §12) are
defined over selections; forms whose success is grounded in absence or an
upper bound (`No`, `AtMost`, `FewerThan`) select nothing and export
nothing. `Every` exports the full restrictor reference. Binding a witness
never re-evaluates a selection; distinct selections introduce
**distinct discourse referents** (introduction identity — their
witness *values* may still co-refer); and a witness is accessible exactly where the accessibility
table lets its `Bind` scope reach (so nothing here is a free-variable
convention — the binder is visible in the term).

**Dependent witnesses.** A selection in the scope of a quantifier is a
*dependent* selection — one witness per value of each governing binder.
An anaphor binding a dependent witness from outside the governing scope
triggers joint-locus normalization (the donkey rule below, one level up):
the selection raises into a joint locus with its governor, both
restrictions form the antecedent (with the description quantifier's
import preserved — the `Presuppose` wrapper carries over), and the
anaphor's content joins the consequent — **conjoined with the governing
sentence's own assertion, which the normalization must not erase**: the
first sentence claimed the ownership, and a conditional alone would be
vacuously true of a dogless person. Fixture: `ro prenu cu ponse ci
gerku .i ri tatpi` normalizes to

```lisp
; one content, abbreviating the two performed assertions
(Presuppose (∃ (λ {$x :: Entity} {(prenu $x)}))
  (∧
    ; sentence 1's claim, preserved:
    (∀ (λ {$p :: Entity}
      {(→ (prenu $p)
         (∃ (λ {$d :: Referents Entity}
           {(∧ (Distrib (λ {$x :: Entity} {(gerku $x)}) $d)
              (= (CardBasis $d (λ {$x :: Entity} {(gerku $x)})) 3)
              (Close (ponse $p $d)))})))}))
    ; the anaphoric continuation, at the joint locus (strong reading):
    (∀ (λ {{$p :: Entity} {$d :: Referents Entity}}
      {(→ (∧ (prenu $p)
            (Distrib (λ {$x :: Entity} {(gerku $x)}) $d)
            (= (CardBasis $d (λ {$x :: Entity} {(gerku $x)})) 3)
            (Close (ponse $p $d)))
         (Close (tatpi $d)))}))))
```

— each person owns three dogs, and each person's dogs are tired; no
single plural of all dogs is asserted,
and the summation reading is expressible only by explicit collection,
never automatic. Two boundary notes: an embedded xorlo *description*
(`ro prenu cu bevri lo pipno`) is a referential constant shared across the
governor's values, not a dependent witness — only genuinely
quantificational selections depend; and anaphora to a witness that does
not escape its governor is simply inaccessible — a reading the table
correctly refuses.

**Donkey normalization** (ruling P6). When an anaphor binds an
introduction made inside a restrictor (`ro prenu poi ponse su'o xasli cu
darxi ri`), the reading normalizes to the governing quantifier's joint
multi-parameter locus, with the description's import preserved and the
indefinite's variable at the plural type (its witness is a plural
reference; the atomic-pair spelling is the distributive strengthening):

```lisp
(Presuppose (∃ (λ {$x :: Entity} {(∧ (prenu $x)
              (∃ (λ {$y :: Entity} {(∧ (xasli $y) (Close (ponse $x $y)))})))}))
  (∀ (λ {{$p :: Entity} {$d :: Referents Entity}}
    {(→ (∧ (prenu $p)
          (Distrib (λ {$z :: Entity} {(xasli $z)}) $d)
          (Close (ponse $p $d)))
       (Close (darxi $p $d)))})))
```

(The `Distrib` conjunct restores the indefinite selection's own
witness law — the joint locus quantifies exactly the donkey-witness
pluralities, not references with non-donkey residue.) The
restrictor's relational conjunct ties the parameters; no E-type
description or choice function is invoked. Bare mathematical `ro da`
normalizes without the `Presuppose` — the import belongs to description
quantifiers only (pin P2). Configurations beyond the supported fragment
(anaphora out of disjunctive restrictors, stacked indefinites with split
anaphora) are gap-registered.

**Anaphora generally** (ruling P16): the calculus sees bindings. `ri`,
`ra`, `ru`, `vo'a`-series, `ke'a`, and `go'i`-family resolution — CLL
ch. 7's counting discipline applied over the *accessible* referents of
this chapter — are text-to-reading rules in the mapping annex. `goi`
assignment is discourse-scoped binding; an unassigned KOhA is a keyed
`Context` (one retrieval per key, §5.3).

### 5.7 De re, de dicto, opacity

A lexical place is marked in the lexicon as extensional, intensional, or
opaque (§10). Reference placement does the rest: a `Refer` bound inside an
intensional argument is de dicto (evaluated at the attitude's worlds); a
binder placed outside is de re; opaque places (quotation-like) admit no
external binding at all. `mi djica lo nu mi pilno lo karce` receives both
readings by binder placement alone; no world variables appear (§5.1). The
lexicon's marks plus the world-indexed model are jointly what make the
distinction denotational rather than merely structural.

### 5.8 Genericity

`(Generic mode holder? restrictor nuclear) : Content`, with
`mode ∈ ⟨Typical, Stereotypical⟩` and `holder` present exactly for the
stereotype reading (`le'e`: the Speaker, grammatically fixed), is the
axiomatic generic quantifier — restrictor `Fn<(T), Content>` and
nuclear scope `EFn<(T), Content>`, both member-level like the library
GQ restrictors (§12): it relates the pure restrictor and nuclear
scope through a normality ordering **that may depend on the nuclear
predicate**. It is not `∀`, not `∃`, and yields no referent: `lo'e cinfo
cu se kerfa lo clani` and `lo'e cinfo cu jbena lo cinfo` are supported by
different normality classes (adult males; adult females), which is why no
fixed "typical lion" reference exists to verify both. Generic anaphora
(`lo'e mlatu … .i ri …`) is gap-registered. The operator is frankly
axiomatic — its normality structure is constrained, not defined; the
rationale records why this honesty beats both a fixed-prototype reference
and a silent lexical relation.

## 6. Explicit vagueness

### 6.1 The recovery test and the classification

The decision rule for §5.3's triad, applied to every underspecified
construct in Lojban:

> **The recovery test.** If a cooperative hearer is expected to arrive at
> a *specific* value — and communication fails when they cannot — the
> construct is `Context`. If the speaker waives specificity, so that
> recovery yields at most an admissible family with no fact of the matter
> selecting a member, it is `Vague`. If the meaning simply lacks the
> dimension, it is **absence** (§1.4) and gets no machinery at all.

The normative classification:

| Construct | Class | Notes |
|---|---|---|
| omitted places, `zo'e` | `Context` | one distinct site per omission (P15) |
| `co'e` (elliptical selbri), `do'e` (elliptical tag) | `Context` | the ellipsis family expects recovery; a deliberately waiving use is written with explicit `Vague` |
| `zu'i` | `Context` | with a typicality constraint |
| deictic grounds; demonstrative grounds | `Context` | `ShiftedGround` values are constructed, never resolved |
| scale **dimension** of gradable/scalar predication | `Context` | which scale (beauty, price, speed) is recoverable |
| soritical **cutoffs/regions** on a scale | `Vague` | includes `no'e`'s neutral-region width, riding a `Context` scale |
| tanru modification link | `Vague` | CLL ch. 5's constitutive vagueness; the library's named link values (manner, material, purpose, …) are precisification constants a resolved reading may commit to |
| `tu'a` | `Vague` | admissible values are abstractions of some content (`∃c,k. a = the abstraction of c under k`) bearing `srana`-aboutness to the operand; the abstraction-shape conjunct is required — aboutness alone is too weak |
| `joi`'s connecting relation; mixture kind | `Vague` | the exact non-logical connectives (`jo'u`, `ce`, `ce'o`, `fa'u`, `ku'a`, `jo'e`, `pi'u`) are exact |
| vague-quantity thresholds (`so'i`, `so'e`, …; `ji'i` tolerance) | `Vague` | sorites: no fact fixes the boundary |
| `du'e` / `mo'a` / `rau` | `Vague` threshold **constrained by** a `Context` standard/purpose | two parameters; the purpose is recoverable, the boundary is not |
| `na'i`'s defect dimension | `Context` | the hearer is expected to see what is defective |
| bare `jai` (no tag) | `Vague` | raises a participant out of the abstraction filling the host's x1 (the abstraction moves to `fai`); *which role* the raised argument plays there is the vague dimension — `tu'a`'s raising inverted (CLL 9.12, 11.10); `jai`+tag specifies the role and is exact (library expansion) |
| bare-`kau` exhaustivity; unmarked distributivity | **absence** | no hole, no parameter (P9, P4) |
| tenselessness | reading-multiple (P8) | episodic readings carry a `Context` time; habitual/gnomic readings carry nothing; never a default — the reading is chosen upstream |

### 6.2 Tanru

`(Tanru M H) : PredTerm<ρ(H)>` — modification of head `H` by modifier
`M`; a **defined** operator, the expansion below being its definition
(only `TanruAdmissible` inside it is primitive).
The result's row is the head's row (CLL ch. 5: the tanru's places are the
tertau's). Its semantics: the head predication holds, and an admissible
modification link relates `M` to that predication —

```lisp
((Tanru M H) fills…) ≝
(Bind {$link :: PredTerm ρ(H)}
        (Vague (λ {$r :: PredTerm ρ(H)} {(TanruAdmissible M H $r)}))
  {(∧ (H fills…) ($link fills…))})
```

`TanruAdmissible` is part of tanru's meaning, not a lookup: it requires
that the link make `M` modify *something* in the head predication (the
event's manner, a participant, a purpose, a source, …) and nothing
stronger — no x1-sharing, no intersectivity. The library's named links are
the common precisifications; a lujvo is a lexicalized precisification.

Surface grouping (`bo`, `ke…ke'e`) and inversion (`co`) are ⊳
text-to-reading: `A co B` ≡ `ke B ke'e A`, with any trailing sumti
routed to the seltau's places as `be`-fills — hence invisible to
`vo'a`/`go'i`, which see only bridi places (CLL 5.8); multiple `co`
right-group. Jek-connected units lower through `TanruLinkConnect`
(§12, pin P33).

The gismu `tanru` is this operator's shadow relation (§16.5), and an
exact one: its official x4 ("giving meaning ⟨4⟩") and x5 ("in
usage/instance ⟨5⟩") places state precisely this occasion-relative
resolution, with operand places officially typed "both text or both
si'o concept" — inert operands in the program's sense (§16.2).

### 6.3 Scalar operators

`(Scalar k P)`, `k ∈ ⟨OtherThan, Opposite, Neutral⟩`, is the `na'e`/
`to'e`/`no'e` family: an operation on `P` relative to a scale or
admissible-alternative set. The scale dimension is `Context` (lexically
fixed when the dictionary provides one); soritical region boundaries are
`Vague` per §6.1. Each operator **denies `P`'s stated region and
positively asserts an alternative** — CLL 15.4: a selbri negation
"asserts that a relationship exists other than that stated", and "the
result of `na'e` negation remains an assertion of some specific truth" —
so all three entail `¬P` at the stated region, differing in the region
asserted: `OtherThan` some admissible alternative (chosen `Vague`-ly
within the scale/set), `Opposite` the antipodal region, `Neutral` the
midpoint region (excluding both extremes). Scalar negation is therefore
*stronger* than `¬`, not weaker: `ta na'e melbi` denies beauty and
asserts a contextually admissible alternative aesthetic standing. The
`Opposite` operator doubles as the documented fallback for indicator
polarity where the lexicon names no `nai`-pole (§7.6; CLL 15.7 applies
scalar negation's opposite-end rule to indicators).

### 6.4 Gradable predication and vague quantities

Gradable predication exposes its two parameters through the library's
`Grade` schema:

```text
Grade : GradableRel<ρ,ℓ> × Scale × Region<Scale> → PredTerm<ρ>
```

with the scale obtained by `Context` when not lexical (which dimension —
size, price, beauty — is recoverable) and the region boundary by `Vague`
(no fact fixes the cutoff). `ta barda` is `Grade(barda, Context-scale,
Vague-region)` applied; the `na'e` family (§6.3) operates on the same
scale value.

The degree quantifiers (`Many`, `Few`, `TooMany`, `TooFew`, `Enough`,
`Most`; §12) are cardinal comparisons against thresholds whose
admissibility predicates are declared with them (§12), each with an
axiomatic nonemptiness clause discharging VC1: the threshold is `Vague`,
and for the purpose-relative kinds (`du'e`/`mo'a`/`rau`) it is
constrained by a `Context`-recovered standard/purpose. The
region-admissibility predicate for gradables (`AdmissibleCutoff`, §12)
carries the same nonemptiness clause. `ji'i n` is `Vague` tolerance about
a stated `n` — a different shape from `so'i`'s vague threshold. None of
these rounds to an exact number, and none fails: `so'i prenu cu klama`
has exactly the truth conditions its vagueness permits — the family of
readings over admissible thresholds (§5.3, §6.5).

### 6.5 The composition law for `Vague`

Normative, and complete — no operator interacts with precisification sets
in any way not stated here:

- **VC1 (Denotation).** A `Vague` computation denotes the nonempty set of
  its admissible precisifications and no choice among them; a reading
  containing a `Vague` parameter denotes the family of precisified
  readings. Nonemptiness is a **static proof obligation of the formation
  judgment**: `(Vague P)` is well-formed at `A` only under a discharged
  judgment `⊢ ∃a:A. P(a)` — supplied by the construct's definition (the
  library's admissibility predicates are defined nonempty) or by the
  mapping when it introduces the parameter; an empty admissibility set is
  thereby a failure to form the term, never an evaluation outcome.
- **VC2 (Pointwise lifting).** Every operator — application, `Bind`, the
  logical operators, quantifiers, force constructors, question formers,
  abstraction crossings — lifts pointwise over precisification sets.
  `na so'i prenu cu klama` denotes the family, over admissible thresholds
  t, of "not more than t people go"; an act built from vague content is a
  family of acts; a question over a vague domain ranges over precisified
  alternatives.
- **VC3 (Consistency).** One precisification per parameter per binding
  site: occurrences of one parameter under one binder take the same
  precisification; occurrences under distinct binders are independent;
  distinct parameters are independent unless identity is expressed. (The
  `Vague` analogue of `Context`'s site/key identity, §5.3 — the spec
  states them adjacently on purpose.)
- **VC4 (Effects ride the lift).** Presupposition triggers and supplement
  sides emitted under a `Vague` parameter lift pointwise with their
  content; handler placement is a fact about term structure, never about
  the precisification choice.
- **VC5 (No resolution).** A `Vague` parameter is never resolved by
  `Context` and never coerced inside the core. A reading that commits to
  a precisification says so explicitly, with a library precisification
  constant or an exact value — and the commitment must itself pass the
  recovery test. Absence of commitment is `Vague`; absence of the
  dimension is nothing at all (§1.4); the two are never conflated.

## 7. Speech acts and discourse

### 7.1 Acts and forces

Force constructors turn content into first-class acts:

```text
Assert  : Content → Act<Assertion>      Ask      : Query<A> → Act<Question>
Command : Referents<Entity> × Content → Act<Directive>
Express : Content → Act<Expressive>     Vocative : Referents<Entity> → Act<Address>
Mention : T → Act<Expressive>           (use/mention: displays a value)
```

Constructing an act does not perform it. The typing discipline:

```text
Perform : Act<F> → Discourse
Do      : Discourse × Discourse × … → Discourse   (flattening, associative)
```

Denotationally, an `Act<F>` value is a **force-tagged content package**:
the force `F` together with the content computation (for `Ask`, the
query; for `Command`/`Vocative`, the addressee too), constructed
inertly — building it runs nothing. `Perform` injects the package into
the performance level: the content's computation runs there with `F`'s
commitment effects (assertion commits, question raises, and so on). Act
identity is term identity — acts compared, quoted, or anaphorically
targeted are the `Let`-bound values the terms visibly share.

A document denotes one `Discourse`, whose top-level `Do` sequence is
called the **spine**; an `Act` written directly in a `Do` operand —
or anywhere a `Discourse` is required, a `Bind` body included — is
notation for its `Perform` (the coercion is notational, §2, never
semantic), and a specimen displayed as a bare act denotes the one-act
discourse performing it. `Do` sequences with the `∧`-row's accessibility. `Discourse`
never embeds where `Content` is required — in particular never under
`Reify`. Reported speech mentions constructed acts (`mi cusku lu ko klama
li'u` describes a directive without issuing it); only `Perform` executes.

### 7.2 Discourse structure

`NewTopic, Resume : Discourse → Discourse` are the `ni'o`/`no'i`
transitions — discourse-structural operations with no truth
conditions but with stated effects on the **segment structure** the
information state carries (§5.1): a state holds the current discourse
segment and a stack of suspended ones. `NewTopic` suspends the
current segment onto the stack and opens a fresh one — keyed
`Context` retrievals (§5.3) are per-segment, so keys re-retrieve
after it, and the segment-bounded ⊳ rules (`ki` stickiness, `go'i`
reach) reset — while `Resume` pops the most recently suspended
segment and reopens it for keyed retrieval. NIhO depth grades the
reset (CLL 19.3): the assignment-clearing level — `ni'o` spoken,
`ni'o ni'o` written — clears the resolver's assignment stores with
the new segment (the ⊳ face of `da'o`), and the next level up
(CLL's "drastic change") additionally resets tenses and indicators;
further depth marks larger topic scale only. `no'i` resumes what its
`ni'o` dropped — assignments and, at the drastic level, tense — along
with the suspended segment. The spoken/written level shift is ⊳
text-to-reading. Discourse
*relations* (contrast `ku'i`, addition `ji'a`, parallel `si'a`,
elaboration `no'u`, …) are library relations over acts; the prior act is
an ordinary `Let`-bound value in `Do` (no prior/following-discourse
constants exist). Constituent-level additive/exclusive focus (`ji'a` on a
sumti, `po'o`) derives via `Presuppose` over alternatives (§12).

### 7.3 Metalinguistic rejection

`na'i` is a derived discourse act: an objection targeting a prior
utterance or act, predicating a defect whose dimension is a `Context`
parameter (§6.1), with the objected content not performed. It is neither
`¬` (no truth-conditional negation occurs) nor `Scalar` (no scale is
invoked); the three-way `na`/`na'e`/`na'i` contrast is thereby three
different operators.

### 7.4 Utterance tokens

`(Utterance {$u :: UtteranceToken} {fact…})` is the **transcript-entry
notation**: a token variable with facts about it — ordinary
predicates: `SpeakerOf`, `AudienceOf`, `LocutionOf`, `DeicticTimeOf`,
`DeicticPlaceOf`, `TextOf`, `Realizes` (the token realizes an act
value of whatever force — the force index is existential here),
`Utters` (agent utters token). It is **defined**, and its definition
is a λ, not a computation:

```lisp
(Utterance {$u :: UtteranceToken} {fact…})
  ≝ (λ {$u :: Referents UtteranceToken} {(∧ fact…)})
```

(The entry notation ascribes the token *sort*; the definition binds at
the singleton-lifted reference type, §3.2 — specimens keep the sort
spelling.) Two **declared partial projections** serve utterance
anaphora (§11):

```text
RealizedAct<F> : Referents<UtteranceToken> ⇀ Act<F>
   ; the act the selected token/span realizes — defined (projectively,
   ; §5.5) where the span realizes exactly one act, of force F: the
   ; force partiality lives HERE.
RealizedDiscourse : Referents<UtteranceToken> ⇀ Discourse
   ; the sibling for spans realizing act sequences.
ActContent : Act<Assertion> → Content
   ; total at its assertion-indexed domain: the content the
   ; constructor packaged (no evaluation; the access InterpretContent
   ; already exercises for signs).
```

— a *pure token-description property*. The λ suspends the facts by
nature (nothing is performed, nothing introduced — quoted material
introduces no discourse referents), and `StructuredQuote` (§7.5)
consumes exactly this property type, supplying the sign boundary's
opacity itself: the primitivity in this neighborhood belongs to the
sign constructors, not to the entry notation. (A `Bind`/`Refer`
spelling, by contrast, would be a computation — the wrong category
for a value behind an opaque boundary.) What likewise needs no
special form is performed-level token talk: asserting facts about an
utterance token in open discourse is ordinary reference introduction
at the token sort. The `Sign` entry notation of §7.5 is the same
defined λ at the sign-token sort. Transcript entries carry unperformed
acts.

### 7.5 Signs and quotation

`Sign<K>` classifies signs by kind `K` (Name, Sentence, Word, Letteral,
Quotation, MathExpression, Structured, Opaque, Text, Connective — and
`Expression` and `Telescope`, the elaborated-core-notation kinds whose
term-language semantics is §7.7, with the program consequences in
§16.3).
Constructors: `(OpaqueQuote text)` (`lo'u…le'u`, `zoi`),
`(StructuredQuote entry)` (`lu…li'u` — the operand a pure
token-description property, §7.4; the constructor supplies the opaque
boundary),
`(NameSign text)`, `(SentenceSign content)`, `(LetteralSign text)`,
`(WordSign text)`. `(Sign {$s :: SignToken K} {fact…})` describes sign
tokens with facts (`TextOf`, `Quotes`, `Denotes`) — the §7.4 defined
entry notation at the sign-token sort. Interpretation is explicit and
typed: `(InterpretContent sign) : Content` and the force-indexed
partial family `InterpretAct<F> : Sign<K> → Act<F>` — defined exactly
when the sign's realized (or intended) act has force `F`, since a
sign does not carry its force — the `la'e` crossings; `lu'e` is the inverse sign-of crossing.
On a transcript entry (a structured quote whose token realizes an act),
`InterpretAct` yields that act, and `InterpretContent` is defined
exactly when the realized act is an assertion, yielding its content —
the content projection; other forces have no content projection and
interpret only as acts. Quotation boundaries are opaque to dynamics
(§5.4).

### 7.6 Indicators: attitudes, evidentials, discursives

Indicators (UI) are **lexical relations in the displayed-content family**,
not generated wrappers. (The specimens' placeholder names for these
relations — `Happiness`, `Unhappiness`, `Desire`, `EvidentialBasis` —
are §16 placeholders like any other PascalCase name; the audit maps
them to the `-nmo` indicator-emotion family, §16.5.) Display has two
spellings, by the level of its
target — no dedicated operator is needed:

- **Act-level** (the target is a performed act — the top-level case): the
  display is an `Express` act beside the host on the discourse spine,
  its content the indicator relation applied to the bound host act:
  `(Do (Perform $a) (Express (Close (i-rel Speaker $a degree))))`.
  Expressive force is itself non-at-issue commitment, and the family
  **force clause** holds: an evidential displayed this way *grounds* the
  host act — a mode of commitment, not a second claim — and a host-force
  profile (below) may subordinate the host instead of performing it.
- **Content-level** (the target is embedded content, a referent, or a
  sign): the display is a `Supplement` whose anchor is the target's
  first-order object — for content, its reification — and whose side is
  the indicator predication of that object. The content occurs **once**,
  under a pure `Reify` shared by `Let`, and is evaluated through the
  primitive `Holds` (`Reify`'s inverse, §9.1):

  ```lisp
  (Let {$p :: Proposition} (Reify c)
    {(Supplement $p (Close (i-rel Speaker $p degree)) (Holds $p))})
  ```

  so anchor, side, and evaluated body all speak of the same content with
  the same contextual sites; the side projects per §5.5.

Targets are always bound terms or pure object-formers — never free
names. Each indicator's lexicon entry (§10) provides:

- its relation with typed roles — for attitudes: experiencer, a
  first-class **target** at the closed union type `Target` — a
  `Proposition` (content targets go through `Reify`), an act value, a
  plural reference, or a sign, with the mapping resolving which — and
  a **degree** place on the library's intensity scale, whose named
  regions are `Intense` (`cai`), `Strong` (`sai`), `Moderate`
  (unmarked), `Weak` (`ru'e`), and `Neutral` (`cu'i`);
- its **`nai`-pair**: `nai` selects the lexically paired polar indicator
  (`.uinai` is unhappiness, a named emotion — not "other than happy"), and
  all other modifiers compose over the *pair* in surface order — `.uinai
  cai` is intense unhappiness (degree selects the pair's scale region),
  `dai` shifts the pair's experiencer, `cu'i` selects the neutral region
  of whatever relation it reaches. CLL's own mechanism (13.4, 15.7,
  13.8) is polar: `nai` refers the indicator to the **opposite end of
  its scale**, and the pair lexeme is the lexicon *naming* that pole
  (`.uinai` = unhappiness). Where no pair is listed, the documented
  fallback is therefore `Scalar Opposite` over the relation — the
  antipode, exactly CLL's rule — and lexicon review prefers naming the
  pole. Every grammatical `nai` attachment thus has a denotation, by
  named pole or antipode, exhaustively and exclusively.
  The pair carries its own host-force profile, inheriting the entry's
  profile family where it declares none; `nai` never flips a host-force
  profile;
- its **host-force profile**: whether displaying it leaves the host
  content asserted (pure emotions: `.ui do klama` asserts the going and
  displays joy), **subordinated** (propositional attitudes, CLL 13.3:
  `.au mi sipna` displays a desire and does not assert sleeping — the
  content is evaluated at the attitude's worlds, §5.1), metalinguistically
  voided (`na'i`, §7.3), or performative (`ca'e`, COI greetings — the act
  is constituted by its performance);
- for **evidentials** (`za'a`, `ti'e`, `ka'u`, `se'o`, `ba'a`, `pe'i`,
  `ju'a`): the relation experiencer × target × basis-kind — the
  basis-kind values are the closed `BasisKind` enumeration declared
  with the family
  (`Observation`, `Hearsay`, `CulturalKnowledge`, `InternalExperience`,
  `Expectation`, `Opinion`, `BareAssertion`) — with the family
  force clause: when the target is the content of the enclosing performed
  act, the evidential **grounds that act** — the basis of asserting or of
  asking, a mode of commitment, not a second at-issue claim; at embedded
  targets (`mi jinvi lo du'u ti'e do klama`) it displays the speaker's
  basis for the local content. `Assert`-with-basis spellings are library
  sugar for the top-level case.

`dai` shifts the experiencer role; `pei` forms an `OpenQ` over the
attitude or degree; `ba'e` is sign-level focus. Indicator target selection
is a text-to-reading rule (mapping annex; `FUhE`/`FUhO` delimit extended
scope).

### 7.7 Core reflection

The core can quote its own notation. This section is the term-language
semantics of that ability; the content-word consequences live in §16.

**Types.** `Expression<Γ, A, ε>` is the indexed refinement of the
`Expression` sign kind (`Expression<Γ, A, ε> <: Sign<Expression>`,
§7.5): **elaborated, scoped core expressions** — α-equivalence classes
of core syntax with resolved binding (Harper's abstract binding trees,
analogically; the context-indexed code type is Contextual Modal Type
Theory's `[Γ ⊢ A]`, likewise analogically — this core inherits neither
system's metatheorems, notably rejecting anti-quotation) — **open in
exactly the typed context Γ**, of result type `A`, with effect class
ε ∈ ⟨`Pure`, `Effectful`⟩ deciding whether an abstraction over the
code is `Fn` or `EFn` (write `Arrow_Pure = Fn`,
`Arrow_Effectful = EFn`). `Telescope<Γ; Δ>` is the quoted
binder-extension category (`{$x :: T}`, concatenated
`{{$x :: T} {$y :: S} …}`), the indexed refinement of
the `Telescope` sign kind. Both are formed only by writing braces —
quote formation is a typing judgment over already-elaborated notation,
applying after all text-to-reading resolution (readings, anaphora,
donkey normalization), never to raw Lojban text:
`{(Close (klama Speaker))}` is code; `lu mi klama li'u` is a
linguistic quotation sign (§7.5) — different kinds, never
interchangeable. Γ, `A`, and ε are derivable and elided in ordinary
notation. **The capture/open split fixes Γ**: a quote's free names
divide into those a consuming word's telescope operand designates as
open — exactly Γ, bound later through interpretation — and all others,
which must be bound at the write site and are **captured**: a quote
literal forms its value where it is evaluated, packaging the code with
the values its captured variables then have (binding *resolution* is
fixed at elaboration, S8 below; value *capture* happens when the
literal's position is evaluated — so a quote written under an outer λ
captures that λ's argument on each application). A bare quote consumed
by no telescope is closed: Γ = ∅. Constants never enter Γ and are
never captured — they are stage-schematic vocabulary.

**Elaboration discipline.** A quote is elaborated *at its written
occurrence*, against the lexical context it is written in — a quote is
code plus the context it was written under, and evaluation never
consults the evaluator's ambient context (the closure clause). Site
identities (`Context`/`Vague`, §5.3) are assigned at elaboration on
α-invariant, name-independent keys, so α-equivalent quotes have
identical site and dependency structure; two written occurrences of an
α-equal quote carry *distinct* site instances, while sharing one bound
`Expression` value shares one elaboration. Elaboration is **stable**
(law S8): an Expression's binding resolution, site identities, and
reading resolutions are fixed at its written occurrence; no later
evaluation re-elaborates or re-resolves. Notation desugaring (fills to
`At`, sugar expansion per S1–S7) happens at elaboration; β-reduction
does not — rewriting inside a quote changes which sign it is.

**Interpretation.** The typed, stage-indexed family
`Interpret : Expression<Γ, A, ε> × Env<Γ> ⇀ A` interprets code: the
captured part of the quote's environment rides inside the value, and
`Env<Γ>` — the typed record of values for exactly the open context Γ —
supplies the rest. For a closed quote (Γ = ∅) the environment operand
is empty and elided: `(Interpret {a})` is the stated elision of
`Interpret({a}, ⟨⟩)`. Evaluation never reads the evaluator's ambient
context — everything comes from the package or the typed operand.
Interpretation for stage-n code is a stage-(n+1) operation (the
staged shape of MetaML and of Davies–Pfenning's modal analysis,
analogically — the stage discipline is taken, their languages are not:
no anti-quotation, no cross-stage persistence, none of their
metatheorems inherited), there is
no untyped universal `Eval`, and **the family is bootstrap floor and
unreflectable** — no `MakeEval`, ever (a same-stage self-interpreter
is the liar row of §16.4). When `A` is a computation type,
interpretation *returns* the computation as a value; running it
remains the job of `Bind`, the dynamic operators, or `Perform`. Values cross stages only through
binding — an environment or an application supplies them — never
through splicing: **there is no anti-quotation** and no
`Persist : A → Expression`; reflection is schematic (code with
variables, values flowing in at use), which is the accepted price of
the discipline below.

**The no-reification discipline (D3).** In Wand's fexpr calculus,
contextual equivalence collapses to α-congruence — the theory of terms
is trivial. The design inference drawn here (motivating, not identical
to, the theorem): a language whose operators can observe the syntax of
ordinary operands forfeits its equational theory. The core stays on the right side of that cliff by
five clauses: (i) no operator turns a running value, continuation, or
evaluation state into an `Expression` — quotes are only ever written;
(ii) an unbraced (active) operand is consumed as its semantic value —
no word can request the caller's operand syntax or environment;
(iii) `Expression` values are **constructive-only**: no destructors, no
pattern-matching, no structural observation, and no `=` at the
`Expression` kind — code is built, composed, and interpreted, never
inspected; (iv) only the typed, staged `Interpret` family exists —
stage polymorphism of the vocabulary is a metalanguage schema, never an
object-language universal evaluator; (v) the transition to syntax is
always visible — braces in the source are the only place any word
receives code. This is the code-level twin of the refused truth-capture
reflection (rationale §1.5): no dynamic-to-static reflection, at the
truth level or the syntax level.

**The one primitive sign-function.** The kernel is already applicative —
its operators consume values — so exactly one word needs to consume
code:

```text
MakeLambda : Telescope<Γ; Δ> × Expression<Δ, B, ε> → Arrow_ε<(Δ), B>
```

(the body is *written* under ambient Γ, but its `Expression` index —
its open context — is exactly the Δ the telescope designates; the
ambient names are captured into the value, per the split above, and
never appear in the index; the telescope's own Γ index is different in
kind — a telescope means "in Γ, introduce Δ", recording its write site
for elaboration, and no environment ever feeds it).

Its clause: `(MakeLambda {Δ} {b})` — the telescope designates Δ as
`b`'s open part, ambient Γ being captured per the split above — is the
function that, applied to values `v̄` for Δ, is
`Interpret(b, ⟨Δ ↦ v̄⟩)` — the captured part of `b` rides in the quote
value, the arguments fill the open part. `λ` **is** `MakeLambda` — the
glyph is an alias (and, like every PascalCase name, `MakeLambda` is a
§16 placeholder awaiting its content word). Two further sign-functions
are **defined**, with `Bind` and `Let` their aliases:

```text
MakeLet  : Telescope<Γ; ($x:A)> × A × Expression<($x:A), B, ε> → B
(MakeLet {$x :: A} v {b})  ≝ ((MakeLambda {$x :: A} {b}) v)     ; v pure

MakeBind : Telescope<Γ; ($x:T)> × RefComp<T>
           × Expression<($x:T), C, ε> → C
    ; a schematic family, one member per computation-denoting term
    ; category C — Content, RefComp<S>, Act<F>, Discourse (§5.2)
(MakeBind {$x :: T} c {b}) ≝ (bind c (MakeLambda {$x :: T} {b}))
                      ; c consumed as a value; the result is itself a
                      ; computation — nothing runs at construction
```

where `bind` is the §5.1 carrier's sequencing operation (the model-
level `Comp<A> × (A → Comp<B>) → Comp<B>`): every category the family
ranges over denotes in that one carrier (§5.1), so the single carrier
equation defines every member uniformly. The continuation position
demands no
purity — ε is unconstrained in `MakeBind`'s signature, per §3.3's rule
that only comprehension, restrictors, and selections demand it. The
variadic `Bind` spelling nests per
§5.2. A reflective application spelling exists as a defined
form over the floor family —

```text
MakeApply : Expression<∅, Arrow_δ<(A), B>, ε₁> × Expression<∅, A, ε₂> → B
(MakeApply {f} {a}) ≝ ((Interpret {f}) (Interpret {a}))
```

closed quotes, each operand interpreted once (open code takes its
environment through `Interpret` directly) —
for contexts (notably the self-description program, §16) that need
application as a *word*; `(f a)` itself remains grammar. Facades for
the remaining operators follow one generic schema and are materialized
only on demand: for a binder-consuming operator, compose with
`MakeLambda` (`(MakeForall {Δ} {b}) ≝ (∀ (MakeLambda {Δ} {b}))`, and
likewise `MakeExists`, `MakeRefer`, `MakeSetOf`, `MakeOpenQ`, …); for
an ordinary operator `O`, `(MakeO {a₁} … {aₙ}) ≝
(O (Interpret {a₁}) … (Interpret {aₙ}))`, one interpretation per
operand, left to right. No facade exists for the sign constructors
(their operands are already inert by kind), for `Perform`'s host
commitment, or for `Interpret` itself.

**The reflection law.** Every binder form *is* its Make-word applied
to quotes — the aliases and definitions above — so the
term-expression grammar has
exactly three formers: atoms, braces, application (telescope contents
and the types after `::` carry the §2 subgrammar). For the derived
facades the law is stated once: each facade equals its definition,
with `≡` contextual equivalence at the result type, never equality of
signs. Each law preserves S1–S7: one interpretation per operand, sites mapped
one-to-one, no policy or typing change. One consequence is stated
rather than left to inference: evaluating one `Expression` value twice
runs its retrievals twice — a quote is code, and each run is a run;
site identity governs occurrences within one elaboration, not across
evaluations.

**Why this section exists** (the design's point, argued in the
rationale): with binding delegated to one sign-consuming word and the
term-expression grammar reduced to atoms, braces, and application,
every operator of
the core is a *nameable function* — a content-word candidate with
sign-typed places — and the same stage-schematic vocabulary lets one
text describe the stage below it, which is what makes a Lojban
description of Lojban's own semantics well-founded (§16; rationale).

## 8. Questions and answers

### 8.1 Query formation

`(Polar c) : Query<Bool>` (`Bool` the two-element answer type, §3.1);
`(OpenQ f) : Query<A>` for `f : EFn<(A…), Content>` — typed answer
domains, including tuples (`ma klama ma`), relation variables (`mo` — the
one-place row shown in samples is the common case; the general domain
quantifies over rows accepting the fill), place labels (`fi'a`, §4.7),
connectives and operators by domain enumeration, tags (`cu'e`), and
attitudes/bases (`pei`, `ju'apei`). `(Ask q)` makes the question act;
`(QuestionOf q) : Question` reifies a query as an embeddable
object — the path for question-*object*-selecting lexical places (a
`preti`-shadow object one can utter, translate, or repeat), distinct
from the `kau` answerhood path below, which builds a `Proposition`
through `Answer`.
(Embedded question objects in Lojban carry `kau` — `lo du'u ma kau
cortu`. A bare interrogative inside `du'u` is **not** an embedded
question: CLL 11.8 is explicit that "`ma` always signals a direct
question", so `mi djuno le du'u ma pu klama le zarci` means "Who is it
that I know goes to the store?" — the mapping gives bare interrogatives
utterance-level scope, turning the whole act into the question; only
`kau` builds the question object.)

### 8.2 Answers

`Answer : Query<A> × Selection<A> → Content` pairs a query with a
selection from its typed answer domain. The query formers are kept as
named primitives with denotation clauses rather than reduced to bare
function types — deliberately: spelling `(Polar c)` as a λ over `Bool`
would copy `c` textually into both branches (two contextual sites,
doubled handlers — the `↔` lesson of §4.5), and the named `Query` type
keeps question denotations a distinct, inspectable kind. The
denotations: a query is its
**answer-content function** — `(Polar c)` sends `Yes ↦ c` and
`No ↦ (¬ c)`; `(OpenQ f)` sends each domain tuple `a` to `(f a…)` —
and `Answer` applies it: `(Answer q (TupleAnswer a))` is the content
`q`'s function assigns to `a`, evaluated as ordinary content (its
dynamics are its operators'; nothing question-specific is added), and
`(Answer q (PolarAnswer s))` likewise at `Bool`. The `Exhaustive`
marker conjoins the completeness claim — every domain value whose
assigned content holds is among the selected tuple — and
`MentionSome` marks the weakest reading explicitly, adding nothing:
its content is that of the unmarked form, its value is the overt
contrast with `Exhaustive`. The `Selection<A>` family:
`(PolarAnswer Yes|No) : Selection<Bool>` and
`(TupleAnswer tuple [Exhaustive|MentionSome]) : Selection<A>` are the
base forms of the answer-selection family; `ContextualAnswer` — the
semantics of bare `kau` — is licensed only as `Answer`'s second
operand, and the *composite* is the defined form making the
contextual retrieval explicit:

```text
(Answer q ContextualAnswer) ≝                     ; open q : Query<A>
  (Bind {$a :: A} (Context) {(Answer q (TupleAnswer $a))})
(Answer q ContextualAnswer) ≝                     ; polar q : Query<Bool>
  (Bind {$a :: Bool} (Context) {(Answer q (PolarAnswer $a))})
```

— the retrieval is at the query's answer domain, and the selection
constructor follows that domain: `TupleAnswer` at open domains,
`PolarAnswer` at `Bool` (the `xu kau` case); no exhaustivity marker
either way (absence, per P9). `Answer` yields `Content` and
so embeds under `Reify` as any content does. **The exhaustivity operand is optional and its
absence is meaningful** (ruling P9): unmarked answerhood carries no
exhaustivity conjunct — truth-conditionally the weakest (mention-some-
compatible) reading — and strengthenings enter only by explicit marker or
lexically (an embedding predicate such as `djuno` may contribute its own
completeness presupposition through §5.5; it never rewrites the answer).
Lojban has no grammatical means to mark `kau` exhaustivity, so no `Vague`
parameter is posited: a decision point the language cannot express is
silence, not vagueness.

### 8.3 Place and relation questions

`fi'a` asks over the compatible-label refinement of `Label<ρ>`
(§4.7); `mo` binds a `PredTerm`-typed
variable; both are ordinary `OpenQ` at their domains. No dedicated
question machinery exists beyond typed domains.

## 9. Abstractions

### 9.1 One primitive bridge

`(Reify c) : Proposition` is the single primitive content-to-object
crossing — `du'u`. A proposition is a first-order object standing in a
representation relation to the content's intension; it is what `djuno`,
`krici`, `cusku` embed, quantify over, and identify. Its inverse is the
primitive `(Holds p) : Content` — the content the proposition object
represents — with the axiom pair that evaluating `(Holds (Reify c))`
is evaluating `c`, and `(= (Reify (Holds p)) p)` for every
proposition: each proposition represents exactly the content `Holds`
returns for it. The pair is the sole Proposition↔Content bridge (the
sign and event crossings — `SentenceSign`, `EventOfContent` — cross
to *other* sorts). The axiom pair speaks at evaluation: `Reify`
itself is inert — constructing the object runs nothing and introduces
nothing (the §5.4 opacity row) — while evaluating `(Holds p)` runs
the represented content at the `Holds` occurrence, its contextual
sites those fixed at the content's elaboration (§5.3) and its dynamic
escapes governed by the operators around the `Holds`.

**The bridge's shape generalizes** — a reservation, not a baseline
commitment. Nothing in the pair is special to the empty row: for any
row ρ one can posit a reified-predicate sort with its own
crossing pair and row-wise round-trip axiom, making `Proposition` the
row-⟨⟩ member of a family rather than a one-off (Chierchia & Turner's
nominalization pair, analogically) — this is what property *objects*
(referents for `lo ka` where discourse-referent behavior is wanted,
property anaphora, predicate quantification) would be. The baseline
defines only row ⟨⟩; the rest is a registered gap (§14). The
experimental cmavo pair `me'ei`/`me'au` (turn a selbri into an
abstract-predicate sumti; use such a sumti as a selbri of the
referent's arity) is the attested surface exponent of the two
directions. At the propositional case `me'au` is `Holds` in selbri
position, defined — like the numeric crossings of §9.2 — at the
reference type `lo du'u` actually yields, under a **singleton
condition** with singularity projective. The remark's precise shape:

```text
(Meau0 r) ≝
(Presuppose
  (∃ (λ {$p :: Proposition}
    {(∧ (CoRef r $p)
       (∀ (λ {$q :: Proposition} {(→ (CoRef r $q) (= $q $p))})))}))
  (∃ (λ {$p :: Proposition}
    {(∧ (CoRef r $p)
       (∀ (λ {$q :: Proposition} {(→ (CoRef r $q) (= $q $p))}))
       (Holds $p))})))
```

(the member `$p` singleton-lifts at the referential `CoRef`
positions, §3.2; the uniqueness conjunct makes the representative
single-valued outright — §4.8 deliberately assumes no atomicity, so
bare co-reference with *some* proposition would not by itself
guarantee one). For `abu` a singleton
reference to a prior `lo du'u c`, `(Meau0 abu)` is extensionally
`(Holds p)` at the sole member, so `me'au abu gi'a me'au by` is the
content-level disjunction of the two claims (contrast
`abu jetnu gi'a by jetnu`, two truth-predicate
claims *about* the objects — truth-conditionally aligned by the axiom
pair, structurally distinct). A non-singleton proposition reference
has **no baseline reading**: silent distribution would violate P4's
no-default-distributivity stance, so the plural case is registered in
§14 (the universal reading — `Holds` distributed over the members —
is the recorded candidate). Conversely `me'ei` at the propositional
case is `Reify` in the sumti-forming direction; beyond arity zero
both belong to the reserved family.

**What the axioms fix, and what stays open.** The round-trip pair
makes `Reify` and `Holds` mutual inverses at row ⟨⟩: proposition
identity is exactly content identity — identity of the model's
state-transformer denotations, intensional and dynamic, finer than
logical equivalence (contents differing only in presuppositions or
effects reify distinctly) — and this is **fixed by the axioms, not
model-supplied**. Likewise any future row's crossing is a function
over the extensional `PredTerm<ρ>` (§3.3 identifies relations equal
on every row record), so β/η- and pointwise-equal predicates would
reify identically — the family is extensional over `PredTerm` by
construction. What remains open is only the adoption-shape question:
whether each reserved row takes the same bijective shape, and the
design of any row-isomorphism or cross-row operators (cross-row
identity is not even formable until typed). No normative statement
decides those today.

### 9.2 The abstraction relations

Every other abstractor is a **named abstraction relation with a labelled
row**, parameterized by the abstracted content — CLL's own shape: CLL
assigns these abstractors place structures (CLL ch. 11 §3 for the event
types, §5 for `ni`, §6 for `jei`, §9 for `li'i`/`si'o`/`su'u`):

```text
(NiRel c)   : PredTerm⟨ x1:Referents<Amount>,        x2:Referents<Scale> ⟩
(JeiRel c)  : PredTerm⟨ x1:Referents<TruthValue>,    x2:Referents<Epistemology> ⟩
(LihiRel c) : PredTerm⟨ x1:Referents<Experience>,    x2:Referents<Entity> ⟩  ; experiencer
(SihoRel c) : PredTerm⟨ x1:Referents<Concept>,       x2:Referents<Entity> ⟩  ; mind
(SuhuRel c) : PredTerm⟨ x1:Referents<AbstractNature>, x2:Referents<Entity> ⟩ ; category
(PuhuRel c) : PredTerm⟨ x1:Referents<Process>,   x2:Referents<Eventuality> ⟩ ; stages
(ZuhoRel c) : PredTerm⟨ x1:Referents<Activity>,  x2:Referents<Eventuality> ⟩ ; repeated actions
(DuhuRel c) : PredTerm⟨ x1:Referents<Proposition>, x2:Referents<Sign<Sentence>> ⟩
```

`DuhuRel` is derived — formally: `((DuhuRel c) x1 x2) ≝
(∧ (CoRef x1 (Reify c)) (Distrib (λ {$s :: Sign Sentence} {(CoRef
(Reify (InterpretContent $s)) (Reify c))}) x2))` — its x1 the reified
content, its x2 sentence signs whose interpretation reifies the same
(CLL 11.7's x2 and `se du'u`); the others are the
family proper. `DuhuRel` — and with it `se du'u` — is defined only
for the 0-adic case: under explicit-`ce'u` extraction (§11) the
`du'u` abstraction is a λ, not a content, and sentence signs express
closed sentences (`InterpretContent` is defined for sentence signs,
not open properties), so `se du'u` under extraction has no baseline
reading; the natural future x2 witnesses for an n-adic `du'u` are
`Expression` signs under the §7.7 `Interpret` family — reserved-family
territory (§14). Reference applies **outside** the relation, exactly as for
any selbri: `lo ni mi klama` is `Refer` over
`(λ {$a :: Referents Amount} {(Close ((NiRel …) $a))})` — so the
`lo`/`le` contrast, outer quantification,
and relative clauses all work on abstractions for free, and an omitted x2
is ordinary closure into `Context` (the `su'u` categorizer's contextual
default — CLL 11.9's "type x2" — is this general rule, not a special
one). Event abstraction (`nu` and its one-place sort refinements
`mu'e`/`za'i`) is `Refer` over a property of eventualities satisfying the
clause; `pu'u`/`zu'o`, having real x2s, live in the relation family
above, and `li'i` is its own abstractor (`LihiRel`), not an event
refinement. `ka` is not in this family: property abstraction is `λ`
(implicit `ce'u` pinned in P12). Sort discipline and no-coercion (P13)
are unchanged; adjacent-sort recastings are explicit named operators in
the library — including the **numeric crossings**

```text
AmountValue     : Referents<Amount> × Referents<Scale> → Number
TruthValueDegree: Referents<TruthValue> → Number      ; fuzzy jei ∈ [0,1]
```

(defined at the reference types `lo ni`/`lo jei` actually yield, with the
singular-reading condition their lexicon rows state; CLL 11.5: a `ni`
sumti is semantically a number, and `mo'e` maps to `AmountValue`, so
`li pa vu'u mo'e le ni …` type-checks. The `jei` crossing carries a
sourcing caveat: CLL 11.6 records the numeric [0,1] reading as a
proposed convention that never became established practice — adopting
`TruthValueDegree` is this specification's own ruling, a documented
divergence pending a dedicated pin, and a conforming reading may
decline the crossing).

## 10. The lexicon interface

The core is parameterized over an external, curated lexicon. This chapter
fixes only the **schema** of lexical knowledge — what a dictionary entry
must provide for the core to interpret predications over it:

| Field | Content |
|---|---|
| row | the labelled, typed place row (§3.3), with the distinguished event place where licensed |
| defaultability | per place: whether closure (§4.6) may introduce a `Context` there; non-defaultable places must be filled or abstracted |
| scope policy | per place: extensional / intensional / opaque (§5.7) |
| plurality behavior | optional, per place: how the relation composes with plural arguments — lexical knowledge, never a covert operator (§4.8). Two independent facts may be declared per place: **subreference-monotone** (satisfaction is preserved under subreference — `Among r' r` and `P … r …` entail `P … r' …` at that place; the pluralization of Eberban's subset-monotonicity star) and **collective-capable** (jointly satisfiable configurations are admissible). Either may be affirmed, denied, or left undeclared; the values state lexical entailments of the word, never a reading parameter (P4) |
| deletions | which `DropPlace` deletions are meaningful, with the deleted role's semantic characterization (§4.3) |
| degree | optional: for gradable entries, the graded place label ℓ and degree projection `deg_R` consumed by `Grade` (§6.4) |
| kind admission | whether a place admits kind-like referents (ruling P3) |
| abstraction sorts | for places selecting abstractions: which sorts (§9), with drift cases adjudicated in the dictionary, not coerced |
| tag reductions | for tense/modal cmavo: the event-predicate expansion (`pu` → `purci(e, anchor)`, BAI → their gismu relations with the licensed host-event link), consumed by the mapping annex |
| indicator entries | for UI: relation, roles, degree place, `nai`-pair (with `Scalar Opposite` fallback where unpaired — §7.6, §6.3), host-force profile, evidential basis-kind where applicable (§7.6) |

Adopted collection entries (P5): official `gunma` already takes its
components as x2, and `selcmi` — a community lujvo (xorxes), which
the Contemporary CLL edition itself now uses and glosses in its
set-descriptor expansion (ch. 6) — already takes its members as x2;
both are adopted with plural
x2 read as plural references. (The genuine defect in this area is
official `cmima`'s x2 being glossed as a *set*; the library avoids
`cmima`, and the lexicon program may propose broadening its x2.) The
`le`-description relation is **`skicu` itself** — official row "x1 tells
about/describes x2 (object/event/state) to audience x3 with description
x4 (property)", an
exact fit place-for-place, and the analysis the community's formal gadri
commentary has used all along (guskant: `le broda` = `zo'e noi mi ke'a
do skicu lo ka ce'u broda`). The describing event is anchored by the
mapping annex's clause (§11): it is the current utterance's own locution
— saying `le broda` *is* the describing, so the anchor holds by
construction through the token machinery (§7.4). `voi` uses the
audience-deleted variant `(DropPlace skicu 3)` restrictively — the
deletion is semantic (no audience role exists in a `voi` description),
per pin P10.

## 11. Mapping annex: Lojban constructs to core terms

Normative lowering schemas, one line each; the cited pins carry the
arguments. Text-to-reading rules (marked ⊳) resolve before the calculus
and contribute no term constructors.

**Predication and places.** Bridi → lexical predication + `Close` at the
force boundary. FA/conversion → labelled fills / row routing (§4.2).
`zi'o` → `DropPlace`. `zo'e`/omission → per-site `Context` (P15). `fi'a` →
`OpenQ` over `Label<ρ>`. `co'e`/`do'e` → `Context` at relation/tag type.
⊳ `si`/`sa`/`su` erase before reading; quoted text preserves them.

**Prenexes, topics, imperatives** (P26, P27). Quantifier prenex
(`… zo'u`): prenexed `PA da [poi …]` terms lower to the
quantifier/selection prefix in **surface order — prenex order is scope
order** (P18's surface-scope doctrine; CLL 16.2), scoping across an
I-connected tail and across a `tu'e…tu'u` group when the syntax makes
that group the matrix; bare selbri variables take the implicit
`su'o` of the `bu'a` row. Topic `zo'u` → the `Topic` schema (§12):
the topic binds normally, and a `Vague` `TopicResolution` — fill an
admissible unfilled place of the open comment frame, or
`srana`-aboutness to the closed comment — resolves the deliberately
vague link (CLL 19.4's fish; pin P26); no segment-state effect
(`ni'o` owns segments). `ko` → fills its place with the **active
addressee** (the `doi`-updated `do` binding, falling back to the
utterance's Audience) and ⊳ marks the **nearest performed clause** as
the command force (§7.1, addressee = the same active value);
quotation and content abstractions are inert — `lo nu ko klama`
constructs content, commands nothing (pin P27); CLL 14.13's
obedience gloss is a remark, not machinery.

**Descriptions** (P1, P10, P11). `lo P` → `(Refer P)`, veridical,
number-neutral. `le P` → `Refer` via `skicu(Speaker, ·, Audience, P)`
with the anchoring clause — the describing event is this utterance's own
locution. The anchored reference property, in full, conjoins the
locution fact at the utterance's own token u₀ (the `dei` value, §7.4):

```text
(λ {$r :: Referents Entity}
  {(∃ (λ {$e :: Referents Locution}
    {(∧ (LocutionOf $e u₀)
       (skicu :1 Speaker :2 $r :3 Audience :4 P :Eventuality $e))}))})
```

for which `(Close (skicu Speaker $r Audience P))` is the **licensed
display abbreviation** (P10; the samples book's brief spelling) — an
abbreviation of this term, not a local reinterpretation of `Close` —
and
the speaker's commitment that the audience can identify the referent is
a cooperative-use commitment stated here in prose, not machinery;
non-veridical, speaker-identifying. `la N` → `Refer` via naming
(`Named`/`NameSign`). `lo'e P`/`le'e P` → `Generic(Typical|Stereotypical,
[Speaker], P, ·)` at their predication (§5.8). `loi`/`lo'i` → `Refer` to
group/set objects via `gunma`/`selcmi` (P5), the base being the **maximal
plurality of the description** (`lo'i gerku` is the set of the dogs, not
of some dogs — the library's maximal-base form supplies it). Inner PA →
unit count of the selected base (`CardBasis`); outer PA → witness-set
selection / subreference selection (P1, §4.10). Inner `no` → the
zero-count schema, never `Refer` (special case, P22). A leading possessor sumti
in a description (`le mi ratcu`) is the `pe`-associator restriction
(CLL 8.7: `le mi ratcu` ≈ `le ratcu pe mi`) — a restrictive `srana`
conjunct beside the description head. `lei`/`le'i` →
the P10 `skicu` base bound first, then `Refer` to the `gunma` group /
`selcmi` set object over it; `lai`/`la'i` → the naming base likewise
— `Group<T>`, `Set<T>`, and `Referents<T>` stay distinct, inner PA
constrains the base, outer PA counts the objects (P5's two sites).

**Relative clauses.** `poi` → conjunct in the reference property; `noi` →
`Supplement` anchored at the referent (P7); `voi` → the audience-deleted
`skicu` (`(DropPlace skicu 3)`, P10) restrictively; `goi` →
discourse-scoped binding; `ke'a` → the property's
parameter. Outer `poi` after `ku` → restriction on the outer selection;
maximal-subreference readings are explicit library content, not
defaults. GOI associators (CLL 8.3's own expansions, nested as CLL
nests them): `pe X` → restrictive `(srana ke'a X)` conjunct; `po X` →
restrictive `se steci srana`; `po'e X` → restrictive
`jinzi ke se steci srana` (nested, not conjoined); `po'u X` →
restrictive P23 identity (`=`/`CoRef` as sort dictates); `ne`/`no'u`
→ the incidental (`Supplement`) counterparts; `X` is computed and
bound before the pure restriction forms. `zi'e` → restrictives
conjoin in the reference property, incidentals stack as separate
`Supplement`s; order-insensitive **truth-conditionally** — bindings
and supplements keep source order at the effect level. `vu'o` → ⊳
widens attachment to the whole connected sumti: an incidental clause
anchors at the joint unit but predicates **once of each immediate
connectee** (`(∧ (Q r₁) (Q r₂))` — never of the `Combine` collectively,
never member-distributed into a plural connectee); a restrictive
clause restricts each operand under the connective's structure; a
group-forming joik instead supports the clause on the resultant
object (CLL 8.8 attests the incidental case; the restrictive rule is
this specification's extension; pin P34).

**Quantification and connectives** (P2, P17, P18). `ro` over descriptions
→ importing `Every` (`Presuppose` nonemptiness + `∀`); bare `ro da` → `∀`.
PA-quantifiers → library cardinal GQs over a counting basis. Termsets
(`ce'e`, `nu'i`) → co-selected witness sets at one joint locus with the
full product; no coordinate maximality (the coordinate-closed profile is a
named strengthening). `da'a n` → the `SelectAllBut`
selection (§12; default n = 1). `bu'a`/`bu'e`/`bu'i` → **typed
quantification at `PredTerm<ρ>`** — predicate-typed variables, not
predicate objects (the §9.1 reserved family is untouched; pin P30):
the row ρ is ⊳ fixed consistently across every occurrence (the exact
resolved row; incompatible uses = no resolved reading); bare `bu'a`
carries implicit `su'o`, and any other quantifier requires the prenex
(CLL 16.107); restrictions must be pure and already typed at
`PredTerm<ρ>` — an ordinary first-order `ke'a` clause on a predicate
variable does not type (reserved-family territory, §14). `cei` +
`broda`-series → ⊳ **bridi-template** binding (CLL 7.5): the template
stores fills, tense, and negation, and expansion applies the
documented later-fill override before lowering — the `go'i` machinery,
not a bare `PredTerm` value; unassigned `broda`-series words are
CLL's schematic sample predicates, not contextual retrievals.
Logical connectives → `¬ ∧ ∨ → ↔ ⊕` with surface
grammar fixing structure; `na` ≡ left-edge `naku`; `naku` movement flips
quantifiers per CLL ch. 16; `ja'a`/`je'a` → identity at their loci —
transparent (`na je'a broda` ≡ `na broda`) — except that an affirmer
⊳ **overrides inherited negation** in a pro-bridi expansion
(`ja'a go'i` over a negative template removes the `na`; pin P31);
`Scalar` gains no fourth kind, emphasis is absence or `ba'e` focus.
Sentence-level **logical** connection (`.i je`, `.i ja`, …) → **one
performance of the connected content** — `(Assert (∨ c₁ c₂))` for
`.i ja`, which forces the uniform rule; the host's single force is
shared by the connection (a force conflict has no resolved reading);
the schema is stated for the content-taking forces (`Assert`,
`Command`) — an interrogative host queries the connected content;
UI targeting distinguishes the compound act from its clauses (pin
P32). `.i joi` and the non-logical ijoiks stay in the
discourse-joining arm (`Do`) of the `joi` row — one act per sentence,
the established reading. `.i TAG bo` → the same single performance with both event
binders exposed and the tag conjunct inside:
`(Assert (∃e₁ (∧ C₁(e₁) (∃e₂ (∧ C₂(e₂) (tag e₂ e₁))))))` — never
closed contents beside free event variables. Jek at the tanru-unit
locus → `TanruLinkConnect` (§12; pin P33): shared head asserted once,
one `Vague` link per conjunct, connective over the link applications;
distinct-head units connect as whole predications; joik at either
tanru locus → the mixture semantics, `nai` there constraining the
mixture kind to other-than-named alternatives. BIhI: `X bi'o Y` →
the ordered `Interval` (a `Set` object) with GAhO endpoint kinds;
`bi'i` → ⊳ symmetrization (normalize endpoint order with their
kinds) then the same; `mi'i` → `MetricBall` (§12 — no endpoint
arithmetic); `bi'o nai` → `RegionComplement` in a Context universe;
joigik forethought = the same units; the region object fills the
host place, whose lexical semantics does the rest. BIhI at tanru and
sentence loci: **no standard resolved mapping exists** (CLL 14.16
says no meanings have been found) — a documented no-mapping, and an
implementation must not invent one. Non-logical: `jo'u` → `Combine`; `ce` → set;
`ce'o` → list; `fa'u` → `ZipWith`; `joi` **by syntactic position** —
sumti `joi` → group formation with the mixture kind a **visible**
`Vague` bind over `AdmissibleMixture` (§12); tag/facet
joining → `∧`; discourse joining → `Do`; residual genuinely-unspecified
connection → `Vague` over the connecting relation; `ku'a`/`jo'e`/`pi'u`
→ `∩`/`∪`/`×`.

**Events, tense, modals** (P8, P24). Each bridi introduces its event
existentially unless shared explicitly. Tense/aspect/spatial cmavo and BAI
→ event-predicate conjuncts per the lexicon's tag reductions, joined by
`∧` at the tag locus; tense chains (`pu pu`) compose as anchor paths.
Tenseless bridi → per the selected reading (P8): episodic → a
`Context`-anchored temporal facet; habitual/gnomic → no temporal
conjunct. ⊳ Reading selection is upstream; `ki` stickiness propagates
resolved tense by source order; ⊳ story time (CLL 10.14) supplies
narrative sequencing as reading inference, not semantics. CAhA: `ka'e` → the library's capability
schema; `ca'a` → `fasnu` actuality conjunct. ZAhO → boundary relations per
lexicon rows (gap-registered until filled). `n roi` → **replaces**
the single-event existential closure with the counted
instantiation-set schema of §12 (`Card` over the `During`-restricted
event set = n; all surface arguments and the interval bound
before the pure `SetOf`); `roi nai` negates the count condition;
subjective counts reuse the threshold-GQ policy over the set's
cardinality; the default interval is the Context-recovered anchor
with `Vague` extent (CLL 10.9), overridable by explicit ZEhA/`ze'e`
(whole-interval) forms (pin P35). `fi'o P` → `P` as tag with the
lexicon's host-event link.

**Anaphora** (P16). ⊳ `ri`/`ra`/`ru` by CLL ch. 7 counting over accessible
referents (§5.6); `vo'a`-series → bridi-place bindings; KOhA assigned →
bound variable; unassigned → keyed `Context`; ⊳ `go'i`-family → expansion
with the antecedent's resolved context; `ra'o` → re-resolution under
`InContext`/`ShiftedGround` (§5.1). The `di'u` series → utterance
anaphora at `Referents<UtteranceToken>` (a selected transcript span):
⊳ recency resolution over the transcript at three distances, past
(`di'u`/`de'u`/`da'u`) and future (`di'e`/`de'e`/`da'e`); `dei` → the
current entry's own bound token; `do'i` → `Context` for the salient
token/span — `Vague` only in the span's boundaries (pin P28). `la'e`
on an utterance anaphor crosses through the token's realized act —
`(ActContent (RealizedAct u))`, the force partiality in
`RealizedAct` alone (§7.4; `ActContent` is total at assertions) —
into the **host-sorted** crossing: `EventOfContent` for the
state-of-affairs reading, `Reify` only where a proposition is
demanded; no universal coercion (P13), and a non-assertion antecedent
yields partiality where content is demanded (P21). `doi X` → the `Vocative X` act beside the host **plus** ⊳
binding of the active `do` (CLL 2.14 — `do` "now refers to" X): `do`
and `ko` consult the active binding before falling back to the
utterance's Audience, which itself is never mutated (each utterance's
ctx carries its own audience as a fact about it; pin P27). `da'o` →
⊳ cancellation of **all** resolver assignments (KOhA, letteral, and
pro-bridi stores); `ni'o` levels are segment-stack transitions with
per-level cleared registers — the assignment-clearing level (`ni'o`
spoken, `ni'o ni'o` written) clears assignments, the drastic level
(one more `ni'o`) also resets tenses and indicators, and `no'i`
resumes what its `ni'o` dropped along with the suspended frame —
never a destructive `da'o` alias (CLL 7.13, 19.3).

**Abstractions** (§9, P13, P14). The `ce'u`-capable abstractors of
this baseline are exactly **`ka` and `du'u`**. The `du'u` case split:

```text
du'u body, extracted row ⟨⟩    ↦ (Reify closed-body)
du'u body, extracted row ρ ≠ ⟨⟩ ↦ the λ over ρ, exactly as ka
                                  (no DuhuRel, no se du'u — §9.2, §14)
```

so `lo du'u ce'u klama` is the goer property, and the Rosta
n-adic doctrine (n distinct extracted variables = n-adic; bare `du'u`
the 0-adic case, whose extracted relation *is* the content,
`PredTerm<⟨⟩>` ≅ `Content`, then reified) holds as a theorem of this
mapping over `ka`/`du'u`. Elided places inside `du'u` close
ordinarily (`zo'e` ≡ omission, P15); only explicit `ce'u` extracts.
Arity counts **distinct extracted variables**: ⊳ `ce'u goi` aliasing
identifies occurrences and `ce'u xi` indexing selects the extracting
abstraction, both resolved at the text-to-reading layer. Explicit
`ce'u` in the other abstractors is unmapped at baseline, and not by
blanket referral to the reserved family: each would need a
**result-specific typed analysis** — `lo ni ce'u clani` calls for an
argument-indexed amount abstraction, and `jei`/`li'i`/the event
abstractors likewise have their own codomains, none of them a
reified `PredTerm<ρ>` (§14). The Rosta all-`ce'u` reading of `si'o`,
which genuinely nominalizes a predicate into a concept *object*, is
the one reading that belongs to the reserved family (§9.1). Baseline
`si'o`
has no covert `ce'u`, closes its inner bridi normally, and maps
through `SihoRel` with the conceptualizing mind at x2 (CLL 11.9) —
a stated divergence from the Rosta proposal's clause 7. `nu` +
sorts → `Refer`
over event properties; `ka` → `λ` (⊳ implicit `ce'u` at first unfilled
place, counting converted places; P12, a rule of `ka` alone — the
experimental lambda-prenex
`ce'ai` names binder order explicitly where multiple readings arise); `ni`/`jei`/`li'i`/`si'o`/`su'u`/`pu'u`/`zu'o` →
the abstraction relations with reference outside; `mo'e` → the
`AmountValue` numeric crossing; `tu'a X` → `Vague` abstraction
constrained by shape + `srana`-aboutness, **sort selected by the host
place** (an event place gets an event-sorted abstraction); `jai`+tag →
explicit role promotion, old x1 to the fillable `fai` place (library
expansion); bare `jai` → participant raising out of the abstraction-x1
with the role `Vague` (§6.1); `la'e`/`lu'e` → interpretation /
sign-of crossings.

**Questions and answers** (§8, P9). `xu` → `Polar`; `ma`/`mo`/`fi'a`/
`xo`/`ji`/`cu'e`/`pei` → `OpenQ` at their typed domains — ⊳ bare
interrogatives take utterance-level scope even from embedded positions
(CLL 11.8; §8.1); `kau` →
`ContextualAnswer` with absent exhaustivity; `go'i` as answer → `Answer`
with polar selection.

**Indicators and discourse** (§7, P19). ⊳ UI target selection by
grammatical attachment (FUhE/FUhO extend); UI → displayed-content
relations per lexicon entries with host-force profiles; evidentials →
the family force clause; `dai` → experiencer shift; `nai` → lexical pair;
degree words → intensity regions. `.i` sequencing → `Do`; `ni'o`/`no'i` →
`NewTopic`/`Resume`; discursives → library discourse relations; `po'o`,
constituent `ji'a` → focus derivations; COI → performative expressive
acts; `mi'e` → performative self-naming; `na'i` → the objection act
(§7.3). `n mai`/`n mo'o` → `EnumerationOrdinal` display facts (§12) at
the **attachment-selected** constituent (CLL 19.7 numbers sumti inside
one bridi — not always the utterance), item and section level
respectively; sequence key and resets Context-recovered; no temporal
order implied.

**Quotation, signs, MEX** (§7.5, §4.9). `lu…li'u` → `StructuredQuote`;
`lo'u…le'u`/`zoi` → `OpaqueQuote`; `zo` → `WordSign`; letterals →
`LetteralSign` (⊳ letteral anaphora keys bindings); `me'o` → mention of a
math-expression sign; `li` → the value; `du` → `=` / `CoRef` (P23);
operators → typed
functions; `xi` subscripts → application. `me X [me'u]` →
`(MePred X)` (§12); number + MOI → the MOI relation families (§12);
`me … me'u MOI` composes them. MEX conversions `na'u`/`nu'a`/`ma'o`/
`ni'e` → the §12 partial interfaces (definedness projective;
`ma'o`'s function recovery is `Context`, pin P36); `se` on operators
→ argument permutation. Numeral notation (`pi`, `fi'u`, `pi'e`,
`ki'o`, `ra'e`, `ce'i`) → ⊳ numeral syntax producing `Number`
constants (fractions, mixed radix with `pi'e`'s base data, grouping
with `ki'o` zero-padding, repeating digits, percent); `xo'e`
(experimental) → `Context` at `Number` (P15's analogue); `ji'i` → the
§12 approximation schemas by position — prefix/medial approximate
(`AdmissibleTolerance`), suffix rounds, directional under
`ma'u`/`ni'u` (pin P37). `la'o` → the ordinary naming route at
the opaque text payload (`(NameSign t)`/`Named` unchanged, §12);
`zo'oi` (experimental) → the word-level
opaque sign.

## 12. Library

Normative derived forms, **defined in the core language**; each
definition is its specification (Eberban's from-scratch discipline).
Metalanguage recursion (over `Natural`, over list structure) is permitted
in definitions; the term language itself has no recursion former (§4.4).
Schematic variables: `P, Q` properties; `r` plural references; `n`
naturals; `ρ` rows.

**Cardinal and logical quantifiers** (witness-set semantics, §4.10;
export status per §5.6). Types: restrictors `P : Fn<(T), Content>` are
pure member-level properties; the witness forms' nuclear scope `Q` is a
property **of the witness reference**, `EFn<(Referents<T>), Content>` —
neutral plural predication, per P4; `Every`'s nuclear scope is
member-level (`ro` is each — CLL ch. 16), as is `GlobalExactly`'s:

```text
(Exactly n P Q)  ≝ (Bind {$w :: Referents T} (SelectExactly n P) {(Q $w)})
(AtLeast n P Q)  ≝ (Bind {$w :: Referents T} (SelectAtLeast n P) {(Q $w)})
(Some P Q)       ≝ (Bind {$w :: Referents T} (SelectSome P)      {(Q $w)})
(Every P Q)      ≝ (Bind {$w :: Referents T} (MaxRefer P)
                     {(Distrib Q $w)})          ; the import is MaxRefer's
                                                ; own presupposition (below),
                                                ; emitted before any witness
                                                ; can fail; exports w
(No P Q)         ≝ (¬ (Some P Q))                          ; no export
(AtMost n P Q)   ≝ (¬ (AtLeast n+1 P Q))                   ; no export
(MoreThan n P Q) ≝ (AtLeast n+1 P Q)
(FewerThan n P Q)≝ (¬ (AtLeast n P Q))                     ; total at n = 0
(GlobalExactly n P Q) ≝ (= (Card (SetOf (λ {$x :: T} {(∧ (P $x) (Q $x))}))) n)
(Distrib Q r)    ≝ (∀ (λ {$x :: T} {(→ (Among $x r) (Q $x))}))
                   ; T the member type of r; $x lifts to a singleton
                   ; reference for Among — Distrib is unit distribution
```

**Zero and the selection floor.** The selections are formed only at
n ≥ 1: `SelectExactly 0` and `SelectAtLeast 0` are ill-formed — a
witness reference is nonempty by type (§3.2), so there is no
zero-strength witness to select. The boundary GQ cases are defined
directly, with no selection and no export:

```text
(AtLeast 0 P Q)  ≝ ⊤                ; trivially satisfied, exports nothing
(Exactly 0 P Q)  ≝ (No P Q)         ; the zero count is absence (P22)
```

The rest follow from the definitions: `MoreThan 0` = `AtLeast 1`;
`AtMost 0` = `No`; and `FewerThan 0` = `(¬ ⊤)` — never true, as
arithmetic demands.

`GlobalExactly` and `Most` place their operands inside `SetOf`, so
**both operands must be pure there**: the mapping hoists a nuclear
scope's contextual sites and introductions out of the comprehension
first (site identity, §5.3, makes the hoist meaning-preserving), and
an unhoistable nuclear scope simply has no global reading.

`no prenu cu jmaji` is `(No prenu-property (λ {$w :: Referents Entity} {(Close (jmaji $w))}))` —
"no people-witness gathers", the reading a distributive quantifier
could not express at all (§4.10).

**The export contract.** The exporting forms are exactly the definitions
whose expansion is an outer `Bind` of a selection or maximal reference
(`Exactly`, `AtLeast`, `Some`, `MoreThan`, `Every`); that `Bind` may be
spelled at any width up to the enclosing `Do` — the accessibility table's
witness row licenses the widening, and the mapping spells the binder at
the width later anaphora requires (narrow when nothing refers back, over
the continuation when something does). The non-exporting forms (`No`,
`AtMost`, `FewerThan`, `GlobalExactly`) contain their selection under `¬`
or comprehension, where nothing escapes.

**Degree quantifiers** (§6.4; `θ` a `Vague` threshold, `σ` a `Context`
standard where marked). Admissibility predicates, declared here with
their VC1 nonemptiness axioms: `AdmissibleThreshold : ThresholdKind ×
Fn<(T),Content> × [Referents<Entity>] → Fn<(Natural), Content>` — with
`ThresholdKind` the closed enumeration `ManyK | FewK | TooManyK |
TooFewK | EnoughK` (an index type, nothing to do with the rejected
`Kind` sort of individuals, P3) — (for
every kind, restrictor, and standard, some threshold is admissible) and
`AdmissibleCutoff : Scale × Region<Scale> → Content` (every scale has an
admissible region — the gradable analogue, consumed by `Grade`'s
`Vague` region):

```text
(Many P Q)   ≝ (Bind {$θ :: Natural} (Vague (AdmissibleThreshold ManyK P))
                 {(AtLeast $θ P Q)})
(Few P Q)    ≝ (Bind {$θ :: Natural} (Vague (AdmissibleThreshold FewK P))
                 {(FewerThan $θ P Q)})
(Most P Q)   ≝ (> (Card (SetOf (λ {$x :: T} {(∧ (P $x) (Q $x))})))
                  (Card (SetOf (λ {$x :: T} {(∧ (P $x) (¬ (Q $x)))}))))
(TooMany P Q)≝ (Bind {$σ :: Referents Entity} (Context)          ; purpose
                      {$θ :: Natural} (Vague (AdmissibleThreshold TooManyK P $σ))
                 {(MoreThan $θ P Q)})
(TooFew P Q) ≝ (Bind {$σ :: Referents Entity} (Context)
                      {$θ :: Natural} (Vague (AdmissibleThreshold TooFewK P $σ))
                 {(FewerThan $θ P Q)})
(Enough P Q) ≝ (Bind {$σ :: Referents Entity} (Context)
                      {$θ :: Natural} (Vague (AdmissibleThreshold EnoughK P $σ))
                 {(AtLeast $θ P Q)})
```

Gradable predication: a `GradableRel<ρ,ℓ>` is a lexical relation whose
entry's **degree field** (§10) declares its graded place `ℓ : Label<ρ>`
and a degree projection

```text
deg_R    : Record ρ × Scale → Amount    (the degree may consult any
                                         place of the row, not only ℓ —
                                         comparison classes and standards
                                         live in the other places)
InRegion : Amount × Region<Scale> → Content
```

(`Region<Scale>` — poles, midpoints, intervals — declared here for the
whole document). Then

```text
(Grade R s reg) : PredTerm<ρ> ≝
  (λ {$rec :: Record ρ} {(InRegion (deg_R $rec s) reg)})
```

— the relation holding of a row record exactly when its degree
on scale `s` lies in region `reg`. No `…` remains in this chapter.

**Complement selection** (`da'a`, CLL 18.8; default n = 1). A
**declared** primitive member of the §5.6 selection family (like its
siblings, its witness law is its axiom) — neutral witness sets,
ordinary export:

```text
(SelectAllBut n P) : RefComp<Referents<T>>   ; witness law:
   ; (∧ (Distrib P w)
   ;    (= (Card (SetOf (λ {$x :: T} {(∧ (P $x) (¬ (Among $x w)))}))) n))
   ; — the witness satisfies P member-wise AND leaves exactly n
   ; P-individuals behind, spelled by comprehension: the plural kernel
   ; has no difference operator and needs none. Which individuals are
   ; left out is not a semantic parameter (neutral witness selection,
   ; P17); under distributive scope they may vary per instance (CLL's
   ; ro ratcu cu citka da'a re …). Nonemptiness of the witness follows
   ; from the reference type; model-side existence of a qualifying
   ; witness is the selection's success condition.
```

**Approximation** (`ji'i`, CLL 18.9; completes §6.4's classification).
`Precision` is the numeral's ⊳-supplied precision descriptor (which
digits/places are stated — an index sort of numeral syntax, never a
term-level computation). `AdmissibleTolerance` is the `Vague`
admissibility former for approximate number regions,
`AdmissibleThreshold`'s sibling:

```text
AdmissibleTolerance : Number × Precision → Fn<(Number), Content>
   ; admissible values: numbers within the tolerance region about the
   ; anchor at the given precision; the region's boundary is the Vague
   ; dimension; nonempty by VC1.
```

Position matters (CLL 18.9), and the numeral's value is what changes:
a prefix or medial `ji'i` numeral **denotes the computation**
`(Vague (AdmissibleTolerance n prec))` — a Vague-selected `Number`,
bound at its use site like any effectful operand (`prec` the
numeral's own precision descriptor); a suffix-`ji'i` numeral likewise
denotes a Vague-selected `Number`, over the **rounding preimage** —
`AdmissibleRounding : Number × Precision × Direction → Fn<(Number),
Content>` admits the numbers whose rounding at `prec` toward the
`ma'u`/`ni'u` direction (both sides unmarked; `Direction` the closed
Up | Down | Either) is the stated value — so the underlying quantity
is explicitly the bound `Number`, the stated digits exact by
construction of the region (nonempty by VC1; pin P37).

**Plurality and collections:** `UnitSet`/`CardBasis` (§4.8); `lu'a r` ≝
distribution over members (`Distrib` at the use site);
`(Overlap a b)` ≝ `(∃ (λ {$c :: Referents T} {(∧ (Among $c a) (Among $c b))}))`;
`(Interval a b k₁ k₂)` ≝ `(SetOf (λ {$x :: T} {(∧ (cmp₁ a $x) (cmp₂ $x b))}))` with
`cmpᵢ` strict/nonstrict per the `ga'o`/`ke'i` endpoint kinds. The
reciprocal schema (consumed by `simxu`'s and `soi`'s lexicon rows):

```text
(Reciprocate r P) ≝
  (∀ (λ {$x $y :: T}
       {(→ (∧ (Among $x r) (Among $y r) (¬ (= $x $y)))
           (P $x $y))}))    ; member-wise, both ways: T is r's member
                            ; sort; the units singleton-lift at Among
                            ; and at P's places (§3.2). Vacuous on a
                            ; unitless (atomless) reference —
                            ; reciprocity of unstructured stuff needs
                            ; an explicit basis and is not claimed.
```

**Lists and `fa'u`** — the mandated full expansion. `ZipWith` is defined
by metalanguage recursion over list structure:

```text
(ZipWith f (List) (List))                 ≝ ⊤
(ZipWith f (List a as…) (List b bs…))     ≝ (∧ (f a b)
                                               (ZipWith f (List as…) (List bs…)))
```

so the `fa'u` specimen expands completely:

```lisp
; mi fa'u do tavla do fa'u mi
(ZipWith (λ {$s $l :: Referents Entity}
           {(Close (tavla $s $l))})
  (List Speaker Audience)
  (List Audience Speaker))
; ≡ (∧ (Close (tavla Speaker Audience))
;      (Close (tavla Audience Speaker)))
```

**Reference utilities:**

```text
(CoRef x y)     ≝ (∧ (Among x y) (Among y x))    ; plural co-reference
(Named t x)     ≝ (Close (cmene (NameSign t) x)) ; bearer of name-sign t,
                                                 ; naming convention from
                                                 ; the lexicon's cmene row
(MaxRefer P)    : RefComp<Referents<T>> ≝
  (Presuppose (∃ P)                       ; defined only when P is
    (Refer (λ {$r :: Referents T}          ; inhabited
      {(∧ (Distrib P $r)
          (∀ (λ {$x :: T} {(→ (P $x) (Among $x $r))}))
          (∀ (λ {$r' :: Referents T}
               {(→ (Among $r' $r)
                   (∃ (λ {$x :: T} {(∧ (P $x) (Overlap $x $r'))})))})))})))
                ; all P-satisfiers, only P-covered parts: every unit is P,
                ; every P-satisfier is Among it, and every subreference
                ; overlaps a P-unit (no atomless residue) — the maximal
                ; base (lo'i/loi, Every's export). Models must supply
                ; this reference for each inhabited pure restrictor the
                ; mapping can form (a model condition: plural
                ; comprehension for P).
```

(`Holds`, `Reify`'s primitive inverse, is declared with it in §9.1.)

**Temporal incidence** (ROI's interface; P35). Declared:

```text
During : Referents<Eventuality> × Set<Time> → Content
   ; the eventuality's temporal extent lies within the interval —
   ; the same lexical facts the tense facets consult, packaged as a
   ; relation the counted schema can restrict by
```

The `n roi` schema, for host event property `P` (pure) and bound
interval `I`:

```text
(= (Card (SetOf (λ {$e :: Eventuality} {(∧ (P $e) (During $e I))}))) n)
```

— this **replaces** the single-event existential closure; `roi nai`
negates the equation; subjective counts substitute the threshold-GQ
condition for `=`.

**Events and tags.** Two primitives are *declared* here beside the
helpers they serve (they have no expansions — prose-and-axiom
definitions like any primitive): the adjacent-sort crossing
`EventOfContent : Content → Referents<Eventuality>` (the eventuality
of a clause, used by `tu'a`'s shape conjunct and `nu`-recasting), and
the modal relation `InnatelyCapable : Referents<Entity> ×
Fn<(Referents<Entity>, Referents<Eventuality>), Content> → Content` —
`jinzi`-grounded possibility of `P`-events with the bearer, evaluated
at capability worlds (§5.1); likewise the lexical projection
`MotionVector : Referents<Eventuality> × Referents<Entity> ×
Referents<Entity> → Content` (the `mo'i` heading: the event's `muvdu`
motion with `farna` direction). The defined forms over them, with
`P : Fn<(Referents<Entity>, Referents<Eventuality>), Content>`:

```text
(Realized b P) ≝ (∃ (λ {$e :: Referents Eventuality}
                    {(∧ (P b $e) (fasnu $e))}))
(nu'o b P)     ≝ (∧ (InnatelyCapable b P) (¬ (Realized b P)))
(pu'i b P)     ≝ (∧ (InnatelyCapable b P) (Realized b P))
```

Tense helpers per the lexicon's tag-reduction rows. Tagged `jai`: for
a lexical row ρ with promoted role ℓ, writing ρ' for ρ with ℓ
relabelled x1 and x1 relabelled `fai`,

```text
(JaiPromote R ℓ) : PredTerm<ρ'> ≝
  (λ {$r :: Record ρ'}
    {(R ⟨the ρ-record with ℓ = $r.x1, x1 = $r.fai, rest unchanged⟩)})
```

— the promoted role becomes x1 and the old x1 becomes the labelled,
*fillable* `fai` place (closing contextually like any place when
unfilled — CLL 9.12); bare `jai` per §6.1.

**Acts and discourse:** discourse relations `Contrast`, `Addition`,
`Parallel`, `Elaboration` — lexical relations over two act values,
displayed act-level per §7.6; the `na'i` objection ≝

```lisp
(NahiObjection t) ≝
  (Bind {$d :: DefectKind} (Context)
    {(Express (Close (MetalinguisticallyDefective t $d)))})
```

for a bound prior target `t` (`DefectKind` — wording, form, implication,
presupposition, register — is declared with the objection relation); COI
schemas ≝ performative `Express` of the COI lexical relation
(`coi-greeting`, `ki'e-thanks`, …), schematically `(COIExpress R
addr) ≝ (Express (Close (R Speaker addr)))` with the entry's
performative host-force profile; `(GroundedBy b a)` ≝
`(Do (Perform a) (Express (Close (EvidentialBasis Speaker a b))))` —
the act-level evidential spelling of §7.6 (named to
avoid the `Ground` sort, §5.1); focus for
a host content frame `H[·]` and focused sumti `f : Referents<T>`
(the alternatives `$y` singleton-lift into `CoRef` at `f`'s type):
`(Only f H) ≝ (Presuppose H[f] (¬ (∃ (λ {$y :: T} {(∧ (¬ (CoRef $y f)) H[$y])}))))`
(`po'o`), and `(Additive f H) ≝ (Presuppose (∃ (λ {$y :: T} {(∧ (¬ (CoRef
$y f)) H[$y])})) H[f])` (constituent `ji'a`).

**Sumti-based selbri** (`me`, CLL 5.10): the Among-property —

```text
(MePred X) ≝ (λ {$w :: Referents T} {(Among $w X)})   ; X's computation,
   ; if any, is bound before the pure property forms; T is X's sort.
   ; Singleton X: extensionally the P23 identity/co-reference.
```

The ratified gadri definitions expand `lo PA sumti` through `me`, so
this form retroactively grounds the P1 inner-PA machinery.

**MOI relation families** (CLL 18.11): five lexical relation families
indexed by the number `n`, catalogued with exact rows — not term
expansions (their content is lexical):

`Ordering<T>` is the pure comparison type `Fn<(T, T), Content>`
(total and transitive as a definedness condition on its uses).
The rows, labelled and typed (P25's referential discipline; the
`Ordering` place is function-typed, the `InnatelyCapable` precedent):

```text
(MeiRel n)  : PredTerm⟨ x1:Referents<Group<T>>, x2:Referents<Set<T>>,
                        x3:Referents<T> ⟩
   ; lexical content: x1 is the gunma-group over x2's members, and
   ; (= (Card s) n) at the presupposed sole set member s of x2 (the
   ; §9.2 projective singular pattern); x3 among s's members.
   ; Objective-indefinite n extends the row with the comparison set
   ; x4:Referents<Set<T>>; subjective n extends it with the standard
   ; place (the degree quantifiers' σ, a Referents<Entity>).
(MoiRel n)  : PredTerm⟨ x1:Referents<T>, x2:Referents<Set<T>>,
                        x3:Ordering<T> ⟩
   ; x1 is the n-th member of x2 under x3; x3 Context-recovered when
   ; unstated; definedness: n within x2's cardinality.
(SiheRel n) : PredTerm⟨ x1:Referents<Entity>, x2:Referents<Entity> ⟩
   ; x1 is an n-fraction portion of the mass x2 (CLL: portion of
   ; mass); the fraction n a Number in (0, 1].
(CuhoRel n) : PredTerm⟨ x1:Referents<Eventuality>,
                        x2:Referents<Eventuality> ⟩
   ; event x1 has probability n under conditions x2 — an opaque
   ; lexical relation; formation condition 0 ≤ n ≤ 1; the model
   ; supplies the measure. NO probability calculus enters the core
   ; (pin P29).
(VaheRel n) : PredTerm⟨ x1:Referents<Entity>, x2:Referents<Scale> ⟩
   ; x1's degree on x2 (through the gradable projection its lexical
   ; content names) lies in position n's region.
```

The `me X me'u MOI` composite (CLL Example 18.93) applies the family
the MOI cmavo selects at the number the `me`-complement supplies —
the complement's referent under the projective singular condition and
the `Number` sort (`li ny. su'i pa` supplies its sole numeric
member); never a property in the number index. The **non-numeric**
composite (CLL Example 18.94's `cu'o` snowball) is a **registered
divergence-gap**: its CLL reading would need value-indexed families
beyond the `Number` index, and no analysis is assigned (§14).

**Regions and intervals** (BIhI, CLL 14.16). `Metric<T>` is the pure
distance type `Fn<(T, T), Number>`, Context-recovered (spatial
distance, duration, …). Endpoint and center sumti are references;
each former below is defined — like the §9.2 numeric crossings — at
the reference type under the projective singular condition (the sole
member is what the definition consumes). `bi'o` takes the ordered
`Interval` (above) at ordered domains, endpoint kinds per GAhO;
`bi'i` at an ordered domain is its symmetrization (⊳ normalize
endpoint order together with their GAhO kinds), and at a metric
domain it is the betweenness span; `mi'i` is metric, never endpoint
arithmetic:

```text
(MetricBall c rad d k) ≝ (SetOf (λ {$x :: T} {(cmpₖ (d c $x) rad)}))
   ; cmpₖ = ≤ or < per the GAhO kind k; rad : Number — a measure
   ; sumti supplies it through AmountValue at its scale (§9.2)
(SpanRegion a b d k₁ k₂) ≝
   (SetOf (λ {$x :: T}
     {(∧ (= (+ (d a $x) (d $x b)) (d a b))
        (endₖ₁ $x a) (endₖ₂ $x b))}))
   ; metric betweenness; endₖ is ⊤ for ga'o and (¬ (= $x ·)) for
   ; ke'i — the endpoint kinds govern membership, as Interval's cmpᵢ do
(RegionComplement U A) ≝ (SetOf (λ {$x :: T} {(∧ (∈ $x U) (¬ (∈ $x A)))}))
   ; U the Context-recovered universe — the bi'o-nai reading
```

**MEX conversions** (CLL 18.18, 18.19, 18.21): **declared partial
crossings**, row-indexed, each with a projective definedness
condition (§5.5) — the core supplies no totality or unique-result
guarantees:

```text
RelToOp<ρ> : PredTerm<ρ> ⇀ Fn<(Number …), Number>       ; na'u
   ; defined only at rows whose x1 and operand places take
   ; Referents<Number> (each fill projectively singular): the
   ; operator maps the operands' sole members to the sole x1 member —
   ; definedness includes functionality of the relation in x1 there.
OpToRel : Fn<(Number …), Number> → PredTerm⟨x1:Referents<Number>,
                                            x2…:Referents<Number>⟩
   ; nu'a — total: x1's sole member is the operator's result at the
   ; operands' sole members (P25's referential places; singular
   ; conditions formation-level).
OperandToOp : Number → RefComp<Fn<(Number …), Number>>  ; ma'o
   ; the intended function is a Context recovery — hence the
   ; computation type; the constant-function ambiguity CLL 18.21
   ; records is a recovery, not a default (pin P36).
AmountOperand<ρ> : PredTerm<ρ> ⇀ RefComp<Number>        ; ni'e
   ; its own crossing, NOT `NiRel` (which reifies an abstraction):
   ; defined where the row names a Number-sorted result place; the
   ; result is the computation that closes the remaining places per
   ; §4.6's discipline and selects the result place's sole member.
```

`se` on operators = argument permutation (a pure λ rewrite at the
known arity). Everything beyond these crossings — including `mo'e`'s
general sumti-to-operand cases past the §9.2 `AmountValue` route —
remains in the §14 MEX gap.

**Foreign names** (`la'o`; `zo'oi` experimental): parsing yields an
opaque text payload `t : Text`, and `la'o` is simply the §11 naming
route at that text — `(NameSign t)` and the `Named` relation apply
unchanged (no new former; the payload's being non-Lojban is a fact
about the text, not a type). `zo'oi` quotes one non-Lojban word as an
opaque word-level sign.

**Enumeration ordinals** (MAI, CLL 19.7): a non-at-issue metadata
relation — **declared**, not defined — displayed through the §7.6
machinery. `EnumerationLevel = Item | Section` is a closed index
type; `SequenceKey` is its own declared index sort (a sequence
identifier, Context-recovered with its reset behavior — distinct from
§5.3's retrieval-site keys); the target is the
⊳ attachment-selected constituent's bound value (a referent, sign, or
act — CLL 19.7 numbers sumti within one bridi, so the target is NOT
always the containing utterance):

```text
EnumerationOrdinal : Target × Number × SequenceKey × EnumerationLevel
                     → Content
   ; Target the union of the attachable values; `mai` = Item,
   ; `mo'o` = Section; NO temporal ordering of denoted events implied.
```

Display placement is §7.6's exactly: a constituent target takes one
`Supplement` anchored at the bound target with the ordinal fact as
side content; an act-level target takes an `Express` beside the
shared host act.

**Topic resolution** (`zo'u`, CLL 19.4). The comment frame is a
**mapping-level schematic** — the comment's open predication with its
row ρ, never a term-language object; `TopicResolution<ρ>` is the
closed union indexed by that row:

```text
TopicResolution<ρ,T> = PlaceFill(ℓ : CompatibleLabel<ρ,T>) | About
   ; CompatibleLabel<ρ,T> — the refinement of Label<ρ> to the places
   ; whose sort accepts Referents<T>, so the fill branch types
   ; statically
TopicAdmissible : Referents<T> × PredTerm<ρ>
                  → Fn<(TopicResolution<ρ,T>), Content>
   ; declared admissibility predicate (TanruAdmissible's sibling):
   ; PlaceFill(ℓ) is admissible for ℓ unfilled; About is admissible
   ; when srana-aboutness holds.
```

The lowering (pin P26), for topic `t` and open comment `R` with
unfilled row ρ:

```text
topic zo'u comment ↦
(Bind {$res :: TopicResolution<ρ,T>} (Vague (TopicAdmissible t R))
  {(∨ (∧ (= $res (PlaceFill ℓ₁)) (Close (At R ℓ₁ t)))
      …one disjunct per ℓ ∈ CompatibleLabel<ρ,T>…
      (∧ (= $res About)
         (Let {$p :: Proposition} (Reify (Close R))
           {(∧ (Holds $p)
              (Close (srana t $p)))})))})
   ; the closed union eliminates by the finite equality-guarded
   ; disjunction (§3.5 — the §4.7 label-case precedent): one disjunct
   ; per compatible label (the topic fills ℓ; Close handles the rest)
   ; plus the About arm, whose single shared reification is the
   ; catalog 1.31 display — the comment holds AND the topic pertains
   ; to it.
```

CLL's fish (`le finpe zo'u citka`) is the `PlaceFill` choice — eater
or eaten; `tu'e…tu'u` scopes one topic binder over the sequence's
`Do`.

**Mixture admissibility** (sumti `joi`). The mixture kind — *how*
the components compose into the group (mass, team, aggregate, …) — is
`Vague`, bound visibly:

```text
AdmissibleMixture : Referents<T>
   → Fn<(PredTerm⟨x1:Referents<Group<T>>, x2:Referents<T>⟩), Content>
   ; admissible values: composition relations refining gunma for the
   ; given components — the §6.1 mixture vagueness, typed; nonempty
   ; by construction (gunma itself is the trivial refinement — the
   ; VC1 witness)
```

The sumti-`joi` group formation binds one:
`(Bind {$mix :: PredTerm⟨…⟩} (Vague (AdmissibleMixture base))
{… (∧ (gunma $g base) ($mix $g base)) …})`.

**Tanru link connection** (jek at the tanru-unit locus; pin P33).
`TanruLinkConnect`: for a shared head, bind one `Vague` link per
conjunct (each with its own admissibility), assert the head
predication once, and join the link applications with the connective —

```text
((TanruLinkConnect ⊙ M₁ M₂ H) fills…) ≝
(Bind {$l1 :: PredTerm ρ(H)} (Vague (λ {$r :: PredTerm ρ(H)} {(TanruAdmissible M₁ H $r)}))
      {$l2 :: PredTerm ρ(H)} (Vague (λ {$r :: PredTerm ρ(H)} {(TanruAdmissible M₂ H $r)}))
  {(∧ (H fills…) (⊙ ($l1 fills…) ($l2 fills…)))})
```

with ⊙ the jek's operator; links bound first so the connective ranges
over fixed precisifications; NA/SE/NAI decorate ⊙ as at any locus.
Distinct-head units connect as whole predications —
`(⊙ ((Tanru M₁ H₁) fills…) ((Tanru M₂ H₂) fills…))` — and a joik at
either locus routes to the mixture semantics (`joi`'s arm), with
`nai` there constraining the Vague mixture kind to admissible
alternatives other than the named one (§6.3's alternative-set
discipline at the mixture domain).

**MEX:** by metalanguage recursion over `Natural` and lists:
`(te'a x 0) ≝ 1`, `(te'a x (n+1)) ≝ (× x (te'a x n))`;
`(gei x y) ≝ (× y (te'a 10 x))`; subscript
`(xi (List a as…) 1) ≝ a`, `(xi (List a as…) (n+1)) ≝ (xi (List as…)
n)` (undefined past the end — a projective definedness condition,
§4.9); operators are functions and `me'o` mentions their
expression signs (§7.5); `AmountValue` per §9.2.

**Tanru links:** named precisification constants — `MannerLink`,
`MaterialLink`, `PurposeLink`, `SourceLink`, `InstrumentLink`,
`ResemblanceLink`, … — each a relation of the head row asserting the
modifier's specific bearing; usable wherever a resolved reading commits
(§6.2), each satisfying `TanruAdmissible` by construction.

## 13. Pin annex

Numbered rulings resolving accidental underspecification; each cites its
evidence here, and the genuinely contested pins carry full arguments in
the rationale (§3) — the remainder rest on the evidence stated with
them. (Deliberate vagueness is never pinned; it is classified in §6.1.)

- **P1** No default quantifiers (xorlo). `lo P` = `Refer P`; inner PA
  counts the selected base's units; outer PA selects witness sets /
  subreferences; nonemptiness from the reference sort.
- **P2** `ro` over descriptions imports via `Presuppose`; bare `ro da` is
  mathematical `∀`.
- **P3** No automatic kind lift, no `Kind` sort; `Entity` open to
  kind-like referents where lexicon and model admit them.
- **P4** No distributivity default and **no covert cover parameter**;
  neutral plural predication is the resolved reading; marked readings are
  explicit; lexical plurality behavior lives in the lexicon.
- **P5** `loi`/`lo'i` denote group/set objects via `gunma`/`selcmi`,
  whose x2s (official components; xorxes' members) are read as plural
  references; inner PA = group/set size, outer PA counts groups/sets.
  (`cmima` x2-as-set is the one defective gloss nearby; avoided.)
- **P6** Donkey configurations normalize to joint multi-parameter loci;
  dynamic accessibility includes restrictor introductions; CLL 7.6
  counting is the mapping discipline over accessible referents.
- **P7** `noi` is projective supplement, anchored; dependent supplements
  commit per instantiation inside their binder.
- **P8** A tenseless bridi is
  **reading-multiple**, per CLL 10.1's own enumeration (past, present,
  perfect, future, "I continually go…" — "context resolves which is
  correct"): an *episodic* reading carries a `Context`-anchored temporal
  facet (the contextually relevant occasion — the reading on which "I
  didn't turn off the stove" denies a particular failure, not all past
  ones); *habitual/gnomic* readings carry no temporal conjunct at all.
  The semantics never inserts a default; selecting the reading is
  upstream (§1.5), `ki` is text-to-reading stickiness, and **story time**
  (CLL 10.14) is one named text-to-reading resolver, never a semantic
  default.
- **P9** Bare `kau`: answerhood with exhaustivity **absent** — weakest
  truth conditions; strengthenings lexical/pragmatic/explicit. (Absence,
  not `Vague`: Lojban has no grammatical precisification route.)
- **P10** `le` lowers through **`skicu`** — exact
  official fit, guskant-precedented — with the utterance-locution
  anchoring clause (§11) answering act-vs-identification: the describing
  event is this very utterance, true by construction. Speaker-indexed,
  non-veridical, number-neutral; `voi` = `(DropPlace skicu 3)`
  restrictive variant. No dictionary change (full argument:
  rationale §2.6).
- **P11** `lo'e`/`le'e` via the axiomatic `Generic` operator (mode +
  holder); no fixed prototype reference.
- **P12** Implicit `ce'u` — a rule of `ka` alone (§11): exactly one,
  first unfilled place, counting
  converted places; multiple candidates are distinct readings.
- **P13** No implicit coercions among abstraction sorts; named explicit
  crossings; dictionary adjudicates sort drift.
- **P14** `tu'a` = `Vague` abstraction (shape conjunct + `srana`
  aboutness, host-place sort); `co'e`/`do'e` = `Context` at their types.
- **P15** `zo'e` ≡ omission; distinct sites distinct; `zu'i` adds
  typicality as an **admissibility condition on the retrieval** (part
  of the site's key, §5.3): only the place's typical filler is an
  admissible recovery — the term is `Context`, the key differs.
- **P16** Anaphora resolution is text-to-reading; calculus sees bindings;
  `goi` discourse-scoped; unassigned KOhA = keyed `Context` (one value per
  key — `ko'a du ko'a` is reflexively true).
- **P17** Termsets: co-selected witness sets, full product, **no
  maximality** — CLL ch. 16 §7's own gloss of `ci gerku ce'e re nanmu cu
  batci` (Examples 16.41–16.45; the gloss is 16.45) is two picked groups
  with every dog biting each man, and says nothing stronger; the
  coordinate-closed profile is a named strengthening; referential members
  need no termset semantics at all (16.7: unquantified descriptions are
  constants outside scope distinctions, and only explicit `ro…ro`,
  16.46, spells the full product). The bare-PA half is a **documented
  divergence from CLL's letter**, in two respects: ch. 16 §6 glosses
  bare numeric quantification globally ("exactly two things, no more or
  less" — Example 16.34) *and* distributively (`PA broda` "is shorthand
  for `PA da poi broda`" — a singular variable), while this
  specification pins **neutral witness-set selection** instead (§4.10) —
  the xorlo-era reading that composes with witness export and termsets,
  and the only default under which collective predicates survive
  quantification (`su'o prenu cu jmaji`; P4) — with
  the CLL-literal global reading available as `GlobalExactly` and the
  each-reading as `Distrib`/`lu'a`.
- **P18** Connective scope from surface grammar; accessibility rows are
  meaning; `na` ≡ left-edge `naku` with ch. 16 flip rules.
- **P19** UI target = grammatically attached constituent (text-to-reading),
  a first-class value in the term; modifier composition in surface order.
- **P20** `da` ranges unrestricted; `poi` is the only domain restriction.
- **P21** Two truth values; partiality by projective definedness.
- **P22** Inner `no`: a description with inner `no` never lowers through
  `Refer` (plural references are nonempty by type); it is
  **special-cased at the mapping layer** to the zero-count schema —
  `lo no broda` in a bridi frame `R[·]` lowers to
  `(No (λ {$x :: Entity} {(broda $x)}) (λ {$w :: Referents Entity}
  {R[$w]}))`, guskant's unofficial
  `naku su'oi da poi ke'a broda` relativized to the frame ("gadri: an
  unofficial commentary from a logical point of view", the "Cannot say
  zero" section). This is what makes answer substitution work: `lo xo
  prenu cu jmaji …` answered by `no` is elliptical `lo no prenu cu
  jmaji …`, and `go'i`-inherited frames likewise. Anaphora to an
  inner-`no` description is inaccessible (`No` exports nothing) — there
  is nothing to refer to. `no lo broda` remains the fully explicit outer
  form.
- **P23** `ba'e` = sign-level focus; `du` = `=` between first-order
  individuals and `CoRef` between plural sumti (§4.5).
- **P24** Fresh event per bridi unless shared explicitly; ZAhO pinned as
  boundary-relation shape, contours filled lexically.
- **P25** Lexical argument rows take plural references, not sets. The
  set-typed alternative was examined in full: under the
  discipline of §4.8's representation note the two designs are
  intertranslatable, so the choice is architectural, and this
  specification chooses the design in which the discipline is
  type-theoretic — nonemptiness in the type, the member-wise/object-wise
  distinction as a sort split (`Referents<T>` vs `Set<T>`) rather than
  a per-place convention, and no atomistic basis imposed. Set objects
  keep their places where Lojban talks about collections as
  individuals (`lo'i`, `cmima`, `kampu`, `sisku` x3, the set
  operators); the "distributive" value of the lexicon's plurality
  field is defined by subreference monotonicity (§10). Reopens on the
  rationale's standing invitation: a construction where
  set-objecthood at a lexical place does work member-wise predication
  plus `SetOf` cannot.
- **P26** Prenex order is scope order (CLL 16.2; the P18 surface
  doctrine at the prenex); topic `zo'u` resolves by a `Vague`
  `TopicResolution` — an admissible unfilled place of the open
  comment frame, or `srana`-aboutness to the closed comment
  (CLL 19.4's own vagueness, typed); no segment-state effect.
- **P27** Imperative and address: `ko` = the active addressee with
  command force on the nearest **performed** clause — no force
  extrusion through `Reify` or quotation; `doi` performs `Vocative`
  and ⊳ binds the active `do` (CLL 2.14); the Audience projection is
  never mutated — each utterance's ctx carries its own audience.
- **P28** `do'i` is `Context` at the salient transcript token/span
  (`Vague` only in span boundaries); `la'e` over utterance anaphors
  crosses host-sorted through `ActContent ∘ RealizedAct` (§7.4 — the
  partiality is `RealizedAct`'s; `ActContent` is total at
  assertions) — no universal coercion (P13 applied at the
  token sort).
- **P29** `cu'o` is an opaque lexical relation with a `Number` place
  in [0,1]; the model supplies the measure; **no probability
  calculus** enters the core (the `JeiRel`/`TruthValueDegree`
  precedent).
- **P30** `bu'a`-series = typed quantification at `PredTerm<ρ>` —
  variables, not objects; exact-row consistency across occurrences;
  non-`su'o` quantifiers prenex-only (CLL 16.107); only pure
  higher-order restrictions type. `cei`/`broda`-series bind bridi
  **templates** (fills, tense, negation; later fills override —
  CLL 7.5), not bare relation values.
- **P31** `ja'a`/`je'a` are transparent identities that ⊳ override
  inherited negation in pro-bridi expansions (`ja'a go'i` over a
  negative template removes the negation); no fourth `Scalar` kind.
- **P32** Sentence-level **logical** connection is **one performance
  of the connected content** (forced by `.i ja`; stated for the
  content-taking forces, interrogative hosts querying the connected
  content; `.i joi` stays in the discourse `Do` arm); `.i TAG bo`
  exposes both event binders with the tag
  conjunct inside the performed content.
- **P33** Jek at the tanru-unit locus = `TanruLinkConnect`: shared
  head asserted once, one `Vague` link per conjunct, connective over
  the link applications; distinct heads connect as whole
  predications.
- **P34** `vu'o` distributes an incidental clause **once per
  immediate connectee** (never collectively over `Combine`, never
  member-distributed into a plural connectee); restrictives restrict
  each operand under the connective structure; group-forming joiks
  take the clause on the resultant object. CLL 8.8 attests the
  incidental case; the restrictive rule is this specification's
  extension.
- **P35** `n roi` **replaces** the single-event existential closure
  with the counted instantiation-set schema (Card over distinct
  eventualities in the interval); the default interval is a
  Context-recovered anchor with `Vague` extent.
- **P36** `ma'o`'s operand-to-operator reading is a `Context`
  recovery of the intended function — never a constant-function
  default.
- **P37** `ji'i` is position-indexed, and both positions denote
  `Vague`-selected `Number`s: prefix/medial over the
  `AdmissibleTolerance` region, suffix over the `AdmissibleRounding`
  preimage (the stated digits exact by the region's construction),
  directionally under `ma'u`/`ni'u`; both regions VC1-nonempty.

## 14. Gap register

Meanings this specification currently assigns no analysis, each with the
reason; a gap is an obligation on future revisions, never a license to
approximate:

- **`da'i` and counterfactual/hypothetical mood.** The discursive `da'i`
  marks content for evaluation under a hypothetical (possibly
  contrary-to-fact) scenario; CLL gives it no scope semantics, no
  persistence rule, and no scenario-identity criterion, and the core
  assigns its readings no analysis. The world-indexed model (§5.1) fixes
  the shape of any treatment — a shift of the evaluation world, a new
  member of the `Shift` operator family of which `InContext` is the
  utterance-context member (the two shift different indices and must not
  be conflated), never world variables in terms —
  and a treatment must define three things: (1) the **scope** of the
  shift (attached act only, persistence across `.i` until reset, reset at
  `ni'o`?); (2) **dynamic binding under the shift** — `da'i su'o gerku cu
  klama .i ri melbi` needs the hypothetical dog accessible to `ri`, i.e.
  the accessibility table commuting with the shift; (3) **scenario
  identity** across repeated `da'i` (`da'i mi ricfu .i da'i mi citka lo
  nobli` is one scenario), which is the dimension most likely to force
  new machinery — attempt a constraint form (same segment, no reset,
  compatible content) before conceding a visible scenario binder.
  Boundaries: `da'i` inside `Reify` needs nothing new (the reified
  intension is hypothetical); inside attitude complements it composes
  with the attitude's worlds; inside quotation it shifts nothing.
- **Generic anaphora** to `Generic` predications (§5.8).
- **`Generic`'s inference theory.** The operator is typed and its
  normality reading stated (§5.8), but no entailment axioms are yet
  fixed, so `Generic` currently licenses no inferences beyond typing;
  candidate axioms are under review, and until they land the operator
  is an interface with a stated intended reading, not a source of
  consequences.
- **ZAhO contours** pending their lexicon rows (P24); habituals (TAhE)
  likewise.
- **Exotic donkey configurations**: anaphora out of disjunctive
  restrictors; stacked indefinites with split anaphora (§5.6).
- **Termset witness export** (joint anaphora to termset selections) and
  mixed-quantifier termsets where no coherent product reading exists
  (P17).
- **Reified predicates above row ⟨⟩** (§9.1's reservation): property
  and relation *objects* — referents for `lo ka` with
  discourse-referent behavior (`lo ka ce'u klama goi ko'a`, anaphora
  and quantification over property *objects* — distinct from the
  `bu'a`-series, which quantifies predicate-typed **variables** at
  `PredTerm<ρ>` with no objects involved, P30), the
  non-propositional readings
  of the experimental `me'ei`/`me'au` pair, the plural-reference
  `me'au` case (§9.1's singleton condition; the universal reading is
  the recorded candidate), `se du'u` under `ce'u` extraction (§9.2),
  the Rosta
  all-`ce'u` `si'o` (a genuine predicate nominalization into concept
  objects — the one explicit-`ce'u` reading outside `ka`/`du'u` that
  is reserved-family territory proper),
  and the open design points a
  family raises: row-isomorphism under `se`-relabeling, and typed
  cross-row operators (identity *within* a row is already fixed
  extensional over `PredTerm`, §9.1). The baseline lowers `lo ka`
  directly to the λ and defines reification at row ⟨⟩ only. The
  **adoption contract**: adding the family is additive — an indexed
  first-order sort family beside `Set<T>`/`Sign<K>` (§3.1's reserved
  opening) whose members are ordinary domains for `Refer`, anaphora,
  descriptions, and typed quantifiers; application-consuming lexical
  places stay `Fn`-typed and `lo ka` keeps its direct-λ lowering
  there, reified objects entering at referent positions with the
  row's crossing pair mediating (`me'ei P` ↦ the row's reification;
  `me'au` consumes through the row's `Holds`, plurality rule as at
  row ⟨⟩) — so adoption fills this declared hole without retyping
  any baseline place or reopening the bridge.
- **Explicit `ce'u` in the non-`ka`/`du'u` abstractors** (§11): each
  needs a **result-specific typed analysis** — an argument-indexed
  amount abstraction for `ni`, and per-abstractor codomains for
  `jei`/`li'i`/the event abstractors likewise — none of them a
  reified `PredTerm<ρ>`, so this is its own gap, not part of the
  reservation above (whose one member from this territory is the
  all-`ce'u` `si'o` listed there).
- **The non-numeric `me … me'u MOI` composite** (CLL Example 18.94's
  `cu'o` snowball): its reading would need value-indexed MOI families
  beyond the `Number` index (§12); no analysis is assigned.
- **MEX beyond the library fragment**: non-decimal bases, arrays,
  indefinite operators.
- **Prosody and stress** as meaning carriers; conversational repair as
  reportable structure beyond quotation.

## 15. Adequacy

The coverage claim of this specification: every meaning expressible by a
Lojban utterance under a resolved reading either (a) denotes a core term
by the schemas of §11, (b) is a library form of §12, or (c) appears in
the gap register §14 with its reason. Clause (c) is an accounting of
honesty, not a denotation: a gap-registered meaning has no core term
yet, and the header's every-utterance-denotes claim holds exactly over
(a) and (b) — the analyzed coverage. The coverage matrix:

| Construct family | Schema | Library | Gap | Samples |
|---|---|---|---|---|
| predication, places, `zi'o`, conversion | §11 ¶1 | — | — | §1 |
| tense/aspect/space, BAI, CAhA | §11 ¶5 | tag helpers, `MotionVector`, capability, `nu'o`/`pu'i` | ZAhO contours, TAhE | §2 |
| gadri, descriptions, `lo'e`/`le'e` | §11 ¶2 | `Named`, `MaxRefer`, `Generic` at §5.8 | generic anaphora | §3 |
| relative clauses, `goi`, `voi` | §11 ¶3 | audience-deleted `skicu` (P10) | — | §4 |
| quantifiers, termsets, negation scope | §11 ¶4 | GQ family, `GlobalExactly`, `Distrib` | mixed termsets, termset export | §5 |
| vague quantities, gradables | §6.4 | degree GQs, `Grade` | — | §5, §8 |
| anaphora, KOhA, `ra'o` | §11 ¶6 | — | exotic donkeys | §4, §5 |
| abstractions, `tu'a`, `jai`, `mo'e` | §11 ¶7 | abstraction relations, `AmountValue`, `JaiPromote` | reified predicates; non-`ka`/`du'u` `ce'u` cases (§14) | §8–§10 |
| questions, answers, `kau` | §11 ¶8 | domain-enumeration schemas | — | §6 |
| indicators, evidentials, discursives, COI, `na'i` | §11 ¶9 | discourse relations, focus, objection, COI schemas | — | §7 |
| quotation, signs, letterals | §11 ¶10 | sign constructors | — | §10 |
| MEX | §11 ¶10 | `te'a`, `gei`, indexing, `Interval`, the conversion crossings, numeral schemas (`ji'i`, `da'a`, punctuation) | bases, arrays, indefinite operators, general `mo'e` | §10 |
| plurality, masses, reciprocals | §4.8, §11 ¶2 | `lu'a`, `Reciprocate` (`simxu`/`soi`) | — | §3, §5 |
| prenex, topic, imperative, vocative | §11 ¶1a | `Topic`/`TopicAdmissible`, `RealizedAct`/`ActContent` (§7.4) | — | — |
| associators, `zi'e`, `vu'o`, `me`, MOI, group/set gadri | §11 ¶2–3, ¶10 | `MePred`, the MOI families | — | — |
| utterance anaphora, `da'o`, NIhO depth, MAI | §11 ¶6, §7.2 | `EnumerationOrdinal` | — | — |
| relation variables, templates, connective residue, BIhI, ROI | §11 ¶4–5 | `TanruLinkConnect`, region formers, `SelectAllBut` | first-order restrictive clauses on `bu'a` (§14); the non-numeric MOI composite | — |
| hypothetical mood | — | — | `da'i` | §13 |
| repair, prosody | §11 ⊳ | — | registered | §13 |

A claim of coverage that cannot cite a schema, a library definition, or a
gap entry is a defect in this document.

### Appendix: the kernel

The primitive inventory, for reference — audited so that nothing sits
here by historical accident; the criterion is that a primitive has no
term-language expansion, only its prose-and-axiom definition. The
primitives: the type formers of §3 (except `PredTerm`, a transparent
alias); function types and application over labelled records (the
pure λ-substrate — the binder *word* `λ` is `MakeLambda`'s alias,
§7.7, counted once there); `bind`, the computation carrier's
sequencing operation (the surface `Bind` binder word is defined,
§7.7); lexical
predication (dictionary relations as constants); `DropPlace`;
`¬ ∧ ∨ → ↔ ⊕ ∀ ∃ =`; `Combine`, `Among`; `SetOf`, `Card`, `∈`, the
arithmetic base; `Refer`, `Context`, `Vague`, the `Select` family;
`Presuppose`, `Supplement` (display is its §7.6 spelling); `Generic`;
`Reify`/`Holds`; `TanruAdmissible` (the `Tanru` operator itself is
defined, §6.2), `Scalar`; the
force constructors, `Perform`, `Do`, `NewTopic`, `Resume`; the sign
constructors (where quotation's opacity lives), the quote former with
`Expression<Γ,A,ε>`/`Telescope` and the floor `Interpret` family, and
`MakeLambda` (§7.7 — `λ` is its alias);
`InterpretContent`/`InterpretAct<F>`, the partial
`RealizedAct<F>`/`RealizedDiscourse` projections with the total
`ActContent`, and the token/sign
fact relations; the declared MEX conversion crossings, `During`,
`EnumerationOrdinal`, and the
`SelectAllBut` member of the selection family (§12); `Deictic`, `ShiftedGround`, `InContext`, and the
context projections; `Polar`, `OpenQ`, `QuestionOf`, `Answer` with the
answer-selection values; the abstraction relations (§9.2, minus the
derived `DuhuRel`), the crossings `AmountValue`/`TruthValueDegree`/
`EventOfContent`, `InnatelyCapable`, `MotionVector`; and the axiomatic
admissibility predicates (§12). **Defined forms** (term-language
expansions; everything else is library or lexicon): `Close`, `⊤` (the
empty conjunction, §2), `At` with
all fill notation, `Let` and the braced binder spellings with
`MakeBind`/`MakeLet`/`MakeApply` and the facade schema (§7.7), the
demonstratives, `Tanru` (§6.2), `TanruLinkConnect`, `MePred`, the
region formers (`MetricBall`/`SpanRegion`/`RegionComplement`), the
`Topic` lowering,
`SelectSome`, the `Utterance`/`Sign` entry notations (§7.4),
`PredTerm`, `UnitSet`/`CardBasis`, `DuhuRel`,
`ContextualAnswer`, and the library of §12. The
[catalog](catalog.md) carries one entry per name — prose, formal
definition where one exists, purpose, example, and links; each name's
content-word status is in §16.

## 16. The content-word program

The end state of §1.2's program: only content words serve as predicates.
This chapter specifies what that means operator by operator, how far the
reduction over first-class signs goes, and where it provably stops.
**Status:** the chapter is the program's normative discipline plus its
initial audit; the full per-entry catalog accretes under §16.2's schema,
and its completion is a standing obligation of this specification (like
the gap register), not an achieved end state.

### 16.1 Three cash-out classes

"Placeholder for a content word" cashes out differently across the
inventory:

- **Class P — genuine predicates** (relations over individuals, acts,
  tokens, signs): the direct targets. Each is *exact-fit* (an existing
  word's official row serves, possibly through place baking, deletion,
  or `se` — the standard combinators), *near-fit* (an existing word
  would serve after a **proposed redefinition**: exact current wording,
  exact proposed wording, blast-radius assessment, committee-decided,
  never silently applied), or *no-fit* (a coinage is owed; until coined,
  the PascalCase placeholder carries the predicate-style definition).
- **Class O — operators over content, computations, or signs** (`Refer`,
  `Context`, `Vague`, `Close`, `Bind`, the force constructors, the
  question formers, `Presuppose`/`Supplement`, `Tanru`/`Scalar`,
  `DropPlace`, the selections — while defined machinery like `At`
  (record application) and library λs like `JaiPromote` are Class M
  under §16.2's machinery status): not predicates over
  individuals. Their content-word fate is the sign reduction of §16.3,
  and it reaches exactly as far as the bootstrap floor of §16.4 permits.
  Where a natural *shadow relation* exists (a predicate that describes
  the operator's result — `xusra` for what `Assert` builds, `danfu` for
  answerhood, `smuni` for interpretation), the entry names it: the
  shadow is real vocabulary either way, since acts, tokens, and signs
  are first-class objects the language must talk *about*.
- **Class M — metalanguage**: type formers, rows, typing judgments, the
  evaluator, metalanguage recursion in library definitions. **No content
  word is owed**, and the committee should coin none: a sort *predicate*
  (`fasnu` for eventhood) is a content word; the sort *system* is not.

### 16.2 Catalog entry schema

Each §16 entry carries: the placeholder name; a **predicate-style
definition** (an x1…xn row, even for binder- and force-like operators —
a binder relates a scoped sign to a closure, a force constructor relates
an act to its content); **status** (exact-fit / near-fit / no-fit /
machinery); **see-also** — nearby existing words with verified official
rows and the reason each does or does not serve; **proposed
redefinition** (near-fit only; the sole current near-fit is the
`-nmo` indicator-emotion family, §16.5, whose rows need the intensity
place — the remaining candidates are recorded with the combinator
route their adoption would take, §16.5's audit note stating which
routes still owe their expansion equations); and the
formal fields the reduction needs: *semantic class* (content-producing,
value-producing, computation-producing, binder-producing, act-producing,
type/index — determining what a definition may claim), *effect profile
and sequencing law* (computation-producing entries are not defined by
their predicate row alone), *binding arity and scope types* (binder
entries consume scoped signs, never raw text), *sign-operand policy*
(**active**: evaluation effects flow to the host; **inert**: the opacity
row applies — declared per word, immutable by definition), *stage
requirement*, and *basis or derived* status with the expansion equation
(derived entries terminate in basis vocabulary — Brismu's
dependency-order discipline).

### 16.3 Evaluation over signs: the adopted architecture

Signs stratify. Raw `Text` and the opaque sign kinds (§7.5) remain what
they are — quoted material, never auto-interpreted. The sign kind
**`Expression`** covers elaborated, *scoped* core expressions, with its
full term-language semantics — types, elaboration, interpretation, the
no-reification discipline, and the `MakeLambda` basis — in **§7.7**;
`{…}` is this specification's notation for it, and it is
**core-only notation** — no surface cmavo has, or may ever acquire,
active-eval semantics (reassigning `lu…li'u`, `la'e`, or `me'o` to
active evaluation would make quotation commit its speakers to quoted
referents: the paradigm rug-pull). Any future *spoken* evaluation word
is a new coinage through the lexicon program. What §7.7 adds to this
program: the binder words themselves (`MakeLambda` and its defined
kin) are sign-consuming *functions* — Class-O operators with
sign-typed places, content-word candidates like any other — and the
stage-schematic vocabulary is what makes a Lojban self-description of
these semantics well-founded (one text, meaningful at every stage,
describing the stage below).

Two evaluations, not one:

- **Inert evaluation** — sign to value, no effects — has two typed
  homes: *linguistic* signs interpret through the
  `InterpretContent`/`InterpretAct` family (§7.5), while
  *core-expression* signs interpret through the staged, typed
  `Interpret` family of §7.7, per category (a sentence-expression at
  `Content`, a sumti-expression at `RefComp`, a property-expression at
  a function type; one untyped `Eval` is not typable).
- **Active evaluation** — effects flowing into the host — exists at act
  level already: `Perform` of an interpreted act re-issues quoted
  discourse *with* its dynamics. Sub-sentential active evaluation (a
  defined gadri taking effect inside a host sentence's reference
  computation) is **floor** (§16.4): a content word can *describe* an
  evaluation's effects; describing an introduction does not introduce.

A mechanical `{}`-definition (sugar) is **admissible** only under the
soundness law:

- **S1 Accessibility uniformity** — the expansion preserves meaning
  under every row of §5.4, not merely at top level.
- **S2 Linearity** — effectful operand positions expand exactly once;
  operand sharing goes through explicit binding, never textual
  repetition (the `↔`/`⊕` lesson as a law).
- **S3 Identity preservation** — `Context` sites and keys, and `Vague`
  binding sites, map one-to-one through the expansion.
- **S4 Resolution first** — readings resolve (anaphora, donkey
  normalization, erasure, reading selection) *before* any expansion
  applies; `{}` boundaries are scope islands, and expansions are local
  where normalizations are global.
- **S5 Acyclicity** — definitions in dependency order; no definiendum in
  its own transitive definiens.
- **S6 Policy immutability** — no definition alters the active/inert
  policy of the signs it consumes.
- **S7 Typing immutability** — no definition relaxes a well-formedness
  side condition (§1.6); an ill-formed term stays non-denoting, never
  merely false.

### 16.4 The bootstrap floor

The reduction stops here; these are machinery, not content words, and
the doctrine sentence of §1.2 exempts them by design:

| Floor item | Why no content word can be it |
|---|---|
| scope and hygiene — realized as §7.7's quote former (elaboration, environments, capture-avoiding instantiation) | relocated, not discharged: raw text carries no capture-free binding; the quote former is where the machinery lives, and it remains machinery |
| staged, partial evaluation (`Interpret`, §7.7 — unreflectable: no `MakeEval`) | a same-stage total evaluator yields the liar diagonal; evaluation is defined at the stage above its operand, and elaboration is partial |
| the lexical basis interpretation | definitions bottom out: some words' meanings are model-given, or the dictionary is a cycle |
| effect sequencing | ordering of introductions, retrievals, and obligations is an operation, not a truth condition — a predicate's extension cannot carry it |
| effect-flow policy | active vs inert consumption is not at-issue content; it is declared per consuming word and enforced by the semantics — the braced spelling (§7.7) makes it visible in the syntax, which is display, not discharge |
| force performance | if asserting were predication, describing or quoting an assertion would perform it; `Perform` stays external |
| typing judgments | well-formedness is decided before terms denote; as at-issue predication it would turn undefinedness into mere falsity (S7) |

Sort *predicates* are content words (many exist: `fasnu` for
eventualities, `pruce` for processes, `namcu` for numbers, `sinxa` for
signs, …) — a consequence of the audit, not a separate program.

### 16.5 The audit (initial population)

Summary of the initial audit (full entries accrete under §16.2's
schema; every official row cited here was verified against the
official dictionary or CLL). One orthogonality governs the reading:
**content-word status is independent of term-language status** — an
"exact fit through combinators" records a committee-pending *adoption
plan* (the lexicon program never applies proposals silently), so a
relation with such a fit remains a term-language primitive until
adoption turns it into a defined form over the adopted word; and a
term-defined form (`UnitSet`, `CardBasis`) may still *owe a name*, its
no-fit entry being about the missing content word, not about
definability:

- **Adopted now (exact-fit):** `skicu` for the `le` description (P10,
  with the §11 anchoring clause); `cmene` (`Named`); `gunma`, `selcmi`
  (P5); `purci`/`balvi`/`cabna` (tense facets); `srana` (`tu'a`
  aboutness); `fasnu` (actuality, realization); the BAI tag gismu that
  double as the named tanru-link relations (`tadji` manner, `mukti`
  purpose, `krasi` source, `marji` material, `pilno` instrument, `simsa`
  resemblance).
- **Candidate fits through combinators (adoption blocked on displayed
  equations):** `klani` for `NiRel`/`AmountValue` (bake the measured
  place; its scale place is the crossing's x2); `se lifri` for
  `LihiRel`; `sidbo` for `SihoRel`; `pruce` for `PuhuRel` (delete
  inputs/outputs); `mintu` for `CoRef` (delete the standard);
  `frica`/`simsa` for `Contrast`/`Parallel` (act-typed relata);
  `smuni` for the interpretation crossings; `sinxa`/`cusku`/`tavla`
  projections for the token-fact vocabulary. **Audit note:** for the
  content-parameterized relations (`NiRel`, `LihiRel`, `PuhuRel`,
  `SihoRel`) the official rows carry no place for the abstracted
  content `c`, so place surgery alone cannot derive `XRel(c)` — each
  candidate owes the displayed equation linking its row to `c` (e.g.
  through `EventOfContent` or an explicit realization conjunct)
  before it can be called exact; `smuni` and the token-fact
  projections likewise stand as shadows until their crossings are
  derived rather than described. Until those equations exist these
  are see-also candidates, not adopted fits.
- **Near-fit (proposed extension):** the **`-nmo` indicator-emotion
  family** for the indicator relations: community fu'ivla of the form
  *indicator* `zei cinmo` — `uinmo`
  ("feels happy about", glossed synonym of `gleki`), `u'inmo`,
  `le'onmo`, `fi'inmo`, `ue'inmo`, `uu'inmo`, `a'anmo`, … — one word
  per indicator by a mechanical derivation that extends to every UI
  and both `nai` poles, where the emotion gismu cover only a
  scattering. The generic `inmo` — "feels the emotions expressed by
  indicators x2 (text) about x3" — is the family's schema, and a
  dictionary-attested relation with a sign-typed place: exactly the
  shape §16.3 predicts. The near-fit delta, recorded per §16.2: the
  jbovlaste rows are
  unofficial and carry experiencer × target only, so this
  specification's intensity place is an extension to propose (the
  `le'onmo` entry's own `no'e`/`to'e` note shows the family already
  composes with the scalar operators); the emotion gismu (`gleki`,
  `badri`, `djica`, `ganse`, …) remain see-alsos.
- **No-fit (coinage owed; placeholder carries the definition):**
  `Among`, `Combine` (the plural algebra — `pagbu`/`cmima`/`gripau` all
  cross the plurality/object line and are rejected), `ZuhoRel`,
  `SuhuRel`, `JeiRel`, `Reify`/`Holds` (one coinage, two directions via
  `se`; see-also the experimental `me'ei`/`me'au` pair, the attested
  surface exponents of the two directions — §9.1), `UnitSet`/`CardBasis` (see-also `zilkancu`, which carries two
  competing community definitions and guskant's own vagueness warning —
  the unsettled record supports placeholder status), `InRegion`,
  `AdmissibleThreshold`, `Addition`, `MetalinguisticallyDefective`,
  `Realizes`/`TextOf`/`Quotes`, `Vocative`/`Mention` shadows.
- **Rejected fits (the method note):** `fadni` for `Generic` — its
  official row ("x1 [member] is ordinary/… typical/… in property x2 (ka)
  among members of x3 (set)") is verbatim the specimen theory the
  split-normality witness
  killed (the `Generic` ruling, P11): the audit's standing warning that
  surface resemblance must be checked against the semantics before
  adoption.
- **Class O shadows (vocabulary either way):** `tanru` — the
  modification operator's own name, and the sharpest shadow in the
  inventory: its official row "⟨1⟩ is a binary metaphor formed with ⟨2⟩
  modifying ⟨3⟩, giving meaning ⟨4⟩ in usage/instance ⟨5⟩" (operands
  "both text or both si'o concept") is the §6.2 semantics stated as a
  dictionary entry, place for place — x2/x3 are typed "both text or
  both si'o concept" (inert operands in §16.2's sense), x4 is the
  resolved
  reading `TanruAdmissible` admits, and x5 is the occasion that
  resolves it: the dictionary itself records tanru meaning as
  per-occasion, which is §6.1's Vague doctrine in an official row.
  (`Tanru` the operator stays Class O — composition is an operator —
  but its shadow relation needs no coinage at all.) Further: `xusra`
  (assertion),
  `preti` (question text — its quoted-text x1 fits the sign machinery),
  `minde` (command), `cinmo` (display), `danfu`/`spuda` (answerhood /
  answering act), `drata` (the individual-level shadow of scalar
  otherness).

## References

Works cited across this document set (specification, primer, rationale,
samples). Inline citations name the work and, where applicable, the
chapter/section or dictionary entry. Living sources (wiki pages,
jbovlaste) were last verified 2026-08-22; the repository snapshots
used for source verification are noted per entry.

- **CLL** — Cowan, John Woldemar, *The Complete Lojban Language*,
  Logical Language Group, 1997. Chapter/section citations ("CLL 15.4" =
  chapter 15, section 4) and example numbers (chapter-sequential:
  "Example 16.34") follow the maintained **Contemporary Lojban
  Language** edition (<https://github.com/int19h/cll>), an up-to-date
  fork of the book; the in-text xorlo ratification cited in the header
  is its §6.2 ("The meaning of `lo` given here is the fruit of a reform
  the community calls 'xorlo', after the nickname of its principal
  author; it is now the ratified standard"). The original text is also
  served at <https://lojban.github.io/cll/>; its section and example
  numbering differ in places from the citation edition. (Snapshot:
  fork commit `82f72ae5e19bd4ea5cd9b800433e6a301e7aa0d4`, 2026-08-17.)
- **The official dictionary (jbovlaste)** —
  <https://jbovlaste.lojban.org/>. "Official" place structures and
  definitions are the entries credited to *officialdata*; entries are
  cited by word.
- **The baselined gismu list (1994)** — the official gismu wordlist
  with its original place-structure annotations,
  <https://lojban.org/publications/wordlists/gismu.txt>.
- **xorlo** — "How to use xorlo",
  <https://mw.lojban.org/papri/How_to_use_xorlo>.
- **guskant** — "gadri: an unofficial commentary from a logical point
  of view",
  <https://mw.lojban.org/papri/gadri:_an_unofficial_commentary_from_a_logical_point_of_view>.
- **Brismu** — *brismu: a relational interpretation of Lojban*,
  <https://brismu.systems/>; the chapter "Sets, not Masses" is at
  <https://brismu.systems/sets-not-masses.html>.
- **solpahi** — "A Simpler Quantifier Logic", 2016,
  <https://solpahi.wordpress.com/2016/09/25/a-simpler-quantifier-logic/>.
- **Eberban** — reference grammar,
  <https://eberban.github.io/eberban/> (source:
  <https://github.com/eberban/eberban>); chapters cited by title
  ("Logic framework", "Dictionary conventions", "Eberban from
  scratch"). (Snapshot: commit
  `65a4bc1d64bf7aaf2ed6b11d8758c10e301f605d`, 2026-08-15.)
- **Toaq / Kuna** — Toaq Delta reference grammar,
  <https://toaq.net/refgram/introduction/>; Kuna, its reference semantic
  implementation, <https://github.com/toaq/kuna> (the effect-constructor
  inventory cited in the charter is Kuna's semantics modules as of the
  Delta-era implementation, 2026; snapshot: commit
  `91b20daaac683f568557cc1badc085f8901d64f4`).
- **And Rosta et al.** — "ka, du'u, si'o, ce'u, zo'e", Lojban Wiki,
  <https://mw.lojban.org/papri/ka,_du%27u,_si%27o,_ce%27u,_zo%27e>
  (the n-adic abstraction doctrine discussed in rationale §2.10).
- **Chierchia & Turner** — Chierchia, Gennaro and Turner, Raymond,
  "Semantics and Property Theory", *Linguistics and Philosophy* 11(3),
  1988, pp. 261–302 (the nominalization/predicativization pair behind
  §9.1's reservation).
- **BPFK Abstractors** — "BPFK Section: Abstractors", Lojban Wiki,
  <https://mw.lojban.org/papri/BPFK_Section:_Abstractors> (the
  proposed `ce'u` definition discussed in rationale §2.10 — a
  proposed, partial extension: `ce'u` "almost solely used in `ka`",
  with `si'o`/`du'u`/`su'u` noted as able to "make some sense").
- **Boolos** — Boolos, George, "To Be Is to Be a Value of a Variable
  (or to Be Some Values of Some Variables)", *The Journal of
  Philosophy* 81(8), 1984, pp. 430–449.
- **Oliver & Smiley** — Oliver, Alex and Smiley, Timothy, *Plural
  Logic*, 2nd edition, Oxford University Press, 2016.
- **Wand** — Wand, Mitchell, "The Theory of Fexprs is Trivial",
  *Lisp and Symbolic Computation* 10(3), 1998, pp. 189–199 (the ground
  for §7.7's no-reification discipline).
- **Nanevski, Pfenning & Pientka** — "Contextual Modal Type Theory",
  *ACM Transactions on Computational Logic* 9(3), 2008 (the contextual
  type `[Γ ⊢ A]` is §7.7's `Expression<Γ, A>`).
- **Harper** — Harper, Robert, *Practical Foundations for Programming
  Languages*, 2nd edition, Cambridge University Press, 2016 (abstract
  binding trees — the formulation behind elaborated, α-classed quotes).
- **Taha & Sheard** — "MetaML and Multi-stage Programming with
  Explicit Annotations", *Theoretical Computer Science* 248, 2000
  (typed staging with open code).
- **Davies & Pfenning** — "A Modal Analysis of Staged Computation",
  *Journal of the ACM* 48(3), 2001 (staging as modal logic — the
  evaluation-above-stage discipline).
- **Heim & Kratzer** — Heim, Irene and Kratzer, Angelika, *Semantics in
  Generative Grammar*, Blackwell, 1998.
- **Groenendijk & Stokhof** — Groenendijk, Jeroen and Stokhof, Martin,
  "Dynamic Predicate Logic", *Linguistics and Philosophy* 14(1), 1991,
  pp. 39–100.
- **Kamp** — Kamp, Hans, "A Theory of Truth and Semantic
  Representation", in *Formal Methods in the Study of Language*,
  Mathematisch Centrum, 1981 (Discourse Representation Theory).
- **Link** — Link, Godehard, "The Logical Analysis of Plurals and Mass
  Terms: A Lattice-theoretical Approach", in *Meaning, Use, and
  Interpretation of Language*, de Gruyter, 1983.
- **Hamblin** — Hamblin, Charles L., "Questions in Montague English",
  *Foundations of Language* 10(1), 1973, pp. 41–53.
- **Karttunen** — Karttunen, Lauri, "Syntax and Semantics of Questions",
  *Linguistics and Philosophy* 1(1), 1977, pp. 3–44.
- **Potts** — Potts, Christopher, *The Logic of Conventional
  Implicatures*, Oxford University Press, 2005 (published online
  December 2004).
- **Searle** — Searle, John R., *Speech Acts: An Essay in the Philosophy
  of Language*, Cambridge University Press, 1969.

# Catalog of the core forms

One entry per named identifier of [the specification](spec.md), in two
sections. **Primitives** are the names with no term-language expansion:
their entire definition is the prose and axioms the spec gives them,
restated here. **Defined forms** are everything else — each expands, by
its `≝`, into primitives and other defined forms, and the expansion is
its specification. Every entry gives the informal definition first
(even where a formal one exists), then the formal definition if there
is one, then what the form is for with an example of use, then where
the details live ([spec](spec.md) by section, [primer](primer.md) by
chapter, [rationale](rationale.md) where the shape is argued).

Tightly coupled families (the force constructors, the sign
constructors, the abstraction relations, the cardinal quantifiers)
share one subsection with per-name coverage inside it, so that their
common story is told once.

The scope is the **term language**: model-theory symbols
(`Comp`, `InformationState`, `Obligations`, `Unit`, the `ctx` record,
the world set W) are not forms and live in the short appendix at the
end. Two notational facts are catalogued here once rather than per
entry:
multi-place fill notation (positional fills, `:n` labels, FA routing,
`se`-conversion) desugars to nested single-place `At` (spec §4.1); and
a specimen displayed as a bare act denotes the one-act discourse
performing it (spec §7.1).

## 1. Primitives

### 1.1 The sort hierarchy

**Informally.** First-order individuals are sorted: `Entity` at the
top; beneath it `Eventuality` (with subsorts `Achievement`, `Process`,
`Activity`, `State`, `Experience`, and `Locution`, an uttering event),
`Location`, `Time`, `Amount`, `Scale`, `Epistemology`, `TruthValue`,
`Concept`, `AbstractNature`, `Proposition`, `Question`, `Number` (with
`Natural` and `Cardinal` beneath it), `Text`, the collection and sign
sorts of the entries below, `UtteranceToken`, and `Ground`. Subsorting
is subset inclusion; a subsort term stands wherever the supersort is
required, never conversely; there are no implicit crossings between
sorts (pin P13).
**For.** Lexical selection — `fasnu` selects an `Eventuality` where
`barda` selects an `Amount`-bearer — and the no-coercion discipline:
swapping a `du'u` for a `ni` is ill-typed, not false.
**See.** [Spec §3.1](spec.md); [primer ch. 8](primer.md).

### 1.2 `Referents<T>` — the plural reference type

**Informally.** Nonempty, number-neutral pluralities of `T`s: one or
more things *referred to together*, which are not a set-object, not a
mereological sum, and not a group — no object exists over and above
the things. There is no empty plural reference; a single `T` lifts to
a singleton reference at referential positions. Covariant in `T`.
**For.** The type of every ordinary lexical argument place. `mi jo'u
do bevri lo pipno` — a plurality carries; no set carries anything.
**See.** [Spec §3.2, §4.8](spec.md); [primer ch. 3](primer.md);
[rationale §1.7, §2.8](rationale.md).

### 1.3 `Set<T>`, `Group<T>`, `List<T>` — collection object types

**Informally.** First-order *objects* that package other things: a set
(extensional, with membership and cardinality and possibly empty), a
group (a concrete collective with its own properties — a crowd can
surround a building), a list (order-bearing). Distinct from plural
reference: none unwraps implicitly to its members.
**For.** `lo'i gerku` denotes a `Set<Entity>`; `loi prenu` a group via
`gunma`; `ce'o` builds lists. The two-sort split (reference vs object)
is what makes `lo selcmi cu simxu` unambiguous.
**See.** [Spec §4.9](spec.md); [primer ch. 3](primer.md) ("Not the
same as!"); [rationale §2.8](rationale.md).

### 1.4 `Fn` and `EFn` — the function types

**Informally.** `Fn<(A…), B>` is the pure function type: a body that
performs no dynamic effects when its result is evaluated — no
introductions, no contextual retrievals, no projective emissions.
`EFn` is the effectful arrow. Purity is demanded exactly at set
comprehension, quantifier and `Generic` restrictors, and selection
restrictors; nuclear scopes are `EFn`.
**For.** Properties are `Fn<(T), Content>`; `ka` abstractions are λs
at these types. A restrictor that smuggles a `Refer` simply fails to
have the pure type — the purity discipline is a typing fact, not an
algorithm.
**See.** [Spec §3.3](spec.md); [rationale §1.14](rationale.md) (the
pure/effectful seam).

### 1.5 `Record ρ` and `Label<ρ>` — rows

**Informally.** A place row ρ is a finite sequence of labelled, typed
places; `Record ρ` is the type of complete fills for it; `Label<ρ>` is
the finite type of its place labels. Labels are semantically real:
Lojban reorders, deletes, and *asks about* places by label.
**For.** `klama fi'a ti` is a question over the compatible-label
refinement of `Label<ρ(klama)>` (spec §4.7 — sort-incompatible places
and the event place contribute no branch); the
fill notation computes labels (spec §4.1). `PredTerm<ρ>` (defined
section) is the row-function alias over these. (`Record` and `Label`
are type constructors of the record theory, not first-order sorts —
they do not appear in §3.1's hierarchy.)
**See.** [Spec §3.3, §4.7](spec.md); [rationale §1.1](rationale.md).

### 1.6 `Content` — dynamic propositional content

**Informally.** The type of what can be asserted, questioned, negated,
and embedded. Its denotation is a world-indexed context-change
potential: run against an information state, it filters and extends
that state and accumulates projective obligations. No world variable
ever appears in a term.
**For.** Every bridi's meaning lands here before force applies.
**See.** [Spec §3.4, §5.1](spec.md); [primer ch. 1, ch. 4](primer.md).

### 1.7 `RefComp<T>` — reference computations

**Informally.** Computations that return a `T` while possibly
performing dynamic effects: introducing referents (`Refer`,
selections), consulting context (`Context`), or denoting
precisification families (`Vague`). Consumed by `Bind`.
**For.** The type of every description and selection before its
witness is bound.
**See.** [Spec §3.4, §5.2–5.3](spec.md).

### 1.8 `Act<F>` and `Discourse` — speech-act types

**Informally.** An `Act<F>` value is a force-tagged content package —
force `F` (Assertion, Question, Directive, Expressive, Address) plus
the content computation — built inertly: constructing an act runs
nothing. An act is a pure value, not a computation — only `Perform`
(§1.36) injects it into the dynamic carrier. `Discourse` is performed
discourse: sequences of performed
acts and transitions. A document denotes one `Discourse`.
**For.** Quotation and report: `mi cusku lu ko klama li'u` mentions a
directive without issuing it, because only `Perform` executes.
**See.** [Spec §3.4, §7.1](spec.md); [primer ch. 6](primer.md);
[rationale §1.11](rationale.md).

### 1.9 `Query<A>`, `Selection<A>`, `Bool` — question types

**Informally.** A `Query<A>` is a question with typed answer domain
`A`, denoting its answer-content function; a `Selection<A>` picks from
that domain; `Bool` is the two-element polar answer type (distinct
from the epistemology-relative `TruthValue` sort).
**For.** `xu`, `ma`, `mo`, `fi'a`, `pei` all land in `Query` at
different domains; `kau` supplies the contextual answer selection
inside `Answer` (a `Proposition` results), while `QuestionOf` reifies
a query as a `Question` object for question-object-selecting places.
**See.** [Spec §8](spec.md); [primer ch. 6](primer.md).

### 1.10 `Sign<K>`, `SignToken<K>`, `UtteranceToken` — sign types

**Informally.** Signs are quoted or mentioned linguistic material,
classified by kind `K` (Name, Sentence, Word, Letteral, Quotation,
MathExpression, Structured, Opaque, Text, Connective — and
`Expression` and `Telescope`, the elaborated-core-notation kinds,
§1.47);
sign tokens and utterance tokens are the concrete occurrences facts
attach to. Sign boundaries are opaque: no referent, presupposition, or
introduction crosses them.
**For.** Use/mention discipline — the reason Lojban can talk about
Lojban without paradox.
**See.** [Spec §7.4–7.5](spec.md); [primer ch. 10](primer.md).

### 1.11 `Ground`, `GroundDescription`, `Proximity` — deictic ground types

**Informally.** A ground is an orientation center with its perspective
facts — what demonstratives point against; `Proximity` is the closed
three-value type `Proximal | Medial | Distal`; ground descriptions are
the specifications grounds are constructed from.
**For.** `ti`/`ta`/`tu` and `ra'o`-style re-orientation.
**See.** [Spec §5.1](spec.md).

### 1.12 `Region<Scale>` — scale regions

**Informally.** Regions of a scale — poles, midpoints, intervals — the
values gradable cutoffs and scalar operators work over.
**For.** `Grade`'s vague cutoff and the `na'e`/`to'e`/`no'e` regions.
**See.** [Spec §6.3–6.4, §12](spec.md).

### 1.13 The pure function substrate

**Informally.** Typed functions over labelled-record-aware parameters,
with juxtaposition as application — the pure functional substrate:
function types, application, and the laws (β-reduction, substitution,
α-conversion are unconditionally meaning-preserving here, which is
exactly what the effectful fragment must not silently inherit — see
`bind`). The binder *word* `λ` is not a second primitive: it is the
alias of `MakeLambda` (§1.48), the one primitive sign-function, and
this entry's abstraction notation is that word's application.
**For.** Properties (`ka` with `ce'u` = λ, pin P12), quantifier
bodies, everything higher-order.
**Example.** `lo ka se klama` →
`(λ {$x :: Referents Entity} {(Close (klama :2 $x))})`.
**See.** [Spec §4.4](spec.md); [primer ch. 8](primer.md).

### 1.14 `bind` (and the `Bind` word)

**Informally.** The computation carrier's sequencing operation
`bind : Comp<A> × (A → Comp<B>) → Comp<B>`: run the computation once,
sequencing its effects before the continuation, and pass its *result*
— never the computation. It is function application under mandatory
call-by-value at computation types, made visible: the pure λ-fragment
keeps unconditional β-equality, and every effect-sequencing point is a
`bind` node the accessibility table can name. Uniform across the
computation categories: the continuation may yield content, a
reference computation, or a discourse (a bare act body stands for its
performing one-act discourse — spec §7.1's display coercion), so a
referent introduced before an act sequence stays bound across it. The surface binder word `Bind` — `(Bind {$x :: T} comp
{body})` — is the *defined* telescope-spelled face: it is the alias of
`MakeBind` (§2.28), which expands to `bind` over `MakeLambda`.
**For.** Cross-sentence reference: `(Bind {$cat :: Referents Entity}
(Refer mlatu-prop) {(Do (Assert …) (Assert …))})` — the
introduction runs once, the witness is reused in both acts.
Multi-binding `Bind` is left-to-right nesting (spec §5.2).
**See.** [Spec §5.2](spec.md); [primer ch. 4](primer.md);
[rationale §1.14, §2.4](rationale.md) (why not λ; why not CPS; the
statics/dynamics seam).

### 1.15 Lexical predication

**Informally.** Dictionary words (`klama`, `gerku`, …) are relation
constants over their labelled rows, with the row, defaultability,
scope policy, plurality behavior, meaningful deletions, and the rest
supplied by the lexicon interface. The core is parameterized over the
lexicon; a predication applied to fills for its row is `Content`.
**For.** Every bridi. `(Close (klama Speaker This))` — the remaining
places handled explicitly by `Close`'s contextual slots (or by λ or
`DropPlace`), never silently.
**See.** [Spec §4.1, §10](spec.md); [primer ch. 1](primer.md);
[rationale §2.6](rationale.md).

### 1.16 `DropPlace`

**Informally.** `(DropPlace R n)` is the relation with place `n`
*removed* — semantic surgery, not omission: the resulting relation has
no such role at all. Which deletions are meaningful, and what the
deleted role's absence means, is stated per entry in the lexicon.
**For.** `zi'o`. `mi klama ti zi'o` predicates a four-place going with
no origin role — something neither `zo'e` nor closure can say. Also
`voi` = `(DropPlace skicu 3)` (no audience role).
**See.** [Spec §4.3](spec.md); [primer ch. 1](primer.md) ("Not the
same as!"); [rationale §1.8](rationale.md).

### 1.17 `¬`, `∧`, `∨`, `→` — the dynamic connectives

**Informally.** Classical truth conditions plus a normative
accessibility row each: `∧` passes introductions left to right and
lets both survive; `∨` keeps them branch-local; `¬` lets nothing
escape; `→` feeds the antecedent's introductions to the consequent and
exports nothing. The rows are part of the meaning. (`⊤` — the
trivially true content, `∧`'s unit, spec §2 — is the defined empty
conjunction, not a further primitive.)
**For.** `ganai da mlatu gi da ciska` (donkey feeding), `.ija`
(branch-local), `naku` (blocking) — three policies no truth table
derives.
**See.** [Spec §4.5, §5.4](spec.md); [primer ch. 4](primer.md);
[rationale §1.5](rationale.md).

### 1.18 `↔`, `⊕` — biconditional and exclusive-or

**Informally.** Once-per-operand evaluation of two truth-functional
shapes, with nothing escaping. Primitive precisely because their
classical rewrites duplicate operand text — two `Context` sites,
doubled supplement handlers, reshaped accessibility — and no sharing
route exists in a calculus that (deliberately) lacks truth-capture
reflection.
**See.** [Spec §4.5, §5.4](spec.md); [rationale §1.5](rationale.md).

### 1.19 `∀`, `∃` — the logical quantifiers

**Informally.** Classical quantifiers over typed λ-bodies with
(multi-parameter) joint loci; restrictorless, domain-unrestricted
(`da` — pin P20). The restrictor position of derived quantifiers is
pure; body introductions are local per instantiation; exporting
quantifiers are built from selections, not from bare `∃`.
**For.** `ro da zo'u …` and the joint loci of donkey normalization.
**See.** [Spec §4.5, §5.6](spec.md); [primer ch. 4–5](primer.md).

### 1.20 `=` — typed equality

**Informally.** Primitive identity at every first-order sort — except
the constructive-only syntax kinds (`Expression`/`Telescope` signs: no
code equality, §1.47) — and at
the discrete index types (`Bool`, place labels, the closed
enumerations); never at the plural reference type, where co-reference
(`CoRef`, mutual `Among`) does the work; plural-sumti `du` lowers to
`CoRef` (P23).
**For.** `li re su'i re du li vo`; `ko'a du ko'a` reflexively true
under keyed retrieval (pin P16) — at `CoRef` when the referents are
plural.
**See.** [Spec §4.5, §4.8](spec.md).

### 1.21 `Combine`

**Informally.** Plural join: the reference to these-and-those
together. Associative, commutative, idempotent. With `Among` it is the
whole plural algebra: no atomicity, no covers, no distributivity
assumptions.
**For.** `jo'u`. `mi jo'u do` = `(Combine Speaker Audience)`.
**See.** [Spec §4.8](spec.md); [primer ch. 3](primer.md);
[rationale §1.7](rationale.md).

### 1.22 `Among`

**Informally.** The subreference order: these are some of those.
Axiomatized with `Combine` (`Among x y` iff `Combine x y` and `y`
co-refer). Singulars lift to singleton references, so `Among x r` with
`x` a unit reads "x is one of r".
**For.** `me`-style membership talk, `Distrib`, subreference selection
(`re lo mu plise`), and the subreference-monotonicity criterion of the
lexicon's plurality field.
**See.** [Spec §4.8, §10](spec.md); [rationale §1.7, §2.8](rationale.md).

### 1.23 `SetOf`, `Card`, `∈`, and the arithmetic base

**Informally.** Extensional set comprehension over a *pure* property;
membership; cardinality (`Card : Set<T> → Cardinal`); and the number
operators `+ − × ÷ < ≤` (with `>`/`≥` defined), partial operations
carrying projective definedness conditions.
**For.** Mathematics (`li`, `mekso`), the global readings
(`GlobalExactly`, `Most`), and `UnitSet`-based counting.
**See.** [Spec §4.9](spec.md); [primer ch. 5](primer.md).

### 1.24 `Refer`

**Informally.** Introduce a **new discourse referent**: a nonempty
plurality satisfying the given property veridically, fixed for its
force segment, accessible to later anaphora per the table. No implicit
quantifier, no uniqueness, no default cardinality (xorlo, pin P1).
Embedded under a quantifier it stays a referential constant — it does
not covary (that is the selections' job).
**For.** `lo`/`le`/`la` descriptions. `lo mlatu cu blabi .i ri jbena` —
the cat outlives its sentence and survives negation.
**See.** [Spec §5.3](spec.md); [primer ch. 3](primer.md);
[rationale §1.3](rationale.md).

### 1.25 `Context`

**Informally.** Retrieve a contextually salient value of the declared
type: nothing asserted, nothing introduced, recovery *expected* — if
the hearer cannot find the value, communication failed. Site/key
identity: one retrieval per syntactic site per performance; keyed uses
(unassigned KOhA) retrieve once per key.
**For.** Omitted places, `zo'e`, `co'e`, `do'e`, `zu'i`, salient
scales, episodic tenseless time (pin P8).
**Example.** `mi klama` — the destination is a `Context` slot; `mi na
klama` denies going *there*, not existence of a destination.
**See.** [Spec §5.3](spec.md); [primer ch. 1, ch. 9](primer.md);
[rationale §1.3](rationale.md).

### 1.26 `Vague`

**Informally.** Denote the nonempty family of admissible
precisifications, with *no fact of the matter* selecting one — the
speaker waives specificity. Composition is by the VC law: pointwise
lifting, one precisification per parameter per binding site, truth
simpliciter as supertruth. Never resolved by context, never coerced.
**For.** The tanru link, `tu'a`, soritical thresholds (`so'i`), `joi`'s
mixture kind, bare `jai`'s role.
**See.** [Spec §5.3, §6](spec.md); [primer ch. 9](primer.md);
[rationale §1.3](rationale.md).

### 1.27 `SelectExactly`, `SelectAtLeast`, `SelectAllBut` — the primitive selections

**Informally.** The quantifier-strength members of the `Refer`
family: introduce a witness reference of the stated cardinal strength,
with the restrictor pure and the strength n ≥ 1 (the zero floor, spec
§12: a witness reference is nonempty by type, so no zero-strength
selection forms). The witness laws: `(Distrib P w)` holds, and
`(CardBasis w P)` is `= n` (`SelectExactly`) or `≥ n`
(`SelectAtLeast`). Unlike `Refer`, a selection under a governing
quantifier is *dependent* — one witness per value of the governor (the
dependence law) — which is what dependent anaphora normalizes over,
and why no `Refer`-plus-cardinality spelling can replace them (a
`Refer` is a governor-invariant constant). Binding a witness never
re-evaluates a selection; distinct selections introduce distinct
discourse referents (introduction identity — the witness values may
still co-refer). `SelectSome` is **defined** (§2.22).
**For.** Bare-PA terms: `ci gerku cu bajra` selects a three-dog
witness and predicates running of it, neutrally.
`SelectAllBut n P` (`da'a`; default n = 1) is the complement-count
member: its witness satisfies P member-wise (`Distrib P w`) and
leaves exactly n P-individuals behind, spelled by `SetOf`
comprehension (spec §12); the omitted individuals are not a
parameter.
**See.** [Spec §5.6, §4.10](spec.md); [primer ch. 5](primer.md);
[rationale §1.6](rationale.md).

### 1.28 `Presuppose`

**Informally.** Impose a projective condition: it must hold at the
nearest boundary that can commit it (or be accommodated there), and it
survives negation, disjunction, conditionals, and question force.
Introductions inside the condition stay local to it. Polymorphic over
the computation categories —
`Presuppose : Content × Comp<A> → Comp<A>` (the §2.10 `MaxRefer` use).
**For.** `ro`-import (pin P2), definedness of partial operations,
lexical presuppositions. `naku ro gerku cu blabi` still grants dogs.
**See.** [Spec §5.5](spec.md); [primer ch. 5](primer.md);
[rationale §1.4](rationale.md).

### 1.29 `Supplement`

**Informally.** Commit a side content about an anchor while the
at-issue value passes through: new information, speaker-committed,
projecting past negation and question force. Dependent sides commit
per instantiation inside their binder. Not interchangeable with
presupposition: supplements always commit anew.
**For.** `noi`, `sei`, `to…toi`, content-level indicator display.
`xu lo gerku noi blabi cu melbi` questions beauty, never whiteness.
**See.** [Spec §5.5, §7.6](spec.md); [primer ch. 11](primer.md);
[rationale §1.4](rationale.md).

### 1.30 `Generic`

**Informally.** The axiomatic generic quantifier: relate a pure
restrictor and nuclear scope through a normality ordering that may
depend on the nuclear predicate; mode Typical or Stereotypical (the
latter with the Speaker as holder). Not `∀`, not `∃`, no referent
introduced; its normality structure is constrained, not defined —
frankly axiomatic (and currently inference-free beyond typing — the
spec §14 gap entry). Restrictor and nuclear scope are member-level:
`Fn<(T), Content>` and `EFn<(T), Content>` (spec §5.8).
**For.** `lo'e`/`le'e`. The split-normality witness (maned male lions,
birthing female lions) kills every fixed-specimen theory.
**See.** [Spec §5.8](spec.md); [primer ch. 3](primer.md);
[rationale §1.9](rationale.md).

### 1.31 `Reify` and `Holds`

**Informally.** The one bridge between content and object: `Reify`
turns content into a `Proposition` (a first-order object representing
the content's intension); `Holds` is its primitive inverse, with the
axiom pair: evaluating `(Holds (Reify c))` is evaluating `c`, and
`(= (Reify (Holds p)) p)` for every proposition — so every
proposition, however introduced, represents exactly the content
`Holds` returns for it. The pair is the sole Proposition↔Content
bridge (the sign and event crossings target other sorts).
Construction is inert — nothing runs at `Reify` — while `(Holds p)`
runs the represented content at its own occurrence, escapes governed
by the surrounding operators (spec §5.4, §9.1).
**For.** `du'u`; attitude objects; single-evaluation display
(`Let`-shared `Reify` with `Holds` as the evaluated body). The shape
generalizes row by row to reified predicates — a §9.1 reservation
(registered gap), with the experimental `me'ei`/`me'au` pair as the
attested surface exponents; at the propositional case `me'au` is
`Holds` in selbri position under §9.1's singleton condition
(the `Meau0` schema — singularity projective; no plural baseline
reading).
**See.** [Spec §9.1, §7.6, §14](spec.md); [primer ch. 8](primer.md);
[rationale §1.10, §2.10](rationale.md).

### 1.32 `TanruAdmissible`

**Informally.** The axiomatized admissibility constraint behind tanru
modification: a relation of the head's row is admissible as the
modification link exactly when it makes the modifier bear on
*something* in the head predication (the event's manner, a
participant, a purpose, …) and nothing stronger — no x1-sharing, no
intersectivity. Nonempty by axiom: some link always exists,
discharging the `Vague` formation obligation. The `Tanru` operator
that consumes it is **defined** (§2.6).
**For.** Constraining `sutra klama`'s open modification relation
(CLL ch. 5).
**See.** [Spec §6.2](spec.md); [primer ch. 9](primer.md);
[rationale §1.8](rationale.md).

### 1.33 `Scalar`

**Informally.** `(Scalar k P)`, `k ∈ ⟨OtherThan, Opposite, Neutral⟩`:
deny `P`'s stated region on a contextually recovered scale *and*
positively assert an alternative region — some admissible other
(`na'e`), the antipode (`to'e`), the midpoint (`no'e`). Stronger than
`¬`, never weaker.
**For.** `ta na'e melbi` denies beauty and asserts an alternative
aesthetic standing. Also the `nai`-fallback for unpaired indicators
(`Opposite`).
**See.** [Spec §6.3, §7.6](spec.md); [primer ch. 7](primer.md);
[rationale §1.8](rationale.md).

### 1.34 `AdmissibleThreshold`, `AdmissibleTolerance`, `AdmissibleMixture`, `AdmissibleCutoff`, `InRegion`, `deg_R`

**Informally.** The gradable/vague-quantity interface: the axiomatic
admissibility predicates. `AdmissibleTolerance : Number × Precision →
Fn<(Number), Content>` and its rounding sibling `AdmissibleRounding`
serve `ji'i` (the tolerance/rounding-preimage regions about an anchor
at the numeral's precision, nonempty by VC1 — spec §12, pin P37;
`Direction` — the closed `Up | Down | Either` — is declared with the
rounding former);
`AdmissibleMixture` serves sumti-`joi` (the composition relations
refining `gunma` — nonempty by construction, `gunma` the trivial
refinement; spec §12);
the threshold predicates serve the degree quantifiers (indexed by
the closed `ThresholdKind` enumeration — `ManyK | FewK | TooManyK |
TooFewK | EnoughK`, an index type unrelated to the rejected `Kind`
sort) and gradable
scale regions (each nonempty by axiom, discharging the `Vague`
formation obligation), the region-membership relation
`InRegion : Amount × Region<Scale> → Content`, and the per-relation
degree projection `deg_R : Record ρ × Scale → Amount` declared by a
gradable entry's lexicon row (`GradableRel<ρ,ℓ>` classifies such
entries by their graded place ℓ).
**For.** `so'i`, `du'e`/`mo'a`/`rau`, `ta barda` via `Grade`.
**See.** [Spec §6.4, §10, §12](spec.md); [primer ch. 9](primer.md).

### 1.35 `Assert`, `Ask`, `Command`, `Express`, `Vocative`, `Mention` — the force constructors

**Informally.** Turn content (or a query, or an addressee, or any
value) into a first-class act of the corresponding force: assertion,
question, directive, expressive display, address, and use/mention
display of a value. Constructing performs nothing.
**For.** One content under four forces: `do klama` / `xu do klama` /
`ko klama` / displayed. `Mention` covers bare-sumti display and
specimen fragments.
**See.** [Spec §7.1](spec.md); [primer ch. 6](primer.md);
[rationale §1.11](rationale.md).

### 1.36 `Perform` and `Do`

**Informally.** `Perform` injects an act into the performance level —
the content's computation runs with the force's commitment effects;
`Do` sequences performed discourse (flattening, associative, with
`∧`'s accessibility row). Act boundaries close force segments:
introductions inside an unperformed act do not escape.
**For.** The discourse spine; `.i` sequencing.
**See.** [Spec §7.1, §5.4](spec.md); [primer ch. 6](primer.md).

### 1.37 `NewTopic` and `Resume`

**Informally.** The `ni'o`/`no'i` transitions,
`Discourse → Discourse`: discourse-structural operations with no
truth conditions but with stated effects on the information state's
segment structure — `NewTopic` suspends the current discourse segment
onto the suspended-topic stack and opens a fresh one (keyed `Context`
retrievals are per-segment, so keys re-retrieve; segment-bounded
text-to-reading rules like `ki` stickiness and `go'i` reach reset);
`Resume` pops the most recently suspended segment and reopens it.
**See.** [Spec §7.2, §5.1, §5.3](spec.md).

### 1.38 The sign constructors

**Informally.** `(OpaqueQuote text)` — unparsed quoted text
(`lo'u…le'u`, `zoi`); `(StructuredQuote entry)` — a transcript entry
carrying an unperformed act (`lu…li'u`; the entry operand is a pure
token-description property, §2.27, and the constructor supplies the
opaque boundary); `(NameSign text)`,
`(WordSign text)` (`zo`), `(LetteralSign text)`,
`(SentenceSign content)`. All build `Sign<K>` values; all boundaries
are opaque to dynamics.
**For.** Quotation, names (`Named` goes through `NameSign`), letteral
signs, `me'o` expression mention.
**See.** [Spec §7.5](spec.md); [primer ch. 10](primer.md).

### 1.39 `InterpretContent` and `InterpretAct`

**Informally.** The explicit, typed interpretation crossings from
signs (`la'e`; `lu'e` is the inverse sign-of): a sign to the content
or the act it expresses. `InterpretAct<F>` is a force-indexed
*partial* family — defined exactly when the sign's realized (or
intended) act has force `F`, since a sign does not carry its force. On
transcript entries, `InterpretAct` yields the realized act;
`InterpretContent` is defined exactly when that act is an
assertion (the content projection); a question, directive, or
expressive entry has no content projection and interprets only as an
act.
**For.** `la'e lu mi klama li'u` — the content, not the sentence.
**See.** [Spec §7.5, §16.3](spec.md); [primer ch. 10](primer.md).

### 1.40 The token and sign fact relations

**Informally.** The vocabulary for talking about utterances and signs
as objects — ordinary assertable relations, placeholder content words
under the §16 program. Signatures (u an `UtteranceToken`, s a
`SignToken<K>`, each relation `Content`-valued): `SpeakerOf u
speaker`, `AudienceOf u audience` (both at `Referents<Entity>`);
`LocutionOf locution u` (the locution first, at
`Referents<Locution>` — the order the §11 anchoring clause writes);
`DeicticTimeOf u t`
(`Time`); `DeicticPlaceOf u l` (`Location`); `TextOf u|s text`
(`Text`); `Realizes u a` (`a` an act value of whatever force — the
force index is existential); `Utters agent u`; `Quotes s x` (`x` the
quoted material: a sign or `Text`); `Denotes s x` (`x` a value of any
sort — denotation is sort-polymorphic).
**For.** Transcript entries, reported speech, the `le`-anchoring
clause (the describing event is this utterance's locution).
**See.** [Spec §7.4–7.5, §10–11](spec.md).

### 1.41 `Deictic`, `ShiftedGround`, `InContext`, and the context projections

**Informally.** The utterance context is a typed record (speaker,
audience, time, place, ground) with projections `Speaker`, `Audience`,
`Now`, `Here`. `Deictic` picks referents at a proximity against a
ground; `ShiftedGround` *constructs* a ground from a description
(never a contextual resolution); `InContext` evaluates content with
deictic projections from a given ground — the explicit context shift
(`ra'o`), currently the sole member of the index-shift family.
**For.** `mi`/`do`, `ti`/`ta`/`tu` (via the defined demonstratives),
narrative perspective shifts.
**See.** [Spec §5.1](spec.md); [rationale §2.3](rationale.md).

### 1.42 `Polar`, `OpenQ`, `QuestionOf`, `Answer`, and the answer selections

**Informally.** `(Polar c)` is the two-valued query (`Yes ↦ c`,
`No ↦ ¬c`); `(OpenQ f)` the open query whose answer-content function
sends each domain tuple `a` to `f a…`; `QuestionOf` reifies a query as
an embeddable `Question` object. `Answer` applies a query's
answer-content function to a selection: `(PolarAnswer Yes|No)`,
`(TupleAnswer a [Exhaustive|MentionSome])` — `Exhaustive` conjoining
the completeness claim, `MentionSome` overtly marking the weakest
reading, and absence of the marker meaning absence (pin P9).
**For.** `xu`/`ma`/`mo`/`fi'a`/`pei` questions; `kau` answerhood via
the defined `ContextualAnswer`.
**See.** [Spec §8](spec.md); [primer ch. 6](primer.md).

### 1.43 The abstraction relations

**Informally.** CLL's non-event abstractors are named relations with
labelled rows, parameterized by the abstracted content; reference
applies *outside*, so gadri, quantifiers, and relative clauses work on
abstractions for free. The rows (each `(XRel c) : PredTerm⟨…⟩`, every
place at `Referents<·>`): `NiRel` ⟨x1: Amount, x2: Scale⟩ (`ni`);
`JeiRel` ⟨x1: TruthValue, x2: Epistemology⟩ (`jei`); `LihiRel`
⟨x1: Experience, x2: Entity — experiencer⟩ (`li'i`); `SihoRel`
⟨x1: Concept, x2: Entity — mind⟩ (`si'o`); `SuhuRel`
⟨x1: AbstractNature, x2: Entity — category⟩ (`su'u`); `PuhuRel`
⟨x1: Process, x2: Eventuality — stages⟩ (`pu'u`); `ZuhoRel`
⟨x1: Activity, x2: Eventuality — repeated actions⟩ (`zu'o`). Event
abstraction (`nu` and its sort refinements) is plain `Refer` at the
event sort; `ka` is λ; `du'u` is `Reify`; `DuhuRel` is derived
(defined section). Where the §16.5 audit records a combinator fit
(`klani` for `NiRel`, `se lifri` for `LihiRel`, …), that is a
committee-pending adoption plan: upon adoption the relation becomes a
defined form over the adopted word; until then it stands primitive —
content-word status and term-language status are independent axes.
**For.** `lo ni mi klama cu barda` — an amount, referred to like
anything else, its scale a contextual slot.
**See.** [Spec §9.2](spec.md); [primer ch. 8](primer.md);
[rationale §1.10](rationale.md).

### 1.44 `AmountValue`, `TruthValueDegree`, `EventOfContent`

**Informally.** The named adjacent-sort crossings (pin P13 allows no
implicit ones): `AmountValue : Referents<Amount> × Referents<Scale> →
Number` — an amount's numeric value on its scale (`mo'e`; CLL 11.5);
`TruthValueDegree : Referents<TruthValue> → Number` — a truth value's
fuzzy degree in [0,1] (CLL 11.6); and `EventOfContent : Content →
Referents<Eventuality>` — the eventuality of a clause's content (used
by `tu'a`'s shape conjunct and `nu` recasting).
**See.** [Spec §9.2, §12](spec.md).

### 1.45 `MetalinguisticallyDefective` and the named value enumerations

**Informally.** The objection relation behind `na'i` (a prior
utterance or act is defective in a contextually recovered dimension),
with `DefectKind` (wording, form, implication, presupposition,
register) declared beside it; the evidential `BasisKind` enumeration
(`Observation`, `Hearsay`, `CulturalKnowledge`, `InternalExperience`,
`Expectation`, `Opinion`, `BareAssertion`); and the intensity-scale
regions (`Intense`/`cai`, `Strong`/`sai`, `Moderate`/unmarked,
`Weak`/`ru'e`, `Neutral`/`cu'i`).
**See.** [Spec §7.3, §7.6](spec.md); [primer ch. 7](primer.md).

### 1.46 The placeholder lexical relations

**Informally.** Relations the core uses that await their Lojban
content words under the §16 program. The indicator relations —
`Happiness`, `Unhappiness`, `Desire` : experiencer × `Target` ×
intensity region → `Content`, and
`EvidentialBasis` : experiencer × `Target` × `BasisKind` → `Content`
(`Target` the closed union of §7.6: a `Proposition` — content targets
go through `Reify` — an act value, a plural reference, or a sign) —
with the §16.5 audit mapping them to the `-nmo` indicator-emotion
family (*indicator* `zei cinmo`: `uinmo`, `u'inmo`, `le'onmo`, …, the
generic `inmo`; one word per indicator, mechanically extensible to
every UI and both `nai` poles) as its sole near-fit — the unofficial
rows carry experiencer × target, and the intensity place is the
proposed extension; the emotion gismu (`gleki`, `badri`, `djica`, …)
are see-alsos. The discourse
relations — `Contrast`, `Addition`, `Parallel`, `Elaboration` : two
act values → `Content` (audit: `frica`/`simsa` for contrast and
parallel). The named tanru-link precisification constants —
`MannerLink`, `MaterialLink`, `PurposeLink`, `SourceLink`,
`InstrumentLink`, `ResemblanceLink` — each a relation of its head row
satisfying `TanruAdmissible` by construction, shadowed by the BAI
gismu (`tadji`, `marji`, `mukti`, `krasi`, `pilno`, `simsa`); an open
family — a resolved reading may name links beyond these six.
PascalCase marks exactly this placeholder status; as with §1.43, a
recorded fit becomes a definition only when the committee adopts it.
**See.** [Spec §7.6, §7.2, §12, §16.5](spec.md);
[primer ch. 0, ch. 7](primer.md); the indicator instances appear in
[samples §7, §11](samples.md).

### 1.47 `Expression<Γ, A, ε>`, `Telescope`, and the quote former

**Informally.** The reflection types: an `Expression` is an
elaborated, scoped, α-classed piece of core notation — code — open in
the typed context Γ, of result type A, with effect class ε deciding
`Fn` vs `EFn` under abstraction; a `Telescope` is a quoted binder
extension: one flat group (`{$x :: T}`, `{$x $y :: T}`) or a
left-scoping concatenation of two or more groups
(`{{$x :: T} {$y :: S} …}`). The quote former
`{…}` is bootstrap floor: quotes are only ever written, elaborate at
their written occurrence against the context they are written in
(closure — free names a consuming word's telescope designates as open
form exactly Γ; all others are captured, packaged with their values
when the literal's position is evaluated), carry α-invariant site
identities fixed at elaboration
(law S8), and are constructive-only — no destructors, no code
equality, no reification of running values, no anti-quotation, and no
`MakeEval` (the design inference from Wand's fexpr result — contextual
equivalence collapses to α-congruence — is the cited reason).
`{}` quotes core notation only — never Lojban text, which is `lu`/
`zoi` territory (§1.10, §1.38).
**For.** `{(Close (klama Speaker))}` — code; compare
`lu mi klama li'u` — a linguistic sign.
**See.** [Spec §7.7, §2, §16.3–16.4](spec.md);
[rationale §2.9](rationale.md).

### 1.48 `MakeLambda`

**Informally.** The one primitive sign-function: applied to a
telescope and a body quote, it produces the function that, given
values for the telescope, interprets the body in its elaboration
environment extended with them — suspension from the quote,
hygiene from elaboration, purity class from the body (`Fn` if pure,
`EFn` otherwise). **`λ` is its alias**: `(λ {$x :: T} {body})` is an
ordinary application, and in term-expression syntax `()` is
application and nothing else (telescopes and the types after `::`
carry the §2 subgrammar). Like every PascalCase name, a §16 placeholder
awaiting its content word — the move that makes binders nameable
vocabulary at all.
**For.** `lo ka se klama` → `(MakeLambda {$x :: Referents Entity}
{(Close (klama :2 $x))})`.
**See.** [Spec §7.7](spec.md); [rationale §2.9](rationale.md);
[samples §12](samples.md).

### 1.49 `Interpret`, `Env<Γ>`, and `Arrow_ε`

**Informally.** The bootstrap-floor interpretation family:
`Interpret : Expression<Γ, A, ε> × Env<Γ> ⇀ A` interprets a code value
against `Env<Γ>`, the typed record of values for exactly its open
context Γ (the captured part rides inside the value; for closed code
the empty environment is elided — `(Interpret {a})`). Stage-indexed:
interpreting stage-n code is a stage-(n+1) operation; there is no
untyped `Eval` and no `MakeEval`, ever. `Arrow_ε` names the effect
class's arrow — `Arrow_Pure = Fn`, `Arrow_Effectful = EFn` — deciding
what abstraction over code produces. When A is a computation type,
interpretation *returns* the computation; running it stays with
`bind`, the dynamic operators, or `Perform`.
**For.** `(MakeApply {f} {a}) ≝ ((Interpret {f}) (Interpret {a}))` —
the family is what the defined reflection vocabulary (§2.28) bottoms
out in.
**See.** [Spec §7.7, §16.3–16.4](spec.md); [rationale §2.9](rationale.md).

### 1.50 `InnatelyCapable` and `MotionVector`

**Informally.** Two lexically grounded primitives declared with the
§12 helpers they serve. `InnatelyCapable : Referents<Entity> ×
Fn<(Referents<Entity>, Referents<Eventuality>), Content> → Content` —
`jinzi`-grounded innate possibility of P-events with the bearer,
evaluated at capability worlds (the CAhA base). `MotionVector :
Referents<Eventuality> × Referents<Entity> × Referents<Entity> →
Content` — the `mo'i` heading: the event carries the mover's `muvdu`
motion in the `farna` direction.
**For.** `ka'e` (via the capability forms, §2.21) and the `mo'i`
motion tags.
**See.** [Spec §12, §11](spec.md).

### 1.51 `TopicAdmissible` and `TopicResolution`

**Informally.** The typed interface for `zo'u` topic-comment (P26):
`TopicResolution<ρ,T>` is the closed union indexed by the comment's
row and the topic's sort — fill an unfilled compatible place
(`PlaceFill ℓ`, ℓ : `CompatibleLabel<ρ,T>` — the refinement that
makes the fill branch type statically), or
bear `srana`-aboutness to the closed comment (`About`) — and
`TopicAdmissible` is the axiomatic admissibility predicate over
resolutions, `TanruAdmissible`'s sibling. The `Topic` schema binds a
`Vague` resolution: CLL 19.4's fish is exactly the place choice
(eater or eaten), typed.
**For.** `le finpe zo'u citka`.
**See.** [Spec §12, §11](spec.md), pin P26.

### 1.52 The MOI relation families

**Informally.** Five lexical relation families indexed by a number
(CLL 18.11), catalogued with exact rows: `MeiRel n` (group formed
from an n-membered set, members among it; comparison set for
objective-indefinite n; by-standard for subjective), `MoiRel n`
(n-th under a pure `Ordering<T>`, Context-recovered), `SiheRel n`
(typed portion), `CuhoRel n` (opaque probability, 0 ≤ n ≤ 1, the
model's measure — P29: no probability calculus), `VaheRel n` (scale
position via the degree projection). Lexical families, not term
expansions.
**For.** `lei mi ratcu cu cimei`; `ti pamoi le'i mi ratcu`.
**See.** [Spec §12, §11](spec.md), pin P29.

### 1.53 The declared partial projections and crossings

**Informally.** Declared, definedness projective (§5.5):
`RealizedAct<F>` / `RealizedDiscourse` (the act or act-sequence a
transcript token/span realizes — utterance anaphora's crossing, P28)
with the total `ActContent` (an assertion's packaged content);
`During` (an eventuality's temporal extent within an interval — the
ROI count schema's restriction, P35); and
the MEX conversions `RelToOp<ρ>` (`na'u`, at Number-rowed relations,
functional in x1), `OpToRel` (`nu'a`, total), `OperandToOp` (`ma'o`,
computation-typed: the function is a `Context` recovery — P36),
`AmountOperand<ρ>` (`ni'e`,
the Number-result computation at a Number-rowed relation). `se` on
operators is pure argument permutation.
**See.** [Spec §7.4, §12, §11](spec.md), pins P28, P36.

### 1.54 `EnumerationOrdinal`

**Informally.** MAI's declared display relation: the
attachment-selected constituent bears ordinal n in a
`SequenceKey`-identified enumeration at the closed
`EnumerationLevel` (`Item` for `mai`, `Section` for `mo'o`);
non-at-issue — placed by §7.6's machinery (`Supplement` at a
constituent target, `Express` beside an act-level target); no
temporal ordering of denoted events implied (CLL 19.7 numbers sumti
inside one bridi).
**For.** `mi klama pamai le zarci .e remai le zdani`.
**See.** [Spec §12, §11](spec.md).

## 2. Defined forms

Everything below expands into the primitives (and other defined forms,
acyclically). The expansion *is* the specification; the prose says the
same thing a first time.

### 2.1 `PredTerm<ρ>`

**Informally.** The type of relations over row ρ — a transparent alias,
not a new type: relations are row-functions, partial filling is
abstraction over the residual row, and a relation over the exhausted
row is its content.
**Formally.** `PredTerm<ρ> ≝ Record ρ → Content`, with
`PredTerm<⟨⟩>` applied at the empty record ≡ `Content`.
**For.** Keeping labels load-bearing (FA, `zi'o`, `fi'a` all speak in
labels) with the ontology of functions.
**See.** [Spec §3.3](spec.md); [rationale §1.1](rationale.md).

### 2.2 `At` and the fill notation

**Informally.** The single-place fill: fill place ℓ of relation `R`
with value `v`, yielding the relation over the residual row. All
multi-fill notation — positional fills, `:n` labels, the
continue-after-`n` rule, FA routing, `se`-conversion — desugars to
nested single fills. Distinct-label fills commute (fills are values),
which is why Lojban's free surface order is pure notation. With a
*computed* label (`fi'a`), `At` abbreviates the finite case split over
literal fills.
**Formally.** `(At R ℓ v) ≝ (λ {$rest :: Record ρ−ℓ} {(R ⟨$rest
extended with ℓ = v⟩)})`;
`(klama :2 This Yonder) ≝ (At (At klama x2 This) x3 Yonder)`.
**For.** `klama fe ti tu`; `klama fi'a ti` at the computed-label case.
**See.** [Spec §4.1, §4.7](spec.md); [primer ch. 1](primer.md).

### 2.3 `Let`

**Informally.** Pure sharing: bind a value for a body — definable as
immediate application, retained for legibility and for identity of one
value used twice (`goi` aliasing, act targets). May not bind an
effectful computation; that is `Bind`'s job, by type.
**Formally.** `(Let {$x :: T} v {body}) ≝ ((λ {$x :: T} {body}) v)`.
**For.** `(Let {$a :: Act Assertion} (Assert …) {(Do (Perform $a)
(Express (… $a …)))})` — the display targets *that* act.
**See.** [Spec §4.4](spec.md); [primer ch. 7](primer.md).

### 2.4 `Close`

**Informally.** Complete an open predication into content: close the
event place existentially (where the row licenses one) and give each
remaining defaultable place its own contextual slot — one distinct
site per omission, staying put under negation.
**Formally.** `(Close P) ≝ (Bind {$v1 :: T1} (Context) … {$vk :: Tk}
(Context) {(∃ (λ {$e :: Referents Eventuality} {(P :p1 $v1 … :pk $vk
:Eventuality $e)}))})`.
**For.** Every unmarked bridi: `mi klama` commits to a contextually
recoverable destination — not "some destination", not nothing.
**See.** [Spec §4.6](spec.md); [primer ch. 1](primer.md);
[rationale §1.2](rationale.md).

### 2.5 `This`, `That`, `Yonder`

**Informally.** The demonstratives, as deictic picks at the three
proximities against the context's ground.
**Formally.** `This ≝ (Deictic Proximal g)`, `That ≝ (Deictic Medial
g)`, `Yonder ≝ (Deictic Distal g)`, where `g` is the enclosing
utterance context's ground (the `ctx` record's ground projection,
spec §5.1).
**For.** `ti`/`ta`/`tu`.
**See.** [Spec §5.1](spec.md).

### 2.6 `Tanru`

**Informally.** Modification of a head by a modifier: the head's row,
the head's predication, plus an admissible modification link — a
`Vague` parameter ranging over the relations `TanruAdmissible`
(§1.32) admits, with no fact of the matter selecting one.
**Formally.** `((Tanru M H) fills…) ≝ (Bind {$link :: PredTerm ρ(H)}
(Vague (λ {$r :: PredTerm ρ(H)} {(TanruAdmissible M H $r)}))
{(∧ (H fills…) ($link fills…))})`.
**For.** `sutra klama` — a goer, with `sutra` bearing on the going
*somehow*; the library's named links are the common precisifications,
a lujvo a lexicalized one.
**See.** [Spec §6.2](spec.md); [primer ch. 9](primer.md);
[rationale §1.8](rationale.md).

### 2.7 `UnitSet` and `CardBasis`

**Informally.** Basis extraction: the set of P-satisfying units among
a reference, and counting as counting units *under a description*
within a reference — how inner cardinality works, with no canonical
atomic basis assumed.
**Formally.** `(UnitSet P r) ≝ (SetOf (λ {$x :: T} {(∧ (P $x) (Among $x r))}))`;
`(CardBasis r P) ≝ (Card (UnitSet P r))`.
**For.** `lo ci gerku` — counted as dogs, three; the same plurality
may count differently under another basis (three dogs, one pack).
**See.** [Spec §4.8](spec.md); [primer ch. 3, ch. 11](primer.md).

### 2.8 `CoRef` and `Overlap`

**Informally.** Plural co-reference (mutual subreference — the
equivalence the plural type uses instead of `=`) and plural overlap
(some common subreference).
**Formally.** `(CoRef x y) ≝ (∧ (Among x y) (Among y x))`;
`(Overlap a b) ≝ (∃ (λ {$c :: Referents T} {(∧ (Among $c a) (Among $c b))}))`.
**See.** [Spec §4.8, §12](spec.md).

### 2.9 `Distrib` and `lu'a`

**Informally.** The marked each-reading: the property holds of every
unit among the reference. `lu'a` is this distribution applied at its
use site. Never a default — unmarked plural predication is neutral
(pin P4).
**Formally.** `(Distrib Q r) ≝ (∀ (λ {$x :: T} {(→ (Among $x r)
(Q $x))}))`, `T` the member type.
**For.** "each of them", `ro`'s nuclear scope, forced distributive
readings.
**See.** [Spec §12, §4.8](spec.md); [primer ch. 3](primer.md);
[rationale §2.5](rationale.md).

### 2.10 `MaxRefer`

**Informally.** The maximal base: the reference to *all* the
P-satisfiers and nothing else — every unit is P, every P-satisfier is
among it, every part overlaps a P-unit. Defined only for inhabited P
(a presupposition), with the model required to supply the reference
(plural comprehension).
**Formally.**

```text
(MaxRefer P) ≝
  (Presuppose (∃ P)
    (Refer (λ {$r :: Referents T}
      {(∧ (Distrib P $r)
         (∀ (λ {$x :: T} {(→ (P $x) (Among $x $r))}))
         (∀ (λ {$r' :: Referents T}
              {(→ (Among $r' $r)
                 (∃ (λ {$x :: T} {(∧ (P $x) (Overlap $x $r'))})))})))})))
```

Models must supply this reference for each inhabited pure restrictor
the mapping can form (plural comprehension — a model condition).
**For.** The `lo'i`/`loi` base ("the set of *the* dogs") and `Every`'s
witness export.
**See.** [Spec §12, §11](spec.md).

### 2.11 `Reciprocate`

**Informally.** The reciprocal schema: every two distinct members of
the witness stand in the relation, both ways (member-wise; vacuous on
a unitless reference — mass reciprocity needs an explicit basis).
Consumed by `simxu`'s and `soi`'s lexicon rows.
**Formally.** `(Reciprocate r P) ≝ (∀ (λ {$x $y :: T} {(→ (∧ (Among $x r) (Among $y r) (¬ (= $x $y)))
(P $x $y))}))` — `T` the member sort; the units singleton-lift at
`Among` and at `P`'s places.
**For.** `ci jbopre cu simxu lo ka tavla` — pairwise mutual talk.
**See.** [Spec §12](spec.md); [samples §5](samples.md).

### 2.12 The cardinal quantifiers

**Informally.** The witness-set family: select a witness of the stated
strength and predicate the nuclear scope of it **neutrally** — the
each-reading comes from the lexicon or `Distrib`, never from the
quantifier (pin P17, pin P4). `Every` is the importing universal:
presuppose the restrictor inhabited, export the maximal base,
distribute (`ro` is each). The negative/bounded forms contain their
selection under `¬` and export nothing.
**Formally.**
`(Exactly n P Q) ≝ (Bind {$w :: Referents T} (SelectExactly n P)
{(Q $w)})`;
`(AtLeast n P Q)` / `(Some P Q)` likewise over their selections;
`(Every P Q) ≝ (Bind {$w :: Referents T} (MaxRefer P) {(Distrib Q
$w)})` — the import is `MaxRefer`'s own presupposition; `(No P Q) ≝ (¬ (Some P Q))`; `(AtMost n P Q) ≝ (¬ (AtLeast n+1
P Q))`; `(MoreThan n P Q) ≝ (AtLeast n+1 P Q)`; `(FewerThan n P Q) ≝
(¬ (AtLeast n P Q))`; `(GlobalExactly n P Q) ≝ (= (Card (SetOf (λ {$x :: T} {(∧ (P $x) (Q $x))}))) n)` (pure operands; the marked global reading).
Zero floor (spec §12): the selections form only at n ≥ 1;
`(AtLeast 0 P Q) ≝ ⊤` and `(Exactly 0 P Q) ≝ (No P Q)`, with the
bounded forms following from the definitions.
**For.** `ci gerku cu bajra .i ri tatpi` (witness export); `no prenu
cu jmaji` (the collective reading a distributive default cannot say).
**See.** [Spec §12, §4.10, §5.6](spec.md); [primer ch. 5](primer.md);
[rationale §3 (P17)](rationale.md).

### 2.13 The degree quantifiers

**Informally.** Cardinal comparisons against thresholds that are
`Vague` (and, for the purpose-relative kinds, constrained by a
`Context`-recovered standard): many, few, most, too many, too few,
enough.
**Formally.** (`θ` a `Vague` threshold; `σ` a `Context` standard;
kinds from `ThresholdKind`, §1.34; `P`, `Q` pure for `Most`.)

```text
(Many P Q)    ≝ (Bind {$θ :: Natural} (Vague (AdmissibleThreshold ManyK P))
                  {(AtLeast $θ P Q)})
(Few P Q)     ≝ (Bind {$θ :: Natural} (Vague (AdmissibleThreshold FewK P))
                  {(FewerThan $θ P Q)})
(TooMany P Q) ≝ (Bind {$σ :: Referents Entity} (Context)
                       {$θ :: Natural} (Vague (AdmissibleThreshold TooManyK P $σ))
                  {(MoreThan $θ P Q)})
(TooFew P Q)  ≝ (Bind {$σ :: Referents Entity} (Context)
                       {$θ :: Natural} (Vague (AdmissibleThreshold TooFewK P $σ))
                  {(FewerThan $θ P Q)})
(Enough P Q)  ≝ (Bind {$σ :: Referents Entity} (Context)
                       {$θ :: Natural} (Vague (AdmissibleThreshold EnoughK P $σ))
                  {(AtLeast $θ P Q)})
(Most P Q)    ≝ (> (Card (SetOf (λ {$x :: T} {(∧ (P $x) (Q $x))})))
                   (Card (SetOf (λ {$x :: T} {(∧ (P $x) (¬ (Q $x)))}))))
```
**For.** `so'i prenu cu klama` — the family over admissible
thresholds; no exact count hides anywhere.
**See.** [Spec §6.4, §12](spec.md); [primer ch. 5, ch. 9](primer.md).

### 2.14 `Grade`

**Informally.** Gradable predication with its two parameters exposed:
the relation holds of a row record when its degree on the given scale
falls in the given region — scale recoverable (`Context`), region
boundary `Vague`.
**Formally.** `(Grade R s reg) ≝ (λ {$rec :: Record ρ} {(InRegion
(deg_R $rec s) reg)})`.
**For.** `ta barda` — big along which dimension is recovered; where
"big" starts has no fact of the matter.
**See.** [Spec §6.4, §12](spec.md); [primer ch. 9](primer.md).

### 2.15 `Interval`

**Informally.** The set of values between two endpoints, each endpoint
strict or non-strict (`ga'o`/`ke'i`).
**Formally.** `(Interval a b k₁ k₂) ≝ (SetOf (λ {$x :: T} {(∧ (cmp₁ a $x) (cmp₂ $x b))}))`.
**See.** [Spec §12](spec.md).

### 2.16 `ZipWith`

**Informally.** Respective pairing over two lists, by metalanguage
recursion — the `fa'u` analysis, expanding completely into a
conjunction.
**Formally.** `(ZipWith f (List) (List)) ≝ ⊤`; `(ZipWith f (List a
as…) (List b bs…)) ≝ (∧ (f a b) (ZipWith f (List as…) (List bs…)))`.
**For.** `mi fa'u do tavla do fa'u mi` ≡ I talk to you ∧ you talk to
me.
**See.** [Spec §12](spec.md); [samples §5](samples.md).

### 2.17 `Named`

**Informally.** Bearing a name-sign, through the lexicon's `cmene`
row: the referent is what the name names, the namer contextual.
**Formally.** `(Named t x) ≝ (Close (cmene (NameSign t) x))`.
**For.** `la .alis.` — `Refer` over `(Named "alis" ·)`.
**See.** [Spec §12, §11](spec.md); [primer ch. 3](primer.md).

### 2.18 `DuhuRel`

**Informally.** The derived `du'u` relation: its x1 is the reified
content, its x2 a sentence sign expressing it (CLL 11.7's x2, `se
du'u`). Derived because `Reify` already carries the crossing.
**Formally.** `((DuhuRel c) x1 x2) ≝ (∧ (CoRef x1 (Reify c))
(Distrib (λ {$s :: Sign Sentence} {(CoRef (Reify (InterpretContent
$s)) (Reify c))}) x2))` — x2's signs are those whose interpretation
reifies the same content.
**For.** `lo se du'u mi klama` — the sentence, not the proposition.
**See.** [Spec §9.2](spec.md); [samples §9](samples.md).

### 2.19 `ContextualAnswer`

**Informally.** Bare `kau`'s answerhood: the answer tuple is retrieved
from context, with the exhaustivity slot absent (pin P9) — the weakest
reading, strengthened only lexically or by explicit marker.
**Formally.** `(Answer q ContextualAnswer) ≝ (Bind {$a :: A} (Context)
{(Answer q (TupleAnswer $a))})` at open domains; at `Query<Bool>` the
retrieval is at `Bool` and the selection is `(PolarAnswer $a)` — the
`xu kau` case (spec §8.2).
**For.** `mi djuno lo du'u ma kau klama`.
**See.** [Spec §8.2](spec.md); [primer ch. 6](primer.md).

### 2.20 `JaiPromote`

**Informally.** Tagged `jai`: promote the tagged role to x1 and move
the old x1 to the labelled, fillable `fai` place (closing contextually
when unfilled — CLL 9.12). Bare `jai` is the mapping's
`Vague`-role raising instead.
**Formally.** Writing ρ' for ρ with ℓ relabelled x1 and x1 relabelled
`fai`: `(JaiPromote R ℓ) ≝ (λ {$r :: Record ρ'} {(R ⟨ℓ = $r.x1,
x1 = $r.fai, rest unchanged⟩)})`.
**For.** `mi jai gau rinka` patterns; `fai` fills.
**See.** [Spec §12, §6.1, §11](spec.md).

### 2.21 `Realized`, `nu'o`, `pu'i` — the capability forms

**Informally.** Over the primitive `InnatelyCapable` (§1.50):
`Realized` — an actual P-event of the bearer occurred; `nu'o` =
capable and never realized; `pu'i` = capable and demonstrated. `P` is
an event property of the bearer,
`Fn<(Referents<Entity>, Referents<Eventuality>), Content>`.
**Formally.**

```text
(Realized b P) ≝ (∃ (λ {$e :: Referents Eventuality}
                    {(∧ (P b $e) (fasnu $e))}))
(nu'o b P)     ≝ (∧ (InnatelyCapable b P) (¬ (Realized b P)))
(pu'i b P)     ≝ (∧ (InnatelyCapable b P) (Realized b P))
```
**See.** [Spec §12, §11](spec.md).

### 2.22 `SelectSome`

**Informally.** The `su'o`-strength selection — at least one unit —
as the weakest member of the selection family.
**Formally.** `(SelectSome P) ≝ (SelectAtLeast 1 P)`.
**For.** `su'o gerku cu bajra` — some dogs (one or more) ran.
**See.** [Spec §5.6](spec.md); §1.27 above.

### 2.23 `NahiObjection`

**Informally.** The `na'i` act: express, of a bound prior target, that
it is metalinguistically defective in a contextually recovered
dimension — performing nothing, negating nothing.
**Formally.** `(NahiObjection t) ≝ (Bind {$d :: DefectKind} (Context)
{(Express (Close (MetalinguisticallyDefective t $d)))})`.
**See.** [Spec §12, §7.3](spec.md); [primer ch. 7](primer.md).

### 2.24 `GroundedBy`

**Informally.** The act-level evidential spelling: display, beside a
performed act, the speaker's basis for it — a mode of commitment, not
a second claim.
**Formally.** `(GroundedBy b a) ≝ (Do (Perform a) (Express (Close
(EvidentialBasis Speaker a b))))`.
**For.** `za'a do cadzu` — the assertion grounded in observation;
negation touches the walking, never the basis.
**See.** [Spec §12, §7.6](spec.md); [primer ch. 7](primer.md).

### 2.25 `Only` and `Additive`

**Informally.** Constituent focus: `po'o` presupposes the host holds
of the focus and denies it of every non-co-referent alternative;
constituent `ji'a` presupposes an alternative and asserts the host of
the focus.
**Formally.** `(Only f H) ≝ (Presuppose H[f] (¬ (∃ (λ {$y :: T} {(∧ (¬
(CoRef $y f)) H[$y])}))))`; `(Additive f H) ≝ (Presuppose (∃ (λ {$y :: T}
{(∧ (¬ (CoRef $y f)) H[$y])})) H[f])`.
**See.** [Spec §12, §7.2](spec.md).

### 2.26 The COI schemas

**Informally.** Performative expressives: a COI greeting/thanks/… is
constituted by its performance — `Express` of the COI lexical relation
with the performative host-force profile.
**Formally.** `(COIExpress R addr) ≝ (Express (Close (R Speaker
addr)))`, `R` the COI entry's lexical relation (`coi-greeting`,
`ki'e-thanks`, …), performed with its performative profile.
**For.** `coi do` — the greeting is the act.
**See.** [Spec §12, §7.6, §11](spec.md).

### 2.27 The `Utterance` and `Sign` entry notations

**Informally.** A token variable with facts about it — the transcript
entry `StructuredQuote` consumes, and the same notation at the
sign-token sort. Defined: the λ suspends the facts by nature (nothing
performed, nothing introduced — quoted material introduces no
discourse referents), yielding a *pure token-description property*;
the opacity belongs to the consuming sign constructor, not to this
notation. Performed-level token talk needs no special form — it is
ordinary `Refer` at the token sort.
**Formally.** `(Utterance {$u :: UtteranceToken} {fact…}) ≝ (λ {$u :: Referents UtteranceToken} {(∧ fact…)})`; the `Sign` notation likewise
at `SignToken<K>`.
**For.** `lu mi klama li'u` → `(StructuredQuote (Utterance {$u :: UtteranceToken} {(Realizes $u (Assert (Close (klama Speaker))))}))`.
**See.** [Spec §7.4–7.5](spec.md); [primer ch. 10](primer.md);
[samples §6, §10](samples.md).

### 2.28 `MakeBind`, `MakeLet`, `MakeApply`, and the facade schema

**Informally.** The defined reflection vocabulary over `MakeLambda`
and the floor `Interpret` family: the braced binder spellings, the
reflective application word, and the generic facade schema by which
any operator acquires a sign-consuming form on demand.
**Formally.**

```text
(MakeLet {$x :: A} v {b})  ≝ ((MakeLambda {$x :: A} {b}) v)    ; Let is its alias
(MakeBind {$x :: A} c {b}) ≝ (bind c (MakeLambda {$x :: A} {b})) ; Bind is its
                                                     ; alias; bind is the
                                                     ; §1.14 carrier op
(MakeApply {f} {a})  ≝ ((Interpret {f}) (Interpret {a}))
(MakeForall {Δ} {b}) ≝ (∀ (MakeLambda {Δ} {b}))     ; and MakeExists,
                                                     ; MakeRefer, MakeSetOf,
                                                     ; MakeOpenQ, … alike
(MakeO {a₁} … {aₙ})  ≝ (O (Interpret {a₁}) … (Interpret {aₙ}))
```

— one interpretation per operand; each law preserves S1–S7; no facade
for the sign constructors, `Perform`'s commitment, or `Interpret`
itself. Nothing runs at construction: `MakeBind` returns
a computation value, inert until consumed by the relevant dynamic
operator or `Perform`.
**For.** The self-description program: with these words, core terms
and their semantics are statable as sentences about quoted code.
**See.** [Spec §7.7](spec.md); [rationale §2.9](rationale.md).

### 2.29 `te'a`, `gei`, and `xi` indexing

**Informally.** MEX helpers by metalanguage recursion: integer
exponentiation, order-of-magnitude, and subscripting as list
indexing (undefined past the end — a projective definedness
condition).
**Formally.**

```text
(te'a x 0)              ≝ 1
(te'a x (n+1))          ≝ (× x (te'a x n))
(gei x y)               ≝ (× y (te'a 10 x))
(xi (List a as…) 1)     ≝ a
(xi (List a as…) (n+1)) ≝ (xi (List as…) n)
```
**For.** `li re te'a ci du li bi`.
**See.** [Spec §12](spec.md); [samples §10](samples.md).

### 2.30 `MePred`

**Informally.** `me` as a defined form: the Among-property of a
sumti's referents — `(MePred X) ≝ (λ {$w :: Referents T} {(Among $w
X)})`, X's computation bound before the pure property forms. The
ratified gadri definitions expand `lo PA sumti` through `me`.
**For.** `la .baltazar. cu me le ci nolraitru`.
**See.** [Spec §12, §11](spec.md).

### 2.31 `TanruLinkConnect`

**Informally.** Jek at the tanru-unit locus (P33): for a shared head,
bind one `Vague` link per conjunct and join the link applications
with the connective — the head asserted once
(`blabi ja cmalu zdani`: a house, whose modification link is
white-flavored or small-flavored). Distinct-head units connect as
whole predications; joiks route to the mixture semantics.
**For.** `ta blabi je cmalu zdani`.
**See.** [Spec §12, §6.2, §11](spec.md), pin P33.

### 2.32 The region formers

**Informally.** The BIhI region formers beyond ordered `Interval`,
all defined by `SetOf` comprehension over a Context-recovered
`Metric<T>` (spec §12): `MetricBall` (`mi'i` — center, radius,
GAhO boundary kind; no endpoint arithmetic), `SpanRegion` (`bi'i` at
metric domains — metric betweenness), `RegionComplement` (`bi'o nai`
— complement in a Context universe). `bi'i` at ordered domains is ⊳
symmetrization of the ordered `Interval` (endpoint order normalized
together with the GAhO kinds). Endpoint/center references take the
projective singular condition (the §9.2 pattern).
**For.** `la .uacintyn. mi'i lo minli be li muno`.
**See.** [Spec §12, §11](spec.md).

## Appendix: model-theory symbols

Not term-language forms — the denotational metalanguage of
[spec §5.1](spec.md), listed so no named symbol goes unaccounted:
`Comp<A> = InformationState → P(InformationState × A × Obligations)`
is the computation carrier (`Content = Comp<Unit>`,
`RefComp<T> = Comp<T>`; discourse denotes at the same carrier with
its commitment effects, while an act value is the pure force-tagged
package only `Perform` injects — spec §5.1, §7.1); an `InformationState` is a set of
world–assignment pairs over the model's world set W; `Obligations`
collects pending projective commitments; `Unit` is the one-value
return type of contentful computations; and `ctx` is the utterance
context record (speaker, audience, time, place, ground) whose
projections §5.1 names. These symbols may change with the model (the
`da'i` gap entry anticipates a world-shift operation) without any term
changing — which is the point of keeping them out of the term
language (rationale §1.14).

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
; la'e di'u crosses through the token's realized act instead:
; (ActContent (RealizedAct dihu)), host-sorted (P28)
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
`Vague`-selected `Number`s — prefix/medial over the
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
order is scope order. Topic use: the topic binds, and a `Vague`
`TopicResolution` fills an admissible place of the open comment frame
or bears `srana`-aboutness to the closed comment (CLL 19.4's fish =
the place choice); `tu'e…tu'u` extends one topic over a sequence.

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
  {👉(∧ (Close (nelci Speaker $d))
     (Close (nelci Audience $d)))👈})
```

```lisp
; mi .a do klama lo zarci — ∨ instead; the store is still introduced
; once, outside the disjunction
(Bind {$z :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(zarci $r)}))
  {👉(∨ (Close (klama Speaker $z))
     (Close (klama Audience $z)))👈})
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
  {👉(∧ (Close (nelci Speaker $d)) (Close (bajra Speaker)))👈})
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
    {(∧ (Close (dunda Speaker $b 👉Audience👈))
       (Close (lebna Speaker $m 👉Audience👈)))})})
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
  {👉(∨ (Close (citka Speaker $p))
     (Close (citka Audience $p)))👈})
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
; mi joi do bevri lo pipno — the mixture kind bound Vague (§12)
(Bind {$mix :: PredTerm ρ}   ; ρ = the composition row of §12's
                             ; AdmissibleMixture signature
      (Vague (AdmissibleMixture (Combine Speaker Audience)))
  {(Bind {$g :: Referents (Group Entity)}
        👉(Refer (λ {$r :: Referents (Group Entity)}
          {(∧ (gunma $r (Combine Speaker Audience))
             ($mix $r (Combine Speaker Audience)))}))👈
    {(Bind {$p :: Referents Entity}
          (Refer (λ {$r :: Referents Entity} {(pipno $r)}))
      {(Close (bevri $g $p))})})})
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
; le verba mo'i ri'u cadzu — rightward: the ri'u direction value,
; ⊳-resolved against the ground
(Bind {$v :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(Close (skicu Speaker $r Audience
           (λ {$y :: Referents Entity} {(verba $y)})))}))
  {(∃ (λ {$e :: Referents Eventuality}
    {(∧ (Close (cadzu :1 $v :Eventuality $e))
       👉(MotionVector $e $v rightward)👈)}))})
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
(P28). `la'e` on these crosses through the token's realized act —
`(ActContent (RealizedAct u))`, the partiality `RealizedAct`'s alone
(spec §7.4) — into the host-sorted crossing; no universal coercion.

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

Event abstraction: `Refer` over event properties — the eventuality
sort refined by the abstractor (Achievement `mu'e`, State `za'i`).
`pu'u` and `zu'o`, which keep real x2 places, live in the
abstraction-relation family instead (next entry; spec §9.2).

```lisp
; lo nu mi klama cu nandu
(Bind {$ev :: Referents Eventuality}
      (Refer (λ {$e :: Referents Eventuality}
        {👉(Close (klama :1 Speaker :Eventuality $e))👈}))
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

Vague abstraction: shape conjunct + `srana`-aboutness, sort selected
by the host place (P14) — the deliberately underspecified "something
about X".

```lisp
; mi troci tu'a lo vorme — an event-sorted abstraction (the host
; place selects the sort), shape conjunct + srana-aboutness (P14)
(Bind {$door :: Referents Entity}
      (Refer (λ {$r :: Referents Entity} {(vorme $r)}))
  {(Bind {$a :: Referents Eventuality}
        👉(Vague (λ {$v :: Referents Eventuality}
          {(∃ (λ {$c :: Content}
            {(∧ (CoRef $v (EventOfContent $c))
               (Close (srana $v $door)))}))}))👈
    {(Close (troci Speaker $a))})})
```

**See.** [Spec §11](spec.md), pin P14.

### jai (JAI)

With tag: explicit role promotion — the tagged role to x1, old x1 to
the fillable `fai` place (`JaiPromote`). Bare: participant raising out
of the abstraction-x1 with the role `Vague`.

```lisp
; mi jai gau rinka lo nu do klama
(Bind {$eff :: Referents Eventuality}
      (Refer (λ {$e :: Referents Eventuality}
        {(Close (klama :1 Audience :Eventuality $e))}))
  {(Close (👉(JaiPromote rinka gau-role)👈 :1 Speaker :2 $eff))})
; the unfilled fai place closes contextually; gau-role is the label
; gau's tag reduction supplies
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
; do klama .i na'i — the objected act Let-bound (§7.2: no
; discourse constants)
(Let {$a :: Act Assertion} (Assert (Close (klama Audience)))
  {(Do (Perform $a)
      👉(NahiObjection $a)👈)})
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
; ko'a du ko'e — unassigned KOhA are keyed retrievals (P16)
(Bind {$a :: Referents Entity} (Context)
  {(Bind {$b :: Referents Entity} (Context)
    {👉(CoRef $a $b)👈})})
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

### .i je / .i ja … — I + jek

Sentence-level logical connection as one unit — NOT `.i` followed by
an independent `je`: **one performance of the connected content**
(P32 — forced by `.i ja`, where no pair of assertions exists), the
host's single force shared by the connection (content-taking forces;
an interrogative host queries the connected content), with `∧`'s
accessibility row shared with `Do`'s (spec §5.4). `.i joi` and the
non-logical ijoiks stay in `joi`'s discourse-joining `Do` arm.

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

## 15. Documented no-mappings and open adjacencies

Every cmavo the baseline treats carries an entry above; what remains
is exactly what the specification itself marks open:

- **Documented no-mapping**: BIhI at tanru and sentence loci — CLL
  14.16 records that no meanings have been found; the mapping states
  no row and implementations must not invent one.
- **Registered gaps** (spec §14): ordinary first-order restrictive
  clauses on `bu'a`-variables; explicit-`ce'u` in the non-`ka`/`du'u`
  abstractors; the non-numeric `me … me'u MOI` composite.

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
  (Bind {$to :: Referents Entity} (Context)
         {$from :: Referents Entity} (Context)
         {$via :: Referents Entity} (Context)
         {$by :: Referents Entity} (Context)
    {(∃ (λ {$e :: Referents Eventuality}
      {(klama Speaker $to $from $via $by :Eventuality $e)}))}))
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
  (λ {$x :: Referents Entity}
    {(Close (klama :2 $x))}))
```

## 2. Events, tense, facets

Facet joining is dynamic conjunction over a shared event — there is no
dedicated joining operator, because plain `∧` over the shared event
variable already says everything one would say:

```lisp
; mi pu citka
(Assert
  (∃ (λ {$e :: Referents Eventuality}
    {(∧ (Close (citka Speaker :Eventuality $e))
       (purci $e Now))})))
```

```lisp
; mi pu pu citka — a tense path: past of a past reference point
(Assert
  (∃ (λ {$e $m :: Referents Eventuality}
    {(∧ (Close (citka Speaker :Eventuality $e))
       (purci $m Now)
       (purci $e $m))})))
```

```lisp
; mi klama ti sepi'o ti — an instrumental facet, same event
(Assert
  (∃ (λ {$e :: Referents Eventuality}
    {(∧ (Close (klama Speaker This :Eventuality $e))
       (Close (pilno :2 This :3 $e)))})))
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
  (∃ (λ {$e :: Referents Eventuality}
    {(∧ (Close (citka Speaker :Eventuality $e))
       (fasnu $e))})))
```

Tenseless `mi citka` is **reading-multiple** (pin P8), never a default
present. Its episodic reading carries a `Context`-anchored occasion —

```lisp
; mi citka — the episodic reading: at the contextually relevant occasion
(Assert
  (Bind {$occ :: Time} (Context)
    {(∃ (λ {$e :: Referents Eventuality}
      {(∧ (Close (citka Speaker :Eventuality $e))
         (cabna $e $occ))}))}))
```

— while the habitual/gnomic reading carries no temporal conjunct at
all. Which reading was meant is resolved upstream, like any ambiguity.

## 3. Reference and descriptions

```lisp
; lo mlatu cu blabi              [pin P1]
(Bind {$cat :: Referents Entity}
        (Refer (λ {$x :: Referents Entity} {(mlatu $x)}))
  {(Assert (Close (blabi $cat)))})
```

Pinned reading: a new referent — one or more real cats, number-neutral,
no quantifier. Contrast: `su'o mlatu cu blabi` quantifies (though its
selected witness stays referable — §5 below); `lo` introduces with no
quantificational force at all.

```lisp
; lo mlatu na jbena — the referent scopes outside negation
(Bind {$cat :: Referents Entity}
        (Refer (λ {$x :: Referents Entity} {(mlatu $x)}))
  {(Assert (¬ (Close (jbena $cat))))})
```

```lisp
; le mlatu cu blabi              [pin P10]
(Bind {$it :: Referents Entity}
        (Refer (λ {$x :: Referents Entity}
          {(Close (skicu Speaker $x Audience
            (λ {$y :: Referents Entity} {(mlatu $y)})))}))
  {(Assert (Close (blabi $it)))})
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
(Bind {$alis :: Referents Entity}
        (Refer (λ {$x :: Referents Entity} {(Named "alis" $x)}))
  {(Assert (Close (klama $alis)))})
```

```lisp
; lo'i gerku — a set object via selcmi (xorxes' lujvo: x2 = members) [P5]
(Bind {$base :: Referents Entity}
        (MaxRefer (λ {$x :: Entity} {(gerku $x)}))   ; the maximal base:
                                                    ; THE dogs, not some
  {(Bind {$sets :: Referents (Set Entity)}
          (Refer (λ {$s :: Referents (Set Entity)}
            {(Close (selcmi $s $base))}))
    {(Mention $sets)})})
```

`loi gerku` is the same shape through `gunma` at `Group`. Neither object
unwraps to its members implicitly.

```lisp
; lo'e mlatu cu cinri            [pin P11]
(Assert
  (Generic Typical
    (λ {$x :: Entity} {(mlatu $x)})
    (λ {$x :: Entity} {(Close (cinri $x))})))
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
(Bind {$cat :: Referents Entity}
        (Refer (λ {$x :: Referents Entity}
          {(∧ (mlatu $x) (blabi $x))}))
  {(Assert (Close (jbena $cat)))})
```

```lisp
; le gerku voi blabi cu jbena — voi: non-veridical restriction  [pin P10]
(Bind {$dog :: Referents Entity}
        (Refer (λ {$x :: Referents Entity}
          {(∧ (Close (skicu Speaker $x Audience            ; the le-head:
               (λ {$y :: Referents Entity} {(gerku $y)}))) ; "my dog"
             (Close ((DropPlace skicu 3) Speaker $x       ; the voi
               (λ {$y :: Referents Entity} {(blabi $y)}))))}))   ; restriction
  {(Assert (Close (jbena $dog)))})
; the voi conjunct's audience place is DELETED, not omitted — a voi
; description has no audience role; the le-head keeps its audience.
; Three-way contrast: poi (veridical restriction, in the property),
; noi (projective supplement, below), voi (non-veridical restriction
; through the describer).
```

```lisp
; lo gerku noi blabi cu na melbi     [pin P7]
(Bind {$dog :: Referents Entity}
        (Refer (λ {$x :: Referents Entity} {(gerku $x)}))
  {(Assert
    (Supplement $dog (Close (blabi $dog))
      (¬ (Close (melbi $dog)))))})
```

Pinned reading: whiteness is a projective side commitment — the negation
touches only the beauty claim. Contrast: `xu lo gerku noi blabi cu melbi`
questions beauty and still commits whiteness; and the restrictive
`poi`-variant above puts whiteness *inside* what `na` can reach through
the description.

```lisp
; mi tavla le pendo goi ko'a — aliasing is shared binding
(Bind {$friend :: Referents Entity}
        (Refer (λ {$x :: Referents Entity}
          {(Close (skicu Speaker $x Audience
            (λ {$y :: Referents Entity} {(pendo $y)})))}))
  {(Assert (Close (tavla Speaker $friend)))})
; later ko'a occurrences consume the same binding.  [pin P16]
```

Contrast (`ko'a` never assigned): a keyed contextual retrieval — one
value per key, so `ko'a du ko'a` is reflexively true.

## 5. Quantifiers, witnesses, anaphora

```lisp
; ci gerku cu bajra .i ri tatpi      [spec §5.6]
(Bind {$dogs :: Referents Entity}
        (SelectExactly 3 (λ {$x :: Entity} {(gerku $x)}))
  {(Do
    (Assert (Close (bajra $dogs)))
    (Assert (Close (tatpi $dogs))))})
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
  (Presuppose (∃ (λ {$x :: Entity} {(prenu $x)}))
    (∧
      ; sentence 1's own claim — the ownership, never erased:
      (∀ (λ {$p :: Entity}
        {(→ (prenu $p)
           (∃ (λ {$d :: Referents Entity}
             {(∧ (Distrib (λ {$x :: Entity} {(gerku $x)}) $d)
                (= (CardBasis $d (λ {$x :: Entity} {(gerku $x)})) 3)
                (Close (ponse $p $d)))})))}))
      ; the anaphoric continuation at the joint locus (strong reading):
      (∀ (λ {{$p :: Entity} {$d :: Referents Entity}}
        {(→ (∧ (prenu $p)
              (Distrib (λ {$x :: Entity} {(gerku $x)}) $d)
              (= (CardBasis $d (λ {$x :: Entity} {(gerku $x)})) 3)
              (Close (ponse $p $d)))
           (Close (tatpi $d)))})))))
```

Pinned reading: each person owns three dogs, and each person's dogs are
tired — the anaphor normalizes into a joint locus with the governing
quantifier, and the normalization keeps the first sentence's assertion
(a bare conditional would be vacuously true of a dogless person). The
summed reading ("all the dogs together") requires explicit collection.

```lisp
; ro prenu poi ponse su'o xasli cu darxi ri — donkey   [pin P6]
(Assert
  (Presuppose (∃ (λ {$x :: Entity}
                {(∧ (prenu $x)
                   (∃ (λ {$y :: Entity} {(∧ (xasli $y) (Close (ponse $x $y)))})))}))
    (∀ (λ {{$p :: Entity} {$d :: Referents Entity}}
      {(→ (∧ (prenu $p)
            (Distrib (λ {$z :: Entity} {(xasli $z)}) $d)
            (Close (ponse $p $d)))
         (Close (darxi $p $d)))}))))
; $d at the plural type: the witness donkeys — the Distrib conjunct
; is the selection's own witness law, so the locus ranges over
; donkey-witness pluralities only; the atomic-pair spelling is the
; distributive strengthening.
```

```lisp
; ro gerku cu blabi — importing universal   [pin P2]
(Assert
  (Presuppose
    (∃ (λ {$x :: Entity} {(gerku $x)}))
    (∀ (λ {$x :: Entity} {(→ (gerku $x) (Close (blabi $x)))}))))
```

Contrast: `naku ro gerku cu blabi` — the nonemptiness presupposition
projects; only the universal is negated. Bare-logic `ro da` carries no
presupposition.

```lisp
; lo xo prenu cu jmaji — ... no — inner-no answer      [pin P22]
; the answer "no" is elliptical lo no prenu cu jmaji (guskant),
; which lowers through the zero-count special case, never Refer:
(Assert
  (No (λ {$x :: Entity} {(prenu $x)})
      (λ {$w :: Referents Entity} {(Close (jmaji $w))})))
; the nuclear scope is reference-typed (spec §12): "no people-witness
; gathers" — the collective reading a distributive quantifier could not
; state at all.
; answer substitution into the question's frame works; anaphora to
; the form is inaccessible (No exports nothing — nothing to refer to).
```

```lisp
; ci gerku ce'e re prenu cu nelci    [pin P17]
(Bind {$dogs :: Referents Entity}
        (SelectExactly 3 (λ {$x :: Entity} {(gerku $x)}))
        {$people :: Referents Entity}
        (SelectExactly 2 (λ {$x :: Entity} {(prenu $x)}))
  {(Assert
    (Distrib (λ {$d :: Entity}
      {(Distrib (λ {$p :: Entity}
         {(Close (nelci $d $p))}) $people)}) $dogs))})
; co-selected plural witnesses (the selections commute — one joint
; locus, P25's referential discipline); the member-wise Distrib nest
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
(Bind {$trio :: Referents Entity}
        (SelectExactly 3 (λ {$x :: Entity} {(jbopre $x)}))
  {(Assert
    (Reciprocate $trio
      (λ {$a $b :: Referents Entity}
        {(Close (tavla $a $b))})))})
; simxu's lexicon row consumes the library's Reciprocate schema:
; pairwise both ways among the witness.
```

```lisp
; so'i prenu cu klama — vague quantity    [spec §6.4]
(Bind {$n :: Natural}
        (Vague (AdmissibleThreshold ManyK (λ {$x :: Entity} {(prenu $x)})))
  {(Assert
    (AtLeast $n (λ {$x :: Entity} {(prenu $x)})
                (λ {$w :: Referents Entity} {(Close (klama $w))})))})
```

No exact count hides here: the term denotes the family over admissible
thresholds, and `na so'i prenu cu klama` negates pointwise (spec §6.5).

## 6. Acts, questions, answers

```lisp
; xu mi klama
(Ask (Polar (Close (klama Speaker))))

; ma klama
(Ask (OpenQ (λ {$x :: Referents Entity} {(Close (klama $x))})))

; ti mo — an open relation question
(Ask (OpenQ (λ {$r :: PredTerm ⟨x1:(Referents Entity)⟩}
  {(Close ($r This))})))

; klama fi'a ti — a place question           [spec §4.7]
(Ask (OpenQ (λ {$p :: CompatibleLabel klama (Referents Entity)}
  {(Close (At klama $p This))})))
; the computed-label domain is the compatible refinement (§4.7): the
; event place and any sort-incompatible place contribute no branch
```

```lisp
; mi cusku lu mi klama li'u — reported, not performed
(Assert
  (Close
    (cusku Speaker
      (StructuredQuote
        (Utterance {$u :: UtteranceToken}
          {(∧ (SpeakerOf $u Speaker)
          (Realizes $u (Assert (Close (klama Speaker)))))})))))
```

```lisp
; mi djuno lo du'u ma kau klama      [pin P9]
(Assert
  (Close
    (djuno Speaker
      (Reify
        (Answer
          (OpenQ (λ {$x :: Referents Entity} {(Close (klama $x))}))
          ContextualAnswer)))))
```

Pinned reading: answerhood committed; the exhaustivity slot is *absent* —
the weakest reading, with any completeness demand coming from `djuno`'s
own lexical presupposition, never from `kau`.

## 7. Indicators

```lisp
; .ui do klama — pure emotion: host asserted, joy displayed
(Let {$a :: Act Assertion} (Assert (Close (klama Audience)))
  {(Do (Perform $a)
      (Express (Close (Happiness Speaker $a Moderate))))})

; .au mi sipna — propositional attitude: host subordinated  [spec §7.6]
(Express (Close (Desire Speaker (Reify (Close (sipna Speaker))))))
; no assertion of sleeping occurs — the host-force profile of .au.

; .uinai cai do klama — paired emotion, then degree   [spec §7.6]
(Let {$a :: Act Assertion} (Assert (Close (klama Audience)))
  {(Do (Perform $a)
      (Express (Close (Unhappiness Speaker $a Intense))))})
```

```lisp
; za'a do cadzu — evidential grounding the act        [spec §7.6]
(Let {$a :: Act Assertion} (Assert (Close (cadzu Audience)))
  {(Do (Perform $a)
      (Express (Close (EvidentialBasis Speaker $a Observation))))})
; act-level display: an Express beside the bound host act; the family
; force clause grounds the assertion (a mode of commitment);
; na za'a do cadzu negates the walking, never the basis.

; mi jinvi lo du'u ti'e do klama — evidential on embedded content
(Assert
  (Close
    (jinvi Speaker
      (Reify
        (Let {$p :: Proposition} (Reify (Close (klama Audience)))
          {(Supplement $p
            (Close (EvidentialBasis Speaker $p Hearsay))
            (Holds $p))})))))
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
  (Let {$a1 :: Act Assertion} (Assert (Close (klama Speaker)))
    {(Do (Perform $a1)
        (Let {$a2 :: Act Assertion} (Assert (Close (stali Audience)))
          {(Do (Perform $a2)
              (Express (Close (Contrast $a2 $a1))))}))}))
```

```lisp
; do klama .i na'i — metalinguistic objection         [spec §7.3]
(Let {$prior :: Act Assertion} (Assert (Close (klama Audience)))
  {(Do (Perform $prior)
      (Bind {$defect :: DefectKind} (Context)
        {(Express
          (Close (MetalinguisticallyDefective $prior $defect)))}))})
; the defect dimension is contextually recovered; nothing is negated,
; and the objection itself performs nothing beyond the display.
```

## 8. Vagueness

```lisp
; sutra klama — the tanru link is Vague       [spec §6.2]
(Assert
  (Close ((Tanru sutra klama) Speaker)))
; ≗ (Bind {$link :: PredTerm ρ(klama)}
;         (Vague (λ {$r :: PredTerm ρ(klama)}
;                  {(TanruAdmissible sutra klama $r)}))
;     {… (∧ (klama …) ($link …))})
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
(Bind {$book :: Referents Entity}
        (Refer (λ {$x :: Referents Entity} {(cukta $x)}))
  {(Bind {$a :: Referents Eventuality}          ; sort from djica's x2
          (Vague (λ {$v :: Referents Eventuality}
            {(∧ (∃ (λ {$c :: Content}
                 {(CoRef $v (EventOfContent $c))})) ; shape: an abstraction
               (Close (srana $v $book)))}))      ; ... about the book
    {(Assert (Close (djica Speaker $a)))})})
```

Pinned reading: some eventuality-sorted abstraction — its content
deliberately withheld — pertaining to the book, the sort fixed by the
host place (`djica` x2). The shape conjunct matters: aboutness alone
would admit nearly anything.

```lisp
; ta barda — gradable predication: Context scale, Vague cutoff  [spec §6.4]
(Bind {$s :: Scale} (Context)                    ; which size-scale: recoverable
       {$reg :: Region Scale}
         (Vague (λ {$r :: Region Scale} {(AdmissibleCutoff $s $r)}))
  {(Assert (Close ((Grade barda $s $reg) That)))})

; du'e gerku cu klama — Vague threshold, Context purpose  [spec §6.4]
(Bind {$purpose :: Referents Entity} (Context)  ; too many FOR WHAT: recoverable
       {$n :: Natural}
         (Vague (AdmissibleThreshold TooManyK
                  (λ {$x :: Entity} {(gerku $x)}) $purpose))
  {(Assert
    (MoreThan $n (λ {$x :: Entity} {(gerku $x)})
                 (λ {$w :: Referents Entity} {(Close (klama $w))})))})

; mi co'e do — elliptical selbri: Context, not Vague   [spec §6.1]
(Bind {$r :: PredTerm ⟨x1:(Referents Entity), x2:(Referents Entity)⟩}
        (Context)
  {(Assert (Close ($r Speaker Audience)))})
```

The recovery test draws this line: `co'e` expects the hearer to recover
*the* relation; `tu'a` waives recovery.

## 9. Abstractions

```lisp
; lo du'u mi klama cu se djuno do
(Bind {$p :: Referents Proposition}
        (Refer (λ {$q :: Referents Proposition}
          {(CoRef $q (Reify (Close (klama Speaker))))}))
  {(Assert (Close (djuno Audience $p)))})
; CoRef (library) is plural co-reference — mutual Among — since typed =
; stays first-order; Reify is pure and lifts to a singleton reference.

; lo se du'u mi klama — the sentence expressing it (CLL 11.7 x2)
(Let {$p :: Proposition} (Reify (Close (klama Speaker)))
  {(Bind {$s :: Referents (Sign Sentence)}
          (Refer (λ {$x :: Referents (Sign Sentence)}
            {((DuhuRel (Close (klama Speaker))) $p :2 $x)}))
    {(Mention $s)})})
; x1 is filled with the reified content itself — the relation
; identifies it, so leaving x1 to contextual closure would add a
; retrieval the Lojban does not contain.

; lo ni mi klama — an abstraction relation, reference outside  [spec §9.2]
(Bind {$a :: Referents Amount}
        (Refer (λ {$x :: Referents Amount}
          {(Close ((NiRel (Close (klama Speaker))) $x))}))
  {(Mention $a)})
; the omitted scale x2 closed contextually — the same rule as any
; omitted place; le ni …, quantified ni, relative clauses on
; abstractions: all inherited from ordinary reference.

; lo su'u mi klama kei be lo fasnu — explicit categorizer (CLL 11.9)
(Bind {$kind :: Referents Eventuality}
        (Refer (λ {$k :: Referents Eventuality} {(fasnu $k)}))
  {(Bind {$a :: Referents AbstractNature}
          (Refer (λ {$x :: Referents AbstractNature}
            {(Close ((SuhuRel (Close (klama Speaker))) $x $kind))}))
    {(Mention $a)})})

; lo nu mi pu klama — event abstraction: Refer at the event sort
(Bind {$ev :: Referents Eventuality}
        (Refer (λ {$e :: Referents Eventuality}
          {(∧ (Close (klama Speaker :Eventuality $e))
             (purci $e Now))}))
  {(Mention $ev)})
```

## 10. Signs and mention

```lisp
; lu mi klama li'u
(Mention (StructuredQuote
  (Utterance {$u :: UtteranceToken}
    {(Realizes $u (Assert (Close (klama Speaker))))})))

; lo'u mi klama le'u — text, uninterpreted
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
; the content projection on assertion-realizing entries (spec §7.5).

; li re te'a ci du li bi — MEX with te'a (library)
(Assert (= (te'a 2 3) 8))
; contrast: me'o re te'a ci mentions the EXPRESSION sign, not 8:
; (Mention (Sign {$s :: SignToken MathExpression} {(TextOf $s "re te'a ci")}))

; li pa vu'u mo'e lo ni mi klama — the numeric crossing (CLL 11.5)
(Bind {$scale :: Referents Scale} (Context)      ; ONE scale, hoisted:
  {(Bind {$amt :: Referents Amount}                 ; it fills NiRel's x2
          (Refer (λ {$a :: Referents Amount}     ; AND reads the value
            {((NiRel (Close (klama Speaker))) $a $scale)}))
    {(Mention (− 1 (AmountValue $amt $scale)))})})
; mo'e = AmountValue: the amount's numeric value on the SAME scale that
; defined it (distinct Context sites would allow a mismatch — pin P15).

; lo jei mi klama — fuzzy truth degree (CLL 11.6)
(Bind {$ep :: Referents Epistemology} (Context)
  {(Bind {$tv :: Referents TruthValue}
          (Refer (λ {$v :: Referents TruthValue}
            {((JeiRel (Close (klama Speaker))) $v $ep)}))
    {(Mention (TruthValueDegree $tv))})})   ; a Number in [0,1]

; la .bab. goi by. cu klama .i by. prami — letteral-keyed binding
(Bind {$bob :: Referents Entity}
        (Refer (λ {$x :: Referents Entity} {(Named "bab" $x)}))
  {(Do (Assert (Close (klama $bob)))
      (Assert (Close (prami $bob))))})
; the letteral by. is a binding KEY resolved at the mapping layer;
; both occurrences consume the one binding.
```

## 11. The spiral sentence, in full

```lisp
; lo ci gerku noi blabi cu na batci re prenu .i .uinai cai ri tatpi
; (episodic readings: each sentence's occasion is Context-anchored, P8)
(Bind {$dogs :: Referents Entity}
      (Refer (λ {$r :: Referents Entity}
        {(∧ (gerku $r)
            (= (CardBasis $r (λ {$x :: Entity} {(gerku $x)})) 3))}))
  {(Do
    (Bind {$occ1 :: Time} (Context)          ; the biting's occasion — bound
      {(Let {$a1 :: Act Assertion}         ; OUTSIDE the negation, so na
            (Assert                       ; denies biting AT that occasion
              (Supplement $dogs (Close (blabi $dogs))
                (¬ (Exactly 2 (λ {$x :: Entity} {(prenu $x)})
                     (λ {$ppl :: Referents Entity}
                       {(∃ (λ {$e :: Referents Eventuality}
                          {(∧ (Close (batci $dogs $ppl :Eventuality $e))
                              (cabna $e $occ1))}))})))))
        {(Perform $a1)})})
    (Bind {$occ2 :: Time} (Context)
      {(Let {$a2 :: Act Assertion}
            (Assert
              (∃ (λ {$e :: Referents Eventuality}
                {(∧ (Close (tatpi $dogs :Eventuality $e))
                    (cabna $e $occ2))})))
        {(Do (Perform $a2)
             (Express (Close (Unhappiness Speaker $a2 Intense))))})}))})
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

## 12. Reflection

Quotes of core notation, with binders as ordinary words applied to
them (spec §7.7) — the notation every specimen in this book uses,
shown here with its reflection made explicit.

```lisp
; lo ka se klama — λ IS MakeLambda: one word, two names
(λ {$x :: Referents Entity} {(Close (klama :2 $x))})
(MakeLambda {$x :: Referents Entity}
  {(Close (klama :2 $x))})
```

```lisp
; lo mlatu cu blabi .i ri jbena — cross-sentence reference
(Bind {$cat :: Referents Entity}
      (Refer (λ {$x :: Referents Entity} {(mlatu $x)}))     ; active operand:
  {(Do (Assert (Close (blabi $cat)))                       ; a computation,
       (Assert (Close (jbena $cat))))})                    ; consumed as a
                                                           ; value; body inert
```

```lisp
; the reflective application word — for talking about application itself
(MakeApply {(MakeLambda {$x :: Referents Entity} {(mlatu $x)})}
           {This})
; ≡ ((λ {$x :: Referents Entity} {(mlatu $x)}) This) — each quoted
; operand interpreted exactly once (spec §7.7)
```

Contrast, one more time: `{(Close (klama Speaker))}` is quoted *core
notation* — code, evaluable one stage up; `lu mi klama li'u` is quoted
*Lojban* — a linguistic sign, interpreted only through the §7.5
crossings. Different kinds; the braces are core-only notation and no
Lojban word ever gains active-eval semantics.

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
```

# Rationale for the Lojban semantic core

Why each piece of [the specification](spec.md) exists, why it is shaped as
it is, and what was tried and rejected. The [samples](samples.md) supply
the worked specimens cited here. Sources — CLL (and the edition whose
section numbering is used), the official dictionary, the baselined gismu
list, the xorlo page, guskant's commentary, Brismu, solpahi's articles,
the Eberban and Toaq reference materials, and the plural-logic
literature — are cited inline by name and section; full citations with
URLs are collected in the specification's References section.

## 0. Method

A construct earns a place in the kernel only by a **necessity witness**: a
Lojban meaning that the rest of the core cannot express. A construct that
merely *helps* is defined in the library, where its definition is its
specification. Each entry below follows one template:

1. **Job** — the contrast the construct represents.
2. **Witness** — the shortest Lojban that requires it.
3. **Why not …?** — the plausible reductions, each with the exact
   sentence that kills it.
4. **Shape** — why this signature rather than the neighbors.
5. **Cost** — what the choice makes awkward, honestly.

Pins (rulings on accidental underspecification) follow a different
standard — CLL/xorlo evidence rather than necessity — and are argued in
§3. The global design essays (§2) cover the choices that cut across
constructs.

## 1. The constructs

### 1.1 Labelled place rows

**Job.** Lojban predicates have named, reorderable, deletable places;
functions have positions. **Witness.** `klama fe ti tu` (out-of-order
fill), `mi klama ti zi'o` (place deletion), `klama fi'a ti` (a question
*about places*). **Why not plain curried functions?** Position-only
application cannot state "x2, whichever argument position that ends up
being" — FA reordering, `zi'o`, and `fi'a` all speak in labels, so labels
must exist semantically. **Why not a primitive relation type distinct
from functions?** No witness separates two extensionally equal
row-functions, so `PredTerm<ρ>` is a *transparent alias* for
`Record ρ → Content`: the name and machinery of labels with the ontology
of functions. **Shape of filling.** One former: the single-place `At`
(itself record partial application), with all multi-fill notation
desugaring to nested single fills (spec §4.1). Fills are values, so
distinct-label fills commute — which is the semantic fact that makes
FA reordering and `se`-conversion pure notation: the order of fills
never was part of the meaning. **Cost.** The type theory needs
labelled records — which it needs for `fi'a` anyway.

### 1.2 `Close` as a defined operation

**Job.** An unmarked bridi with omitted places still makes a complete
claim. **Witness.** `mi klama` — committed to a contextually recoverable
destination and an event, not to "some destination" and not to nothing.
**Why not existential closure of omitted places?** Negation: `mi na
klama` does not mean "there is no destination I go to"; the contextual
destination stays fixed under negation, an existential would not. **Why
not a primitive?** Because its expansion — event quantification plus one
`Context` per defaultable place — *is* its content; a primitive would
just hide the expansion. The spec therefore defines it normatively and
keeps the name for exposition. **Cost.** Fully explicit terms are
verbose; that is the assembly-language bargain.

### 1.3 The specificity triad: `Refer`, `Context`, `Vague`

The single most consequential design decision. Three constructs, because
Lojban distinguishes three ways of not spelling something out, and
collapsing any two produces wrong meanings:

- **`Refer`** — *introduce*. Witness: `lo mlatu cu blabi .i ri jbena` —
  the cat outlives its sentence. Why not `∃`? An existential's witness is
  inaccessible after its scope closes and re-quantifies under negation
  (`lo mlatu na jbena` keeps *the* cat; `∃` would not). Why not ι (the
  definite)? xorlo `lo` claims no uniqueness. This is the dynamic
  indefinite of DRT/DPL, plural from birth.
- **`Context`** — *recover*. Witness: `mi klama` (destination), `co'e`
  (the relation we both know), `zu'i` (the usual value). Why not `Refer`?
  Nothing is introduced or described — `mi na dunda` denies the giving of
  the contextual thing, not the existence of a describable gift. Why not
  a free variable? Free variables have no discipline: `Context` declares
  its type, its dependencies, and its site/key identity (one retrieval
  per site per performance — which is exactly why `mi .e ti klama` shares
  one destination, and why `ko'a du ko'a` is reflexively true under the
  keyed rule).
- **`Vague`** — *waive*. Witness: the tanru link (`sutra klama` — CLL
  says the relation is constitutively open), `tu'a lo cukta`
  ("something about the book" — deliberately withheld), `so'i` (no fact
  fixes where "many" starts). Why not `Context`? The recovery test: no
  cooperative hearer is expected to land on one value, and communication
  has not failed when they don't. Why not ambiguity (several readings)?
  The speaker uttered *one* reading whose meaning is the constrained
  family; disambiguation upstream cannot help. The composition law
  (spec §6.5) makes the family compute like a meaning: pointwise lifting,
  consistent choice per binding site, supertruth where truth simpliciter
  is needed.

The classification of each Lojban construct into this triad (or into
**absence** — no machinery at all) is itself normative (spec §6.1), with
the recovery test printed as the decision rule. The borderline entries
were fought over and settled as follows: `co'e`/`do'e` sit with `zo'e` in
`Context` because CLL presents them as the ellipsis family — recovery
expected; the tanru link stays `Vague` because CLL's ch. 5 catalogue of
"possible relations" is offered as examples, not as a recovery target —
after context has done all it can, a family remains; gradable predication
splits — *which scale* is `Context` (say the wrong scale and you've
misunderstood), *where the cutoff sits* is `Vague` (sorites); and
unmarked distributivity is **absence**, not a parameter (see §2.5).

### 1.4 Projective content: `Presuppose` and `Supplement`

**Job.** Some commitments escape the operators wrapped around them.
**Witnesses.** `naku ro gerku cu blabi` still grants dogs (`Presuppose` —
import survives negation); `xu lo gerku noi blabi cu melbi` questions
beauty, never whiteness (`Supplement`). **Why not conjunction?** `∧` puts
both conjuncts under the negation/question — flatly wrong truth
conditions in both witnesses. **Why two constructs and not one?**
Presuppositions can be *satisfied* by prior context (no new commitment);
supplements always commit anew. Conflating them loses accommodation.
**Shape.** `Supplement` carries an explicit anchor, and a side that
depends on a quantified variable commits per instantiation inside the
binder — `ro gerku noi ke'a se cmene cu bajra`-type dependencies would
otherwise have no coherent projection site. **Cost.** A handler
discipline in the dynamics; the accessibility table carries it.

### 1.5 The accessibility table

**Job.** State, once, what each operator lets subsequent discourse see.
**Witness.** The `ganai da mlatu gi da ciska` conditional (antecedent
feeds consequent) versus `.ija` (branch-local) versus `naku` (nothing
escapes) — three connectives, three policies, none derivable from truth
tables. **Why a table rather than derived behavior?** Because the
policies *are* the connectives' dynamic meanings; deriving them from an
effect algebra is possible (and the model theory does — spec §5.1), but
the table is the single normative statement, so surface and model can
never drift apart. **Why are `↔`/`⊕` primitive?** Their classical
rewrites evaluate operands twice; under effects, twice-evaluated
introductions and supplements are real differences, not stylistic ones.
**Why not share the operands instead of duplicating them?** No sharing
route exists. The classical rewrite `(A → B) ∧ (B → A)` *textually
copies* each operand: two syntactic occurrences are two `Context` sites
(site identity is per occurrence, spec §5.3), two supplement handlers
committing the side twice (handler placement is a fact about term
structure — VC4), and a reshaped accessibility structure (in the
rewrite, the second conjunct sees the first's introductions through
`∧`, which the original `↔` never granted). `Let` cannot rescue it:
`Let` is the *pure* sharing form — spec §4.4 forbids binding an
effectful computation with it, precisely so that sharing a term never
silently shares an evaluation. `Bind` shares an evaluation but shares
its *returned value*, and `Content` returns unit — the meaning is the
state transformation, and no boolean comes back to reuse. The derivation
could be forced through by minting a truth-capture operator
(`TruthOf : Content → RefComp<Bool>` — run once, reify the truth
outcome), but that is not a reduction: it is a general
**dynamic-to-static reflection**, strictly more powerful than the two
connectives it would replace, usable anywhere as an escape hatch
(testing content in a restrictor without its effects), and needed by no
Lojban construct. `↔` and `⊕` are that same once-per-operand evaluation
confined to two closed truth-functional shapes with stated accessibility
rows — capabilities minimized, not operator names. In a pure,
effect-free logic both would be derivable; they are primitive *given*
effects and given the deliberate absence of any reflection operator to
route the sharing through.

### 1.6 Witness export without run objects

**Job.** `ci gerku cu bajra .i ri tatpi` — quantifier picks stay
referable. **Why not a term-level "retrieve the witnesses of run R"
operator?** Because the object needed is just the referent: an
accessibility rule ("a successful exporting evaluation introduces its
witness referent") supplies it with no run identities, no retrieval
operator, and no bookkeeping — and every construction expressible with a
retrieval operator is expressible by binding the referent. The dependent
case (`ro prenu cu ponse ci gerku .i ri tatpi`) generalizes the same rule
one scope level up via donkey normalization, rather than adding
machinery. **Cost.** The normalization rules must be stated per
configuration; the exotic ones are gap-registered rather than guessed.

### 1.7 The plural algebra, without covers

**Job.** Number-neutral reference with subreference and join. **Witness.**
`mi jo'u do bevri lo pipno` (a plurality acts; no set object exists to
act), `re lo mu plise` (subreference selection). **Why not sets?** In
the nonempty, atomistic, member-wise fragment the two designs are
intertranslatable — the honest answer is an equivalence-plus-choice,
argued in full in §2.8. The short form: sets used the way a set-typed
lexicon actually uses them (nonempty, predication reading the members,
never the set-object) are a plurality wearing set-notation clothing, and the
clothing costs more than it carries — the plural axioms return as
side conditions, the member-wise/object-wise distinction moves from
the type system into per-place convention, and coverage is lost where
Lojban is deliberately non-atomistic. (The familiar objection — "the
crowd can be large while the set is abstract" — attacks set-*object*
predication, which no serious set-typed design proposes; this document
does not lean on it.) **Why no distributivity/cover
parameter?** See §2.5 — the strongest single "less is more" decision in
the core. **Cost.** Marked readings need marks (`lu'a`, `Distrib`,
group gadri) — which Lojban has.

### 1.8 `DropPlace`, `Tanru`, `Scalar`

Three relation formers, three witnesses: `mi klama ti zi'o` (a relation
with the role *gone* — neither `zo'e` nor closure can remove a role);
`sutra klama` (constitutive modification vagueness — §1.3); `ta na'e
melbi` (scalar otherness is not `¬` — it is *stronger*: CLL 15.4, a
selbri negation "asserts that a relationship exists other than that
stated" and "remains an assertion of some specific truth", so `na'e P`
denies P's stated region *and* positively asserts an admissible
alternative on the recovered scale; `to'e` asserts the antipode, `no'e`
the midpoint. An earlier analysis had `na'e` weaker than
`¬`; the primary text overruled it, and the King-of-France passage of
CLL 15.4 — selbri negations "still make affirmative claims" — is the
decisive witness). Why not lexicalize scalar forms per predicate? The
operators are productive across the whole lexicon; three formers beat
thousands of entries.

The `Tanru` analysis has independent lexical corroboration: the gismu
`tanru`'s official row gives the compound its "meaning ⟨4⟩ in
usage/instance ⟨5⟩" — occasion-relative resolution as a dictionary
fact, adopted as the operator's shadow relation in spec §16.5.

### 1.9 `Generic`

**Job.** `lo'e`/`le'e` talk about typicality without a specimen.
**Witness (against every specimen theory).** `lo'e cinfo cu se kerfa lo
clani` (maned — normal *males*) with `lo'e cinfo cu se jbena lo cinfo`
(bears young — normal *females*): no single typical lion verifies both,
so a fixed "typical-lion reference" gives wrong conjunctions under
referential transparency. **Why not `∀`/`∃`/`Refer`?** Generics tolerate
exceptions (`∀` fails), claim more than instances (`∃` fails), and
introduce nothing anaphorically stable (`Refer` fails — generic anaphora
is honestly gap-registered instead). **Shape.** One operator, mode
Typical/Stereotypical, holder fixed to Speaker for `le'e` (a grammatical
fact, so it lives in the operator, not the lexicon). **Cost.** The
normality ordering is constrained, not defined — the operator is
*frankly axiomatic*, because genericity is an open problem in semantics
at large and pretending otherwise would be false precision.

### 1.10 `Reify` and the abstraction relations

**Job.** Lojban predicates select different abstraction sorts. **Witness.**
`lo du'u mi klama cu se djuno do` (knowledge takes propositions) against
`lo ni mi klama cu barda` (bigness takes amounts): swap them and both are
gibberish — the sorts are real. **Why is the `Reify`/`Holds` pair primitive?**
Because `du'u` is the one genuine Proposition↔Content crossing —
`Reify` inward, its axiomatized inverse `Holds` outward — while the
others — `ni`, `jei`, `li'i`, `si'o`, `su'u`, `pu'u`, `zu'o` — are
abstractors to which CLL itself assigns place structures (CLL 11.3, 11.5,
11.6, 11.9: "x1 is the amount of … on scale x2"), so the core renders
them as named abstraction relations and
lets reference apply outside: `lo ni …` and `le ni …` then differ exactly
as `lo` and `le` always differ, outer quantifiers and relative clauses
work unchanged, and the omitted x2 (`su'u`'s "type", `ni`'s scale) is
ordinary contextual closure. A family of primitive
`Content × operand → sort` constructors was rejected because it would
re-derive all of that machinery, worse, per sort. **Cost.** Terms are a
little longer; uniformity pays for it.

### 1.11 Acts, performance, tokens, signs

**Job.** Force, quotation, and reported speech. **Witnesses.** One content
under four forces (`do klama` / `xu` / `ko` / displayed); `mi cusku lu ko
klama li'u` (a directive described, not issued — construction ≠
performance); `lo'u mi do du le'u` (quoting the unparseable — signs carry
text, not meaning); `la'e lu mi klama li'u` (a sign and what it expresses
are different things, and Lojban crosses between them explicitly).
**Why opaque quotation boundaries?** Anaphora and presupposition must not
leak out of mentioned material, or quotation collapses into use.
**Cost.** Tokens and signs enlarge the ontology; every element is
independently witnessed.

### 1.12 Indicators: displayed content with lexicon discipline

**Job.** `.ui nai cai`, evidentials, discursives — meaning that is shown.
**Witnesses**, one per design decision: `.au mi sipna` (host
*subordinated* — no sleeping asserted: host-force profiles are real and
lexical); `.uinai cai` (intense *unhappiness* — `nai` selects the paired
emotion, then degree applies: pairing must precede degree, so pairing is
lexical, with `Scalar Opposite` only as documented fallback — CLL 15.7's
opposite-end rule); `mi jinvi
lo du'u ti'e do klama` (hearsay marked on *embedded* content — so
evidentials cannot be an operand on assertion force; they are targeted
display whose force-grounding effect fires when the target is the
enclosing act's content); `pei` (attitudes are questionable — so they are
first-class relations, not wrappers). **Why not a closed generated
inventory?** The UI lexicon is open; the core supplies the *shape*
(relation, target, degree, pair, profile) and the dictionary supplies the
instances. **Cost.** The lexicon carries real semantic load — by design
(§2.6).

### 1.13 Why facet joining is plain conjunction

**Why not a dedicated operator.** A dedicated non-logical joining
operator for tense/modal facets sharing an event might look necessary
— surely "same locus" needs a connector — but no witness separates it
from dynamic `∧`: the shared event is an explicit variable, so locus
identity is carried by binding, not by a connector; and the
tag-negation paradigm *derives* from `∧`-placement what a dedicated
operator would have to stipulate — `mi klama ti
sepi'onai ti` negates just the instrument conjunct (`klama ∧ ¬pilno`)
while bridi `na` negates the whole (`¬(klama ∧ pilno)`), and tense
chains (`pu pu`) need precisely `∧`'s left-to-right accessibility for
their anchor anaphora. The jobs such an operator would claim
distribute cleanly: sumti `joi` is
group formation, discourse joining is `Do`, and the genuinely
unspecified connection is a `Vague` relation (spec §6.1). **Cost.**
None found; the decomposition is pure simplification.

### 1.14 `Bind`

**Job.** Run an effectful computation once and use its result under a
binder — the seam between the pure λ-fragment and the dynamics.
**Witness.** `lo mlatu cu blabi .i ri jbena`: the introduction must run
*once*, with its witness reused across two performed acts —
`(Bind {$cat :: Referents Entity} (Refer P) {(Do a₁ a₂)})`. **Why not
ordinary λ-application?** In the calculus as typed, application simply
*cannot* consume a computation where a value is demanded — `Bind` is
`RefComp`'s eliminator, and that type mismatch is the primary
necessity witness. The live alternative is a different calculus: a
direct-style call-by-value core where application itself sequences
effectful arguments. There the two would coincide — the honest gloss
is that `Bind` *is* application under mandatory call-by-value at
computation types, made visible — but the direct-style calculus pays
with a value-restricted β-law: substitution copies the argument's
*text*, so β-equality would hold only for value arguments, with every
effectful application node an unmarked sequencing point. The core
prefers the discipline visible: β holds unconditionally in the pure
fragment, and every sequencing point is a `Bind` node the
accessibility table can name (witness-export width is stated in terms
of it). **Why not the CPS/state encoding?** `Bind` is famously
λ-definable if `RefComp<T>` is spelled as its *transparent*
state-threading function type — but then information states and
continuations become first-class term values, and the term language
acquires meanings no Lojban sentence has: state inspection, double-shot
continuations (backtracking), and truth-capture-without-effects — the
reflection operator §1.5 deliberately refuses — all free of charge and
all requiring ban-conditions to re-exclude. (An *abstract* or
linearity-disciplined encoding avoids the junk exactly by reimposing
the monadic interface — which concedes the point.) The transparent
encoding also freezes §5.1's carrier into the definition (any carrier
refinement — the `da'i` gap entry already commits to extending it
with a world-shift operation — would rewrite the type of every term
ever written) and turns the definition
from an interface with many models into a description of one machine.
**Comparative note.** Kuna — the loglang implementation nearest this
territory — makes the same choice: its expression language is a typed
λ-calculus plus named effect constructors and named combinators
(`and_then` — monadic bind — among its built-in constants), not a CPS
expansion; exactly one of its effects (`Cont`, scope-taking) is
deliberately continuation-typed. Eberban has no `Bind` because it has
no distinct computation type to eliminate — see §2.4. **Cost.** Two binder forms
(`Let`/`Bind`) where one calculus habit expects one; the distinction
is load-bearing and must be taught.

## 2. Design essays

### 2.1 Why not plain predicate logic

FOL loses, in order: cross-sentence anaphora (no discourse referents —
spec §5.6), donkey readings (no compositional dynamic binding — the
truth conditions are classically statable, the anaphoric route to them
is not; §5.6), projective
content (one dimension of meaning — §5.5), force (assertion only —
§7.1), plurals (singular terms — §3.2/§4.8), vagueness-as-meaning
(bivalent atoms only — §6), and use/mention (no signs — §7.5).
Each loss above is a witnessed Lojban phenomenon. The core is exactly
FOL's spine — typed λ, connectives, quantifiers — plus the
disciplined extensions those witnesses force.

### 2.2 Why two truth values (against Eberban's three)

Eberban builds true/false/unknown into its logic. The phenomena "unknown"
covers split, in Lojban, into things the core keeps apart: contextually
unresolved values (`Context`), unasserted content (force), presupposition
failure (projective definedness), and unanswered questions (`Query`
values). Bundling them into a truth value forfeits those distinctions —
e.g. negation treats presupposition failure and plain falsity
differently, which strong-Kleene tables cannot see. Two values plus
projection recovers every honest use of "unknown" with none of the
collateral.

### 2.3 Why explicit context (against the threaded context argument)

Eberban threads a hidden context parameter through every predicate —
elegant, and it makes tense and deixis nearly free. The core declines it:
a definition optimizes for *auditability*, and a hidden argument on every
relation is the single largest source of "where did that reading come
from?". Instead the utterance context is one explicit record, deictics
are its projections, `Context` computations consult it per site, and
`InContext`/`ShiftedGround` shift it visibly — so `ra'o`-style shifts,
which the threaded design gets for free, cost one visible operator here,
and everything else stays inspectable. The trade is verbosity for
transparency, which is this project's trade everywhere.

### 2.4 Why worlds live only in the model (and effects only in the model)

De re/de dicto and opacity are real (`mi djica lo nu mi pilno lo karce`
has two readings), so the model theory is world-indexed. But no Lojban
sentence *binds* a world: the candidates were hunted down (attitudes, CAhA, `da'i`,
property-internal descriptions — `lo ka viska lo pavyseljirna` included)
and every candidate resolves by binder placement plus lexical
intensional-place marking, evaluated in the world-indexed model. So terms
stay world-free; `da'i` waits in the gap register for the treatment its
three open dimensions deserve. The same restraint governs effects: the
dynamics *is* one algebraic computation type in the model, but the
normative surface is the named operations and the accessibility table —
Kuna demonstrates the algebraic surface working for Toaq, and also
demonstrates its cost (a composition search and ten wrapper types between
the reader and the meaning). One content, two presentations; the
definition shows the readable one and states the equivalence.

Worth stating once, because it locates this whole design: **dynamic
semantics is static semantics at a higher type**, twice over. A
supported at-issue declarative discourse — once its readings,
contextual parameters, and precisifications are fixed — has
classically statable truth conditions: the
donkey normalization's output *is* a classical formula; normalization
is the desugaring, performed by the mapping. (Questions, directives,
displays, and the projective dimension carry more than truth
conditions; for them the desugaring target is the model's
state-transformer objects, the second sense below.) And sentence meanings are
statable statically too, at the state-transformer type — §5.1's
carrier is a plain set-theoretic function space. What cannot be
recovered by any desugaring is *compositional locality*: no assignment
of ordinary truth-condition-type meanings to sentences makes `.i`
conjunction and lets `su'o gerku cu klama .i ri melbi` come out right,
because the witness closes inside sentence one before sentence two
exists. A semantics of Lojban discourse must either raise the sentence
type (the transformer model) or globalize the translation (per-
configuration normalization); this core does the second in the mapping
for the supported fragment and justifies those rules uniformly with the
first in the model — with `Bind` as the visible seam (§1.14).

The comparison with Eberban sharpens here. Eberban is a *sentence*
logic with a threaded context parameter: its binding particles desugar,
in its own refgram's equations, to conjunction, ∃-closure, and argument
routing in static HOL, and its `ze` family gives latest-instance
cross-sentence anaphora that reaches even a preceding existential's
witness (the refgram equates the follow-up sentence with the first
sentence's witness, and marks the multiply-evaluated/donkey cases as
an open TODO). Its conversation context is genuinely carried
between sentences and updated by dedicated predicates (the refgram's
`an` family), so what it lacks is neither conversational state nor
simple witness anaphora but the general case: a *distinct computation
type* with compositional witness export — covariant (donkey)
dependence across binders — and a formal projective-commitment layer
(at-issue vs aside). Nothing propositional is thereby inexpressible
(HOL states any classical truth condition, given restructuring into
one sentence with shared variables); the anaphoric route is what is
absent. Lojban's grammar makes exactly that route
core (`ri`, `go'i`, witness export, `noi`), so its definition cannot
decline the discourse level; a language that adds covariant
cross-sentence binding faces the same fork, and the fork is a fact
about the phenomena, not a house style.

### 2.5 Why there is no distributivity parameter

The tempting design: unmarked plural predication carries a covert cover
variable (context supplies it, or it's vague). Rejected on three grounds.
First, xorlo says unmarked gadri are *unspecified* for distributivity —
and a parameter is not unspecification, it is a question the sentence
now silently asks. Second, plural logic's lesson ("the rocks rained
down" hides no quantifier over ways-of-raining) — the predicate holds of
the plurality, and *how* it holds is the predicate's lexical business, which
the lexicon interface records per place. Third, the cover readings fail
the vagueness test from the other side: each-carried and
together-carried are things speakers separately *mean* and hearers
recover — reading-level choices, which live upstream in
disambiguation — while the unmarked sentence's configurations (the
piano carried, however the three shared the load) verify it without any
cover fact existing at all. A covert parameter would turn every
unmarked plural sentence into that upstream question, silently asked.
So: neutral predication is
the reading; `lu'a`, `Distrib`, and the group gadri are the marked forms.
Absence means absence.

### 2.6 Why the lexicon is a first-class interface

Many disputes that look semantic are lexical: which places are
intensional, which deletions are meaningful, what `djuno` demands of its
answer, which emotion `.uinai` names, how `bevri` composes with plural
carriers. A definition that inlined all of this would be a dictionary; one
that ignored it would be unusable. The core's answer is a typed interface
(spec §10): the *schema* of lexical knowledge is normative, its *content*
is curated data. No collection entry needed legislating after all —
source verification showed
official `gunma` x2 is already the components and `selcmi` (a xorxes
lujvo, now also glossed and used by the Contemporary CLL edition's
set-descriptor expansion) already takes its members as x2; both are
adopted with plural-reference x2. The defective gloss in this area is
official `cmima`'s x2-as-set, which the library simply avoids.
The `le`-description analysis deserves its history spelled out, since
it was contested during drafting. `skicu`'s official definition — "x1 tells
about/describes x2 (object/event/state) to audience x3 with description
x4 (property)" —
makes its x4 a property, so a `skicu`-based `le` (the property applied
to x2 by `skicu`'s own definition) is expressively adequate. The
question closed when guskant's own `le` expansion surfaced —
`zo'e noi mi ke'a do skicu lo ka ce'u broda` (the commentary's gadri
definitions) — showing the community's
formal analysis was the `skicu` analysis all along, and the one
surviving concern (that `skicu` names a describing *event*) is
answered by the anchoring clause: the describing event is this
utterance's own locution, true by construction, with the token
machinery already there to say it. So `le` lowers through `skicu`,
exact official fit, no dictionary change. (Why not a dedicated
`DescribedBy` relation: it might look cleaner than reusing a
dictionary word, but both of its would-be supports fail — reading
`skicu`'s x4 as a "medium of expression" misreads the official row,
and requiring core relations to be definable independently of the
dictionary imposes a constraint nothing needs, since the lexicon
program defines gismu semantics.)

### 2.7 Alternatives shaped like implementations

A recurring failure mode in formalizing a language: machinery that mirrors
how a *processor* would work — run identities for quantifier retrieval,
error taxonomies as meanings, canonical spellings as semantics, registry
lookups as analyses, "unresolved" as a semantic value. This project's
history included several such shapes, and each died the same death: ask
for the *meaning* the machinery denotes and there is none — only a
process state. The tests that killed them are usable on any future
proposal: Does it survive alpha-conversion and re-serialization? Does a
sentence witness it? Does it still make sense on paper, with no program
running? Nothing in the core fails those tests; §14's gap register exists
so that honesty about coverage never again requires inventing semantic
objects for process states.

### 2.8 Why lexical arguments are plural references, not sets

The most serious alternative to §1.7's plural algebra is a set-typed
lexicon: every argument place currently typed `Referents<T>` becomes a
nonempty `Set<T>`, as Eberban's dictionary does throughout (its `tce`
type is a *non-empty* set; a `*` marks places whose satisfaction
survives passing a subset — refgram, "Dictionary conventions") and as
Brismu's foundations choose ("sets are free over a universe of
individuals … an inevitable structure" — Brismu, "Sets, not Masses").
The pre-xorlo dictionary ran a partial version of the same experiment:
in the baselined gismu list (1994), roughly thirty places carry
set-typed annotations — the word "set" in the place gloss, usually with
a completeness side condition; the literal "(set)" marker on about a
dozen entries (`sisku` x3 "complete specification of set"; `kampu`,
`simxu` x1, `cuxna` x3, the `-mei`/`cmima` cluster).
This section records what a full examination established, so the
choice is never again defended with less than its real argument.

**First, the concession.** Under the discipline a working set-typed
lexicon actually imposes — call it **D**: sets nonempty; members drawn
from the individuals (atomistic generation); predication at lexical
places reading the *members*, never the set-object; extensional
identity, with discourse-introduction identity carried separately;
representation sets kept distinct from first-order set objects — the
two designs are intertranslatable. `Combine` is union, `Among` is
subset, the singleton lift sends each individual to the set
containing exactly it, and
`Referents<T>/CoRef ≅ NonEmptySet<T>` is a theorem. Inside D nothing
expressible distinguishes the designs; "the crowd is large while the
set is abstract" is no objection there, because under D largeness is
never predicated of the set-object at all. Eberban's own gloss of
eating shows the discipline at work: the set is a delivery mechanism
for the members, and the word's definition says how the members
satisfy it (refgram, "Dictionary conventions": the `bure` example).

**Second, the choice, and its grounds.**

1. *The isomorphism is conditional, and the core sits outside its
   conditions on purpose.* D's atomicity clause is a strict
   strengthening of the plural algebra: §4.8 assumes no atoms
   ("nothing requires that references bottom out in singletons"), and
   counting is `CardBasis` — units under a description — rather than
   cardinality of a canonical member basis. That is deliberate
   plural-logic territory (guskant's indefinitely divisible bread;
   mass-like reference generally). A set-typed lexicon either loses
   that coverage or re-legislates it.

2. *Inside D the re-spec is relabeling plus obligations.* The plural
   axioms do not disappear; they return as side conditions —
   nonemptiness at every place (Eberban's `tce` states it in the
   argument's type just as our reference type does), ur-element
   legislation, the member-wise reading imposed per place, and
   provenance labels re-creating the co-reference/introduction
   distinction that extensional sets collapse. Meanwhile lists, groups,
   and genuine set objects survive untouched, so "one collection
   machinery" is not delivered by any actual set-based design: Eberban
   itself needs a wrapped/unwrapped split ("mostly use these 'wrapped
   versions' unless … speaking about nested sets" — refgram, "Eberban
   from scratch", the sets chapter) — which is the
   `Referents<T>`/`Set<T>` distinction with the names filed off,
   enforced by convention where this core enforces it by type.

3. *The two-sort split structurally excludes a real ambiguity.* With
   plural references and set objects as different sorts, `lo selcmi cu
   simxu lo ka tavla` has one analysis (set objects don't talk; the
   members-reading goes through membership machinery). With one
   set-type everywhere it is genuinely ambiguous — several sets
   reciprocally related, or one set's members — which is solpahi's
   argument ("A Simpler Quantifier Logic") that a place cannot accept
   both readings without "a true ambiguity", and is where the
   pre-xorlo set places actually hurt.
   Under a uniform set re-spec the exception class that must be carved
   out — `cmima`, `selcmi`, `kampu`, `sisku` x3, the set operators —
   is exactly the current `Set<T>` vocabulary. The core is not
   set-averse; it is place-precise, and the re-spec's own exceptions
   recover its shape.

4. *The dictionary record.* The set annotations of the baselined
   gismu list were inconsistently applied (the paradigm collective
   predicate `sruri` carries none), dragged completeness side
   conditions that plural reference does not need, and were re-read as
   plural by xorlo-era practice without the text ever changing — the
   official jbovlaste entry for `simxu` still says "(set)" as of this
   writing, while the community's formal treatments (guskant's
   commentary; solpahi's articles) reconstructed the plural reading
   externally. Plural
   reference is what the set annotations were reaching for; the core
   says it directly. The per-place audit itself is owed under both
   designs (spec §10's plurality-behavior field is the same docket as
   Eberban's stars); what differs is the failure mode — under the
   re-spec a misassigned member-wise/object-wise call silently moves
   truth conditions, while an unpopulated lexical field leaves
   vagueness, not error.

5. *Brismu's second-order objection does not weigh here.* "Plural
   logic is equiconsistent with monadic second-order logic, given a
   predicate for masses" ("Sets, not Masses" — an assertion the chapter
   supplies without proof) is, even granted, idle: equiconsistency is far
   weaker than equivalence of designs, the hedge concedes that plural
   quantification is present either way, and second-orderness is no
   incremental cost in a core that is already a typed λ-calculus with
   comprehension. The metatheory may freely use sets to model plural
   extensions — §4.10's witness sets already do — without lexical
   places denoting set objects.

**Third, what was adopted from the set side.** The sharpest thing in
Eberban's conventions is the star's definition, and the lexicon
interface now uses it: the plurality-behavior field's
subreference-monotonicity value means *satisfaction preserved under
subreference* (`Among`) — a checkable lexical criterion — with
collective capability recorded as an independent fact (a satisfying
plurality need not satisfy in its parts, which is an absent guarantee,
not a counter-entailment); per P4, never a reading parameter. Not imported: the cumulative default
Eberban writes into definitions like its eating verb (everyone eats at
least one; every apple is eaten) — that is a resolved cover reading,
which P4 declines as a default and Lojban marks when it means.

Solpahi's "A Simpler Quantifier Logic" stands in the record as
independent convergence: plural constants demand plural variables (the
2004 Clifford–xorxes exchange, quoted there), and bare PA as
plural-existential
witness-sets is P17 arrived at from the other direction — including
the scope-commutativity bonus. His hybrid-era gap (`no prenu cu
jmaji` inexpressible) was the price of xorlo's no-rewrite move, and
this core pays the other half of that bill with plural selections and
joint loci — a repair orthogonal to sets.

### 2.9 The reflection layer: why quote-and-apply, and why not fexprs

Spec §7.7 reduces the term grammar, in its braced spelling, to atoms,
quotes, and application, with one primitive sign-function
(`MakeLambda`) and everything else vocabulary. Four arguments shaped
it.

**Why at all.** The content-word program's end state — only content
words as predicates — stalled at the binder operators: a binder is not
a relation over individuals, so no gismu row could be its fit. Making
each binder a *function on quoted expressions* dissolves the obstacle:
a sign-consuming function has an ordinary place structure (its x2 a
quoted-notation sign, like `tanru`'s official text-typed operands), and so has a
content-word fate like everything else. The same move grounds the
self-description goal: because the vocabulary is stage-schematic, one
Lojban text can state the semantics of the stage below it — the
definition of Lojban in Lojban is a tower of one repeated text, never
a level defining itself (Tarski respected, not refuted), floating on
the model-given lexical basis that no language escapes.

**Why explicit quotes and not fexprs.** The lazy road to "operators on
unevaluated operands" is the fexpr: every word receives its operands'
syntax. Wand's result is why that road is closed: in his fexpr
calculus, contextual equivalence collapses to α-congruence — no two
distinct programs are interchangeable, so the theory of terms is
trivial. The design inference (motivating, not identical to, the
theorem): grant unrestricted access to operand syntax and the
equational theory is forfeit. The
core takes the disciplined road instead: the transition to syntax is
always visible (braces in the source are the only place code enters),
active operands are consumed as values only, `Expression` values are
constructive-only (no destructors, no code equality), evaluation is
typed and staged with no same-stage interpreter, and quotes close over
the environment they were written in (evaluation never reads the
evaluator's ambient context — the second ingredient of the fexpr
collapse). This is the same refusal as `TruthOf` (§1.5), made twice:
no dynamic-to-static reflection at the truth level or the syntax
level. The accepted price is stated in §7.7 rather than discovered
later: there is no anti-quotation — reflection is schematic, code with
variables, values flowing in at use.

**Why one primitive sign-function.** The kernel was already
applicative — quantifiers, connectives, the triad, the force
constructors all consume *values* — so the only place surface syntax
genuinely binds text is λ itself. `MakeBind` is the carrier's
sequencing operation `bind` composed with
`MakeLambda`; `MakeLet` is application composed with it; the facades
for everything else are one generic schema, materialized on demand.
The alternative — a `Make*` twin for every operator — would recreate
the duplication the catalog audit just removed, with no semantic
witness for any pair.

**Why one spelling.** The braced spelling makes inert positions
visible at a glance and reduces the grammar to exactly three formers —
atoms, braces, application. A second, parenthesized binder-list
spelling might look like harmless convenience, but a dual costs more
than it carries: every reader must learn both, every tool must accept
both, and the sole benefit — familiarity of the binder names — is
already delivered by the aliases (`λ`, `Let`, `Bind`). A definition
gains more from a single notation than from a courtesy variant (no
canonical *spelling* of terms is thereby defined — spec §2; it is the
binder syntax that is single).
The braces themselves carry teaching weight — the primer's hardest
points (inertness, constructing-without-performing, held-back scope)
are visible in the notation itself.


### 2.10 du'u, nullary ka, and the reserved reification family

An influential community proposal — And Rosta's, on the Lojban
Wiki's "ka, du'u, si'o, ce'u, zo'e" page, endorsed there with
amendments and also recorded with dissent — holds that `du'u`, `ka`,
and `si'o` "are logically
identical. They all express n-adic relations, where n is the number of
overt or covert `ce'u` within the abstraction. A proposition is a
0-adic relation." The BPFK's *proposed* `ce'u` definition goes part of
the same way: `ce'u` is "almost solely used in `ka`", though
`si'o`/`du'u`/`su'u` clauses "can make some sense" with it. On the
proposal, the
abstractors differ only in what elided sumti default to. Is this core
wrong to give `du'u` its own primitive?

No — because the proposal and the primitive answer different
questions, and the core asserts both answers where they are typable.
As a claim about
**abstraction syntax** the doctrine is correct over `ka` and `du'u` —
the baseline's `ce'u`-capable abstractors — and holds there as a
theorem: `ce'u`-marking extracts λ, arity is the count of distinct
extracted variables, and the bare-`du'u` case is
the 0-adic one — whose extracted "relation" is the content itself,
since `PredTerm<⟨⟩>` applied at the empty record *is* `Content`
(§3.3). (`si'o` is the point where this core declines the proposal:
the conceptualizing mind is a lexical place of `SihoRel` — CLL's row,
kept by the BPFK's own proposed `si'o` definition — not an
elision-default rule, so `si'o` stays in the §9.2 relation family and
the all-`ce'u` reading joins the reserved family below. The carve-out
is itself evidence for the two-questions thesis: the proposal
conflates a place-structure fact with an elision default.) Abstracting nothing out of a bridi leaves its content; in that
exact sense `du'u` *is* nullary `ka`. What the doctrine never had the
machinery to ask is the **object** question: what sort of first-class
thing fills `djuno`'s x2, gets counted, identified, and anaphorically
retrieved. `Content` cannot be that thing in this model — it is
computation-typed, deliberately without equality, and putting it in
the domain of individuals would make effects quantifiable objects. So
the crossing the untyped doctrine leaves implicit gets a name:
`Reify`, with `Holds` its inverse and the round trip as axiom (§9.1).
A proposition is the *reification of* a 0-adic relation — the
doctrine's slogan, plus the bridge it needed all along.

The asymmetry with `ka` is then principled, not accidental. Property
places (`ckaji`, `mutce`) are consumed by *application* — the selbri
applies the property — so they take function-typed operands directly
and `lo ka` lowers straight to the λ. Proposition places are consumed
by *aboutness* — nothing applies them — so they take the reified
object, and all the sumti machinery (descriptions, anaphora,
quantification, `du` as `CoRef`) runs on it.

The experimental pair `me'ei`/`me'au` shows where this design is
deliberately unfinished. `me'au` uses an abstract-predicate sumti as
a selbri of the referent's arity; at the propositional case the model
covers it under §9.1's singleton condition — for a singleton
proposition reference `abu`, `me'au abu` is `(Holds p)` at the
presupposed sole member: disquotation rather than the truth-predicate
(`abu jetnu` claims *about* the object; the axiom pair aligns their
truth conditions without conflating their shapes). The plural case
has no baseline reading — silent distribution would breach the
no-default-distributivity stance — and is registered with the
universal reading as candidate. Above arity zero,
`me'au`'s inverse `me'ei` manufactures property *objects* — and this
baseline has none: `lo ka` is a transparent λ, so there is no referent
for `goi` to bind and no domain for property quantification. Rather
than either building the full family now or foreclosing it, §9.1
records the reservation: the `Reify`/`Holds` shape generalizes row by
row (Chierchia and Turner's nominalization/predicativization pair is
the standing prior art), `Proposition` is the row-⟨⟩ member, and the
rest is a registered gap. On identity the reservation is careful
about what is already decided: the axiom pair makes `Reify` and
`Holds` mutual inverses, so proposition identity is exactly content
identity — intensional and dynamic, finer than logical equivalence —
fixed by the axioms, not open; and any future row's crossing, being a
function over the extensional `PredTerm<ρ>`, identifies β/η- and
pointwise-equal predicates by congruence. What stays open is only the
adoption-shape question (whether each row repeats the bijective
shape; how row isomorphism and any cross-row operators are typed),
and that is what makes the reservation cheap: adopting the family
later fills a declared hole instead of reopening the bridge.


## 3. Pin arguments

Condensed; each pin's full context is in spec §13. The ones that were
genuinely fought:

- **P1/P22 (xorlo, inner `no`).** "No default quantifiers. At all." is
  the xorlo page verbatim; everything else follows from `Refer` +
  nonempty plural references. For inner `no` that type argument shows
  only that `lo no broda` cannot be a *reference*; it does not show the
  form is meaningless, and guskant's gadri commentary ("Cannot say
  zero") supplies both the reading and the reason to want one: her
  unofficial `lo no broda = naku su'oi da poi ke'a broda`, motivated by
  answer continuity — `lo xo prenu cu jmaji …` answered by `no`,
  elliptical for `lo no prenu cu jmaji …` — the pattern that also
  carries `go'i`-inherited frames. The pin therefore special-cases
  inner `no` at the mapping layer to the zero-count (`No`) schema over
  the description's property and the bridi frame: substitution into
  question frames works, nothing touches the nonemptiness of the
  reference type, and anaphora to the form is correctly inaccessible
  because `No` exports no witness. (Ruling the form defective outright
  might look simpler, but it would rest on the unverifiable premise
  that usage avoids it — and it breaks the answer-substitution pattern
  that motivates the reading; hence the special case.)
- **P2 (`ro` imports).** Saying `ro gerku cu blabi` commits the speaker
  to there being dogs, and the commitment survives wrapping: `naku ro
  gerku cu blabi` denies the universal while still granting dogs, and
  `xu ro gerku cu blabi` questions the universal while still granting
  them. Surviving negation and question force is the signature of
  presupposition, not of an at-issue conjunct (a conjoined `∃` would be
  negated and questioned along with the rest), so the import is a
  `Presuppose` on the description quantifier's restrictor. The
  non-importing reading is not lost: bare logic's `ro da` maps to plain
  `∀` with no presupposition, so mathematical discourse pays nothing.
  Cost: universal claims over empty restrictors are presupposition
  failures rather than vacuous truths — the standard
  natural-language trade.
- **P9 (`kau` exhaustivity is absent).** Three candidates fought:
  default-exhaustive (adds a claim CLL never makes), a `Vague`
  exhaustivity parameter (posits a decision point that *no Lojban
  expression can settle* — an idle wheel: vagueness machinery is owed
  where the language could precisify, and `kau` has no such route), and
  absence. Absence won, with its consequence stated plainly: unmarked
  answerhood has the weakest (mention-some-compatible) truth conditions,
  and stronger readings come from the embedding predicate's lexical
  presuppositions or explicit markers. The parallel with tenselessness
  and distributivity is exact, and deliberate.
- **P10 (`le`).** The two supports for a dedicated description
  relation fell (§2.6), guskant's expansion supplied the
  precedent, and the anchoring clause answered act-vs-identification:
  `le` lowers through `skicu` with the describing event anchored to
  this utterance's locution — performative, true by construction.
  `voi` = audience-deleted `skicu`.
- **P11 (`Generic`).** See §1.9; the fixed-prototype design died on the
  split-normality witness.
- **P16 (KOhA keyed).** `ko'a du ko'a` must be true; per-site contextual
  holes would let the two sites diverge. One retrieval per key.
- **P17 (termsets, no maximality).** CLL ch. 16 §7 (its examples
  16.42–16.45, print numbering) glosses `ci gerku ce'e re nanmu cu
  batci` as: two picked groups, "every one of the dogs bites each of the
  men" — full product — and stops. The coordinate-closure strengthening
  ("and no other dog bites them") makes the sentence false in situations
  speakers plainly use it for, so it is a named optional profile, not
  the default. The bare-PA half is pinned *against* the letter of CLL
  ch. 16 §6, whose account of bare numeric quantification is global
  ("exactly two things, no more or less" — Example 16.34) and
  distributive (`PA broda` as `PA da poi broda`): this specification
  takes neutral witness-set
  exactness — the xorlo-era reading, the one consistent with termset
  composition and witness export — and keeps the CLL-literal global
  reading as
  the named `GlobalExactly`. The divergence is documented, not
  smuggled — and it carries a positive compositional argument:
  witness-set semantics is what composes *directly* with dynamic
  anaphora — the selection's witness is the referent `ri` binds —
  where the global reading exports at best the maximal extension of a
  size claim, making the non-exclusion facts (§4.10's fourth runner)
  and termset composition awkward; and neutrality is what keeps
  collective predicates expressible under quantifiers at all (`su'o
  prenu cu jmaji` — a reading a distributive default cannot state).
  Motivation by composition and coverage, not preference. Independent convergence:
  solpahi's "A Simpler Quantifier Logic" derives the same reading from
  plural logic alone (bare PA = plural-existential over a PA-membered
  witness), and notes the bonus this specification inherits: witness
  existentials commute, so `ci gerku cu batci re remna` and its
  `se`-conversion agree — the scope asymmetry of globally-exact
  quantifiers was an artifact.
- **P8 vs the present-tense temptation.** CLL
  ch. 10 makes tense optional; "untensed = present" is an anglophone
  reflex, not a rule. But pure absence was also wrong, as compatibility
  review showed: CLL 10.1 itself enumerates the readings of
  the tenseless example and says "context resolves which is correct",
  and the Partee-style stove case (a tenseless denial targets one
  contextually relevant occasion) demands a contextually anchored time
  on episodic readings. The amended pin: tenselessness is
  reading-multiple — episodic readings carry a `Context` time facet,
  habitual/gnomic readings carry nothing, and the semantics never
  inserts a default; the choice among readings is upstream, like every
  ambiguity.
- **P12 (implicit `ce'u` at first unfilled place, counting converted
  places)** — subsumes the x1 tradition, matches practice, and declares
  multi-candidate cases distinct readings rather than vagueness.

- **P26 (prenex scope; topic resolution).** The prenex half is
  CLL 16.2 read at face value plus the P18 surface-scope doctrine —
  the losing alternative (scope normalization independent of prenex
  order) contradicts CLL's own donkey examples. The topic half's
  evidence is CLL 19.4's fish (`le finpe zo'u citka` — "the sentence
  doesn't say" whether it eats or is eaten): the vagueness is a
  *place choice*, so an aboutness link beside a closed comment —
  though it might look sufficient — cannot represent it; the
  `TopicResolution<ρ>` union
  makes place-fill the primary arm with `srana`-aboutness (CLL 19.10's
  money topic) as the other. Why not the Tanru link: types don't fit —
  a topic is a referent, not a modifier over the head's
  row. Why no segment-state effect: `ni'o` owns segments, and two
  owners of one state need an adjudication nothing asks for.
- **P27 (imperatives, vocatives, the active addressee).** CLL 2.14
  says `doi` *sets* `do` — binding language, exactly the `goi`
  mechanism — and mutating the ctx `Audience` instead would make
  "addressee of this utterance" ambiguous with "current do-value" and
  retroactively falsify utterance facts. The active-`do` binding with
  Audience fallback also makes `doi djan. ko klama` command John with
  no extra machinery — the objection that pure binding under-serves
  `ko` dissolves once `ko` reads the same active value. Force marks
  the nearest *performed* clause only: `lo nu ko klama` constructs
  content (the alternative — force extrusion from abstractions —
  would make `Reify` perform).
- **P30 (relation variables; templates).** `bu'a` needs second-order
  *quantification*, not second-order *objects*: the core's
  quantifiers are typed, so `∃` at `PredTerm<ρ>` expresses CLL 16.13
  directly, while reified predicate objects (§9.1's reserved family)
  would bring the identity-granularity questions along for nothing —
  no identity claims occur. The prenex constraint is CLL 16.107
  verbatim. `cei` stores more than a relation (CLL 7.5: fills, tense,
  negation ride along, later fills override), so the binding is a
  bridi template at the ⊳ layer — a `PredTerm` value would wrongly
  make `go'i`-style override inexpressible.
- **P32 (one performance).** `.i ja` decides it: a disjunction is one
  claim, not two acts, and uniformity carries the rule to `.i je`
  (harmless there — asserting a conjunction commits to both, and `∧`
  shares `Do`'s accessibility row, §5.4). The losing alternative (two
  acts plus a cross-act connective) has no act to carry `∨` at all.
  `.i joi` stays a discourse `Do` — one act per sentence — because
  mixture forming at the act level was never attested or needed.
- **P33 (tanru-unit jeks).** With a shared head, connecting whole
  units would duplicate the head predication (two houses from one
  `zdani`); binding one `Vague` link per conjunct and connecting the
  link applications keeps one head and distributes classically
  (`H ∧ (l₁ ∨ l₂)` ≡ the unit-level disjunction) while keeping one
  discourse site per referent. Distinct heads have nothing to share,
  so they connect as whole predications.
- **P34 (`vu'o`).** CLL 8.8's own gloss ("both Frank and George are
  claimed to be men") is per-connectee; predicating collectively of
  the `Combine` would change collective predicates' truth conditions,
  and distributing to *members* would over-distribute into plural
  connectees. Immediate-connectee distribution is the only reading
  that preserves both the CLL claim and the connective's structure;
  the restrictive extension is recorded as ours.
- **P35 (ROI).** Conjoining a count onto the ordinary single-event
  closure leaves an uncounted existential event in scope — the count
  must *replace* the closure, over distinct eventualities in the
  interval. The interval default follows CLL 10.9's own words
  ("unspecified size, at least part … in the past"): a recoverable
  anchor (`Context`) with genuinely loose extent (`Vague`).
- **P37 (`ji'i`).** CLL 18.9 distinguishes positions; one uniform
  tolerance would erase the rounding reading (suffix `ji'i` with
  `ma'u`/`ni'u` direction) that CLL states. Both positions denote
  `Vague`-selected Numbers over different regions — tolerance about
  the anchor vs the rounding preimage of the stated numeral (each
  nonempty by VC1) — so the underlying quantity is always the bound
  Number, never an unconstrained "true value".

## 4. What would change our minds

A design-record note first, owed to accuracy: several of this document's
positions were genuinely contested before they settled — the drops of the closure and witness
primitives, the sort-hierarchy trims, the tanru/scalar formers' survival,
`Generic` over fixed typical references, termset non-maximality, and the
`kau` representation among them; this document records the losing
alternatives beside the winners, and one proposed reading (`na'e`
weaker than `¬`) was overruled by primary text (§1.8). One separation *was* found during
the rounds: the dependent-witness sentence `ro prenu cu ponse ci gerku
.i ri tatpi` genuinely separates an embedded quantifier's witness from
any single top-level plural — and was absorbed by generalizing the
export rule to joint-locus normalization, not by refuting the
simplification.

Standing invitations, recorded so future revisions know where to push:
a witness-separating configuration that joint-locus normalization cannot
absorb (narrows §1.6); a facet-joining sentence
where dynamic `∧` mispredicts (revives a dedicated joining operator); a
sentence forcing world variables into terms (moves intension into the
syntax); a genericity theory that derives `Generic` while preserving the
`lo'e`/`le'e` contrast (demotes it to the library); evidence that
speakers systematically read unmarked `kau` exhaustively even in
non-`djuno` frames (reopens P9); community usage data on termset
maximality (reopens P17's default); and a construction where
set-*objecthood* at a lexical place does work that member-wise
predication plus `SetOf` cannot (reopens §2.8 — the hunt found
none; the candidate that fails is `lo selcmi cu simxu`, which the
two-sort typing resolves correctly and uniform set typing renders
ambiguous). Each was hunted during the design
rounds; where the hunts came back empty the invitations record the
negative result, kept falsifiable, and where a find was absorbed (the
dependent witness, above) the invitation is narrowed to what remains.
