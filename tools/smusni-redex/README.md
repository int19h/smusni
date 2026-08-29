# Smusni Redex checker

This directory contains a derived checker for the notation and selected
static laws in `spec.md`. It is not a semantic authority: when the checker and
the documents disagree, the discrepancy must be diagnosed against the live
normative text.

Milestone 1 covers the declaration mirror, exhaustive classification of the
Markdown `lisp` fences in `spec.md` and `samples.md`, the concrete reader,
elaboration, extrinsic typing, and the static regression ledger. Fences in
derivative documents are outside this bounded corpus until a synchronization
milestone explicitly adds them. Dynamic execution, Lojban lowering, finite
model search, and Lean certificates are later milestones.

Run the milestone checks from the repository root:

```sh
tools/check-smusni
```

The fence classifier uses the tracked sidecar
`inventory/fences.sexp`. Every fence is keyed by source file, ordinal, and
content hash; insertion, deletion, or editing therefore makes the check fail
until the classification is reviewed. This avoids changing normative
documents merely to attach checker metadata.

All Racket list delimiters are semantically identical. Special forms are
recognized by their reserved head atoms and positional operands; the reader
does not preserve or validate brace shape. Its sole pre-read lexical step
protects identifier-internal Lojban apostrophes such as `te'a` outside
comments and strings.

`unchecked` is a manifest vocabulary item only for a durably explained gap;
the runner treats every such entry as a failure. It cannot make an in-scope
specimen green by exemption.

The lexical rows in `inventory/fixtures.sexp` are non-normative scaffolding
pending issue #12. The report lists the forms whose first milestone rules are
bounded pass-throughs rather than full signature checks. A normal run permits
only exact hash-bound findings in `expected-findings.sexp`; use
`tools/check-smusni --strict` to fail while any such document debt remains.

`Refer` admits an `EFn` restrictor at the *reference* level (spec §5.3): a
description property may sequence retrieval sites, and the returned referent
is still introduced by `Refer` itself. A *member-level* restrictor
(`Fn (T) Content`) is the §5.3 `CoveredBy` lift and must be pure; an
effectful member-level restrictor is rejected. Both halves are pinned by
static tests and must not be generalized to the pure positions (`SetOf`,
quantifier/Generic restrictors, and the `Select*` family).

Gate 3b enforces those pure positions directly. `SetOf`, all four
`Select*` members, `Generic`, and the §12 GQ family reject an effectful
restrictor with an `L0.1` pure-position diagnostic. The concrete GQs have their
normative signatures rather than pass-through typing: witness forms take a
pure member restrictor and a reference-level nuclear scope, `Every` takes a
member-level nuclear scope, and `GlobalExactly`/`Most` require both operands
to be pure because both run inside `SetOf` comprehensions. Exporting GQs keep
their witness-introduction effect (with the literal-zero `AtLeast`/`Exactly`
exceptions); `AtLeast 0` is effect-free `⊤` and does not evaluate its nuclear
scope, whereas `Exactly 0 = No` still does. `Card` and its
`GlobalExactly`/`Most` consumers carry the projective finite-set definedness
obligation.

## Checker fidelity follow-ups (#13)

- `Mention` constructs `Act<Expressive>` and is rejected where an assertion
  act is required; displaying a value never supplies assertion force.
- Sign constructors return their §7.5 kind (`Opaque`, `Structured`, `Name`,
  `Sentence`, `Letteral`, or `Word`) instead of collapsing quotation and word
  signs to `Sign<Sentence>`.
- `components_κ` accepts exactly one `Group<T>` object and records the
  complete-cover definedness obligation; plural group references require an
  explicit sole-group projection before crossing.
- `Fn`/`EFn` parameters are contravariant and results covariant. The §7.4/§7.5
  `Utterance`/`Sign` entry spellings keep their token-sort binder annotations,
  but their dedicated rules bind and return the singleton-lifted token-reference
  properties. The implemented `Assert`, `Express`, `Ask`, and `Mention`
  constructors suspend their payload effects, so described acts remain inert
  while a direct effect in an entry fact is still rejected; no general
  parameter-position lift is used for that notation. `SentenceSign` likewise
  stages its Content operand inertly.

The `le` description form `SpeakerDescribes` (#41 item 1) is typed by its §12
signature — described reference (member or plural) and a unary description
property — and is pure; `LocutionOf` and the `CurrentToken` constant carry the
sorts its definition needs; `SpeakerDescribesUnaddressed` (`voi`, #49) shares the
rule with the audience place deleted. `type-compatible?` places the §3.1 collection and
sign object sorts (`Set`, `Group`, `List`, `Sign`, `SignToken`) under `Entity`.

## Model-bank profiles

The model bank prints decision status before every verdict:

- `live-baseline` tests laws already present in the tracked specification;
- `human-adopted-pending-sync` tests an adopted decision not yet fully
  synchronized;
- `reviewer-consensus` tests a peer-settled proposal still awaiting the
  human/adoption or baseline edit recorded by its issue;
- `comparative` tests a still-live alternative profile without treating it
  as either baseline or rejected;
- `rejected-alternative` is expected to reject its discriminating model.

A green result in any non-baseline profile is evidence about that encoding,
never ratification. Named regressions are deterministic. Bounded searches
print the exact signature size and structure count. The divisible-bread
compatibility case uses a symbolic dyadic-interval splitter because a finite
atomless semilattice cannot exist; finite searches are never described as
atomless.

Generated files under `corpus/` are checked in for review. Regenerate them
with:

```sh
racket tools/smusni-redex/extract.rkt --write
```

Do not hand-edit generated corpus files.


## Lowering-rule citations (#9 M1)

`spec.md` §11 numbers every schema `Ln.m` and marks the kind of each: an
unmarked rule is a lowering judgment (the F₀ population); *(gap)*, *(note)*,
and *(reading)* rules are documented no-mappings, explanatory consequences,
and resolved-reading decisions, never citable and never ledgered. The checker
reads ids and kinds from the normative text, never from a copy. Specimens
carry an `(origin "surface"|"core")` clause: a surface specimen lowers
Lojban and must cite the judgments it instantiates as its focal claims (not
every rule its sub-terms touch); a core fixture is a typed term authored
directly in the core and cites nothing. Each specimen entry in
`inventory/fences.sexp` carries a `(rules …)` clause naming the rules it
instantiates, and `inventory/rule-coverage.sexp` ledgers every rule no
specimen cites yet, each with the issue that owns the gap. The run fails on a
specimen without citations, a citation of an unknown id, a rule that is
neither cited nor ledgered, or a ledger entry for a rule that a specimen does
cite. The ledger also carries a **ratchet** `(cited-floor N)`: the number of
rules cited by specimens may never fall below it, and a commit that raises
coverage must raise the floor, so ledgering a rule instead of writing its
specimen is a failing move and any lowered floor is a visible diff. Citing a
rule is a claim about the specimen; it is not checked semantically until #9
M3.

## Executable lowering (#9 M3)

M3 adds a derived lowering gate for live L1, L3, and L5 plus the L0.1 premise
(47 lowering judgments after L5.30; fixtures are explicitly not exhaustive).
`inventory/lowering.sexp` identifies candidate fence keys, while one tracked
`gentufa` JSON fixture and one eight-field `RR` S-expression fixture per fence
preserve ordered cases. The same refresh maintains offline gentufa fixtures for
structural-classifier and in-place-argument regressions, so the ordinary check
remains independent of a local jbotci installation. Refresh parser fixtures
deliberately with:

```sh
racket tools/smusni-redex/lower.rkt --refresh-parses
```

The ordinary check never invokes jbotci. It attempts each candidate case as a
whole term, type-checks every produced core term, symmetrically normalizes only
the documented Close, omitted-place, force-boundary, and L0.1 display
conventions, and compares modulo α-renaming. Reports distinguish matched,
mismatch, unresolved, out-of-fragment, and in-fragment `no-lowering` results.
Missing RR fields and implementation failures fail the gate; missing rows are
report-only unless the manifest promises them; under-specified rules remain
visible #9 findings. Per-case dispositions are authoritative, and a documented
precedence produces the stable fence summary. Formed-rule coverage is printed
separately from M1's focal-citation ratchet.

The parse-to-source adapter recursively inspects tagged gentufa constructs
(`BridiStatement`, bridi/selbri/term nodes, descriptors, quantifiers,
connections, termsets, and LAhE) and treats terminal lexemes as data. It never
dispatches on a whole surface-token sentence. Each handled construct accounts
for all of its direct semantic terminals and terms; an unsupported child makes
the case `no-lowering` instead of disappearing. Familiar descendants are
accepted only through recognized transparent gentufa wrapper paths, so an
unknown parent construct cannot disappear while its terminals survive. Before
building σ, the adapter compares every active parsed modifier with the set the
selected view consumes; leftover counts, tanru, conversion, scalar/negation,
labels, or deletions refuse the case. Ordinary fills first form a labelled
place map, and conversion routes those labels to the base row before
application; each `zi'o` remains a distinct `DropPlace` deletion.
The same path certificate covers lexical selbri units, JOI/termset and
sentence connectives, root statements, and fragments; special handlers do not
bypass it through recursive descendant search. Every accepted semantic node
recursively invokes the same decoder for semantic children: descriptors and
quantifiers decode their child selbri, connectives decode their operands, and
only a leaf rule reads a terminal payload.

RR force, readings, selected rows, and site kind/order/dependencies are
validated exactly for the selected rule path. A nonempty RR field with no M3
consumer is rejected rather than ignored. Candidate-visible semantic gaps are
reported only after that exact validation, so malformed RR remains a failing
`rr-missing` result rather than a non-failing unsupported-rule report. Mutation
regressions require tree structure changes to block lowering, exercise unseen
lexical and place combinations, and require every RR change to alter or reject
output. Deterministic sweeps rename and delete every internal key occurrence in
all fixture parses; a rename must refuse, while deletion must refuse or change
the source view except for explicitly listed syntactic no-ops. Attempt and
failure counts are printed. The report
prints the number of eligible cases for which the gentufa/RR translation
actually formed a Redex source view.

M4's marked-global branch reads `global-exact` only from `RR.readings`. It
derives the omitted sites of both restrictor and nuclear rows from their
selected fixture rows, using role-qualified identities so equal operand rows
remain distinct. It requires an exact `RR.sites` set, rejects duplicate or
unknown sites/dependencies, explicit member dependencies, ambiguous bare
variables, and dependency cycles, then topologically orders the declarations
with source order as the tie-break. Explicit `(outer $var)` dependencies are
recognized separately and report an honest unsupported environment-threading
gap. L0.1 constructs fresh sequential `Bind`s and pure properties; L5.2
constructs the `GlobalExactly` head. The symmetric normalizer expands that
explicit §12 head one way and records the definition name. `Most` expansion is
deferred: its normative `>` primitive is not yet present in the checker
inventory/type judgment, so expanding it would not be type-preserving.

The executable rules are the `(I I O)` Redex judgment `m3-lower`; its named
clauses are live §11 ids, and formed attribution is read from
`build-derivations`, never a manual counter. The display normalizer is a Redex
metafunction applied to both sides, and `SmusniCore` declares canonical
binding forms for λ, `Let`, and sequential `Bind` so comparison uses Redex
`alpha-equivalent?`. Matching additionally requires a binding-sensitive
retrieval-site certificate: site traversal order, `Context`/`Vague` kind, and
the enclosing binders on which each computation depends must be in bijection.
The manifest driver deterministically enumerates and type-checks every fixture
derivation; it is not labelled `redex-check`.
`redex-check` is reserved for the bounded `#:satisfying` generator. This Redex
version rejects generation for the judgment's ellipsis patterns, so the report
records seed/attempts/size as unavailable and labels coverage fixture-only
rather than describing it as randomized testing.

### Non-gating corpus probe (#56 M4 increment 2)

Run `racket tools/smusni-redex/lower.rkt --probe-all` to inspect every surface
specimen with the installed jbotci version. Existing tracked parse/RR fixtures
are labelled `verified`. Every other case is parsed live and receives a
generated eight-field skeleton labelled `unverified-skeleton`; such a result is
discovery-only and is never reported as a match or accepted as promotion
evidence. The command writes no fixture and is not part of `tools/check-smusni`.

The report prints every case, the first refusal where applicable, verified vs
skeleton totals, parse-error count and keys, formed coverage before/after the
increment, promoted verified candidates, and the exhaustive disposition of the
17 starting rule IDs. A parse error is never absence evidence: while any remain,
every no-lead disposition is explicitly limited to parsed cases. Only the live
gentufa call is inside the parse-error boundary; skeleton construction,
lowering, classification, and normalized comparison failures abort the probe.

Rule leads come from parse constructs and grammatical loci; focal citations are
printed only as a cross-check. Every detector excludes quoted ancestry, and an
L5.23 chain requires repeated `joi` nodes in one list container or `se` inside
the same `JoiConnective`; unrelated statements cannot combine into a lead. JOI and
JEK attribution uses the nearest recognized grammatical locus, `.i TAG bo`
inspects only the direct I-tail connective and requires a tag before grouping
`bo`, and L3.10 inspects only the matched description tail's direct quantifier.
The lowering gate compares classifier
leads with derivation rules on every verified fixture parse and reports the
consistency count. Direct classifier tests supply a minimal positive parse for
every starting rule and exercise wrong-locus and quoted-material negatives. M4
increment 2 promotes only specimens with reviewed eight-field RR:
samples #27 (L5.22 constitution-bearing `joi`) and #45 (L3.10 explicit inner
zero). The latter consumes the parsed `no` quantifier itself; question-answer
substitution is explanatory context, not an RR reading or fixture shortcut.

### Place-agnostic argument composition (#56 M4 increment 3)

Descriptions, names, witness-set PA, universal PA, thresholds, and inner PA are
decoded independently of place. The adapter allocates a fresh placeholder for
each computation in parser/source order, sends those placeholders through the
ordinary positional/FA/conversion place map, and then wraps the placed clause
with the same L3/L5 Redex source used by the former sole-term path. It never
selects a handler by place or specimen key. Inner PA reaches its selection
through an L3.9 subderivation; it is not copied into the adapter.

L5.30 is a named Redex pass-through over the driver-ordered source assembled
by the structural adapter; the clause itself does not reorder computations.
The driver applies the P41 partition after placement. Descriptions, names, and
nonzero inner PA wrap at clause level in source order, outside every in-situ
quantifier. Quantified sumti then nest in their own surface order, leftmost
outermost: direct witness selections use the §12 `Exactly`/`Some` content forms,
while `Every`, inner `No`, thresholds, and marked `GlobalExactly` take the
placed body abstracted at their argument position. Termsets stay on L5.3.
Force is introduced once at the first Content-forming quantifier; this includes
a sole `su'o`, whose completed `Some` is wrapped by sentence-level `Assert` or
`Mention` while a Content consumer receives bare `Some`. The sole-term marked
global path has the same category boundary: force-free `GlobalExactly` for
Content, and force outside the completed term for a sentence. Selection and
threshold effects remain in their defined positions rather than being copied
by the adapter.

Exact combined RR validation precedes composition. Marked global readings
derive role-qualified omitted-site identities from both the restrictor and the
routed nuclear row; their Context computations are hoisted outside the pure
`GlobalExactly` operands. When a surface-outer global quantifier would contain
a later referent-introducing quantifier, §12 defines that global reading as
absent: after the complete combined RR profile validates, the report uses the
non-failing `no-reading` cause. Malformed or incomplete profiles remain failing
`rr-missing` results; `no-reading` is never a validation bypass or a semantic
gap. The gate promotes samples #71 and #72 as verified L5.30 cases and keeps
the generated in-place fixture free of RR or expected-output data.

## Redex port Phase 0 instruments (#52)

`port-phase0.rkt` adds migration instruments without changing semantic
behavior. `inventory/definitions.sexp` classifies the live definition heads
extracted from `spec.md`; the denominator is the extracted head/section set,
not a recorded glyph count. Normative status is separate from migration state:
`none`, `legacy-hybrid`, `a0`, or `ported`. `GlobalExactly` and `Close` name
their existing hybrid implementations without satisfying the target-port
gate; 76 written definitions are normatively executable while the target has
zero ported cases. A new head, removed head, stale branch, or an `a0`/`ported`
entry without real named metafunction/relation cases fails. Target cases are
structurally wrapped around their actual Redex clauses and keyed by production
module plus binding. Target modules must first enter the tracked production
module allowlist; comments, test-only definitions, and same-name bindings
in another module cannot satisfy the gate. Nested test submodules and duplicate
case ids/binding registrations are rejected. Legacy-hybrid bindings are
likewise resolved structurally in their named production module. The report prints
every blocked and non-mechanical entry, including `Most` under #66 and the
split equal/unequal `ZipWith` domains under #52/#41.

`inventory/infer-core-branches.sexp` classifies the top-level dispatch of the
legacy inference engine by function, syntax-derived stable id, source pattern,
exact live source range, and source digest. A call-graph check requires every
top-level helper reachable from `infer-core` to be registered (91 inference
handlers plus 34 non-`infer-` helpers). Twenty-three internal `cond`/`match`/
`if` arms in the formerly whole-function handlers are classified separately,
including all 13 `infer-bind` arms. Digests make changes to nested handler logic
stale even when line counts do not move. Metadata refresh refuses a changed
branch/helper/decision denominator; new handlers must be classified first.
The partition is substantive rather than blanket: 21 helpers and 16 internal
decisions are semantic mechanisms that determine types/effects/obligations,
12 helpers and 6 decisions are syntactic/control auxiliaries, and one of each
is an external diagnostic path, with a mechanism-specific reason per entry.
The adjacent diagnostic taxonomy permits term/constructor/location,
inventory declarations, no-derivation, and explicitly non-authoritative
instrumentation as evidence. It forbids a semantic fallback or a duplicate
typing-premise evaluator in the future explainer.

The frozen differential corpus contains deduplicated terms and environments
observed from every classified fence and from executing every pre-port semantic
checker test, including lowering mutations. The Phase 0 instrument's own
self-test is excluded to avoid making the frozen input recursively depend on
the oracle that reads it. Test/spec digests make the corpus stale when those
sources change. In Phase 0 the “new” side intentionally calls the old engine
again. Adversarial self-tests mutate type, effects, obligations, failure class,
source rule, gap status, derivation count, and waiver scope so the gate is not
merely a reflexivity check. Zero unwaived live differences proves the oracle
plumbing without claiming that the port exists. `port-waivers.sexp` is empty;
any later disagreement must name its case, exact allowed fields, and durable
finding. Used waivers are tracked by their full identity, so two field-scoped
waivers for one case cannot hide an unused entry. Every replay case's recorded
inventory digests must match the live inventory or the corpus requires a
deliberate refresh.

The tracked Phase 0 baseline replays all 96 specimen-term occurrences and
records the exact pre-port head, corpus digest, full-gate measurement, and the
pre-registered #52 triggers. Once A0 exists, current old/new/side-by-side modes
instead use the same explicitly reported A0-eligible specimen denominator;
old calls `legacy-record`, new calls `a0-port-record`, and side calls both.
Timing starts after load/warmup, and each mode runs in a fresh child process so
peak RSS is not inherited from an earlier mode. Factor/RSS triggers compare the
current old and A0 modes on that common denominator; the historical baseline
continues to anchor the full-gate trigger. Trigger evaluation is report-only
until Phase B.

Regenerate the two mechanical artifacts deliberately after reviewing their
source changes:

```sh
racket tools/smusni-redex/port-phase0.rkt --refresh-branches
racket tools/smusni-redex/port-phase0.rkt --refresh-corpus
racket tools/smusni-redex/port-phase0.rkt --refresh-baseline --full-gate-ms N
```

## Redex port A0 vertical slice (#52)

`port-a0.rkt` is the typed feasibility slice, not a replacement for the full
checker. `SmusniA0` has a closed type/term grammar for direct `Let`/`Bind`,
`Exactly` (including zero), `GlobalExactly`, `TooMany`, `Massify`, equal-length
`ZipWith`, explicit-row `Close`, and L0.1. It contains no `[τ any]`; generic
application remains an object-language form whose admissibility is decided by
the typing judgment.

Seven definition ledger entries are `port-state a0`. Each structural
`definition-case` is the general equation over its parameters, not an output
table: Let beta; Exactly zero/positive; one GlobalExactly comprehension;
TooMany's ordered purpose/threshold bindings; Massify's canonical selection;
ZipWith's empty/paired recursion; and all three §4.6 Close equations—holding,
implicit direct event, and explicit/shared event—over an explicit
`(row predicate arity event-mode labels)` supplied by the adapter. Explicit
event fills are labeled separately from ordinary places; omitted ordinary
places are bound outside the event abstraction, and the shared-event equation
uses `CoRef` plus `DirectClause` rather than manufacturing a second event. Unequal
ZipWith remains `blocked:#41`, and Most remains `blocked:#66`. The typing rule
still accepts two `List` operands of unequal length because length equality is
not a type property; only the executable expansion has no unequal equation.
Every A0 entry pins the full normative source ranges and their digest; edits anywhere in a
multi-line definition invalidate the ledger.

The two public modes, `a0-synth` and `a0-check`, wrap one recursive Redex
judgment returning a correlated `(typing τ effects obligations)` record.
Expected-type forms (`Context`, `Vague`, selections, `Refer`, `Massify`) use the
checking direction; direct binders, pure/effectful application, quantifiers,
clause closure, reference and performance Bind, and definition forms use named
clauses. `Let` accepts inert syntactic values only; computation expressions and
evaluated applications belong under `Bind`, while a variable already denoting
a computation can itself be aliased without running it. `ZipWith` likewise
takes its function parameter as a syntactic value, so the literal empty case
cannot inherit effects from an expression that computes `f`. The selection floor rejects
`SelectExactly 0`; equality is limited to first-order/discrete-index types;
reference-level `Refer` accepts `Fn` or `EFn` while its member-level lift stays
pure. A malformed `CloseWith` has no derivation instead of escaping as a host
exception. The A0 old/new oracle uses a structural bank-membership classifier
that is independent of whether the new judgment derives a result. It selects
all 31 eligible terms from the retained 337-case fence/test/mutation corpus,
then adds 11 general mechanism probes. The 42 cases have zero unwaived
differences. Ten narrow, tracked waivers remain visible: two legacy `ZipWith`
pass-throughs omit the effect of applying an effectful function, and seven
negative pure-position mutations differ only because A0 deliberately reports
`no-derivation` while the Phase B explainer does not yet reproduce the legacy
failure class. The tenth records the legacy checker's crash on literal empty
lists against A0's record-preserving empty equation. The Phase 0 identity corpus
itself still has zero waivers.

L0.1 consumes `(sites (site id role type pure (deps ...)) ...)` with namespaced
`(site id)`, `(outer variable type)`, and `(member)` dependencies. It detects
introductions from the scoped input term (the full selection family and
`Refer`, including nesting under Let/lambda/Bind), skips quotation/syntax,
captures a well-typed outer variable, orders site dependencies canonically,
audits every free `$` variable in a site role against the member binders, Γ,
and declared dependency namespace, and distinguishes `member-dependent`,
`introduction`, and `malformed-metadata`. The six bank profiles include independent commutation,
one site edge, outer capture, member refusal, direct introduction, and nested
introduction; positive quotation controls are separate. Material outside the
supplied pure-position term is unavailable to the metafunction by construction;
the caller-scope control documents that interface boundary.

A0 derivation coverage has 55/55 required names and an empty dead-clause
report. An adjacent 55-entry table maps every rule name to its live spec
section(s), and every coverage probe plus every differential success must have
exactly one proof derivation rather than merely one deduplicated result. Native
metafunction coverage exercises all 15 definition/L0.1 cases.
The measured raw generator (seed 520, size 8, 500 attempts) produced 34
well-typed terms: 93.2% discard, roughly 79 cases/minute in the latest standalone
run, one compound constructor, seven rule names, and binder depth one. It is therefore reported
`fixture/enumeration-only`; A0 does not claim useful whole-language random
properties.

At A0 the ordinary benchmark denominator was four eligible specimen terms
out of the historical 96. Five warm runs measure the legacy engine, A0 engine,
and true side-by-side execution separately. The report also gives the top five
A0 proof rules by inclusive attributed term time; this is clause-level hotspot
evidence, not exclusive profiler time.

The formerly unavailable size-growth trigger now runs against the closed A0
judgment. It times first derivations for distinct nested-`Let` terms at depths
16, 32, and 64, using a median of three trials per depth after structurally
matched warmups. The current run is a report-only trigger: about 35 ms, 191 ms,
and 1,053 ms, or 5.4× and 5.5× for the two doublings, both above the pre-registered
4× threshold. This is redesign evidence for Phase B, not a green performance
claim.

Hand-authored data on the A0 path is limited and tracked: the eleven mechanism
probes, six L0.1 profile environments, definition-source ranges, and the ten
field-scoped differential waivers. The remaining differential population is
computed from the frozen corpus; row declarations and lexical function types
are derived from the live checker inventory rather than keyed by fixture text.

## Redex port B1 quantifier/selection family (#52)

B1 begins with the pre-registered growth trigger rather than hiding it behind
new clauses. On the same inert-value nested-`Let` profile at depths 16/32/64,
the merged A0 judgment took 39.470/203.902/1116.855 ms. Host compatibility and
record canonicalization together account for less than 0.01 ms at depth 64;
`Check-Synth` and `env-lookup` are not used by the trigger term. Shadow
judgments show that a constant environment still scales nearly quadratically,
while growing the environment adds a secondary cost. B1 removes whole-list
environment splits from every binder rule and makes lookup one host association
search; the immediate after-local profile is 34.012/184.243/919.325 ms, a
17.7% depth-64 improvement, but both doubling ratios remain above 4×. The
tracked profile records the premise counts, microbenchmarks, shadow controls,
and the remaining plan: repeated Redex full-subterm/cache-key matching needs a
larger representation redesign before later family growth. The trigger remains
visible and report-only as briefed. With all B1 clauses loaded, the exact full
run reports 48.111/260.418/1363.879 ms (5.413×/5.237×), so family growth has not
made the unresolved architecture disappear.

The closed grammar and judgment add the exhaustive B1 family: `AtLeast`
(separate zero, provably-positive, and symbolic typing cases), `Some`, `Every`, `No`, `AtMost`, `MoreThan`,
`FewerThan`, `Distrib`, `MaxRefer`, `SelectSome`, `CoveredBy`, and `Overlap`,
plus the required selection/logical/presupposition primitives. Primitive `+`
is the v1.4 support exception: schematic `n+1` is represented as `(+ n 1)`,
and `Natural + Natural` remains `Natural`. The primitive selection floor accepts
a positive literal or a typed successor in either orientation; a bare Natural
variable proves no positivity for `SelectAtLeast`. Defined `AtLeast` itself is
total at every Natural, including a symbolic variable, with positive-branch
effects as a static upper bound. Obligations contributed by the restrictor or
nuclear scope are not upper bounds: the symbolic typing record guards each as
`(when-positive n obligation)`, because the zero instantiation reduces to `⊤`
and contributes none. Its two-equation metafunction cannot choose a
zero/positive reduction before substitution; the ledger records that executable
limitation without calling the term ill typed.

`Presuppose` emits `projective` and a structured obligation containing the
alpha-normalized condition and body computation category. Obligation union is
set-like modulo alpha, including variables bound outside the condition by a
surrounding lambda, `Let`, or `Bind`. The complete obligation set is normalized
under one synthetic binder so one source variable has one canonical identity
across every obligation, even when a genuine free variable reserves a generated
alpha name. The expected-mode Presuppose rule follows nested wrappers only to
an ultimately expected-only reference computation, so a synthable body has
exactly the ordinary `Check-Synth` proof. Generic negation removes only escaping
`refer`, retaining context, projective, effectful-call, performance, and all
obligations. Direct GQ rules are record-equal to their executable expansions:
the exporting forms add `refer`; zero/non-exporting forms do not; `Every`
inherits MaxRefer's projective inhabitedness obligation; and every selection
restrictor is a pure member property.

The definition ledger now has 12 B1 `ported` entries and 18 reviewed equation
ranges total. A parsed-definiens gate reads each RHS with the notation reader,
normalizes source `n+1` to semantic head `+`, excludes LHS/types/prose, and
symmetrically compares dependencies over the full registered semantic-head
universe. Sixty-seven entries remain explicitly `unranged`; none is silently
passed. Four previously ranged A0 dependency lists changed under the declared
rule. A separate migration manifest maps 22 legacy semantic sources to 30
named target rules (14 full, 8 partial) without changing Phase 0 source classes.
Its expected helper sources are derived from live semantic-helper reachability
starting at the selected B1 branches, with shared A0 foundations explicitly
excluded. A live call-site scan rejects `full` whenever an out-of-B1 semantic
branch still invokes that helper.

All 32 deterministic lowering outputs have tracked dispositions: seven select
maximal B1-closed subterms with captured binder environments, paths, fence/rule
provenance and stable ids; 25 contain no B1 family head; none is
unrepresentable. Quote and Syntax are opaque to both head classification and
tree traversal, so semantic-looking quoted data cannot become a replayed
subterm. Those seven join the structural differential automatically.
The current oracle runs 48 eligible frozen cases, 29 general mechanism probes,
and seven lowering subterms: 84 total, zero unwaived differences, 29 used
field-scoped waivers, zero stale. Coverage is 78/78 derivation rules and
anchors, with 28/28 native definition/L0.1 cases and an empty dead-clause
report. Raw generation remains honestly `fixture/enumeration-only`.
The final measurement is 21/500 well-typed terms (95.8% discard), 168.0
cases/minute, zero compound constructors, six witnessed rules, and binder depth
zero.

The current ordinary benchmark uses five B1-eligible specimen terms out of the
historical 96. Five isolated warm runs call the actual named engines: legacy
34.218 ms / 25 derivations, B1 9.713 ms / 25, and true side-by-side 47.756 ms /
50 in the latest standalone gate; deterministic inclusive rule hotspots are
printed. Every ordinary trigger remains clear. Neither legacy lowering hybrid
is retired in B1.
