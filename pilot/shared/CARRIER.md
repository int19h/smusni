# S7 — Shared carrier specification for the #74 pilot

**Status.** Pilot artifact (`pilot/shared`), written once so that every
candidate platform encodes the *same* carrier natively and reviewers can diff
each encoding against this text. It is not normative: it restates what the
live documents settle, names what they leave open as explicit parameters,
and fixes the probe expectations. Sources: `spec.md` §5.1–§5.5, §7.1, §9.1,
§9.3; `review/MODEL_REPAIR.md` (proposal, v2); issue #11 (decision status);
issue #10; the #74 circle record. Where this file and a live document
disagree, the document wins and the discrepancy is a finding.

## 1. Settled (encode exactly; a candidate that deviates fails the probe)

S1. **Branch-relative outcomes.** A computation run on an evaluation
context and a dynamic state yields a *set* of per-branch outcomes, each
either `Live⟨state, value, trace⟩` or `Undef⟨site, trace⟩` (#11 "branch-
relative representation is accepted"). The projective emissions of
branches extinguished by at-issue filtering must remain **observable at
the handler** (S5); *how* they are carried — MODEL_REPAIR's separate
`spent : Seq<Trace>` channel, a per-result residual, or another
representation — is parameter P3, not settled.

S2. **Non-interpretation is not falsity.** Falsity / failed selection = no
`Live` outcomes and no `Undef`; non-interpretation = an `Undef` outcome. A
result whose only outcomes are `Undef` under `¬` yields `Undef`, never truth
(C4; recovery-test doctrine, consensus 3; #11 work item).

S3. **`Context` resolves to one intended value.** A resolved site with
dependency tuple d̄ has exactly one value per (site, d̄) per performance
(retrieve-once, spec §5.3 :1490–1493); an unresolvable site turns *that
branch* into `Undef⟨site, trace-so-far⟩`. Logical embedding never turns
retrieval into quantification over admissible values (§5.4 `Context` row).

S4. **`Vague` is profile-indexed supervaluation.** The denotation is a
family ⟦·⟧π over precisification profiles (spec §5.1 :1227–1235; C2); a
profile is an *index* of evaluation, never a branch choice and never a
memoized state component.

S5. **Projective commitments survive at-issue falsity.** `Presuppose π b`
emits π's closure (with trigger site and handler scope) into the current
branch's obligations and evaluates b; `Supplement a σ b` likewise.
Emissions combine under P3/P4; the emissions of branches that die on
at-issue grounds remain observable at, and are discharged by, the handler
(§5.5). MODEL_REPAIR's `spent` channel is one profile realizing this.

S6. **Accessibility rows are the escape/visibility statement** (§5.4 table):
`∧`/`Do` sequence left-to-right with both operands' introductions
surviving; `∨`, `¬`, `→`, `↔`, `⊕` are *tests* (the incoming state is
returned; nothing escapes; `→`'s consequent sees the antecedent's
introductions); `∃`/`∀` restrictors are pure and body introductions are
local per instantiation; exporting selections introduce their witness into
the current force segment; `Refer`'s reference-level restrictor may be
effectful (`EFn`) and its introductions survive with the referent unless
`Local` projects them; the member-level lift is pure; `Presuppose`'s
condition introductions are local to the check; sign constructors, `Reify`,
`EventOfContent` are inert.

S7. **Dynamic filtering in conjunction.** In `∧`/`Do` the right operand
runs on each *surviving* `Live` outcome of the left (lexical predication
filters `info` by truth at each world; MODEL_REPAIR §3); the right side
never sees branches the left has extinguished.

S8. **Structured `Content`.** `Content = ⟨run : Comp<Unit>, event :
ClauseEventIntension⟩` (§9.3; consensus 15); `Proposition` is `Content`
quotiented by the joint kernel of `run` and `event` (§9.1; MODEL_REPAIR §2).
`Reify : Content → Proposition` is inert; `Holds : Proposition → Content`
(§9.1) returns the represented *structured* content — its event intension
participates in identity — and evaluating it runs that content at the
`Holds` occurrence with the sites fixed at formation (§5.4 row; spec
:2436–2438).

S9. **`Perform` phasing** (§7.1 :2043–2057, fixed without deciding #11's
policies): create the occurrence with a fresh extensional capture and
associate it with `CurrentToken`; run the captured payload; discharge
presuppositions and commit supplements, including those of extinguished
branches (S5); apply the force update per surviving lineage; return the
opaque `ActOccurrence` handle. Two
executions of one act value are distinct occurrences even with equal
captures. An uninterpretable payload may leave an occurrence without a
defined realized Content. No term inspects the capture.

S10. **Site identity.** Each written occurrence is one site, α-invariant;
sharing through `λ`/`Let` preserves a site; copying text mints new sites
(§4.4 :623–626; §5.3 :1496–1499).

## 2. Parameters (encode as explicit parameters of the carrier; probes run under each named profile)

P1. **Mixed-branch combination policy** for `Undef` alongside `Live` under
`∨`, `→`, quantifiers and force: `strict` (any `Undef` is fatal) |
`truth-dominant` (a `Live` outcome wins) | `per-operator` (a table). (#11.)

P2. **Accommodation policy** for presuppositions at a handler: draft
`outermost-legal-scope`; alternatives named by the encoder. (#11.)

P3. **Trace and extinguished-branch representation**: any representation
under which S5's observable requirement holds (a handler sees the
emissions of extinguished branches, per lineage); MODEL_REPAIR's
`⟨outcomes, spent : Seq<Trace>⟩` is one profile, not the requirement.

P4. **Obligation algebra** `(empty, combine)` over obligations that carry
at least (trigger site, captured environment/lineage, handler scope): **no
idempotence, commutativity or order is assumed**. Profiles to run: `set`
keyed by site/capture/handler (the live `union` reading of spec §5.1
:1226 — this profile *collapses* the two probes below), `seq`/multiset
(MODEL_REPAIR §1: "duplicates are two commitments" — non-collapsing),
`occurrence-keyed set` (a set whose key includes an evaluation-occurrence
identity — non-collapsing). The live text *leans* toward two
commitments from one shared site (§5.5 :1552, :1555) and has a tension
with `union` at :1226 — recorded on #11; **the pilot records outcomes, it
does not choose.**

P5. **Handler policies** for supplement commitment order and for whether a
false or `Undef` host still supplies an occurrence-only continuation for
attached UI/grounding (#11 work items). Draft: commit in trace order;
occurrence survives, realized Content undefined.

## 3. Interface signatures (host-neutral; each candidate gives its native rendering)

```
Model      : worlds W; sorted domains; world-indexed lexical interpretation;
             carrier family Comp<A> closed under every declared operation (Henkin);
             a proposition domain PropDom = Content / ker(run, event) with the
             round-trip laws of §9.1 at the intended equality
EvalContext: ⟨ctx (utterance-context record incl. token), resolve : partial
             (SiteKey × DependencyValues) ⇀ Value, lexicon⟩
State      : ⟨info : P(W × Assignment), frames : segment + suspended stack⟩
Trace      : obligations per P3/P4
Outcome<A> : Live⟨State, A, Trace⟩ | Undef⟨SiteKey, Trace⟩
Result<A>  : P(Outcome<A>) together with the extinguished-branch emissions,
             in the profile's representation (P3)
run        : Comp<A> → EvalContext → State → Result<A>
bind       : Comp<A> → (A → Comp<B>) → Comp<B>      -- per Live outcome; Undef outcomes and
                                                       -- extinguished emissions pass through
Reify      : Content → Proposition ;  Holds : Proposition → Content   (§9.1)
Operations : refer, select* (witness laws), context(site, deps), vague(site) via profile index,
             presuppose, supplement, neg, conj, disj, imp, iff, xor, forall, exists, local,
             stateClause, closeClause, eventOfContent, reify, holds, perform(role, act),
             newTopic, resume
```

## 4. Probe expectations (S3 of the plan; outcome column is what the live text fixes)

| id | probe | expected |
|---|---|---|
| C2 | `Vague` site under negation/quantification | denotation is the profile family; no branch per sharpening; supertruth across admissible profiles (live §5.1; C3's open objection to the supertruth reading is recorded in COUNTEREXAMPLES and is not decided here) |
| C4 | `mi na klama` with an unresolvable destination site | `Undef`, never true |
| C4′ | unresolved `Context` in one disjunct, `Live` in the other | per P1 profile; record each |
| FP | a well-formed *false* at-issue content carrying `Presuppose π` | π observable at the handler through the selected P3/P4 profile |
| DF | `∧` whose left conjunct is false on some branches, right conjunct reads state | right runs only on surviving branches |
| ER | `Refer` with an `EFn` restrictor that introduces | introductions survive with the referent; `Local` around it projects them |
| PO | one act value performed twice under distinct captures | two occurrences; `ActContent` identical; `RealizedContent` per capture |
| OB1 | `Let f = λx. Supplement a σ ⊤ in ∧ (f y) (f y)` | one site; **record count under each P4 profile** (#11) |
| OB2 | `Holds (Reify c)` twice, c emitting a projective | one site; **record count under each P4 profile** (#11) |
| NEG | `¬` over a computation with `Live` outcomes that introduced referents | test; nothing escapes; traces collected |
| DIS | anaphor after `∨` to a disjunct-internal introduction | inaccessible |
| Q | S6 quotient exercise (plan): nontrivial `ker(run,event)`, `Reify`/`Holds` round trips, one lifted operation, one representative-sensitive use | round trips at the intended equality; lifted operation respects the kernel |
| FM | one finite model instance | every probe above executes |

## 5. Encoding rules for candidates

- Use the platform's native higher-kinded interface where it exists (Lean,
  Rocq); Isabelle uses a concrete state carrier or a tagged domain and
  records the encoding cost. Do not port Isabelle's encoding to the others.
- No node ids, caches, registries or evaluator bookkeeping may appear in
  `Content`, obligations, or outcomes.
- Every parameter in §2 is a real parameter of the encoding, not a
  hard-coded choice; the report lists the profile each probe ran under.
- A probe whose expected outcome is "record" is reported as an observation
  against #11, never as a pass.
