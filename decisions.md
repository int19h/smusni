# Current decisions and remaining work

This ledger summarizes adopted rules, bounded coverage, and remaining work.
`spec.md` is normative. Earlier review queues and reports preserve design
history but do not determine current status. GitHub
[#20](https://github.com/int19h/smusni/issues/20) and
[#87](https://github.com/int19h/smusni/issues/87) track the corresponding
synchronization work.

Lean and Redex remain derived artifacts until the charter's three-stage
authority transfer. An adopted semantic contract, its implementation, and
a model satisfying it are distinct results. The ledger records all three
where available.

## Settled distinctions

- F01 provides bounded source-preserving assertion formation and laws in
  spec §7.1.1/L8.13. One description source supplies the first assertion and
  a reusable later read. An obtained reference is shared; an absent later
  value gives U rather than a new existence claim. Terminal assertions retain
  eligible prefixes and reached sides and return their occurrence after
  F or U. The combined carrier/quotient embedding, failed-source replay
  coordinates, event definedness, multiple failures, and excluded
  forces/guards remain incomplete.
  [Design review closure](https://github.com/int19h/smusni/issues/9#issuecomment-5625843464).
- P45 permits a reference introduced and consumed wholly within a negative
  Content test without that introduction making the enclosing function
  impure. All other effects and obligation records remain; `Local` and
  other connectives are unchanged. This is a specific rule, not a theorem
  that every non-exporting computation is pure. The human confirmed it on
  September 11, 2026, retaining the earlier PR46/#13/B1 behavior.
  [Approval](https://github.com/int19h/smusni/issues/74#issuecomment-5630303444);
  rationale §2.11 and spec References record the rejected alternative.
- P44 makes bare `me'i` default to `ro`. Its ordinary individual
  meaning is not-all, expressed by negated `IndividualEvery`. Explicit
  bounds are unchanged; `me'i pa` means zero. No positive-satisfier
  requirement, new reference export, or infinite-cardinality comparison
  follows. This human-adopted BPFK-aligned rule departs from CLL v1.1's
  general omitted-`pa` convention.
- P43 adopts conservative accessibility over a plural-capable core.
  Ordinary existential continuity, independently bound references, open
  answer slots, and supported in-scope dependencies remain. Quantification
  does not automatically export numerical or universal groups or dependent
  families beyond their scopes. Static accessibility does not depend on
  computing actual truth. Rationale §1.6a compares P42's rejected recovery
  policy with this rule and states its compatibility cost. General source/force
  construction beyond F01 remains incomplete.
- Q02.a–b uses global exactness for ordinary finite individual counts.
  Exact n counts all P-and-Q qualifiers in the fixed resolved domain:
  a fourth qualifying dog makes `ci gerku cu sipna` false. The September 7
  agreement was confirmed by the human's September 10 application instruction.
  Spec §4.10 states finite exact and range rules. Plural helpers and P17's
  provisional termset policy do not fill missing individual-count mappings.
  Other numerical domains, effects, and termset interactions remain work.
- Q03/P2 makes bare and restricted individual `ro` non-importing:
  universals are true on empty restrictions. Explicit descriptions retain
  their reference requirements. Importing `Every` and `MaxRefer` remain
  library forms, not the ordinary bare-`ro` mapping.
- Ordinary `su'o` quantifies over individuals. At least one satisfier is
  not exactly one, and reference export is a separate question.
  `Some`/`SelectSome` are counted plural helpers, not ordinary `su'o`.
  The SUHO-v2 recommendation met the human's conditional criterion and was
  applied under the September 7 synchronization authorization.
- P41 permits Skolem-like dependencies for `lo`. Invariant descriptions
  are a special case. A dependent description remains referential and must
  be bound within the scope of its dependencies; it does not become an
  existential quantifier. The September 7 clarification and synchronization
  instruction establish this decision.
- C25 preserves description bindings under `na`. An empty reference source
  fails at its actual scope; negation does not reselect its referents.
  The human adopted this behavior on September 6.
- `lo ro` and `lo su'o` can supply collective arguments but do not
  replace plural universal or existential quantification under arbitrary
  embeddings. The gathering examples also depend on `jmaji`'s lexical
  singleton, location, and episode readings.
- A first-order lift need not be an Among-atom. Nonempty reference does not
  imply positive counted units; atomlessness alone does not imply zero units.
- Existing display/force machinery can express a discursive relation without
  deciding its truth during translation. Candidate gismu and model graphs
  do not, by themselves, supply complete core definitions.

Source status remains explicit. Solpahi's plural PA analysis proposes a
reform; the earlier presuppositional `ro` wording was project-authored;
and the first P41 invariance argument misread guskant. These facts belong
to the decision history and cannot independently ratify the current rules.

## Derived artifact status

The following merged results do not transfer semantic authority:

- [PR92](https://github.com/int19h/smusni/pull/92) aligns the Lean pilot with
  E01 and implements the adopted P45 negation-purity rule.
- [PR91](https://github.com/int19h/smusni/pull/91) structurally encodes F01's
  source-preserving assertion construction.
- [PR93](https://github.com/int19h/smusni/pull/93) adds bounded auxiliary F02
  ground-model proofs and a safety audit.

These results do not establish the full carrier, event, Proposition,
quotient, general source/force, or surface-coverage model. That work remains
separate from the current documentation rewrite.

## Agreed directions and remaining application/coverage work

The completed round's remaining compatibility disagreement, Q03, is resolved.
The table distinguishes adopted behavior from missing formation rules, model
constructions, lexical definitions, and surface mappings. An unfinished
construction is not necessarily an unresolved semantic choice.

| ID | Settled extent | What remains | Tracker |
|---|---|---|---|
| Q01 | Individual `su'o`; ordinary existential/independent-reference continuity; P43 conservative barriers; in-scope P6 retained; bounded F01 one-description assertion continuation | Full F01 carrier embedding; general source/force/capture, PA+KOhA/fragment/other-force mapping, permitted dependencies and experimental plural interfaces; not restoration of P42 group export | #9, #17, #36, #90 |
| Q02 | Standard finite individual exact/range counting; exact three is false with four qualifiers; termset product is separate | Other numeric domains/effects, mixed termsets and coordinate policies; non-finite/definedness and generic outer-PA realization remain bounded work | #15, #87 |
| Q03 | Non-importing bare/restricted individual ro; independently bound explicit descriptions retain their own reference requirements | General source/effect and experimental-profile interfaces; not a renewed import vote | #15, #35 |
| Q04 | Fixed and dependent `lo` legitimate; binding respects dependencies; lambdas provide suspension, not an implemented delayed consumer | General dependency-profile factoring, pure-restrictor dependent description evaluation, typed de-dicto consumer/world/export interface | #62, #87 |
| Q05 | Continuation about the same scenario referent; no automatic actual-world witness or arbitrary replacement | Typed scenario/dependency/identity and supported return-to-actuality routes; evidence alone selects no unique carrier | #17, #87 |
| Q06 | Resolved occasions; direct-event and explicit state-verification profiles; initial fractional ROI is finite opportunity proportion with nonempty denominator | Occasion identity, satisfaction, interval incidence and higher-order/composed coverage; duration/completion fractions remain distinct | #3, #10, #87 |
| Q07 | Exact supplied middles, inherited correlated vagueness and meaningful neutral-band variation; no automatic fresh width | Formalize admissibility and partiality without requiring Grade/numeric width; recruited domains must supply their actual structure | #87 |
| Q08 | Claim-level constrained exact values under vague tolerance; exact equality/cardinal tests; aliases share one value, shared tolerance is not shared error | Typed numeric/cardinal mapping, partial arithmetic, negation/effects/retention and standalone ji'i's row-relative center; no universal floor/full reducer required | #87 |
| Q09 | Minimal/invariant common-tail default with required/declared dependencies; one formed site reused per dependency tuple | Encode dependency realization in shared-frame lowering; application arguments are not automatic dependencies | #16 |
| Q10 | Pure Only defined; same-level alternatives, own-subpart exemption, overlapping outsiders permitted; host and exclusion both at issue; ji'a separately displays addition without strict novelty | Effectful frame/display adaptation must avoid duplicate performances and truth-tailored alternatives | #87 |
| Q11 | Recovered criterion is the ordinary default; explicit/admissible existential readings remain distinct; comparison-chain sharing and same-standard nai | Lexical rows, admissibility, typed relata/nonassertive targets and sharing laws; nonunique recovery does not forbid the separately resolved existential reading | #14, #87 |
| Q12 | Resolve occurrence/source indication's target, then retain it by Refer/CoRef; later repointing does not change it; no physical gesture required | Typed indication/source closure and RI mapping across ordinary, quoted and imagined contexts; ground shift alone does not change token | #87 |
| Q13 | Equality-singleton admission and local least covered upper bounds; separate holding-state fusion and event composition; no global atomism/separation | Joint Henkin carrier/quotient, conditional consequences, admitted coverage and State/event inheritance; no unconditional comprehension or full-model claim | #10 |
| Q14 | Strong-Kleene interpretation-failure statuses; eligible prefix/independent-side retention; F01 bounded assertion return; nearest legal consistent accommodation; checkpointed topic-return distinctions | Full carrier/quotient embedding and general guards, other forces, capture and topic transitions; preserve total bivalence and P43 barriers, not excluded group/family recovery | #6, #11 |
| Q15 | Agreed force/quotation/topic/CAhA contracts; direct-reference and set-count mei, correspondence MOI, scalar/exclusion joi-nai, bounded one-object fractions and explicit-value kau | Typed rows, source/output and effect laws; genuinely uncovered lexical data, generic inference, mixed force, ju'e, wider MEX, numeric-jei and remaining subfamilies stay gaps | #6, #9, #12, #14, #23, #24, #37, #87 |

No new survey result is asserted. Archive searches are bounded and not a
representative population sample. Speaker prompts should separate truth,
felicity, projection, comprehension and production, with date/experience recorded.

The remaining semantic work is to formalize the adopted contracts and complete
their stated coverage. Compound-count individual uptake remains unsupported,
not proved impossible. Bare me'i is settled by P44. RD-C05a and the former
candidate-versus-verified recovery debate are historical evaluation questions,
not construction-time gates. See spec References, “Round2 agreed contracts,”
for the final record and participation limits. This inventory does not itself
authorize execution of every remaining task.

The me'i research traced explicit 2002 advocacy, the 2004 BPFK definition and
default, and the 2010 gloss/example. No separate ratification act was located.
The human's September 10 adoption of P44 does not depend on finding one.
[Adoption](https://github.com/int19h/smusni/issues/15#issuecomment-5623520624),
[completed provenance trace](https://github.com/int19h/smusni/issues/15#issuecomment-5623520912).
[Full comparison, source/default limits and corrected peer arguments](https://github.com/int19h/smusni/issues/15#issuecomment-5622385624).

## Full-pass disposition map

Each FP3 finding has a current disposition below. Later corrections supersede
the original report. An open obligation records work still required, not
implemented or verified behavior.

| FP3 | Current disposition |
|---|---|
| C01 | Clarified nonminimal lifts, conditional guskant dependence and per-profile counting; atomism contradiction withdrawn. |
| C02 | Local reference-level Massify/JoiEvent output repair, preserving construction scope; no global separation law or L3.6 rewrite. MePred singleton gloss qualified. |
| C03 | P42 group export retired under P43; in-scope P6 retained, not governor-external family rescue. Stable plural helpers and allowed source realization remain distinct. |
| C04 | De-dicto consumer gap, Q04; lambda availability is settled, hookup is not. |
| C05 | Contextual episode coverage and model debt, Q06/Q13; no proof of count≤1 without a bridge. |
| C06 | Keep JoiClause fasnu; record exactly where redundant. No proved CAhA contradiction. |
| C07 | Same-domain flip conditions; singular su'o removes the old cross-domain surface counterexample, not import/effect obligations. |
| C08 | At-issue host-plus-exclusion and same-level Among boundary selected; effectful Only/Additive surface adaptation remains Q10. |
| C09 | Share formed frames/sites with minimal common-tail default; required/declared dependencies remain explicit. |
| C10 | Constraint-based claim-level approximation selected; typed composition/retention remains Q08, including attested du controls. |
| C11 | Dependency-indexed vague profile and generic value-return/unit interface obligations remain; per-use nonemptiness alone does not prove a shared profile. |
| C12 | Partial InterpretAct signature; SentenceSign interpretation law; se du'u path distinguished from Structured quotation crossing. |
| C13 | Finite tag elimination and named Target injections; no blanket payload equality. |
| C14 | tu'a shape claims narrowed to event sort/represented content/aboutness; non-vacuity remains a model question. |
| C15 | House/nu specimen explicitly de re. |
| C16 | One formed lo se du'u Content reused through Holds; no duplicated Close sites. |
| C17 | Bare and nonzero-inner-PA description class explicit, now subject to declared dependence. |
| C18 | Existing rat-set Example6.52 retained; proposed6.57 correction withdrawn. |
| C19 | Pure individual existential restrictor closure; dependent lo interface remains Q04, not legitimacy choice. |
| C20 | Product retained as explicit policy, not theorem of equal scope or neutral predication; Q02. |
| C21 | Inner-PA samples use Refer plus CardBasis. |
| C22 | Occurrence-sensitive deictic obligation, Q12; old fixed-ground abbreviations do not establish full surface coverage. |
| C23 | Holding verification stated through the model interface; situation-domain scope Q13, no invented shrinking-domain countermodel. |
| C24 | Singleton-admission/local-least-cover contracts selected; joint carrier still owed and full discipline D unadopted. |
| C25 | Human-adopted persistence under na applied and divergence explained. |
| C26 | Zero distinguished per threshold kind; exact/inherited/neutral-band cases selected for no'e without mandatory width. #69 resolved AtLeast formation. |
| C27 | Degree export profile-sensitive; Few/TooFew none, Enough0 none. |
| C28 | Tanru-family equations at complete rows; ordinary partial application supplies residual predicates. |
| C29 | Graph-only projections classified as declared, not falsely term-defined; no numerical primitive reduction claimed. |
| C30 | General typed function-row application and inert passing distinguished. |
| C31 | Fragment value/display wrapper/Mention/force separated; non-answer sumti and general whole-sumti answer completion remain explicit gaps, as does the me'o constructor. |
| C32 | Separate non-cardinal ROI, SEI/TO/ti'o and xu-focus dispositions recorded. |
| C33 | Supplement signature/anchor/category constraints; force-segment continuation separately bounded. |
| C34 | Holding-state fusion selected separately from direct-event composition; inheritance/model controls remain Q13 application gates. |
| C35 | False conditional-export rationale removed; full event-intension preservation required. |
| C36 | Sample/exposition/source-label synchronization; no unreviewed lexical row chosen. |
| C37 | Bounded questions retained in Q01/Q05/Q13–Q15 with current evidence limits. |

P22's intended negative-frame policy is retained, but its displayed formula
changes from counted No to uncounted PluralNo. These are not generally equivalent:
if a satisfying reference/nuclear frame has no counted unit, the old floor can
miss it. Atomlessness alone does not establish that case. Ordinary no, counted
No/AtMost0 boundary equations, and other PA variants need the Q02 cross-domain
audit; a core helper equation is not automatically a revised surface equivalence.

## Decision provenance

- **2026-09-10 P44 adoption/application.** The human explicitly adopts BPFK's
  default-ro definition and permits application, while asking that its history
  be traced for the record. [Exact decision and bounded scope](https://github.com/int19h/smusni/issues/15#issuecomment-5623520624).
  This supersedes the former pending-recommendation label without adopting the
  whole 2002 proposal package or filling unrelated numeric/source gaps.

- **2026-09-10 correction and agreed-contract application.** The human confirms
  the earlier [non-importing ro outcome](https://github.com/int19h/smusni/issues/15#issuecomment-5620579674)
  and directs proceeding with application rather than reopening settled choices.
  The [completed round2 record](https://github.com/int19h/smusni/issues/87#issuecomment-5574595280)
  had Q03 as its sole remaining compatibility disagreement; its other bounded
  agreements are not failed-consensus dockets. Missing constructions and later
  P43 supersession remain explicit. The historical participation/approval limits
  of that record are preserved; new document wording still requires review.

- **2026-09-10 trajectory and exact-count application.** The human adopts the
  [final profile direction](https://github.com/int19h/smusni/issues/90#issuecomment-5619525748)
  as definitive and permits direct working-spec edits, then explicitly agrees
  to applying the settled changes and confirms ordinary exact counting.
  [Application scope and correction of the stale Q02 label](https://github.com/int19h/smusni/issues/15#issuecomment-5619865711).
  P43 supersedes P42's export policy, not the historical evidence. The later
  explicit Q03 clarification above supplies the non-importing decision; broader
  termset/numeric interfaces and unfinished model work are not silently completed.

- **2026-09-08 RI application.** The human's instruction, “Apply these findings,
  then give me the breakdown of the next unresolved issue,” adopts the scoped
  [RI RESULT-v2 recommendation](https://github.com/int19h/smusni/issues/15#issuecomment-5593166813).
  [Four accuracy approvals](https://github.com/int19h/smusni/issues/15#issuecomment-5593235922)
  precede that instruction; they were not themselves adoption. The
  [source audit](https://github.com/int19h/smusni/issues/15#issuecomment-5590819744),
  [reported human judgment](https://github.com/int19h/smusni/issues/89#issuecomment-5592982748),
  [fragment contrast](https://github.com/int19h/smusni/issues/89#issuecomment-5591756386)
  and [same-witness continuation control](https://github.com/int19h/smusni/issues/89#issuecomment-5593193223)
  retain their source/constructed/conditional distinctions. No broader
  P6/model/engine adoption or merge clearance follows merely from that scoped
  RI record. PM's earlier exclusion of Q03 from application was subsequently
  corrected by the explicit human clarification above.
- [FP3-CONSENSUS-v5](https://github.com/int19h/smusni/issues/87#issuecomment-5552770486)
- [C25 human adoption](https://github.com/int19h/smusni/issues/87#issuecomment-5557227964)
- [SUHO result](https://github.com/int19h/smusni/issues/87#issuecomment-5557668671)
- [Discursive result](https://github.com/int19h/smusni/issues/87#issuecomment-5558936444)
- [Archive/fork result](https://github.com/int19h/smusni/issues/87#issuecomment-5565874259)
- [Historical closure and exact-turn locators](https://github.com/int19h/smusni/issues/87#issuecomment-5565949266)
- [Earlier dependent-constant adjudication](https://github.com/int19h/jbotci/issues/352)
- [P41 source correction](https://github.com/int19h/smusni/issues/62#issuecomment-5557262556)

The later human correction explicitly rejects treating dependent lo legitimacy
as still open, followed by authorization for this document synchronization.
Older panel confirmations were recommendations, not authority transfers; their
former open/adopted labels must be read in that temporal order.

For the exact local provenance, see the native PM transcript
`~/.codex/sessions/2026/09/05/rollout-2026-09-05T03-11-56-01a0710d-ab22-7a22-9269-9e2d67e6769f.jsonl`:
user line6887, 2026-09-07T06:44:09.066Z, asks why Skolemization is still treated
as unsettled; PM line6890, 06:44:21.548Z, corrects the status and identifies
invariance as a special case; user line6915, 06:56:56.226Z, authorizes updating
the documents and the genuine open remainder, with subsequent panel review.
This is authorization for the synchronization of determinations, not advance
approval of every authored detail or of unrelated open semantic choices.
