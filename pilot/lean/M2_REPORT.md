# Lean pilot milestone 2 — E02 migration checkpoint

Current code correction: [`E02_NEGATION_FIDELITY.md`](E02_NEGATION_FIDELITY.md).
Human approval now authorizes the generic refer-only negation law; the code
and proof correction makes the four retained cases succeed. PM's exact
P45 commits are integrated; combined M1/M2/root checks pass. Review remains
pending; see the current report for source lineage and bounded coverage.

Previous correction: [`E02_CONSUMER_BATCH01.md`](E02_CONSUMER_BATCH01.md).
At checkpoint eb72540, the strengthened consumer correctly failed four actual typed-outcome
differences: prior 74/74 AST matches were not all successful typed Lean parity.

Prior follow-up: the PM-authorized one-Assert bridge is documented in
[`E02_ASSERT_BRIDGE.md`](E02_ASSERT_BRIDGE.md): 74 typed targets (54 whole-A0,
20 bridge) from the unchanged 192 candidates. It preserves obligation
metadata and requires independent source/target payload typings.

The remainder records checkpoint **3a7edfc**, before that widening; its
54-target oracle counts and timings are preserved historical results.

Migration-checkpoint status: bounded M1/M2 gates pass; independent review and the broader
typed-oracle coverage disposition remain pending. This is not all-S1 exact
parity, a full-migration result, or a transfer of semantic authority.

Input: `18cd6267ad38abde8836a553f1531a4f05f339c6` (integrated E01).
F01's separate PerformSource branch and E03 lowering work are excluded.
The pre-E02 reports, manifests, supplements and oracle are preserved under
`../history/pre-e02/`, first committed in `828c6d2`; they are historical
results, not current validation. `shared/archive_pre_e02.py` reproduces that
archive from the recorded Git revision and refuses differing existing bytes.

## Mechanism and source inputs

The pilot consumes current corpus terms **and their environments**, generated
constructor/definition/typing inventories, exact normative equation ranges,
lexical row arity/event mode, and occurrence context. Definition selection
still follows the original rule: pending-M2 cases with a nonempty defined-head
set wholly contained in the current a0/ported head set. No case-ID output
table, surface-string match, or arbitrary 160-case reset is used.

The generated chain now has 25 ported heads, 3 plan extras, 6 dependency
definitions: 34 selected definitions, 40 clauses, one selected domain,
89 catalog entries. Typing input contains 81 Redex rules plus 29 supplemental
clauses (110 records), nine grammar categories (including the closure and
comparison head families), 21 core constants and 50 pilot lexical rows.

The exact old definition source is `138259e:spec.md`, verified against the
archived manifest's SHA-256. Supplement ranges were transported from that
source, with changed surrounding doctrine reread at the adopted source.
Using the immediately preceding engine base would have cited unrelated text.
The old typing source is `a04cf29:tools/smusni-redex/port-a0.rkt`, likewise
digest-checked. `M2_MIGRATION.json` records every old/current Redex rule body:
the CoRef rule changed, and Closure, Comparison, and Only are new rule inputs;
the other 77 existing rule bodies are identical despite range movement.

General typed templates now implement IndividualSome/No/Every, PluralSome/No,
and pure Only. The closure templates retain individual versus reference
domains, permit the compatible effectful nuclear arrow, and do not export a
selection witness. Only checks both pure property types and expands to host
plus Among exclusion without projection. Massify now constructs a
reference-level Refer restriction with an existential canonical group and
CoRef, not SelectExactly 1. Its basis whole type is consumed and checked
against Group<T>; CanonicalAggregateAt enforces the same domain.
The prior typed templates and recursive dependency certificates remain live.

Hand-authored semantic data on the input-to-output path remains the general
templates and the explicitly cited supplemental typing clauses. The new
comparison rules compute typing from both operands. Nothing selects an output
by corpus identity. Frozen IDs occur only in transported regression assertions.

## Source-to-source accounting

`../shared/M2_MIGRATION.json` retains every term, environment, provenance,
old/current identity, cohort and definition disposition.

| Population | Count |
| --- | ---: |
| Historical S1 inputs | 337 |
| Current S1 inputs | 370 |
| Exact term/environment transports | 285 |
| Of those, identity-only inputs | 279 |
| Of those, changed definition semantics | 6 |
| Retired exact term/environment inputs | 52 |
| New term/environment inputs | 85 |
| Historical parity cohort | 160 |
| Current criterion-derived parity cohort | 192 |

The historical 160 split into 118 identity-only, 2 changed-definition, and
40 retired inputs. Across all 337 inputs, four additional out-of-slice
JoiGroup consumers reach changed Massify through the full ledger dependency
closure; they are not falsely labelled identity-only. Retirement means the
exact input is absent; it is not a
claim that its language meaning was retired. Rewritten terms are not paired
by an old fence ordinal or similarity. E01's tracked source-sync record
supplies the numerical/P2/P43/threshold/description dispositions. Exact term
identity itself is not semantic equivalence when a dependency changed.

The current partition is 192 parity candidates, 3 Grade/Jai extras, 51 M1
primitive cases, 92 residual pending cases, and 32 structurally out-of-slice
cases. Every current case is in exactly one cohort.

## Typed Redex oracle and its limit

Available targets require an actual source A0 typing and a target A0 check
at that source type. Lexical declarations are computed from the actual
fixture arity/event mode for source and target, independently of Lean.
The exporter preserves A0's top spelling until after typing, then converts
the target to the interchange spelling. Each available record carries its
source type. No untyped metafunction RHS is counted as available.

Expected non-admission raises a dedicated domain exception with the actual
stage/input. Unexpected implementation exceptions fail generation instead of
being swallowed as unavailable. Empty typed-oracle output also fails.
The generic effectful CoveredBy member-property guard is preserved. Six
exporter tests exercise that guard, the actual transported symbolic #83 case
(`9179373c…`, formerly `7318097d…`), an unseen effectful equivalent, and an
unseen pure positive control.

Current oracle: **54 available, 138 unavailable** of 192. All 54 are compared:
54 term matches, 54 site-signature matches, zero differences. Unavailable:

- 47 outside the frozen A0 whole-source grammar;
- 90 with no admitted A0 source derivation;
- 1 member-Refer lift whose ledger still has port-state none.

These are explicit non-admission/domain boundaries, not 138 semantic
ill-typing judgments. Among transported old targets, 22 remain available,
61 formerly available targets are now non-admitted, and 37 remain unavailable.
New inputs contribute 32 available and 40 unavailable candidates.
The archived old oracle had not required these whole-term typing witnesses;
its 118 published RHSs cannot be relabelled as current typed parity.

**Coverage follow-up / PM disposition required (#74/#83):** broader parity
for those non-admitted whole terms requires a separately justified typed
oracle interface (including the needed wrapper/row/expected-mode domains).
This checkpoint does not expand the frozen E01 engine or hide that remaining
coverage cost. The selected cohort was not reduced to the available set.

## Lean typing, relations and certificates

All 370 cases are classified: 31 typed unchanged, 157 successful expansions,
62 typed rejections, 48 pending M3, 6 selected-domain blocked, 1 input
unavailable, and 65 final out-of-slice dispositions. Final dispositions and
the structural input partition are different classifications.

There are 59 implemented declarative typing rules and 51 explicitly excluded
manifest rules. All 31 available unchanged-input typings and all 188
successful output typings satisfy the independent manifest-domain predicate.
Comparison was added to the actual executable and declarative rules, with
both soundness and completeness checked. Generated induction handler numbers
moved by two; their named semantic handlers were retained.

TemplateEquation now includes the six new definition families and the typed
group-basis condition. The existing dispatcher soundness/completeness domain
is retained, not replaced with a premise assuming its desired output judgment.
The three existing executable-equality families (Close/DirectClause/ZipWith)
remain declared proof limits. Grade/Jai plan validation and the recursive
surface decoder/site allocator remain outside the converse theorem.
Neither the 59-rule typing slice nor the definition relation is an all-S1
semantic adequacy proof.

The four public typing/dispatch theorem axiom checks report only
`propext`, `Classical.choice`, and `Quot.sound`. No new axioms, omitted
proofs, or test-output special cases were introduced.

Unseen controls cover every new closure at Entity/Eventuality/Number with
effectful nuclear predicates, non-export, pure/effectful-host Only,
Massify's Refer/existential shape and wrong whole-basis rejection, numeric
comparisons and wrong operand types, and explicit dependent-reference
metadata plus malformed-profile mutations. Existing certificate, corrupted
bundle, expected-only, purity and row controls continue to run.

## RR and source/index joins

RR.references is required and decoded as explicit invariant or dependent
profiles. The decoder preserves source offsets, governor lists and scope;
it rejects duplicate sources/governors, empty governors, self-dependence and
scope outside the governor list. This is **shape validation**, not a Lean
proof of source attachment, graph legality or dependent-reference realization.
Those limitations are printed alongside the consumed profiles.

A current RR link requires source ordinal **and exact fence digest**.
Six stale RR files remain explicit HistoricalRRFixture records and are not
fed into current bundles or audits. There are 28 current RR fixtures and
32 linked corpus cases. Context/Vague graph audit: 12 declared sites,
23 operand sites, 6 matched roles/dependency agreements, zero comparable
mismatches, 17 undeclared emitted origins, 17 comparable and 15 unavailable
cases. Reference-source profiles are not conflated with those site graphs.
The sites attached to emitted current RR links total 22; the earlier
unfiltered-link count included non-current paths and is not current coverage.

## Validation at this checkpoint

- `./pilot/lean/check-m1.sh`: passes; 370 source/text round trips,
  51 primitive core round trips, 303 generated round trips; 29.97 s wall,
  2,012,076 KiB maximum RSS on the recorded rebuilding run.
- `./pilot/lean/check-m2.sh`: passes; counts above, all generator checks,
  six exporter tests, existing and unseen controls; 120.66 s wall,
  3,532,448 KiB maximum RSS on the final rebuilding run after including
  the two grammar-family records (earlier rebuilding run: 45.88 s).
- Public theorem axiom inspection: the four checks described above pass.
- `tools/check-smusni`: passes, 152.36 s wall, 376,780 KiB maximum RSS.
  No unchanged E01 suite was rerun during exploration. Final idempotent
  regeneration of the root inventory/fences and the complete M1/M2 chain
  was byte-identical. `git diff --check` and the tracked document checker pass.

This remains derived verification work under #74/#19/#83. Review, merge,
semantic authority transfer, and any separately scoped oracle widening
require their own recorded dispositions.
