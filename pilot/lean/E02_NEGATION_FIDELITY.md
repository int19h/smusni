# E02 human-approved negation fidelity correction

Decision: [human approval on #74](https://github.com/int19h/smusni/issues/74#issuecomment-5630303444),
released to this implementer by
`msg_20260911T061553042583Z_3068de7987844c1b9769b1e757d4f156`.
Base checkpoint `eb72540` remains distinct. This code follows that explicit
decision. Code-only checkpoint `0f67c7c` is separate from PM's P45 documentation:
exact commits `5db3548` and `8bea3ea` were integrated without conflict as
`d451012` and `f4a7b01`. Semantic input is now `8bea3ea`; the frozen Redex
rule remains unchanged from `18cd626`. No source edits beyond the supplied
PM commits, F01 draft input, or E03 lowering were included.

## Generic rule and proofs

Negation first checks its operand as Content. `negationEffects` removes only
`refer`; `negateResult` keeps every obligation and appends the existing
negation/synthesis trace IDs. All other effects are retained, including
context, projective and opaque-call distinctions. Preserving performance in
an abstract observation record does not license a performance computation
as a Content operand.

The declarative `PrimitiveJudgment.negation` has the corresponding
`negateObservation` conclusion and a genuine body checking judgment, not an
executable-equality or desired-output premise. Negation was removed from the
unfiltered unary schema. StateClause now routes through that existing unary
helper with the same unfiltered observation law; a direct control preserves
its contextual effect and ClauseContent category. Local, other connectives,
positive selections and opaque EFn handling keep their existing laws.

`negateResult_observation` connects the executable record with its declarative
observation. The named negation soundness handler consumes the body's
checking induction hypothesis under the unchanged independent trace-manifest
predicate. Both public synthesis and checking soundness compile, as do the
judgment-to-execution completeness bridge and dependent definition/certificate
consumers. Generated mutual-recursion motive/case routing was updated, not
replaced with a second checking proof. The corrected negation path remains
inside the 59-rule supported slice; the prior 51 exclusions remain explicit.

Axiom inspection:

- non-reference effect preservation and absence of refer: propext only;
- executable-to-observation lemma: no axioms;
- public synthesis/checking soundness, synthesis completeness and declarative
  dispatch completeness: only propext, Classical.choice and Quot.sound.

## Controls and code-checkpoint result

All four actual SetOf cases (No, AtMost1, FewerThan1, Exactly0) are now
successful typed Set Entity outcomes through the production classifier and
the strengthened A3 gate. Their IDs, ASTs, site targets and cohort membership
are retained. No helper-name/count/ID special case was added to the rule.

General controls exercise pure and nested negation, a selection with both
restrictor and nuclear property dependent on the enclosing comprehension
candidate, and preservation of that dependency rather than hoisting it away.
Positive selection and Local remain effectful. AtLeast0 does not evaluate
an effectful Q, whereas Exactly0 does and is rejected in the pure position.
Negated Context, Presuppose/Card projectivity, opaque EFn calls and mixed
non-reference effects/guarded obligations remain present; pure positions
still reject them. Arity, Content type, performance category and zero-selection
floor negatives remain checked. All consumer corruption tests are retained.

`./pilot/lean/check-m2.sh` passes at the code-only checkpoint: 113 exporter
assertions, the new negation controls, 18 consumer mutations and two positive
refinements. All-S1: 370 cases; 31 unchanged, 161 expanded, 58 rejected;
192/192 successful output typings and 31/31 available input typings are
inside the independent soundness domain. Parity: unchanged 192 candidates,
74 available (54 whole-A0 +20 Assert), 118 non-admissions, 74/74 term and
site matches, zero differences. Recorded rebuilding run: 37.46 s wall,
1,729,524 KiB maximum RSS.

## Combined source migration and validation

P45 source ranges and their digests were rebased from the exact pre-integration
spec, retaining the same equations and incorporating the new purity
qualification where the cited source spans include it. Constructor, S1,
definition, typing, case and Lean manifests were regenerated. The migration
record names P45 separately from equation/identity transport.

All 370 corpus case records (IDs, terms, environments and provenance) are
identical to `0f67c7c`; the corpus case digest remains
`0cd26d1d494f4b5d0312628ed54d1c2c02ecc7d4`. Each of the four retained
case IDs in `E02_CONSUMER_BATCH01.md` maps to itself. Both the 74-target
oracle and independent source-contract file are byte-identical. Generated
fence headers move with source lines; no specimen is removed or relabelled.

Combined checks:

- `./pilot/lean/check-m2.sh`: PASS; the populations and 74/74 exact term/site
  results above are unchanged. Rebuilding run: 138.43 s wall,
  3,393,552 KiB maximum RSS.
- `./pilot/lean/check-m1.sh`: PASS; 370 surface/text, 51 primitive-core and
  303 generated round trips; 2.92 s wall, 1,668,936 KiB maximum RSS.
- `tools/check-smusni`: PASS; 3,464 Racket and 8 Python tests; 370-case
  identity and 114-case A0/B1 differentials with zero differences, 32 existing
  field-scoped waivers unchanged; 157.32 s wall, 374,712 KiB maximum RSS.
- Final public theorem axiom inspection: the standard-only results above.
- Tracked document checker and `git diff --check`: PASS.
- Final root inventory/fence and complete pilot/source-contract regeneration:
  byte-identical after the source migration.

The existing report-only full-gate performance trigger still fires:
157,320 ms exceeds 107,985 ms (1.5 times the retained 71,990 ms baseline).
No threshold or benchmark baseline was reset; no cause attribution or
performance redesign is claimed.

These are bounded encoding results, not all-S1 exact parity or a semantic
authority transfer. Astra-first and subsequent panel review remain required.
No push or merge.
