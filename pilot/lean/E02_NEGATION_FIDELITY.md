# E02 human-approved negation fidelity correction

Decision: [human approval on #74](https://github.com/int19h/smusni/issues/74#issuecomment-5630303444),
released to this implementer by
`msg_20260911T061553042583Z_3068de7987844c1b9769b1e757d4f156`.
Base checkpoint `eb72540` remains distinct. This code follows that explicit
decision; PM's separate P45 documentation commit must still be integrated
before final review and final source-regeneration gates. No frozen Redex
rule, semantic document, F01 draft or E03 lowering was changed here.

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

These are bounded encoding results, not all-S1 exact parity or a semantic
authority transfer. Final PM-doc integration, regeneration, M1/M2/root checks,
and Astra-first then panel review remain required. No push or merge.
