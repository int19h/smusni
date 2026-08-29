# Step 0 required-rule manifest

Pinned source: `tools/smusni-redex/port-a0.rkt` on main
`892a7040d4f3786be42635089b6aac7743ba6b74` (the Step −1 merge). The live A0
denominator is the 55 unique `A0-*` rules. This kill test requires the 15 rules
below and explicitly omits the remaining 40. Passing this subset admits Rocq
to the full pilot slice; it does not claim full-A0 generation.

## Required rules (15)

1. `A0-Synth` — synthesis wrapper.
2. `A0-Check` — checking wrapper.
3. `A0-T-Natural` — base literal synthesis.
4. `A0-T-Top` — base Content synthesis.
5. `A0-T-Variable` — de Bruijn environment lookup.
6. `A0-T-Lambda-Pure` — binder with pure body.
7. `A0-T-Lambda-Effectful` — binder with effectful body.
8. `A0-T-Check-Synth` — computed compatibility/subsorting bridge.
9. `A0-T-Context` — expected-type-only reference computation.
10. `A0-T-SelectExactly` — expected-only selection with a computed positive-count side condition.
11. `A0-T-SelectSome` — expected-only selection floor.
12. `A0-T-Bind-Reference` — annotated reference `Bind`, including expected checking of its computation and synthesis under the extended environment.
13. `A0-T-Apply-Pure` — pure function application.
14. `A0-T-Apply-Effectful` — effectful function application and correlated effect addition.
15. `A0-T-Equality` — equality-domain and bidirectional-compatibility computed side conditions.

## Required dimensions

- Both judgment modes are generated and checked.
- `Context` and both selections occur under annotated `Bind` in the target relation.
- Compatibility includes equality, `Natural <: Number`, and `Fn <: EFn`.
- `Fn`/`EFn` classification depends on the correlated body record's effects.
- Lambda/Bind use de Bruijn scope; generated variables must resolve in Γ.
- Every success returns one correlated `(type, effects, obligations)` record and a rule-id trace.
- Positivity and equality-domain premises are computed Booleans, not generator defaults.
- Negatives include wrong expected type, zero-count `SelectExactly`, and unbound variable.

## Omitted live A0 rules (40)

- `A0-T-ActualClause-Event-Effectful`
- `A0-T-ActualClause-Event-Pure`
- `A0-T-ActualClause-State`
- `A0-T-AdmissibleThreshold`
- `A0-T-And`
- `A0-T-Apply-ClauseContent`
- `A0-T-Audience`
- `A0-T-Bind-Nest`
- `A0-T-Bind-Performance-Act`
- `A0-T-Bind-Performance-Comp`
- `A0-T-Bind-Performance-Discourse`
- `A0-T-CanonicalAggregateAt`
- `A0-T-Card`
- `A0-T-CloseClause`
- `A0-T-CloseWith`
- `A0-T-CoRef`
- `A0-T-DirectClause-Effectful`
- `A0-T-DirectClause-Pure`
- `A0-T-Exactly-Positive`
- `A0-T-Exactly-Zero`
- `A0-T-GlobalExactly`
- `A0-T-Lambda-Multi-Effectful`
- `A0-T-Lambda-Multi-Pure`
- `A0-T-Let`
- `A0-T-List-Check`
- `A0-T-Massify`
- `A0-T-MoreThan`
- `A0-T-No`
- `A0-T-Perform`
- `A0-T-Refer-Member`
- `A0-T-Refer-Reference`
- `A0-T-SetOf`
- `A0-T-Speaker`
- `A0-T-StateClause`
- `A0-T-ThresholdKind`
- `A0-T-TooMany`
- `A0-T-Vague`
- `A0-T-ZipWith-Effectful`
- `A0-T-ZipWith-Empty-Effectful`
- `A0-T-ZipWith-Pure`

## Gate C accounting boundary

Generic base-type instances, generic list/option/pair infrastructure, and one
mode-indexed relation-derivation invocation are infrastructure. Any
hand-authored term constructor sampler, per-rule frequency knob, or combinator
that restates one typing clause is rule-specific mirroring and fails gate C for
that rule. Gate C status is reported per required rule; it does not alter gate
T's checker/relation soundness.
