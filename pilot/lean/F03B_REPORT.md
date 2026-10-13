# F03-B conditional cycle proofs

This isolated target proves the released F03-B statements for issue #10.
It does not construct an interpretation of the cycle or a model of Lojban.
The full model task remains open.

The baseline is `3ba58e55828845d0e09daeafcc12b0a0b8a70df7`.
The implementation release is [PM comment 6137013804](https://github.com/int19h/smusni/issues/10#issuecomment-6137013804).
The design source is Astra's complete `F03-REVISED-v4.md`, released through Collab message `msg_20261013T024125576995Z_2756e7440962401fa1f4e7a453a80c49`.
This report records the released requirements without requiring access to that ignored design file.
Fable and Grok supplied the reviewed design amendments that distinguish scalar, set, event, and call-cycle claims.

The code uses the existing pilot terms and typing judgments.
It also uses F02's finite nonempty sets, state-bearing outcomes, strict Bind, and partial event relation.
It changes none of those definitions.
The only existing-file change adds two isolated Lake targets.

## Mechanism and generality

The syntax module constructs `L`, `pL`, `H`, and `N` with actual pilot constructors.
Their typing proofs use the declarative pilot judgments.
`L` contains one Context site and no literal self-copy.
Its body becomes `N` through the pilot's capture-avoiding substitution operation.
These facts concern finite syntax, not termination of its interpretation.

The observation interface accepts arbitrary coordinate domains, proposition values, state domains, and supplied observations.
The current bundle uses Lean `Type` domains and a fixed source-coordinate type.
It does not claim dependent source transport.
Every run yields an actual F02 finite nonempty family of state-bearing outcomes.
No finite enumeration of these domains is required.

Within each supplied interpretation, `reifyValue` fixes one representative per closed term across inputs.
Its represented run and event observations can still depend on those inputs.
This bounds the candidate interface, not normative input independence.
It does not cover every input-indexed reification interface.

`RunLaws` supplies generic Context, strict Bind, substitution, and round-trip contracts.
`run_L_eq_N` uses exact Context success and F02 Bind to derive the continuation result.
It then uses body substitution to reach `N`.
`run_H_eq_L` uses the supplied round trip and preserved replay coordinates.
Neither law assumes the desired scalar or set conclusion.

`Scalar(xs,t)` means that every outcome in `xs` has status `t`.
Nonemptiness makes this status unique when it exists.
The scalar theorem combines that uniqueness with the supplied strong-Kleene negation law.
The separate set theorem uses an explicitly stronger outcome-flip premise.
All set operations use extensional membership, not list order or selected branches.

The call relation accepts arbitrary terms that match its three generic constructor rules.
Successful Bind calls the substituted body at the returned state.
Negation calls its operand at the incoming state.
Holds calls the represented term at its replay coordinates.
The cycle follows from these rules and the supplied Context and replay conditions.

No source-string match, fixture-keyed result table, evaluator, or cycle detector exists on the proof path.
The hand-authored terms are the four required probes.
The three-state truth table defines the stated strong-Kleene operation.
The small Boolean-state families are discriminating examples, not implementations of an interpretation.
The general results cover every input satisfying their stated contracts, not a counted fixture corpus.

## Exact assumptions

An input records the profile, inherited source coordinate, context, world, caller state, site, key, dependency tuple, and segment.
The resolver consumes this whole input.
The interpretation must relate these supplied coordinates to its actual resolver domain.
This target neither computes dependency tuples nor constructs that domain.

The scalar theorem requires these separate inputs:

1. A candidate admits the input context.
2. Its resolver returns the represented value of the actual term `L`.
3. Its Context success contract yields exactly `Live(caller,pL)` and no emission.
4. Its Bind contract uses F02 strict sequencing, and its substitution contract interprets the actual instantiated body.
5. Its Holds/Reify contract preserves run observations under replay.
6. Replay preserves every input field, including the caller state, site, key, dependency tuple, and segment.
7. `ReadOnlyUse(H,xi)` supplies no introductions, no emissions, and unchanged input for this negation use.
8. `ScalarNegation` supplies the strong-Kleene law on that declared read-only domain.
9. A proof supplies `Scalar(run(L),t)`.

The conclusion is `t = U`.
The theorem supplies neither a scalar observation nor a singleton family.
The singleton corollary derives a scalar observation from an independently supplied singleton equation.
The no-emission part of Context success also feeds the separate successful-Bind event contract.
It does not follow from the shape of the source-read table.

The three semantic predicates inside `ReadOnlyUse` remain parameters of the candidate interpretation.
No predicate is inferred from the static effects of `H` or `N`.
Their empty static effect sets do not establish read-only execution of represented content.
Successful singleton retrieval also does not make the entire run singleton or homogeneous.

`SetNeg` states `run(N) = image(flipOut,run(H))` at the fixed input.
The set theorem uses it instead of `ReadOnlyUse`, the scalar law, or scalar existence.
It derives `run(L) = image(flipOut,run(L))`.
`flipOut` exchanges Live and Dead at the same state and preserves Undef.
The scalar contract alone does not constrain states enough to imply this equation.

`EventLaws` supplies separate successful-Bind, substitution, round-trip, and negative-event contracts.
The event index has its own type and is not a successful-outcome index.
The Bind and substitution maps compose into `negativeCoordinate`.
The round-trip event map remains explicit in `event_H_eq_L`.
All event comparisons use F02 `PartialEq`, which requires matching definedness and supplied co-reference for present events.

`event_constraint` also needs a supplied holding value for exactly `N = not(Holds(Reify L))` at the mapped event coordinate.
It derives `event(L) ~partial some(hN)`.
The simplified rewrite needs full run/event identity, negation congruence, holding congruence, and transitive event co-reference.
`JointIdentity` compares runs at all inputs and partial events at all matching indices.
It is stronger than equality of one scalar status or one run.

`event_constraint_rewritten` transfers definedness from that supplied holding value through the congruence contracts.
It produces a value already present in the supplied partial holding observation for `not L`.
It does not create a missing event, prove actuality, or make the holding operation total.
The successful-read event clause does not replace the separate no-return Bind clause from spec section 9.3.

The call theorem depends on the explicitly declared `Calls` rules.
Semantic equality alone does not imply the Holds-unfold rule.
At preserved replay coordinates, the rules derive `L -> N -> H -> L` with the same caller state.
No measure into any well-founded relation can decrease on every edge.
This excludes well-founded recursion over these calls, not every possible denotational construction.

## Source and theorem coverage

The source fragments below supply the interfaces and bounded laws.
Their joint applicability to this cycle remains conditional.
No source entry claims that the project already admits this probe in the read-only fragment.

| Source or design requirement | Definitions and kernel proofs | Boundary |
| --- | --- | --- |
| Pilot Context/Bind/Holds/Reify/negation signatures | `source_typed`, `L_typed`, `pL_typed`, `H_typed`, `N_typed` | Names live in namespace `SmusniF03B`, in `Syntax.lean`. Formation only. |
| Spec sections 5.2 and 5.3, finite formed sites | `L_one_site`, `body_instantiation`, `RunLaws.contextSuccess`, `run_L_eq_N` | Exact successful retrieval remains a supplied contract. |
| Spec section 9.1, represented-content inverse | `ReplayAt.eq`, `run_H_eq_L`, `event_H_eq_L` | Run and event laws stay separate. Every replay field remains fixed. |
| Spec section 7.1.1, read-only strong-Kleene law | `ReadOnlyUse`, `ScalarNegation`, `conditional_scalar`, `conditional_singleton` | No read-only or scalar existence claim follows from syntax. |
| F03-B stronger SetNeg proposal | `conditional_set_fixed`, `status_fixed_points`, `same_state_fixed_points` | General effectful negation remains unspecified. |
| Spec section 9.3, successful Bind and negative events | `event_L_eq_N`, `event_constraint`, `event_negative_rewrite`, `event_constraint_rewritten` | Matching indices, supplied holding values, and full congruence remain explicit. |
| F03-B direct-unfolding probe | `Calls`, `call_cycle`, `no_decreasing_measure` | No total evaluator or impossibility theorem for all models. |
| F02 carrier and observation interfaces | `image`, `Scalar`, `flipOut`, `partial_trans` | Finite nonempty carrier only. No new quotient or model construction. |

The historical `MODEL_REPAIR.md` term-model sketch and fallback are proposal history.
This increment does not prove their normalization, closure, or identity claims.
The earlier `COUNTEREXAMPLES.md` C1 and C4 motivate distinct model-construction and undefinedness debts.
The live specification and current issue release control this increment.

## Controls and policy limits

`status_fixed_points` proves exactly three nonempty status fixed sets: `{U}`, `{T,F}`, and `{T,F,U}`.
`same_state_fixed_points` proves the corresponding full outcome classification when every outcome has one supplied state.
The Boolean-state example contains `Live(false,unit)` and `Dead(true)`.
Its status image is fixed, but its full outcome family is not fixed.
It also fails every same-state premise.

The controls retain both mixed families and their successful branches.
Under spec section 5.1's some-branch-success reading, each family and its flip contain a successful branch.
Assigning scalar T to both conflicts with scalar strong-Kleene negation for this probe.
The `{T,F,U}` family also retains its undefined branch.
These costs do not adopt a mixed-set policy or establish read-only admission.

Two Undef outcomes at different Boolean states supply a homogeneous scalar without a singleton family.
A second control satisfies the local scalar-negation implication but violates outcome flipping because its reached states differ.
The event controls reject both mismatched definedness and distinct present events despite equal scalar status.
Strict Bind controls retain Dead and Undef without selecting a successful continuation.
`strict_live_returns` uses independent entry and reached states and an arbitrary continuation to test F02 state threading.
The proofs never aggregate a family or choose a preferred branch.

`RegressionControls.lean` retains Astra's two diagnostic probes and Fable's consistent-premises probe in separate namespaces.
These instantiate the supplied contracts through the public theorem interfaces.
They are diagnostic contract instances, not Lojban models.
The reviewer source is recorded in Astra's confirmation, Collab message `msg_20261013T034511862039Z_831532e1616545e1bcbbee249cf1f453`.
The strict-Live control follows Grok's request and Astra's independent-state refinement in that same message.

| Diagnostic instance | Public interface exercised | Boundary retained |
| --- | --- | --- |
| `AstraPR101.mixed_candidate`, `mixed_set_result`, `mixed_call_result` | `RunLaws`, `ScalarNegation`, `conditional_set_fixed`, `call_cycle` | Successful Context retrieval and ReadOnlyUse do not imply a scalar observation. |
| `AstraPR101.absent_event_laws`, `absent_event_result`, `no_holding_value` | `EventLaws`, `event_L_eq_N` | Absent events satisfy the contracts with nonidentity coordinate maps, without a supplied holding value. |
| `FablePR101.scalar_premises_consistent`, `scalar_result`, `set_result` | `conditional_scalar`, `conditional_set_fixed` | All premises hold together with a real scalar antecedent. Undef means undefined, not ordinary false. |
| `strict_live_returns` | F02 `Run.bind`, `Run.extend` | The continuation receives the reached state, not a restored entry state. |

F03-A quotient maps, tagged anchors, function subcarriers, and transport proofs remain excluded.
The simultaneous proposition/state model, constructor closure, both inverse laws, and realization remain open.
This increment selects no cycle-admission, dependency-rejection, or fixed-point policy.
It changes no normative document, production engine, oracle, or issue #11 decision.
No PR merge transfers formal authority.

## Reproduction and trust

From the repository root, run this isolated command:

```sh
bash pilot/lean/check-f03b.sh
```

The command builds the target with the pinned Lean toolchain and audits every declaration defined in an F03-B module.
The audit includes private declarations and generated lemmas, regardless of their visible namespace.
It accepts only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.
It rejects project axioms and unsafe declarations, including unsafe opaque declarations.
It does not use native proof evaluation.

The actual audit path accepts the existing safe opaque fixture and rejects both existing unsafe opaque fixtures.
One rejection fixture uses a private declaration.
The script keeps its bounded temporary directory for failure diagnosis and prints source hashes.
It runs no unrelated production suite.
The actual pilot typing imports retain their existing unused-variable warnings.

The tracked controls and proofs compile without placeholders.
The isolated audit passed for 334 declarations, including 173 theorem declarations and generated lemmas.
Its safe fixture passed, and both unsafe fixtures failed for the expected reason.
`python3 tools/check-docs.py .` and `git diff --check` also passed.

The handoff records the exact head and final audit counts in issue #10 and durable Collab mail.
Review remains the next gate.
This report does not claim completion of the broad issue #10 acceptance criteria.
