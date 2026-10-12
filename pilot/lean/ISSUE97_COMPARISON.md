# Issue 97 Lean prototype

This file records the initial comparison at `13a8dcf`.
Its counts and size measurements refer to that checkpoint.
The [bounded structural follow-up](ISSUE97_FOLLOWUP.md) records the later proofs and current evidence.

This prototype does not demonstrate a material proof benefit from the explicit defining language over the strongest opaque model account.
It gives the explicit alternative a concrete syntax and a working reviewed-export path.
The panel must assess that evidence before any conditional full implementation starts.

The source baseline is `3ba58e55828845d0e09daeafcc12b0a0b8a70df7`.
The code checkpoint is `62145cf5055b5de72eaa1ac7eccdc19dc158e8e1` on `codex/issue97-lean-prototype`.
The report commit changes no proof source.
The [live issue](https://github.com/int19h/smusni/issues/97) defines the authorization and the panel gate.

## Mechanisms and scope

A terminal observation records success, failure, or undefined interpretation with its reached state.
Both candidates use the merged F02 finite-set carrier.
Both share assignment projection, closed sides, captured obligation values, segment data, Host records, and truth operations in `Smusni97/Common.lean`.
This shared code is not an exclusive gain for either candidate.
Slots contain one ground sort, `Nat`, while returned values include arbitrary small Lean types and functions.

The opaque candidate exposes named operations through `Opaque.Term`.
Its observer calls concrete model equations for Local, Host, and the guarded negative test.
Local maps projection over each complete terminal observation.
Host projects assignments, appends one status record, and returns the supplied occurrence.
Strict Bind passes the actual state and value from each Live result into its continuation.
Dead and Undef bypass that continuation.

The explicit candidate represents boundary bodies as typed expression trees in `Explicit.lean`.
Its state expressions compose support, masks, projection, suffix status, and Host recording.
Typed terminal arms distinguish a Live value from a valueless failure arm.
`RunDef` contains three finite arms, not an arbitrary state function.
The observer interprets those trees without importing the opaque candidate.
Finite-family sequencing is separate observer code, not a full higher-order defining calculus.

O1 means a fixed-body catalogue.
`Explicit.LocalExport`, `HostExport`, and `NegativeExport` require equality to their listed bodies.
O2 means general typed bodies with reviewed named exports.
`Reviewed.lean` supplies O2 records with a name, an actual body, and a kernel proof of the required semantic contract.
`Reviewed.Term` consumes those records at the execution boundary.
The body name never selects a fixture result.

O2 accepts `twiceDef`, a noncanonical body that projects twice.
Its proof uses projection idempotence, which means repeated projection has the same result.
O1 rejects that body because its syntax differs from `localDef`.
Both Local and Host contracts reject `scrub` on concrete counterexamples.
The strong opaque control also supports reviewed named model functions with the same Local contract.
Thus named growth and proof certificates do not depend on an extra syntax layer.

`Admission.lean` defines the same per-use admission requirements for all candidates.
Each public `run` function requires a proof of admission.
Host admission requires preserved incoming values, a valid side-history prefix, unchanged prior records, and a fresh occurrence on every terminal.
Bind checks continuation admission at each actual Live state and value.
Negative admission requires fresh introductions and excludes side emission by its operand grammar.
Raw `observe` functions remain total mathematical probes, not permission to perform an invalid Host.

The raw reference observer returns U on an occupied-slot introduction.
`RefTest.Admitted` excludes that branch, so it supplies no new core collision policy.
Scope eligibility remains a supplied mask, not a derived Lojban scope plan.
Closed side legality and captured obligation values are also supplied.
Host finalization does not discharge pending obligations.

## Evidence and change cost

The following matrix names the shared goals and their evidence.
The implementations use general state operations on their inputs.
No test label or surface string selects a prewritten result.

| Goal | Evidence in `Smusni97/` |
|---|---|
| Local value, truth, incoming slots, sides, obligations | `Opaque` and `Explicit`: `local_value`, `local_truth`, `local_incoming`, `local_fresh`, `local_sides`, `local_obligations`. `Comparison.local_matrix` pairs them. |
| Host prefix, Dead/Undef continuation, side suffix, status | Both modules prove `host_prefix`, `host_returns_dead`, `host_returns_undef`, `host_sides_once`, and `host_record`. `Comparison` and `Cases` cover suffix, incoming values, fresh records, and local versus cumulative status. |
| Strict Bind and unit/associativity | Both modules prove the three Bind laws. `Comparison.bind_routes` covers all terminal tags and passes the actual state/value. The F02 run proofs are shared credit. |
| Guarded negative test | `Common.test_retains`, `test_incoming`, and `test_frame` prove the operand contract. `Comparison.negative_status` and `Cases.guarded_neg_actual_projection` cover T/F/U and removal of an actual new slot. |
| Bad state loss and export rejection | `Cases.scrub_breaks_local`, `scrub_breaks_host`, and both `scrub_fails_*_contract` controls give semantic counterexamples. O1 and O2 reject the body by different rules. |
| Admission at the public boundary | Three repeated-occurrence rejection theorems, `nonprefix_rejected`, and `fresh_intro_required` reject bad uses. `Cases.admitted_execution` exercises all three public execution functions with valid proofs. |
| One new projection consumer | `bodyLeg`, the named `bodyExport` records, `extra_consumer_parity`, and `named_consumer_ordinary` implement one quantifier-body projection leg. They do not implement quantifier aggregation. |

`Comparison.term_parity` proves equal observations for every translated opaque term, not just the fixtures.
`Reviewed.different_body_runs` proves that the noncanonical O2 body works through its term boundary.
The minimal body consumer reuses the canonical projection on both sides.
It adds a name and a wrapper, but no new state operation or independent semantic law.
The double-projection body is an admission control, not a required cost of that consumer.

Source sizes are 118 lines for `Opaque`, 207 for `Explicit`, and 105 for `Reviewed`.
Their theorem declarations and proof blocks contain 47, 59, and 43 nonblank lines respectively, including signatures.
These files include different helper obligations, so those counts alone do not rank the architectures.
`Admission` adds 66 lines across all candidates.
Shared data, cross-candidate proofs, and cases occupy 172, 152, and 225 lines.
The explicit layer adds three expression sorts, nine state-expression constructors, typed value/terminal arms, an observer, and export records.

The extra syntax exposes finite bodies for inspection and rejects ill-sorted expressions before execution.
Lean also checks the state-operation signatures in the opaque model account.
The O2 semantic certificates move proof obligations to each named export, but do not remove those obligations.
Neither candidate automatically derives scope plans or synthesizes export proofs.
This prototype gives no result about the completeness of a future capability-based admission system.

## Reproduction and remaining work

Run this command from the prototype repository root with the installed Lean 4.33.1 toolchain:

```sh
bash pilot/lean/check-issue97.sh
```

The command builds `Smusni97` and audits every declaration from its seven modules, including private generated helpers.
It rejects project axioms, unsafe declarations, and transitive axioms outside `propext`, `Classical.choice`, and `Quot.sound`.
The result is PASS with 98 authored theorems, 1,038 audited declarations, and 470 theorem declarations including generated helpers.
Five negative compilation controls pass: state-sort mismatch, a Dead-arm value, O1 scrub, O2 scrub, and opaque scrub.
These controls reject the supplied malformed files.
The kernel proofs of `¬LocalLaw` and `¬HostLaw`, not diagnostic matching, establish semantic scrub rejection.
There are no new dependencies or changes to existing default Lake targets.

Both candidates still need a bridge from the existing pilot AST and its effect judgments.
The opaque route needs interpretation clauses and proofs for supported operations.
The explicit route additionally needs translation into defining syntax and a reviewed export for each operation contract.
Their effect/category alignment and recursive use-admission obligations need proofs in that integration.
This prototype does not modify the current parser, typing rules, Redex oracle, F02 meanings, or normative documents.

Source-coordinate transport, one shared Act across source alternatives, event intensions, occurrence capture, and full information-state lifting remain open in both candidates.
So do general branching policies, side discharge, heterogeneous slot contexts, higher-order closure, and the Proposition quotient.
The finite carrier supports strict routing of supplied alternatives, but does not determine connective aggregation.
No empty default, invented event, or assumed theorem fills those gaps.
Issues #10, #11, and the #74 authority gate remain unchanged.

The design source is Astra's October 12 revised report at `smusni-97-astra/review/issue97/REVISED-1.md`.
The [PM comparison](https://github.com/int19h/smusni/issues/97#issuecomment-6122254789) records the panel positions and their intellectual provenance.
PM messages `msg_20261012T135808206852Z_f72bd3cb49834e798488a5b8da47565c` and `msg_20261012T141210076458Z_a82bc9924ed5432faaa3478b31bdf99e` prompted the O2 and admission additions.
Current spec §§5.1–5.5, 7.1.1, 9.3, and 14 control the bounded meanings.
The historical consensus and model-repair notes do not override those live clauses.
