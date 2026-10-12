# Issue 97 bounded structural follow-up

The analyzer proves reusable state facts for the requested expression class.
The strong opaque control obtains the same facts through semantic certificate composition.
This experiment therefore does not demonstrate a material advantage that requires the explicit defining language.
It does not rule out practical benefits from syntax in a larger comparison.
Full implementation remains paused for the panel gate.

This is one follow-up to `13a8dcfa982056c2304fd4c165196aace2b26b4b` on draft PR #100.
The branch remains `codex/issue97-lean-prototype`.
The addressed handoff and PR identify the resulting exact head.
No normative document, oracle, prior pilot meaning, or expression constructor changes.

## General evidence

`FrameLemmas.lean` defines `RefFrame`, which adds exact obligation retention to the existing `Frame` contract.
It proves preservation through unit, tests, side emission, strict Bind, Local projection, and the guarded negative test.
`ReferenceFrames.lean` then proves the invariant by induction for arbitrary reference terms in Opaque, Explicit, and Reviewed.
The proofs quantify over states, result types, and member outcomes without an admission premise.
Reviewed projection uses its actual certificate, not a catalogue of body names.

For the current prototype reference grammar, `HostDomain (observe m) s h` is equivalent to `FreshHost h s`.
The forward proof selects an outcome from the nonempty carrier and transports freshness through unchanged Host history.
The reverse proof uses the derived frame invariant for every outcome.
This removes repeated frame work at a Host call without assuming finalizer correctness.
Other admission duties, including fresh reference introductions, remain separate.

`Frame` itself still says nothing about obligations.
`StructuralExperiment.frame_does_not_constrain_obligations` exhibits a frame with arbitrary replacement obligations.
Current reference terms preserve obligations because their grammar and export contracts do so.
A future obligation-changing operation needs a separate contract and a new preservation argument.
This pass does not choose a discharge policy for #11.

`Transport.lean` translates arbitrary Reviewed terms to Opaque terms using their contracts.
Project and negative equations need no Host admission premise.
Reference-term observation parity is also unconditional.
For performance terms, `Reviewed.toOpaque_transport` proves admission transport and observation parity together under Reviewed admission.
Each Host proof constructs `HostUse` from its actual operand terminal and applies that export's `HostLaw`.
`Reviewed.public_run_parity` then relates the proof-required execution functions.

These are induction proofs over terms, not fixture comparisons.
The translation never inspects a list of known export bodies.
The opaque implementation does not import the explicit interpreter.
The proofs establish bounded behavioral comparison, not equal proof costs or full architecture equivalence.

`PublicBoundary.lean` retains Astra's ten passing theorems.
Only the root import changes, and a provenance comment identifies the source.
The retained cases continue after F/U Host payloads and reject handle reuse through Bind in all three routes.
`record_kappa_false` and `record_chi_false` independently prove that an earlier F persists.
Separate corollaries connect each fact to both finalizers and to arbitrary admitted Reviewed Host exports.

## Analyzer and export certificates

A mask selects the slots to retain.
A state path is a chain of state operands.
`ProjectionAnalysis.lean` recognizes paths that start at `reached` and contain only `prune` nodes.
It rejects `entry` roots and every `record` on that path.
Mask expressions remain pure interpretations of the supplied environment.
The analysis does not infer linguistic scope eligibility.

The analyzer computes an environment-dependent mask.
Its soundness proof uses structural induction over the existing typed grammar and the shared `prune_inter` lemma.
Every recognized state expression equals one projection of `Env.reached` by that mask.
The generic result preserves sides, obligations, frames, Host records, κ, and χ exactly.
Each slot retains its reached value or becomes absent.
No entry-state equality or desired preservation theorem is assumed.

The two counterexamples delimit this result.
An `entry` root loses a reached side despite containing no `record`.
`prune eligible reached` passes recognition, but an unrestricted eligible mask can delete an incoming slot.
`eligible_is_not_local` proves that the latter body fails `LocalLaw`.
Recognition alone is therefore not an export certificate.

The generic theorem contributes to exactly two reviewed export demonstrations:

| Export | Derived state work | Remaining certificate work |
|---|---|---|
| Existing noncanonical `twiceDef` Local | Analyze both prunes and derive their combined projection. Reuse all state-preservation facts. | Prove that the computed mask equals incoming support. Preserve the three terminal tags and the exact returned value. |
| New noncanonical `hostTwiceDef` Host | Analyze two Host-mask prunes before one outer record. Reuse the same state facts. | Prove the Host mask equation. Keep one record, payload truth, current side suffix, and returned occurrence. Retain admission requirements. |

Both final certificate proofs call the analyzer soundness result.
Both exports execute through `Reviewed.run` with explicit admission proofs for T/F/U cases.
The Host analyzer does not accept the outer record itself.
The Host certificate proves that separate recording step.
Neither example adds a surface operator.

The internal mixed-mask probe is `prune eligible (prune (support entry) reached)`.
Its computed mask is `eligible ∩ support(entry)`.
`mixed_matches_opaque` proves equality with the corresponding opaque composition for arbitrary environments.
A concrete case distinguishes it from both the Local and Host masks.
It remains internal because the unrestricted eligible mask can delete incoming slots.

## Strong opaque control and costs

`Projection.lean` provides a shared certificate containing a function, its mask, and a proved projection equation.
It derives field preservation and slot facts once for either candidate.
Its `root` and `restrict` constructors compose certificates as they construct ordinary functions.
They require no expression tree or import of the explicit interpreter.
The shared Local and Host certificate builders also avoid repeated field proofs.

`OpaqueProjection.lean` builds the same double Local, double Host, and mixed-mask functions with those constructors.
Its residual mask equations use the same Boolean simplifications as the explicit path.
Terminal routing and Host recording remain fixed by the shared operation builders.
The explicit path instead obtains a state certificate from the analyzer, then proves the terminal and record obligations for its typed arms.
Both paths retain scope and admission premises.

The explicit infrastructure adds a recursive recognizer and its induction proof.
It can analyze a bare expression in the recognized class without a separate certificate for each prune node.
The opaque infrastructure constructs the certificate alongside each function composition.
A raw opaque function outside that interface still needs a separate semantic proof.
A raw explicit expression outside the recognized class still needs a separate semantic proof.
Neither path provides automatic certificates for arbitrary new exports.

The shared certificate module occupies 57 lines.
The analyzer module occupies 71 lines, and the opaque construction module occupies 41 lines.
These counts include definitions and helper theorems, not just proof tactics.
They do not measure integration, debugging, or future maintenance costs.
The observable result is that both paths remove recurring field proofs in this experiment.
The remaining mask, terminal, record, and admission obligations do not disappear on either path.

## Reproduction and limits

Run these commands from the prototype repository root with Lean 4.33.1 installed:

```sh
bash pilot/lean/check-issue97.sh
python3 tools/check-docs.py .
git diff --check
```

The isolated suite passes with 178 written theorem declarations, including ten retained from Astra and the private analyzer induction.
The audit reports 1,281 declarations and 637 theorem declarations including generated helpers.
The transitive axiom set remains exactly `propext`, `Classical.choice`, and `Quot.sound`.
The documentation and whitespace commands pass.
Existing linter notices about three proposition-valued `def` declarations are unchanged and do not prevent the build.

The five negative compilation controls reject their supplied malformed files and require a type-error diagnostic.
That diagnostic match does not prove that every possible certificate for a bad body is impossible.
`Cases.scrub_fails_reviewed_contract`, `scrub_host_fails_reviewed_contract`, and `scrub_fails_opaque_contract` provide the semantic impossibility proofs.
The lawful noncanonical exports provide positive controls.
The harness does not replace those kernel proofs.

All requested bounded theorems are proved without `sorry`, `admit`, project axioms, or a weakened analyzer conclusion.
The experiment does not construct heterogeneous slots, full source transport, event intensions, capture, general branching, discharge, or the full information-state model.
Those obligations remain open in both candidates.
No wider experiment or conditional full implementation starts from this result.
PM owns the new exact-head review and the panel disposition.

The controlling assignment is `msg_20261012T151423170231Z_25ab5fbb9c3e4c4b9316df56e0309b78` under [issue #97](https://github.com/int19h/smusni/issues/97).
Astra's `review/issue97/PR100-CONFIRMATION.md` consolidates the Fable, Kimi, and Grok findings and corrects the reached-root hypothesis.
Astra's `review/issue97/PR100-PUBLIC-BOUNDARY.lean` supplies the retained ten-theorem source.
Both sources reside in `/home/int19h.linux/work/smusni-97-astra/`.
The state analyzer and strongest-opaque controls implement that bounded prescription, not a new semantic ruling.
