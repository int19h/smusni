# F03-A1 tagged carrier and operational transport

This target implements the first released F03-A increment for issue #10.
It constructs general quotient maps and transports operations over the actual F02 carrier.
It does not construct the full Lojban model.
The separate A2 function and event increment remains incomplete and unreleased.

The base is `9b2ec0085a45929b95e9af4a9f467d659dd18648`, the merge of F03-B PR #101.
PM released A1 in [issue comment 6138008395](https://github.com/int19h/smusni/issues/10#issuecomment-6138008395).
The full F03 release is [issue comment 6137938613](https://github.com/int19h/smusni/issues/10#issuecomment-6137938613).
Astra's reviewed `F03-REVISED-v4.md` supplies the design, including the Fable and Grok amendments recorded there.
This report records the implemented scope without requiring that ignored design file.

## Inputs and computation

A quotient identifies representatives related by a supplied equivalence.
A kernel states exactly which inputs a map identifies.
The parameter `R : Setoid P` supplies the arbitrary equivalence on representatives.
Ground values, ground anchors, slot names, and Host handles remain fixed arbitrary types.
The result equivalence `AR : Setoid A` is independent of `R`.

`qValue` maps `Ground + P` to `Ground + Quotient R`.
`qAnchor` does the same for `GroundAnchor + P`.
Both preserve the ground tag and its value.
They map the representative tag through the actual Lean quotient constructor.
They never identify values from different tags.

`qState` applies those maps to every assignment and ordered side anchor in the actual `HostState`.
It preserves missing assignments, side truth bits, history, cumulative payload status, and cumulative side status.
`qOutcome` preserves all three outcome tags and maps the state and returned value.
`mapResults` maps every member of the actual F02 finite nonempty family.
It preserves failure outcomes and merges equivalent alternatives through extensional set membership.

`qState_onto` covers every state in the full declared target type:

```text
HostState Name (Ground + Quotient R) (GroundAnchor + Quotient R) Handle
```

This carrier is not restricted to a selected image or fixture collection.
The proof covers arbitrary assignment functions and arbitrary finite ordered side lists.
No finite-domain premise applies to Name, Ground, GroundAnchor, Handle, or P.
Outcome and finite-family coverage also cover their full declared target types.

`descend` consumes a supplied run with a proof that it respects the state and result relations.
For each quotient input state, it chooses a raw preimage, runs the supplied computation, and maps every terminal alternative.
`descend_at` proves that any raw representative yields that same mapped result.
`qRun` instantiates this mechanism with the actual tagged state and result quotient maps.
The computation equation is:

```text
qRun R AR m (qState R s) = mapResults (qOutcome R AR) (m.val s)
```

`qRun` and `qOutcome` use `Quotient.mk AR` for returned values.
Tagged result shapes use generic `descend` with `qValue`, as `descend_lookupSlot` demonstrates.
This is a wrapper shape limit, not an A1 defect or an A2 prerequisite.

The finite carrier and preimage selections use classical choice.
These are noncomputable Lean denotational definitions, not an executable evaluator or a claimed algorithm for deciding arbitrary equivalence.
Their outputs depend on the entire supplied computation and quotient input.
The representative-independence proof uses the supplied respect property, not a prewritten output equation.

No source-string lookup, fixture dispatch, or descriptor table exists on the general path.
The hand-authored parity, state, side, and resolver examples appear only in `Controls.lean`.
The general results quantify over arbitrary supplied inputs, including inputs absent from those examples.
The only existing-file change adds the two isolated Lake targets.
F02, F03-B, the production engine, and normative documents remain unchanged.

## Exact relations and contracts

`ValueRel` and `AnchorRel` use equality on ground tags, `R` on representative tags, and false across tags.
`OptionRel` requires matching definedness.
`SideRel` requires related anchors and equal truth bits.
`StateRel` contains exactly these clauses:

```text
forall name, OptionRel ValueRel (s.assignment name) (t.assignment name)
ListRel SideRel s.sides t.sides
s.history = t.history
s.kappa = t.kappa
s.chi = t.chi
```

`ListRel` is the design's ordered pointwise `List.Forall2` relation.
The pinned Lean library has no declaration with that name.
The local definition relates two empty lists or two related heads followed by related tails.
Lists of different lengths are unrelated.
Its map-kernel proof preserves both order and pointwise correspondence.

`OutRel` relates only matching outcome tags.
Live outcomes also require related returned values.
`FinRel` requires a related witness in the other family in both directions.
`RunRel` requires that relation at every pair of related input states.
It is not automatically reflexive on unrestricted raw runs.

`RespectingRun` contains a raw run and its self-respect proof.
The run-kernel theorem states an exact equivalence between equal descended functions and `RunRel` on this subcarrier.
`qRun_onto` covers all functions into the declared finite quotient-output carrier of this auxiliary algebra.
It does not admit unrestricted functions into a Henkin model or discharge the A2 function-subcarrier task.
The general Bind relation permits arbitrary relations and heterogeneous carriers before quotient maps require equivalences.

`bind_compatible` requires related input computations and related continuations at every pair of related returned arguments.
It derives the result from actual F02 `Run.bind`, `Run.extend`, and finite union.
It threads each reached state into its continuation.
Dead and Undef retain their states without calling the successful continuation.
`descend_bind_at` connects this general result to the quotient computation equation.

`lookupSlot` reads the current assignment through actual F02 `lookup`.
`putSlot` takes a typed optional value and a slot name with decidable equality.
`projectAssignment` filters assignments using a supplied mask and preserves every other state field.
These helpers select no accessibility policy.
Their generic map and relation laws specialize directly to the tagged quotient maps.

The Host map theorem keeps the eligibility mask and Host handle fixed.
It preserves ordered side length and the truth of the suffix after the incoming side prefix.
`qFinalize_commutes` proves the design's state-map equation using the actual F02 finalizer.
It needs no legal-frame premise because the concrete map equation holds for every supplied terminal.
The separate `qLegalFrame_image` theorem requires an actual raw `LegalFrame` and maps it forward.

The converse legal-frame statement is false.
Equivalent incoming values can be equal after quotienting while differing as raw representatives.
The retained negative control exhibits this exact boundary.
No theorem replaces raw incoming-binding equality with arbitrary related-state transport.

## Coordinates, resolvers, and capture

F02 `Family` retains profiles, inherited coordinates, contexts, and worlds as separate inputs.
The proofs act pointwise and keep those index types fixed.
They allow arbitrary supplied pullback maps and dependent index families already present in F02.
They do not transport `Origin`, quotient an index family, or construct general RR/source eligibility.

`descendFamily` applies the general descent to each supplied respecting run.
`descend_pull` and `descend_capture` commute that construction with actual F02 pullback and capture.
The generic relational capture theorem uses identical saved contexts when the context relation is equality.
Different saved contexts require an explicit context relation and its proof.

`ResolverRel` compares outputs at every pair of related dependency tuples, with matching definedness.
Agreement at visited tuples is insufficient.
`full_resolver_lookup` proves lookup compatibility first.
`captured_resolver_lookup` then applies it through actual F02 capture at arbitrary related tuples.
It uses the saved resolver, not the caller's resolver.

`ResolverEnv` is an auxiliary wrapper for a resolver and an arbitrary `Other` parameter containing all remaining context fields.
It does not change the normative context or claim a full capture-domain quotient.
`EnvRel` requires equality of `Other` and full-domain resolver respect.
The lookup operation observes only the resolver, so its minimal proof uses that component.
For arbitrary families that also observe `Other`, `capture_env_compatible` passes the complete `EnvRel` proof to their supplied family contract.

## Source and theorem ledger

The source laws below guide this derived mechanization.
The reviewed A1 release, not a new semantic decision, authorizes the tagged instantiation and transport results.
The theorem names are in `SmusniF03A1` unless the controls namespace is stated.

| Source or released requirement | General mechanism and proof | Premise or boundary |
| --- | --- | --- |
| F03 v4 tagged values and anchors | `qTag`, `qValue`, `qAnchor`, `tag_kernel`, `tag_onto` | Arbitrary supplied representative equivalence. Tags remain distinct. |
| F02 `Host.lean`, `HostState` and `ClosedSide` | `mapState`, `StateRel`, `state_kernel`, `qState_kernel`, `qState_onto` | Full declared target carrier. Ordered anchors and bits. History and statuses remain fixed. |
| F02 `Carrier.lean`, outcomes and finite families | `mapOutcome`, `OutRel`, `FinRel`, `qOutcome_kernel`, `qResults_kernel`, coverage theorems | All three tags. Matching witnesses in both directions. Finite nonempty output families. |
| Spec sections 5.1 and 5.2, F02 strict sequencing | `extend_compatible`, `bind_compatible`, `descend_bind_at` | Related continuations at every related argument and state. |
| F03 v4 quotient-run equation | `descend`, `descend_at`, `run_kernel`, `qRun_at`, `qRun_kernel`, `qRun_onto` | Self-respecting raw runs. Full auxiliary quotient-run carrier, not Henkin admission. |
| F02 pure and supplied first/later reads | `pure_compatible`, `map_pure`, `read_compatible`, `map_read` | Fixed read phase. Empty and unresolved remain distinct source results. |
| Typed assignment slots | `lookupSlot`, `putSlot`, `projectAssignment`, their map and compatibility proofs | Slot update needs decidable name equality. Masks are supplied. |
| General computation through lookup | `descend_lookupSlot` | Actual descent equals actual lookup on quotient states for every raw state and slot. |
| F02 ordered sides and Host finalization | `side_length`, `side_prefix`, `suffix_truth`, `qFinalize_commutes`, `qLegalFrame_image` | Fixed mask and handle. Raw legal frame only for the forward image theorem. |
| F02 `Fibres.lean`, families and capture | `pull_compatible`, `capture_compatible`, `family_descend_at`, `descend_pull`, `descend_capture` | Fixed index types and saved-context relation. No dependent Origin transport. |
| Spec section 5.3 and F02 full resolver lookup | `ResolverRel`, `full_resolver_lookup`, `captured_resolver_lookup`, `capture_env_compatible` | Every related dependency tuple, matching definedness, and equality of all other compared fields. |

Historical `MODEL_REPAIR.md` model sketches remain unproved beyond these relative results.
The spec still distinguishes the successful-output projection from a completed failure-aware model.
This target uses the existing F02 relative carrier and does not complete that larger embedding.

## Generality and negative controls

`Controls.lean` contains 19 named control theorems.
Several quantify over arbitrary types, equivalences, states, and continuations rather than a finite fixture list.
These proof counts are not a count of semantic cases or model coverage.
The diagnostic parity relation provides equivalent and distinct representatives without supplying the general maps.
The two integration controls follow Fable's requests and Astra's confirmation in Collab message `msg_20261013T045338329543Z_2d9f67de34f849939284dfcc5835461c`.

| Control | What it establishes |
| --- | --- |
| `representative_change`, `distinct_class`, `distinct_tags` | Equivalent representatives identify. Different classes and ground/representative tags remain distinct. |
| `order_retained`, `truth_bit_retained`, `suffix_ignores_old_failure` | Side order and bits survive. Current suffix truth does not include an earlier failed side. |
| `related_side_anchors` | Related proposition anchors identify through the full state map, with an arbitrary existing side prefix and fixed truth bit. |
| `legal_frame_not_reflected` | A quotient legal frame need not be a raw legal frame. |
| `failure_tags_retained`, `two_equivalent_outputs_collapse` | Dead and Undef remain distinct, while equivalent finite alternatives collapse extensionally. |
| `mixed_live_dead_image` | The actual finite image contains both mapped Live and Dead outcomes, even when their states identify. |
| `bind_body_premise_needed` | Related input computations do not suffice when the continuation distinguishes raw representatives. This tests A1 Bind, not A2 function admission. |
| `visited_tuple_insufficient`, `capture_uses_saved_unvisited_tuple` | A visited-tuple match does not supply full resolver respect. Capture retains the saved result at an unvisited tuple. |
| `other_context_fields_matter` | Equal resolvers do not make different remaining context fields related. |
| `arbitrary_quotient_state_covered`, `arbitrary_slot_descends`, `changed_state_is_used` | Full state coverage, general quotient lookup, and independent entry/reached-state sequencing use the public interfaces. |

## Validation and remaining work

From the repository root, run the isolated command:

```sh
bash pilot/lean/check-f03a1.sh
```

The build and audit passed for 276 declarations, including 183 theorem declarations and generated lemmas.
The audit selects declarations by defining module, including private and generated declarations.
It accepts only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.
It rejects own axioms, unsafe declarations, and imports from the production pilot, F03-B, or F03-A2 targets.
The actual audit path accepts the safe opaque fixture and rejects both public and private unsafe opaque fixtures.

The script prints source hashes and retains a bounded temporary fixture directory for diagnosis.
No unrelated production suite runs.
The handoff records the exact commit and documentation/whitespace results.
No placeholder, unchecked proof path, or new project axiom supplies a result.

A2 still owes the respecting function subcarrier, qFun, partial-event and joint-observation kernels, and their transport.
It also owes the descriptor joint-kernel instance and its independent state-respect proof and failure control.
The full simultaneous proposition/state model, constructor closure, realization, and model inverse laws remain open.
No cycle policy, general source transport, normative edit, or formal-authority transfer occurs here.
Issue #10 remains unfinished.
