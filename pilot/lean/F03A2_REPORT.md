# F03-A2 functions and joint observations

This target implements the separately released A2 increment for issue #10.
It builds on the reviewed A1 maps and run descent without changing them.
It proves general function and joint-observation kernels, then exercises them with the required diagnostic instance.
It does not construct a full Lojban model or select a cycle policy.

The base is `cb0c1170b2cd1a895d88e0c51979d91e0bacdc61`, the merge of A1 PR #102.
The [A2 release](https://github.com/int19h/smusni/issues/10#issuecomment-6138689477) records the durable scope.
The addressed assignment is Collab message `msg_20261013T050822302926Z_295af1e633264e9cbdd68d1f8e491b45`.
Astra's reviewed F03 v4 design includes the Fable and Grok amendments behind these requirements.
This report records the implemented scope without requiring access to that ignored design file.

## General function mechanism

A quotient identifies values related by a supplied equivalence.
A kernel states exactly which inputs a map identifies.
`AR : Setoid A` and `BR : Setoid B` are arbitrary supplied equivalences.
The function types and their equivalences are independent of the later descriptor example.

`Respect AR BR f` requires related outputs at every pair of related inputs.
`Respectful AR BR` contains the raw function and its respect proof.
`qFun` uses the actual Lean quotient lift and that proof as its well-definedness argument.
Its computation law is:

```text
qFun AR BR f (Quotient.mk AR a) = Quotient.mk BR (f.val a)
```

`FunRel AR BR f g` compares their outputs at every pair of related inputs.
`qFun_kernel` proves exactly that relation on the respecting subcarrier.
`FunctionImage` names only functions represented by `qFun`.
`representedFun_onto` covers that image, and `representedFun_kernel` retains the exact relation there.
No theorem admits unrestricted raw functions into a Henkin domain or supplies constructor closure.

The identity-function control exercises the computation on arbitrary quotient inputs.
Distinct raw functions identify when their outputs differ only by a related representative.
A raw zero test and an actual Live/Dead continuation both fail respect for the supplied parity equivalence.
The class-separation control also shows that the positive map does not collapse every input.
These controls do not define the general map.

## Partial events and joint descent

`ER : Setoid Event` supplies the equivalence used for event co-reference.
`qEvent` maps `Option Event` to `Option (Quotient ER)` with `Option.map`.
It preserves `none` and maps only present events to their supplied classes.
`event_kernel` identifies its exact kernel with the existing F02 `PartialEq ER.r` relation.
The proof preserves matching definedness rather than replacing absence with an event value.

The content type is the actual F02 structure:

```text
Content Profile Source Context World State Beta Event
```

Here `Source : Profile -> Type` can be a dependent index family.
`Beta` remains a separate supplied event-index type.
It is not a successful-outcome index, a source-origin coordinate, or a dynamic state.
All index types stay fixed when their observations descend.

`ContentRespect SR c` requires state respect for `c.run` at every profile, source coordinate, context, and world.
It imposes no finite enumeration of those domains.
`RespectingContent SR` packages the content and that proof.
On this domain, the relation is:

```text
JointRel SR ER c d :=
  (forall p i e w, RunRel SR Eq (c.run p i e w) (d.run p i e w))
  and
  (forall p i e w beta,
    PartialEq ER.r (c.event p i e w beta) (d.event p i e w beta))
```

`descendContent` combines A1 run descent with the partial-event map.
It consumes an arbitrary supplied content, state map, proof of state-map coverage, and event equivalence.
The general kernel theorem also requires the exact state-map kernel `Kernel fs SR`.
The run component uses the identity map on Unit, so it retains the actual F02 Content result type.
The event component maps the supplied event at the same external and event coordinates.

F02 Content remains Unit-valued here.
Transport for computations returning other types uses A1's supplied result relation and quotient map.
This qualification requires no extension of Content or A2's API.

`qContent` specializes this construction to A1's actual tagged `qState` and its proved coverage.
The state relation is A1 `StateRel (ValueRel R) (AnchorRel R)` for arbitrary `R : Setoid Rep`.
Name, Ground, GroundAnchor, Handle, profile, world, and source-parent interfaces remain fixed.
`qContent_kernel` states that equality of descended content is exactly `JointRel` on the respecting subcarrier.
The two components of the proof use A1's run kernel and the separate event kernel.

The run computation equation maps every terminal outcome using the actual A1 descent.
The event computation equation maps the actual partial event observation independently.
No output table, descriptor match, or expected conclusion supplies either equation.
Classical preimage selection in inherited A1 descent makes joint descent noncomputable denotational Lean code.
It is not an executable evaluator or a procedure for deciding arbitrary equivalence.

## Pullback and capture contracts

`pullContent` and `captureContent` preserve the state-respecting subcarrier through actual F02 operations.
`descendContent_pull` and `descendContent_capture` prove equality of the complete descended Content structure.
They therefore cover event observations as well as runs.
The event index remains separate through both operations.

`joint_capture_fixed` keeps the same saved context on both sides.
Different saved contexts require an explicit `CR` relation and a supplied `ContextJointRel` contract.
That contract includes run respect and event co-reference at every related context pair.
Run agreement alone does not supply the event clause.
`captured_quotient_equal` combines these contracts with the general joint kernel.

`joint_capture_full_env` uses the existing A1 `EnvRel` without weakening it.
Its resolver clause covers every related dependency tuple with matching definedness.
Its `Other` parameter retains equality of all remaining compared context fields.
Both run and event contracts consume that complete relation when comparing saved contexts.
No finite cache of visited tuples or caller-context restoration replaces it.

The indexed control varies source, saved context, and event index while its run remains pure.
It exercises a nonidentity source pullback and shows that event capture uses the saved context instead of the caller context.
The descended-capture control uses the same public joint map.
No dependent Origin quotient, general RR/source eligibility, or full capture-domain quotient is claimed.

## Descriptor instance and independent respect proof

The diagnostic descriptor type is exactly:

```text
P0 = Truth * Option Event * Nat
```

The last component is representation data, not an observation.
The instance uses Unit profiles, source coordinates, contexts, worlds, and event indices.
These inhabited coordinates prevent an empty observation domain from making the kernel proof vacuous.
Its explicit starting state has no assignments, sides, or history, and both cumulative statuses are T.

The state is actual A1 `RawState Unit Unit Unit P0 Unit`.
Thus assignment values and side anchors can carry descriptors through their representative tags.
`Descriptor.observe` uses the Truth component to select the actual Live, Dead, or Undef constructor.
It retains the supplied input state and interprets the optional event component directly.
It does not inspect the annotation.

`Descriptor.Relation ER` requires equal statuses and `PartialEq ER.r` events.
`observationMap_kernel` proves this relation is an equivalence via the status/event-class map.
`joint_observation_kernel` then proves that the actual run/event observations have exactly this relation.
The forward proof evaluates at the explicit starting state and the inhabited coordinates.
The reverse proof works at every pair of related descriptor-valued states.

`state_respect` is a separate proof and does not use that kernel theorem.
It proves respect for every supplied state relation because the fixed status retains its input state.
Only after that proof does `Descriptor.respecting` construct the accepted input to general `qContent`.
`descended_run`, `descended_event`, and `descended_kernel` use the general A1/A2 path.
No specialized descriptor evaluator replaces it.

The controls use different annotations, T and F observation classes, and the explicit event value `false : Bool`.
They also place descriptors in actual assignment slots and use A1 descent over those states.
`stored_annotations_identify` proves that related annotations identify in the whole tagged state map.
`stored_descriptor_run` retains the mapped descriptor-valued state in the outcome.
Undef remains undefined, not an ordinary false claim.

## Why an observation kernel does not suffice

`FailureControl` supplies a separate raw observation family with labels `constant n` and `probe`.
Its own kernel is actual F02 `Content.ObsEq Eq`: equal raw runs at the same inputs and equal partial events.
The kernel is defined before the corresponding state relation.
It does not assume that every observation respects that relation.

`constants_identified` proves that the labels `constant 0` and `constant 1` belong to one class of that own kernel.
Both observations return Live at their input state and expose the same event.
The two states that store those labels are related by the resulting A1 state relation.
The third observation examines the stored raw annotation and returns Live for zero and Dead otherwise.
`probe_not_state_respecting` proves that it distinguishes those related states.

`kernel_equality_not_constructor_congruence` combines the identified constants with the probe's failure of state respect.
The probe is also related to itself by its raw observational kernel.
That fact still does not admit it into `RespectingContent` for the induced state relation.
The raw-tag test is deliberate diagnostic code and appears nowhere on the general implementation path.
This example is not a proposed language model or cycle policy.

## Source and theorem coverage

The reviewed F03 design authorizes these derived interfaces and proofs.
Spec section 9.1 motivates joint Content identity, while section 9.3 retains partial event obligations.
Neither section makes this relative construction the full model.
The implementation imports only the unchanged general F02/A1 path before its diagnostic modules.

| Released requirement | General definitions and proofs | Domain or supplied contract |
| --- | --- | --- |
| Respecting functions and exact kernel | `Respect`, `Respectful`, `FunRel`, `qFun`, `qFun_at`, `qFun_kernel` | Arbitrary input/output equivalences and an actual respect proof. |
| Represented function carrier | `FunctionImage`, `representedFun_onto`, `representedFun_kernel` | Only the represented image is named. No Henkin admission theorem. |
| F02 partial-event kernel | `qEvent`, `event_kernel`, `event_onto` | Supplied co-reference equivalence and matching Option constructors. |
| A1-backed joint observations | `ContentRespect`, `RespectingContent`, `JointRel`, `descendContent`, `joint_kernel`, `qContent_kernel` | Every fixed external coordinate. State-map coverage and kernel. |
| Representative-independent observations | `descendContent_run_at`, `descendContent_event_at` | Actual A1 run descent and a separate partial-event image. |
| Event-side pullback and capture | `descendContent_pull`, `descendContent_capture`, `joint_pull`, `joint_capture_fixed` | Fixed index types and supplied pullback or saved context. |
| Related saved contexts | `ContextJointRel`, `joint_capture_related`, `captured_quotient_equal`, `joint_capture_full_env` | Full run/event context contract. A1 full-domain resolver respect is retained. |
| Actual descriptor kernel | `Descriptor.joint_observation_kernel`, `Descriptor.descended_kernel` | Truth, optional event, annotation. Unit coordinates and explicit starting state. |
| Separate descriptor state respect | `Descriptor.state_respect`, `Descriptor.respecting`, `Descriptor.descended_run` | Independent proof before A1 descent over descriptor-valued states. |
| Raw-kernel failure control | `FailureControl.constants_identified`, `stored_states_related`, `probe_not_state_respecting` | The family's own raw observation kernel does not imply state respect. |

The remaining controls reject a raw-label-sensitive function, distinguish event presence, and separate equal runs from different events.
They also exercise annotation independence, distinct classes, a defined event, the explicit starting state, and separate source/event coordinates.
These are kernel proofs, not a fixture-count claim about semantic coverage.
The arbitrary-R mechanism remains independent of all diagnostic data.

`RegressionControls.lean` retains Astra's two compiled probe groups and the distinct related-context control requested by Fable.
Astra reconciled these requests in Collab message `msg_20261013T055400801682Z_6d32e6a6ddd44aa7a266849caad0f44d`.
The anchored group also covers Grok's Undef/present-event boundary, so the module adds no duplicate of that case.
These are diagnostic contract instances, not Lojban models.

| Regression group | Public path and boundary |
| --- | --- |
| `AstraPR103.annotations_in_slot_and_anchor`, `anchored_side_keeps_false`, `undefined_run_defined_event` | Arbitrary annotations identify through a populated slot and side anchor. The false side bit remains, while Undef and a present event coexist. |
| `AstraPR103.coordinates_remain_separate` | Pullback, saved capture, and joint descent yield the event class of exactly `(source + 5, saved, beta)`. |
| `RelatedCapturePR103.full_context_parity`, `related_saved_captures_equal`, `raw_saved_events_differ` | The full all-coordinate context contract precedes the public `captured_quotient_equal` instance. Saved contexts 1 and 3 give equal descended captures but different raw events. |

## Validation and limits

From the repository root, run the isolated command:

```sh
bash pilot/lean/check-f03a2.sh
```

The build and audit passed for 163 declarations, including 95 theorem declarations and generated lemmas.
The audit covers declarations by defining module, including private and generated declarations.
It accepts only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.
It rejects own axioms, unsafe declarations, and imports from the production pilot, F03-B, or A1 diagnostic controls.
Its safe opaque fixture passes, and both public and private unsafe opaque fixtures fail for the required reason.

The isolated script prints source hashes and retains its bounded temporary fixture directory for diagnosis.
It runs no unrelated production suite.
The handoff records the exact head and documentation/whitespace results.
The only existing-file change adds the two isolated Lake targets.
A1, F03-B, normative documents, and production code remain unchanged.

The full simultaneous proposition domain, constructor closure, source/force transport, event realization, and both model inverse laws remain open.
No evaluator, resolver-cycle policy, full model, or formal-authority transfer is supplied.
The two diagnostic families establish bounded mathematical facts, not joint satisfaction of every Lojban semantic law.
No PR merge changes that boundary.
Issue #10 remains unfinished.
