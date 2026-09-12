# F02 auxiliary ground model and local proofs

Status: local implementation for review, not model adoption or a production
runtime. Task [#10](https://github.com/int19h/smusni/issues/10), addressed PM release
`msg_20260911T234534032747Z_90570bd22ed84e5f8f7a7aeddaf69840`.
Input commit `49615fe6ec01d01310e2545f51fa1bb691cd59dc` (merged F01/PR91).
Branch `work/f02-auxiliary-20260911`; prior F01 branch/head `7426258` preserved.

## What the code does

Given arbitrary ground types, supplied terminal source interpretations and
run/partial-event nucleus interpretations, the definitions construct finite
nonempty sets of state-bearing terminal observations and their strict sequencing,
dependent source fibres, profile-preserving pullbacks, first/later reads, captured
payloads, and a bounded returning Host finalizer. The kernel checks the stated
local laws for these definitions. No source language, AST, string or fixture label
is an input to this construction. There is no evaluator or lookup table of
expected results.

`FSet` is a membership predicate with a *proof* that some finite list has precisely
that membership. `FSet.ext` and `NEFin.ext` make equal membership actual equality,
irrespective of order, multiplicity, or finiteness witness. The list is not
semantic identity. `unionMap` defines membership by existential union and proves
finiteness using a finite concatenation of witnesses; `NEFin.unionMap` proves
nonemptiness from an input member and one member of its output. Classical choice
selects only proof witnesses, not a reference result or profile. As a result this
is a **noncomputable denotational model**, not a runnable finite-set interpreter.
The tests below are kernel proofs, not evaluations of a native program.

`Run.bind` consumes each input outcome. Live passes its actual state and value
to the continuation; Dead/Undef preserve their reached states without invoking
the continuation. The union removes only identical run observations. Content's
independent `Beta → Option Event` component retains distinctions invisible to
run equality. These run monad laws do not assert a general Content/event monad.

`Origin source p` is the dependent sum of an inherited coordinate and an actual
terminal member of its source family. `Family P I E W S A` keeps profiles outside
the outcome set. Pullbacks map indices *within the same profile*. `payload` accepts
a nucleus over `Outer`, not the new source fibre: it passes a returned reference,
the inherited outer parameter, and current context/world/state/event inputs.
No extra nucleus argument exposes K or the saved source state. Only
`firstExecution` supplies the reached source state; replay uses the caller state.

`Host.finalizeState` computes binding projection, retains the terminal side list
once, measures this Host's side suffix, appends its T/F/U record, and applies
strong-Kleene cumulative conjunction. Its projection/retention laws are derived
from that code. It does not infer scope legality from truth.

## Supplied interfaces versus proofs

- Ground `S`, values, `P`, inherited `B p`, current worlds/contexts and event
  index/value types are arbitrary Lean types, at independent universes. No
  finiteness of global B, profiles, worlds, contexts or descendant spaces is
  assumed. Terminal sets alone are finite/nonempty. Empty coordinate types make
  their pointwise statements vacuous; `origin_over_each` exhibits an origin for
  *each supplied coordinate*, and `descendant_over_each` uses explicit pointwise
  nonemptiness. Thus nonempty B yields nonempty origins without a finite-B premise.
- Source `∀ p, B p → Terminal S R` is a supplied observed interpretation. It
  already distinguishes a completed Empty selection from Unresolved; divergence
  is outside this terminating carrier. General source evaluation, eligibility,
  and the finite admitted restriction are not inferred from typing or built here.
- A supplied nucleus has actual run and partial event functions. `Beta` is a common
  interface, not the successful-outcome set. `Content.ObsEq` compares all run
  coordinates and matching partial definedness plus supplied CoRef. Reflexivity,
  symmetry and transitivity use only those corresponding properties of CoRef;
  payload/capture/pullback congruence does not assume its desired conclusion.
- E may include arbitrary full-domain partial resolver functions.
  `capture_full_resolver` covers every dependency tuple, not a saved visited set.
  Capturing E leaves profile, source index, evaluation world and caller state live.
- Reads and Act/occurrence tuples are lexical model values, outside `HostState`.
  Ground states store only assignments of a separately supplied value type, closed
  sides and opaque-handle/status history. No circular type equation identifying
  that value type with this Content/function space is imposed or solved.
- `Host.LegalFrame` describes inputs: old bindings remain unchanged, the side log
  is an append-only extension, and payload work leaves Host history/cumulative
  status unchanged. `eligible : Name → Bool` is supplied scope membership.
  `ClosedSide` carries already-closed anchor data and total Boolean side truth;
  no failed guard, dangling-anchor repair or accommodation is hidden in it.
  The finalizer is defined on all observations; legal-frame premises delimit
  their intended fragment. No theorem asserts all arbitrary Runs preserve frames.
- Freshness and unique token/span selection are external occurrence premises.
  `makeHost` constructs one immutable lexical tuple with its direct raw/captured
  projections. It is not an allocator, transcript-selection implementation, or
  proof of general occurrence closure.

## Source-to-theorem ledger

All names below have the `SmusniF02` prefix. File links are relative to this
report. The full per-declaration transitive axiom list is generated by the check
command, including generated helpers; these are the substantive coverage entries.

| Source obligation | Definitions and kernel-checked coverage |
|---|---|
| F02-v2 §2; spec §5.1 / §7.1.1 terminal carrier | [Carrier.lean](SmusniF02/Carrier.lean): `Outcome`, `FSet`, `NEFin`; `FSet.ext`, `NEFin.ext`, `unionMap` closure proofs; `Run.bind_finite`, `bind_nonempty`, `pure_bind`, `bind_pure`, `bind_assoc`, `bind_congr`. |
| F02-v2 §7 successful projection | `Run.successes_pure`, `successes_bind`: successful relation preserves unit/strict Bind. `Controls.X01_no_success_factor`: no successful-only observation function can implement this returning Host; two legal failed prefixes witness the obstruction. |
| F02-v2 §§3–4 source supports | [Fibres.lean](SmusniF02/Fibres.lean): `Origin`, `Origin.parent/result/reached`, `origin_over_each`; `Descendant`, `parent`, `descendant_over_each`. No finite global support assumption. |
| F02-v2 §4 pointwise run lifting | `Family.pure_bind`, `bind_pure`, `bind_assoc`; `lift_pure`, `lift_bind`; `pull_pure`, `pull_bind`, `pull_comp`, `pull_id`. Pullback/lift is precomposition, so these commute by definitional equality where appropriate. |
| F01 read table; F02-v2 §4 | `read_state`, `read_preserves_caller`, `read_obtained`, `reads_factor`, `pull_reads`, `repeatedRead_diagonal` (all natural-number repetition lengths). No source callback or saved state is an input to `read`. |
| F02-v2 §5 first execution versus replay | `firstExecution` takes world from the source parent and state from its terminal outcome. `Controls.firstHost_obtained` computes a Host through that operation and actual payload/finalizer, not a separately selected expected state. X04 tests replay world sensitivity separately from origin preservation. |
| F02-v2 §5 partial event/read rule | [Content.lean](SmusniF02/Content.lean): `payload_obtained_run/event`, `payload_empty_run`, `payload_unresolved_run`, `payload_no_value_event`, for both read phases. False obtained nuclei retain supplied events; neither no-value tag invokes a fallback event. |
| F02-v2 §§5–6 local congruence | `Content.obsEq_refl/symm/trans`, `payload_congr`, `Content.capture_congr`, `pull_congr`, `pull_payload`, `capture_payload`; `Controls.X03_run_equality_not_content_equality` rejects a run-only identification. This is not congruence for every kernel constructor. |
| F02-v2 §§4–5 capture/reindex | `Family.capture_pull`, `capture_bind`, `Content.capture_pull`; `capture_full_resolver` and X06 caller/context/side tests. No world/profile/state frozen by capture. |
| F02-v2 §5 single lexical association | `Act`, `HostOccurrence`, `makeHost`, `host_raw`, `host_captured`: direct projections of one value with no source index field. Freshness/unique-span selection are supplied, not established by those projection equalities. |
| F01 return law; F02-v2 §5 | [Host.lean](SmusniF02/Host.lean): concrete `keep`, `currentSideTruth`, `finalizeState`, `finalize`, `finalizeAll`; `returns_live`, `retain_incoming`, `retain_eligible`, `drop_local`, `sides_once`, `side_status_is_suffix`, `history_append`, `cumulative_payload/sides`, `prior_failure_stays`, `finalize_congr`. |
| F02-v2 §7 origin obstruction | `Controls.X02_no_origin_erasure`: at fixed current context/world/state, a function of current world/state alone cannot agree with the whole source-fibre payload. |

## Eight discriminator groups

[Discriminators.lean](SmusniF02/Discriminators.lean) contains 30 explicitly authored
theorems (including supporting lemmas), in addition to the general definitions
and laws. These are new Lean proof obligations, not the old Python probe counts.

| Group | Checked control and explicit toy input |
|---|---|
| X01 | Different retained binding/side prefixes, identical empty success projections, different Host returns; impossibility of factoring Host return through success-only observation. Optional reference also loses Empty versus Unresolved. Both prefix frames proved legal. |
| X02 | Actual `Origin toySource` coordinates with Empty/Obtained; same current world/state, different payloads; universal no-origin-erasure consequence. |
| X03 | One false run admits distinct Beta events 10/20; full Content equality cannot follow from run equality. First and later false obtained payloads preserve events; both valueless tags have no event. |
| X04 | Constant-true C08 gives T on obtained-at-w1/replayed-at-w0. A current-world-sensitive nucleus gives F there and T at w1. Empty replay at w1 stays F under arbitrary supplied toy predicate. |
| X05 | Nat-indexed profiles: at the same source world profile 0 is Empty and profile 1 Obtained. One payload has F/T fibres, not an existential profile verdict. |
| X06 | Reads retain every caller state by the universal law. Capture retains caller bindings/sides and appends only the nucleus side, fixes context while raw reuse changes it, and uses saved partial resolver results at arbitrary tuples. First execution has exactly one source side plus one nucleus side. |
| X07 | `firstHost` runs the payload from its source state and finalizes it. `nextSource` consumes that returned assignment: binding 0 gives one alternative, binding 1 gives two; missing/other bindings give Dead/Undef. Dependent children and grandchildren carry actual terminal-membership proofs; every child fibre is nonempty. Read/Bind/composed pullback laws hold. The supplied grandchild source uses the retained binding, not the second source's returned value; no extra dependence is claimed. |
| X08 | Concrete legal frame with prior F/F record and current T/T record: cumulative κ/χ remain F; old history and ordered side prefix are retained. |

Hand-authored data: the illustrative source predicate, ground assignments/sides,
event labels, Boolean nucleus predicates, opaque handles, and the later-source
interpretation are explicit toy inputs. No control chooses behavior by its test
name. The general carrier/read/reindex/capture/finalizer path is shared by all
these tests and its universal theorems; it has no finite fixture-domain bound.

## Verification and isolation

Run from the repository root:

```sh
bash pilot/lean/check-f02.sh
```

This builds only `SmusniF02`, then runs `F02Audit.lean`. Existing default Lake
targets are unchanged. Lean remains pinned to **4.33.1**; no dependency was added
and the existing Plausible pin is untouched (F02 does not import it).

The check passes: **102 explicitly authored theorems**, **619 audited declarations**,
**301 theorem declarations including generated lemmas**. Those latter two counts
describe the compiler environment, not independent semantic claims. The transitive
axiom union is exactly **`propext`, `Classical.choice`, `Quot.sound`**. The audit
enumerates declarations by their defining F02 module (including private/generated
helpers), rejects declared project axioms and any other transitive axiom, rejects
unsafe F02 definitions, and rejects production `SmusniPilot` imports. It therefore
rejects `sorryAx` and native-decide trust rather than accepting a text search.
The script prints each theorem's axioms and SHA-256 identities of the checked
source/toolchain/build/check files. There is no imported desired-law axiom.

`bash -n pilot/lean/check-f02.sh` and `git diff --check` pass. Production
AST/typing/source normalization, oracles, coverage and performance baselines,
normative documents and the shared main checkout are untouched. No root suite,
old 13366/593/236 Python controls, full migration run or performance baseline
was rerun merely to reconfirm unrelated evidence. No global document audit or
formal-authority transfer is claimed.

## Provenance and remaining obligations

The construction is derived from the Astra/High F02-v2 design, not invented by
this implementation. Durable design copy and comparison provenance:
[#10, revised v2](https://github.com/int19h/smusni/issues/10#issuecomment-5641841739).
PM's addressed release and the #10 current body authorize this auxiliary proof
task after Fable/Medium, Kimi/Max and Grok4.6/XHigh's focused ACCEPTs; they do not
adopt a full model. The Fable finite-support clarification, Kimi source/event
axis distinction and Grok C08 distinction are reflected in the definitions and
controls above, as recorded in v2 §9.

Live sources read: merged spec §§5.1–5.2, 5.4, 7.1.1, 7.4, 9.1, the relevant
§9.3 table/laws and §14 gaps; PM's current consensus overlay; MECHANIZATION;
MODEL_REPAIR; COUNTEREXAMPLES C1/C2/C4/C12/C17/C18. MODEL_REPAIR is historical
proposal evidence, not authority for its superseded failed-state or holding/event
equations. The older consensus “F02 design-only/implementer parked” checkpoint is
superseded **only for this task** by the addressed release and current #10 body.

Author files read in full, under
`/home/int19h.linux/work/smusni-fullpass3-astra/review/`:

| File | SHA-256 |
|---|---|
| `f02/F02-REVISED-v2.md` | `d3ccb6f22f4cdd1e910d2f0dcacadf6ddce82611a817431f57020c17a92a3101` |
| `f02/origin_fibres_v2.py` | `51781fb6d12ecfddc58eb3fcfa7baaf3f38f07ba9a10ea98d0297ec8f969193b` |
| `f02/origin_fibres.py` | `0519021ae3ef67ce5902551def84e2c788202f012b4a2db92c3f34baf25565a1` |
| `f01/read_laws_v3.py` (imported definitions) | `af7379aca0e7f24f573b2debfdb73418087b9f5eb10249f5152120450b9495b5` |

Still **not constructed or proved**, and not hidden behind axioms:

1. A simultaneous Henkin/state/Proposition family closed under proposition-valued
   assignments, full higher-order operations and every constructor, with the
   contextual congruence and Reify/Holds round trips. No quotient is constructed
   here, local or global; local equivalence/congruence lemmas are ingredients only.
2. A general source evaluator or a proof that RefComp typing establishes the
   supplied source/scope/frame interfaces. No general RR/source factoring,
   multi-description failure or stronger whole-source-reopening equality.
3. A general event branch algebra, holding/State/situation ontology, holding-joint
   compatibility, event-Bind associativity, or total `EventOfContent` reconciling
   valueless fibres with its object-language signature. The local partial rule
   preserves a supplied event interface; it does not construct that interface.
4. General occurrence allocation/transcript selection, all forces, effectful
   guards, accommodation, topic transitions, or closure of full information-state
   operators that couple alternatives. No production lowering/runtime bridge.

No unmet theorem was replaced with an assumption of itself. The requested local
laws are proved at their declared supplied-ground domains; the larger obligations
above retain their original scope. This is a checkpoint for PM's Astra-first,
then Fable/Kimi/Grok review, not review clearance or closure of #10.
