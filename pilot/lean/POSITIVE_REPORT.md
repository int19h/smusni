# Positive recursive-code experiment

## Result and authority

This derived Lean experiment implements the bounded construction released under [issue #10](https://github.com/int19h/smusni/issues/10#issuecomment-6143863904).
Issue #10 remains unfinished.
The experiment does not establish a model of the full adopted theory.
It changes no normative document, production engine, oracle, or semantic policy.

The source is Astra's `POST-F03-POSITIVE-CONSTRUCTION-v2.md`, with 556 lines.
Its SHA256 is `7c0c738fdebb3c65ffc2dbfdb1c7a7c3483a737ae22f89120d3dfe459bc2db3e`.
The durable full copy is Collab message `msg_20261013T104250979668Z_9ae4ccb14cfc43718b87f28925ae17f4` in project `smusni`.
PM released implementation in `msg_20261013T104815326547Z_d5f1bc53aa354f1cbeea0c5baf3d065f` after the focused Opus and Grok reviews.
PM approved the formal size statement below in `msg_20261013T105955580426Z_e4cec89b54ab4e4aa0ec8b4a17b62c18`.

The construction draws on Grok's reduced-code proposal and Opus's corrected event construction, as recorded in the source paper.
It uses Astra's positive signed judgments and direct derivation induction.
The paper preserves the individual proposal, correction, and review message references.
These sources motivate this experiment, but they do not establish baseline adequacy or adopt its semantic choices.

## General mechanism

A closure is a typed term with finite captured environments.
`Signature` supplies ground values, names, keys, predicates, and finite site and predicate arities.
Those four types share universe `u`.
The world type has an independent universe `v`.
`Model.lexical` supplies a total Boolean interpretation of each predicate at a world and ground tuple.

`Term sig m n` distinguishes `m` ground variables from `n` proposition variables.
Its constructors cover top, bot, atoms, negation, Holds, context retrieval, slot read, and both universal quantifiers.
The paper's `PropTerm` has variable and Reify forms.
`holds` translates these forms to `holdsVar` and `holdsReify` without an additional semantic rule.
`Code` captures every entry of both finite environments, including unused entries.

Raw assignments use the actual F02 `HostState` with proposition slots containing codes.
Its remaining payload types are `Unit`, but the state fields remain present.
Contexts map every declared key and ground tuple to an optional code.
Worlds, contexts, and assignments are external inputs, not captured code labels.

`Evidence` defines positive inductive T/F derivations for every constructor.
Universal true premises quantify over the entire ground or code domain.
False premises supply a counterexample from that same domain.
No U derivation exists.
The readout chooses U exactly when neither signed derivation exists.

`EventEvidence` separately defines partial event observations.
Top, bot, atom, negation, allG, and allP return their own closure token.
Holds, context retrieval, and slot read copy the selected body's event.
The event input has an assignment independent of the run assignment.
Failed retrieval and pure ungrounded copying produce no event.

The definitions handle arbitrary well-typed inputs of these forms.
They contain no fixture table, source-string match, or list of expected observations.
Supplied lexical interpretations are model data, and the atom rule consumes their predicate, world, and evaluated tuple arguments.
The L/J and infinite-chain constructions are controls outside the general interpretation path.

The logical readout is noncomputable.
Classical choice also selects event witnesses and quotient representatives.
This is a mathematical construction, not a terminating evaluator for arbitrary recursive inputs.

## Proof ledger

All paths below are relative to `pilot/lean`.
A kernel is an equivalence induced by equal outputs.
A quotient groups values under an equivalence.
Descent makes an operation independent of the chosen representative.

### Gate 1: formation and environments

`SmusniPositive/Syntax.lean` defines `GroundTerm`, `Term`, `PropTerm`, `Code`, `extend`, `evalProp`, and `evalGround`.
Arity-indexed argument functions prevent malformed tuples.
Finite binder indices prevent free variables outside the declared environments.
`GroundTerm.eval_rename` relates renaming to environment substitution.

`SmusniPositive/Weakening.lean` proves `extend_comp`, `evalGround_rename`, `rename_value`, `rename_event`, and `rename_rj`.
`weakenG_rj` and `weakenP_rj` establish observational preservation after environment extension.
The proofs preserve both truth and event classes, not only term typing.

### Gate 2: evidence and readout

`SmusniPositive/Evidence.lean` defines the actual one-step rule operator `Step`.
`evidence_fixed` proves its fixed-point equation.
`least_prefixed` proves leastness among arbitrary prefixed relations.
A prefixed relation contains every consequence of its own premises.
The theorem assumes neither consistency nor a finite stage bound for the competing relation.
It uses no continuity assumption about countable unions.

`sign_unique` and `consistent` prohibit simultaneous T/F derivations.
`SmusniPositive/Readout.lean` proves exact T/F/U characterizations and every constructor equation.
The `value_allG_*` and `value_allP_*` families contain all three universal readouts.
Their domains are full supplied types, not finite sample lists.

`SmusniPositive/Run.lean` constructs singleton outcomes with the actual F02 tags and unchanged states.
`ctx_strict_bind` and `read_strict_bind` prove the actual F02 lookup and strict sequencing equations.
`neg_run` proves pointwise strong-Kleene negation.
`run_profile_kernel` equates complete run equality with the completed status relation `Rv`.

### Gate 3: truth respect

`SmusniPositive/Respect.lean` defines `Reclose`, `InputRel`, and `EvidenceSound`.
The soundness premise relates observations at the same raw input only.
`evidence_transport` generalizes the partner closure and input before induction on a signed derivation.
It proves transport through every constructor, including both quantifiers and retrieval forms.

The Holds-variable case first transports the same stored code through its reflexively related environment.
It then replaces that code by its related partner at the destination input through fixed-input soundness.
`holds_variable_bridge` states this route explicitly.
`evidence_transport_iff` uses the proved closure and input symmetries for the reverse direction.
`value_transport` transfers the result to completed truth values.

### Gate 4: partial events

`SmusniPositive/Events.lean` proves `event_functional` from the inductive event rules.
`event_some` and `event_none` characterize the chosen readout through the evidence relation.
The constructor equations prove both defined values and absence.
`EventStep` and `event_least_prefixed` supply a separate leastness theorem for event derivations.

`event_evidence_transport` transports event evidence across related closures and inputs.
`event_transport` preserves both the event class and partial definedness.
The reverse direction uses symmetry, so the result also preserves absence.
`reclose_rv` and `reclose_rj` derive environment congruence from these arguments.

Observable tokens are classes of `Rv`, which compares completed status profiles at every raw input.
They are not classes of the stronger joint relation `RJ`.
Raw code tokens remain representation data.
For default rows, `default_rj_iff_rv` proves that the two relations coincide.

### Gate 5: all input domains

`SmusniPositive/Descent.lean` constructs `qS`, `qE`, and the independently named `qB`.
The six `*_kernel` and `*_onto` theorems establish their equivalences and coverage.
`qS` and `qB` use the actual A1 state map.
`qE` maps the optional result at every key and ground tuple.
It does not restrict the domain to tuples visited by a term.

`selected_run_input` and `selected_event_input` separately relate the selected raw representatives to the supplied coordinates.
`denotation_run_at` and `denotation_event_at` prove complete computation equations on those coordinates.
`all_inputs_covered` covers contexts and both independent state coordinates.
`denotation_kernel` proves equality of the full descended content exactly when `RJ` holds.

`RJ` combines actual status profiles with `PartialEq Rv` on partial events at every raw event input.
The construction uses F02 observations, A1 state maps, and A2 joint/event helpers where their types apply.
A2's fixed-index map alone does not supply the new context or event-assignment descent.

### Gate 6: admitted domains and inverses

`SmusniPositive/Descent.lean` defines `Proposition = Code/RJ`.
`SmusniPositive/Admission.lean` defines `Admitted = image(denotation)`.
`holds_reify_inverse` and `reify_holds_inverse` prove the two experimental inverse laws on these domains.
`language_holds_reify`, `language_reify_holds`, and `language_holds_prop` connect them to actual language forms.
The admitted domain does not contain every mathematical respectful function or unrestricted run.

`interpretTerm_at` makes interpretation independent of the proposition environment representatives.
`representedBody_at` and `representedBody_env` prove the represented proposition-body equations and environment independence.
`admitBody` and `admitGroundBody` construct the two image-restricted body families.
They do not construct full higher-order function domains.

`bodyValue_at` and `body_observation_at` connect class-indexed bodies to code bodies and observations.
`allP_true_classes`, `allP_false_classes`, and `allP_undefined_classes` prove quantifier descent over the whole proposition quotient.
The earlier raw-code quantifier proofs do not assume this later descent.

### Gate 7: conditional controls

`SmusniPositive/Controls.lean` requires an explicitly supplied key of arity zero for L and J.
`retrieval_condition_inhabited` proves that a constant resolver can satisfy the required retrieval condition.
`liar_undefined` gives L status U at every world and run state when that key returns L.
`liar_event` gives a defined event at every independent event assignment under the same condition.

`liar_token_global` separately equates the body holding token with the literal negation token under `Rv` at all raw inputs.
It has no self-resolver premise.
`liar_observable_event` combines that global result with conditional event retrieval.
`liar_top_resolver` gives status F when the key returns top.
`liar_absent_resolver` gives U and no event when the key is absent.
Thus L's U result is not universal over all resolvers.

`j_no_evidence` and `j_no_event_evidence` establish absence under a resolver that returns J.
Their consequences are `j_undefined` and `j_absent_event`.
`double_neg_same_runs` proves equal raw runs for any code and its double-negation Holds wrapper.
`j_double_neg_distinct` separates their joint classes through events at the self-returning resolver.

`top_neg_bot_same_class` identifies top with neg(bot) in this witness.
`top_bot_distinct` separates top and bot with an explicit inhabited-world assumption.
These results do not establish a null-unit law or a complete event ontology.
Most generic proofs need no world inhabitant, but this nondegeneracy witness does.

`SmusniPositive/Chain.lean` supplies a separate signature with `Ground = Nat` and one unary key.
`chain_codes_injective` proves distinct addresses produce distinct raw codes.
`ChainRegion` includes both each context closure and its intermediate Holds closure.
`chain_no_evidence`, `chain_no_event_evidence`, and `chain_observations` cover every address, world, and independent assignment.
Only this control requires the declared infinite address supply.

## Size proof and its limit

The pinned Init/Std libraries provide no `Cardinal` or `aleph0` interface.
Mathlib is not a declared dependency, and this experiment adds no dependency.
PM therefore approved finite-word and quotient-section injections as the formal gate.

`SmusniPositive/Coding.lean` defines `Alphabet = Nat ⊕ G ⊕ N ⊕ K ⊕ Pred`.
The alphabet contains no `Code` label.
`codeTree` retains constructor tags, binder counts and indices, arity-indexed arguments, and every entry of both captured environments.
`codeTree_injective` proves that this representation distinguishes actual typed codes.

`treeWords` converts those finite trees to finite words.
Its stack decoder proves `treeWords_roundtrip`.
`encode_injective` then proves the injection from all actual codes into `List Alphabet`.
The decoder proves a tree round trip, not a separately claimed typed-code parsing theorem.

`representative_section` proves that the class map recovers every class from its chosen code.
`representative_injective` supplies the injection from `Code/RJ` into `Code`.
These are Lean theorems for the actual domains, not fixture counts.

Standard set-theoretic arithmetic for finite words gives the following consequence outside Lean's formal library:

```text
|P| <= |Code| <= max(aleph0, |G|, |N|, |K|, |Pred|).
```

This report claims no Lean `Cardinal` theorem, unconditional countability, or cardinal equality.
The bound does not establish adequacy or closure under unrestricted functions.

## Additional controls

`SmusniPositive/IntegrationControls.lean` records additional probes as permanent proofs.
These controls are separate from the implementation path.
They cover the following inputs and distinctions:

- `lexical_world_and_ground_consumed` varies worlds and captured ground arguments against supplied lexical data.
- `all_ground_uses_entire_domain` and `all_propositions_not_finite_samples` use actual full-domain counterexamples.
- `independent_event_assignment` uses a top run slot, a bot event slot, and an absent event slot.
- `full_tuple_context_not_visited_cache` separates contexts beyond one agreeing tuple.
- `context_representatives_identify` identifies different but equivalent resolver representatives.
- `encoding_retains_unused_environments` distinguishes codes with unused captured proposition values.

## Excluded obligations

The experimental grammar is exhaustive for this target, but it is not the full pilot grammar.
No omitted pilot constructor receives a default U interpretation.
No global F03-B `RunLaws` instance is supplied.
The following obligations remain outside this experiment:

- Conjunction, disjunction, and joint operations.
- Holding fusion, null-unit laws, event actuality, event verification, `StateClause`, and `CloseClause`.
- Object-language equality and `CoRef`.
- Full higher-order `Fn`/`EFn` domains and their application and abstraction closure.
- Capture, `RealizedContent`, and proposition-dependent context tuples.
- Ground-valued assignment slots.
- Mutation, general nondeterminism, projectives, other forces, profiles, and issue #11 policy.

Least evidence and the treatment of ungrounded absence as U remain experimental choices.
Total Holds into admitted content does not imply truth-total evaluation.
The experiment does not settle the stronger reading of spec §9.3 law 5 or supply an actuality equation.
It makes no formal-authority transfer or semantic adoption claim.

## Reproduction and audit

The target uses `leanprover/lean4:v4.33.1` and the unchanged dependency manifest.
The existing Plausible revision is `b7eb3304aeae834b12dda98993a37f6a41f6f0bb`.
From `pilot/lean`, run `bash check-positive.sh`.
The script builds only `SmusniPositive`, its imported foundations, and `PositiveAuditSupport` before the isolated audit fixtures.
It prints SHA256 values for the audited sources, harness, fixtures, toolchain, and Lake configuration.

The aggregate target imports thirteen experiment modules.
`PositiveAuditSupport.lean` audits all declarations under the `SmusniPositive` module prefix, including private and generated declarations.
It rejects unsafe declarations and new axioms within that scope.
Its transitive axiom allowlist contains only `propext`, `Classical.choice`, and `Quot.sound`.
It rejects pilot/F03-B imports and the named historical control targets.

The completed run passes with 771 declarations and 386 theorem declarations, including generated lemmas.
The transitive axiom set contains only the three allowed foundational axioms.
The safe opaque fixture passes.
Both public and private unsafe opaque fixtures fail for the expected unsafe-declaration reason.
The aggregate build emits no warnings.
From the repository root, `python3 tools/check-docs.py .` passes with no missing documents, links, pins, or term-balance failures.
`git diff --check` reports no whitespace errors.

No historical production suite is rerun or counted as new evidence.
The only existing tracked-file edit adds two Lake targets.
The new code, audit harness, controls, and report form the delivery.
The PR and durable handoff record the exact delivered commit and repository documentation result.

## Review disposition

This report requests exact-head code review, not merge or baseline adoption.
Astra reviews first under the PM release.
Opus and Grok review after that gate clears.
The implementer waits for PM's combined disposition before corrections.
