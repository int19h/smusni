# Lean pilot milestone 2 report

Status: **candidate gates pass; exact-head review pending.** PR #82 fixed the
Redex oracle defect in #81 and is included through main merge `dc6eaee`.

## Mechanism

The M2 path consumes a `SurfaceTerm`, the canonical corpus environment, the
generated lexical-row/core-constant inputs, an expected type supplied by the
surrounding binder where required, and an explicit occurrence context
`(document, structural ordinal, definition ID)`. It resolves a selected
definition ID from generated manifest records, recursively applies its cited
template clauses, allocates expansion sites from the occurrence context, runs
fail-closed bidirectional typing, and replays the term/metadata/allocation
certificate through M1's proof-producing `Bundle.checked` constructor to obtain
`ValidatedBundle 0`/`BundleCoherence`.

No S1 case ID selects an output. Case IDs provide document identity and join
the corpus to the S1 manifest. No corpus surface string is matched. The
hand-authored data on the path is:

1. the definition templates in `SmusniPilot/M2Templates.lean`, transcribed
   from the manifest's live ranges; and
2. the semantic typing clauses itemized by
   `M2_TYPING_SUPPLEMENT.tsv` where the frozen A0 rule set does not cover the
   v1.2 all-S1/recursive-expansion scope.

## Generated inputs

- `M2_DEFINITION_MANIFEST.json`: 28 selected definitions = 19 a0/ported,
  3 plan-v2 extras, 6 declared dependency-closure definitions; 34 clauses;
  one selected definition domain. It carries ledger/spec/supplement digests,
  the full 85-definition disposition catalog, and the reviewed `Close → CoRef`
  dependency supplement. Template certificates reject a clause outside the
  root definition's transitive declared closure.
- `M2_TYPING_MANIFEST.json`: 107 rules = 78 frozen A0/B1 rules plus 29 cited
  M2 rules; 21 generated core constants; 50 generated lexical fixture rows;
  seven pinned Redex grammar categories. `FirstOrderPrimitive` has no success
  catch-all.
- `M2_CASE_MANIFEST.json`: generated partition of all 337 S1 cases: 160
  definition-parity, 3 Grade/Jai corpus extras, 50 M1 primitive baseline, 93
  residual pending, 31 out-of-slice. The 160 is computed as pending-M2 cases
  with a nonempty defined-head set wholly contained in the generated 19-head
  a0/ported set.
- `M2_REDEX_ORACLE.sexp`: generated from the corrected frozen A0/B1 definition
  metafunctions. It contains 118 honest term targets and 42 explicit
  oracle-unavailable dispositions; no unavailable target is called exact.

The PR #82 typing regeneration changes five semantic rule bodies:
`A0-T-DirectClause-{Pure,Effectful}` and
`A0-T-ActualClause-Event-{Pure,Effectful}` preserve `Fn`/`EFn`, while
`A0-T-CloseClause` exposes the conservative EFn call. `A0-T-CloseWith` and
the apply/synth/check records move only because their source ranges shifted.

All generators run in check mode from `check-m2.sh` and fail on stale output.

## Definition coverage

All 28 selected IDs have general templates. The path handles all declared
clauses, including zero/positive `AtLeast` and `Exactly`, all three
type-directed `Close` rows, structurally recursive equal-length `ZipWith`, the
`Refer` member-property overload, the `Massify → CanonicalAggregateAt →
CompleteGunmaAt → GunmaAt → CoRef` closure, `ActualClause`, and
`DirectClause`.

`Grade` is a pure row-directed schema consuming an explicit `DegreeField`;
`JaiRaise` consumes explicit row reconstruction/projection metadata. Bare jai
has its distinct constrained-`Context` mapping. Synthetic unseen gates cover
both. The positive corpus Jai case remains `input-unavailable` because S1 does
not carry its row reconstruction metadata. `RowOf zzzz` is instead the named
`unknown-row` typed rejection, with an unseen unknown-row gate.

## Current all-S1 result

At the rebased review candidate:

- typed unchanged: 31;
- successful type-directed expansion: 122;
- typed rejection: 60;
- pending milestone 3: 48;
- selected-domain blocked: 10;
- input unavailable: 1;
- out of slice: 65.

These are final case dispositions, not a claim that every typed rejection
failed before expansion. In the 50-case M1 primitive baseline: 31 are typed
unchanged, one is a final successful expansion, and 18 are typed rejections.
Both pure member-level `Refer` occurrences expand; `58c6...` then fails the
enclosing `SetOf` purity rule. `2b3c...` fails `refer-member-purity` and
`61a28...` stays reference-level primitive.

Those four v1.2 Refer cases are hard assertions, not printed observations:
`58c6... = typedRejection/set-property` after the member lift,
`58da... = typeDirectedExpansion/generated definition-domain overload`,
`2b3c... = typedRejection/refer-member-purity`, and
`61a28... = typedUnchanged/bidirectional typing`, including exact expanded-ID
lists. The public member checker and elaborator require an exact member domain
and an effect-free property construction; subsort and construction-effect
mutations have direct unseen gates.

## Declarative relation and theorems

`M2TypingJudgment.lean` is the Prop-valued A0 relation. Its mutually inductive
`SynthJudgment`, `CheckJudgment`, `ApplyJudgment`, positional/row/lexical
argument judgments, and primitive rule classes contain no fuel, search order,
or stored executable equality. The supported rule IDs are selected from the
generated 107-rule manifest; every other manifest record is returned by
`unsupportedTypingRuleRecords` rather than silently defaulted.
The proved relation slice covers 58 generated rule records and lists 49
exclusions. Measured in each case's actual environment, all 31 available
unchanged-input typings and all 153 successful output typings have traces
wholly inside that theorem domain. No excluded ID occurs in a successful S1
output trace. The gate emits every remaining excluded ID individually with the
reason “not observed in a successful S1 output trace”; those records remain
outside the full 107-rule manifest, but not outside the measured S1 slice.

`M2TypingBridge.lean` proves relation-to-executable completeness by one mutual
constructor induction. The checking companion is generated from that exact
recursor/handler proof term, so internal recursive checks and public
`checkBidirectional` cannot drift into two handwritten proof paths. The old
`SynthSupported`/`CheckSupported` characterization has been removed: assuming
that the declarative relation was already inhabited was circular evidence for
executable-to-relation soundness.

`M2TypingSoundness.lean` proves the missing direction on an independent
manifest domain. `TypingManifestSupported result.trace` is only the Boolean
claim that every rule ID emitted by the successful executable result is in the
58-rule implemented manifest slice; it does not mention or assume a typing
judgment. `synth_success_sound` takes executable success plus that trace fact
and constructs `SynthJudgment ... result.observation`. The proof follows the
mutual executable recursion through named handlers for expected checks,
reference and Presuppose checks, primitive schemas, function application and
partial application, PredTerm application, synthesis/check argument lists,
lexical rows, and value operands. Lean-generated `caseNNN` names are dispatch
glue only; the semantic proofs live in those named handlers.

The S1 gate checks the same manifest predicate for all 31 available unchanged
inputs and all 153 successful outputs; theorem
`typingTraceSupported_instantiates_soundness` turns each passing Boolean check
into the exact premise of `synth_success_sound`. Removing one observed rule
from the predicate is a required failing mutation. Thus the 153/153 output
count now instantiates executable-to-relation soundness rather than merely
reporting that traces avoid a list of exclusions.

The public priority theorem exposes the three checking cases:
compatible synthesis gives `fromSynth`; incompatible synthesis gives the named
`type-mismatch` without fallback; synthesis failure invokes exactly the shared
expected-clause interpreter. It also proves synthesis/checking observation
functionality, synthesis-type uniqueness, judgment-relative wrong-type
failure, purity, computation category, and the five-effect bound.

Expected-only Presuppose is classified recursively by
`expectedOnlySynthesisForm`; its declarative counterpart includes recursive
Presuppose bodies. Direct structural theorems and runtime regressions cover a
nested expected-only body, a nested ordinarily synthable body, and a mutation
that accepts every binary Presuppose. The soundness proof additionally exposed
that `predTermArgumentResults` accepted a second labelled `:Eventuality` while
the judgment permits only one. The executable now rejects that duplicate with
`predterm-row`, and an explicit regression exercises the unseen duplicate.

`M2Relation.lean` now states definition side conditions through those typing
judgments (`PurePropertyJudgment`, `ReferenceMemberJudgment`, and
`DecompositionBasisJudgment`), not calls to `synth`. `TemplateEquation` remains
Prop-valued and existential over derivations. The proved interface has both
directions where the relation is inhabited (the domain premise is
`∃ expectedPayload, TemplateEquation ...`) via
`dispatch_sound_against_template` and `declarative_dispatch_complete`, and
relation functionality without dispatcher-success assumptions.
`SupplementalTemplateEquation` covers typed Let and Refer-member-lift leaves.
Grade and JaiRaise were removed from the coverage claim: their synthetic
`GradePlan`/`JaiRaisePlan` values still exercise executable templates, but no
independent judgment validates those plans. The recursive surface decoder/state
allocator is likewise outside the converse theorem.

Three `TemplateEquation` families still carry executable-equality premises:
`close`/`directClause` use `typedClosePlan` (and `expandClose` for Close), and
`zipWith` uses `termAsList`/`expandZipWith`. The other 22 constructors use
typing judgments for semantic side conditions. This is a declared proof gap,
not covered by the sentence above.

The hand-authored template RHSs in `M2Templates.lean` are the declarative
content transcribed clause by clause from the generated manifest ranges; the
dispatcher is proved to produce those RHSs. They are not fixture-keyed output
records. Concrete unseen `ActualClause` and natural-typing instantiations in
`M2Examples.lean` exercise both relation directions and the structural typing
constructor directly.

There are no `sorry`, `axiom`, or `admit` declarations.
`#print axioms synth_success_sound` reports only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`; the proof carries no `native_decide`
oracle axioms.

## Expansion sites and certified bundles

`TooMany` is the required site-introducing specimen. It allocates a purpose
`Context` and threshold `Vague`; the Vague support contains the ordered bound
purpose dependency. The site key uses document/case identity, structural
occurrence ordinal, definition ID, and expansion role/slot. Gates cover:

- identical key → identical pair;
- distinct copied occurrence → distinct pair;
- distinct roles within one occurrence → distinct pair;
- alpha/renaming invariance;
- canonical/bracket-insensitive reserialization invariance; and
- one lambda occurrence shared by two applications → one syntactic pair.

`Grade` introduces no site. Bare jai introduces its one constrained Context.
`buildElaborationBundle` takes the primitive term, RR metadata, allocation
certificate, source map, and RR link and returns M1 `ValidatedBundle` only if
occurrence/table/profile coherence is proved. The version-1 serialized `site`
dependency tag remains decodable but is rejected as a semantic profile;
internal `Dependency.site` is absent.

The RR adoption audit decodes all 29 pinned RR fixtures and searches for an
injective structural embedding of the declared dependency graph in the emitted
Context/Vague graph. Declared RR role names label fixture nodes and are used
only to preserve edges under the injection; they are not matched to emitted
`SiteRole` or `SiteId.expansionRole` names. Extra emitted nodes are retained as
undeclared origins rather than mismatches.
Computed-minimum `Close/default-*` sites are excluded from embedding candidates
and can appear only as undeclared emitted origins.
Across 32 linked cases it sees 13 declared roles and 26 emitted operand sites:
6 declared roles match, all 6 matched dependency lists agree, 7 declarations
remain unmatched, and 20 emitted sites are undeclared (principally
expansion-introduced `Close/default-*` sites). Three cases with declarations
have all roles matched; 16 cases have an emitted term and 16 are unavailable.
All seven unmatched declarations belong to unavailable cases with no emitted
term; no declaration fails to embed in a comparable case.
The gate prints a per-case table with matched roles, dependency results,
missing declarations, and undeclared emitted origins. These report-only
results replace both the former 135/0 self-consistency claim and the uninformative
8/8 length comparison.

Non-zero per-case RR results (the gate also prints all 19 zero rows):

| case | fixture | declared/matched/dep-ok | missing roles | undeclared emitted origins |
| --- | --- | --- | --- | --- |
| `1089e6` | `samples-023#1` | 0/0/0 | — | `Close/default-:2,:3,:4,:5` |
| `250874` | `samples-063#3` | 1/1/1 | — | — |
| `29cfac` | `samples-027#1` | 1/0/0 | `group-basis` | — |
| `302aef` | `samples-071#1` | 0/0/0 | — | `Close/default-:3` |
| `3979ff` | `samples-058#1` | 1/0/0 | `tanru-link` | — |
| `3e12ed` | `samples-063#1` | 2/0/0 | `scale`, `cutoff` | — |
| `411d8a` | `samples-034#1` | 1/0/0 | `group-basis` | — |
| `428f27` | `samples-072#1` | 0/0/0 | — | `Close/default-:3` |
| `433ec3` | `samples-048#1` | 1/0/0 | `threshold` | — |
| `519c65` | `samples-001#1` | 0/0/0 | — | `Close/default-:2,:3,:4,:5` |
| `5f5b05` | `spec-019#1` | 0/0/0 | — | two `Close/default-:3` occurrences |
| `7668b7` | `samples-036#1` | 0/0/0 | — | `Close/default-:2` |
| `a2dc10` | `samples-059#1` | 1/0/0 | `contrast-domain` | — |
| `ae0905` | `samples-063#2` | 2/2/2 | — | `Close/default-:2,:3,:4,:5` |
| `c27acb` | `spec-009#1` | 0/0/0 | — | `Close/default-:2,:3,:4` |
| `ec2d5f` | `spec-010#1` | 3/3/3 | — | — |

Causes for every unmatched declared role (also printed in the gate):

- `group-basis` in `29cfac`/`samples-027#1` and
  `411d8a`/`samples-034#1`: no M2 term is emitted because the cases are
  `outOfSlice` at M1 structural/offending-head provenance.
- `tanru-link` in `3979ff`/`samples-058#1`: no M2 term is emitted because
  `D6.2.Tanru` is pending M3; its fills-parameterized expansion has not reached
  the Redex port.
- `scale` and `cutoff` in `3e12ed`/`samples-063#1`, and `contrast-domain` in
  `a2dc10`/`samples-059#1`: no M2 term is emitted because unselected `D5.1.That`
  is a metatheory/model-law out-of-slice head.
- `threshold` in `433ec3`/`samples-048#1`: no M2 term is emitted because the
  selected definition domain is blocked (`definition-domain`).

## Parity result

The gate compares (1) alpha-normal CoreTerms after SiteId erasure and lexical
row-label normalization, and (2) ordered `(site kind, binder scope,
dependency support)` signatures. After PR #82 correction and regeneration:

- generated cohort: 160;
- honest Redex term targets: 118;
- explicit oracle-unavailable: 42;
- comparable successful Lean terms: 118;
- term matches: 118;
- site-signature matches: 118;
- differences: 0.

Every available target is compared. The 42 unavailable targets are 33 Redex
definition/domain exclusions, 6 missing `Close` row adapter inputs,
1 `Refer-member-lift` (`port-state none`), 1 unavailable typed Massify basis,
and `731809...`, whose Redex purity-oracle defect is tracked in #83. These are
dispositions, not waivers.

The three corpus extras remain separate: the two Grade cases (`3e12...`,
`71ab...`) also contain unselected model-context `That`, so they do not acquire
an exact Grade oracle merely because the pure explicit-row synthetic gate
passes; the positive Jai case (`9ef0...`) is the sole `input-unavailable` case
because S1 lacks row reconstruction metadata. Synthetic Grade, JaiRaise,
bare-jai, TooMany, and unseen Refer/row gates pass. Grade/Jai/Refer term
expansion is never called exact where the ledger has `port-state none`.

## Timing

On this VM after `lake clean`:

- `lake build m2`: 21.04 s wall, 1,712,684 KiB maximum RSS;
- `lake exe m2`: 0.29 s wall, 129,228 KiB maximum RSS;
- full `check-m2.sh` including generators/oracle/build/run: 9.85 s wall in
  the recorded incremental run (338,584 KiB maximum RSS).

## Explicit limits

- Only the manifest-selected definition/domain slice is complete. Symbolic
  `AtLeast`/`Exactly` expansion and unequal-length `ZipWith` remain their
  recorded blocked/unselected domains; pending-M3 heads are not in the
  completeness claim.
- Fixture lexical rows remain pilot-only pending #12; place-row shape and
  event mode are consumed, and missing named rows fail closed.
- The 42 oracle-unavailable parity cases retain the explicit reasons above.
- The converse relation theorem covers `dispatchDefinition`; recursive surface
  decoding/state allocation has a deliberately narrower claim, with explicit
  typed Let/Refer-member template-leaf relations only.
- The measured S1 theorem domain covers 31/31 available input typings and
  153/153 successful output typings. The other 49 manifest rules remain
  explicit, individually reported non-S1 exclusions.
- Final exact-head reviewer dispositions are not yet recorded here.
