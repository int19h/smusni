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

## Declarative relation and theorems

`M2TypingJudgment.lean` is the Prop-valued A0 relation. Its mutually inductive
`SynthJudgment`, `CheckJudgment`, `ApplyJudgment`, positional/row/lexical
argument judgments, and primitive rule classes contain no fuel, search order,
or stored executable equality. The supported rule IDs are selected from the
generated 107-rule manifest; every other manifest record is returned by
`unsupportedTypingRuleRecords` rather than silently defaulted.
The present proved relation slice covers 33 generated rule records and lists
74 exclusions; this is a theorem-domain statement, not a claim that the
executable checker implements only those 33 records.

`M2TypingBridge.lean` proves relation-to-executable completeness by one mutual
constructor induction. The checking companion is generated from that exact
recursor/handler proof term, so internal recursive checks and public
`checkBidirectional` cannot drift into two handwritten proof paths. On the
relation-supported domain, `synth` and `checkBidirectional` are characterized
in both directions. The public priority theorem exposes the three cases:
compatible synthesis gives `fromSynth`; incompatible synthesis gives the named
`type-mismatch` without fallback; synthesis failure invokes exactly the shared
expected-clause interpreter. It also proves synthesis/checking observation
functionality, synthesis-type uniqueness, judgment-relative wrong-type
failure, purity, computation category, and the five-effect bound.

`M2Relation.lean` now states definition side conditions through those typing
judgments (`PurePropertyJudgment`, `ReferenceMemberJudgment`, and
`DecompositionBasisJudgment`), not calls to `synth`. `TemplateEquation` remains
Prop-valued and existential over derivations. The proved interface has both
directions on the supported core dispatcher domain
(`dispatch_sound_against_template` and `declarative_dispatch_complete`) and
relation functionality without dispatcher-success assumptions.
`SupplementalTemplateEquation` covers the Let, Refer-member-lift, Grade, and
JaiRaise leaves. The recursive surface decoder/state allocator is explicitly
outside the converse theorem: its template leaves are related, but the report
does not promote decoding/control-flow equivalence to a semantic theorem.

The hand-authored template RHSs in `M2Templates.lean` are the declarative
content transcribed clause by clause from the generated manifest ranges; the
dispatcher is proved to produce those RHSs. They are not fixture-keyed output
records. Concrete unseen `ActualClause` and natural-typing instantiations in
`M2Examples.lean` exercise both relation directions and the structural typing
constructor directly.

There are no `sorry`, `axiom`, or `admit` declarations.

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

The RR adoption audit decodes all 29 pinned RR fixtures: 32 linked cases,
13 declared sites, 26 operand sites, 16 comparable cases (8 agreement and
8 mismatch), and 16 unavailable cases. These report-only results are not the
former 135/0 self-consistency claim.

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
  Let/Refer-member/Grade/JaiRaise template-leaf relations only.
- Final exact-head reviewer dispositions are not yet recorded here.
