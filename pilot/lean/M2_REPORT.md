# Lean pilot milestone 2 report

Status: **implementation in progress; parity blocked by #81 until PR #82 is
merged and the oracle is regenerated.** This file is not a PASS report yet.

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
- `M2_REDEX_ORACLE.sexp`: generated from the frozen A0/B1 definition
  metafunctions. Before #81 correction it contains 120 honest term targets and
  40 explicit oracle-unavailable dispositions; no unavailable target is called
  exact.

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

At pushed M2 head `ce1cd7c` plus the uncommitted Close-effect alignment with PR
#82:

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

`M2Relation.lean` defines `TemplateEquation`, an independently inductive
relation with a constructor for each executable definition family/case; it is
not defined as `elaborate = ok`. `DeclarativeElaboration` combines that
equation evidence with template-certificate, typing, and executable-agreement
evidence. The current proved interface includes declarative soundness,
executable completeness for a certified derivation, and exact executable
output functionality (therefore stronger than uniqueness up to alpha/site
allocation for a fixed key).

`M2Typing.lean` proves:

- wrong-expected-type failure for the public bidirectional checker;
- purity classifier soundness/completeness;
- computation-category classifier soundness and completeness through a
  dependent certificate; and
- the conservative five-name effect bound for every `TypingResult`.

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

## Parity status

The gate compares (1) alpha-normal CoreTerms after SiteId erasure and lexical
row-label normalization, and (2) ordered `(site kind, binder scope,
dependency support)` signatures. Before Redex correction, the 160 cohort had
120 oracle targets, 119 comparable Lean terms, 54 term matches, 55 site
matches, and 129 differences. All 129 were mechanically attributed to #81;
unexplained differences were zero. The cause is Redex's stale outer placement
of `Close` default binds, versus live §4.6's placement inside the event
property. PR #82 corrects Redex; this report will replace these blocked counts
with the regenerated exact result after merge.

## Limits still to close

- Merge/rebase PR #82 and rerun the full parity cohort.
- Record final plan-extra oracle availability/type-only results.
- Record the RR declaration/emitted-site adoption audit counts.
- Record literal build/run timing and final exact-head reviewer dispositions.
- Request exact-head review only after the above gates are green.
