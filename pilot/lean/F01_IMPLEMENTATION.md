# F01 — direct source-form formation, binding and typing

Source input: `3e45db536c8523d023f70ae25878a3ecb9f79663`, PM's merge of
the accuracy-cleared F01 source with adopted P45 (`01759ba`). Work branch:
`work/f01-encoding-20260911`; the previous E02 branch at `13d2672` is preserved.
Authority: #13 and addressed PM release
`msg_20260911T201227910018Z_44cccb2bc8e34485a4ecd00df619e4fd`.
This is derived structural encoding, not semantic authority transfer.
It checks constructor syntax, lexical scope and typing clauses, not full
admission to §7.1.1's semantic fragment: source eligibility premises remain
outside the current executable input representation.

## Mechanism

The input is an arbitrary direct `PerformSource` term and its declared typing
environment, with the resolved source/frame/continuation supplied by the
caller. The output is a scoped AST, source-site/dependency information and a
typing result or an explicit rejection. No surface string, corpus identifier,
source outcome, or expected output is used to choose the result.

The direct constructor retains S at depth n, C1 at n+1, and D at n+2. x binds
only C1; read/o bind only D, with o at de Bruijn index 0 and read at index 1.
It normalizes the documented omitted-Host spelling and requires literal Host
and Assert. Typed descriptors are checked before their redundant information
is removed from the Lean constructor. Existing outer spellings remain legal;
read/o cannot use the same spelling in their joint scope.

Racket's syntax adapter, free-variable checks, alpha comparison, capture-
avoiding substitution and site/dependency walks preserve these three scopes.
The opaque B2 compiler also retains the binder identities in its three arms;
its restricted typing judgment is not widened. The pure-position guards mark
the new source/Host former as introducing/effectful.
An independent lexical check prevents Context/Vague metadata from concealing
an unbound variable. Elaboration preserves the whole already-resolved C1
subtree, including inert nested Act values; the ordinary force-shorthand
wrapper applies only outside that boundary. There is no strict-Bind expansion.

Lean's Core, typed interchange, byte interchange, decoder, surface elaborator,
renaming, substitution and bundle operations retain the same structure. The
generic binding/interchange/bundle-coherence proofs include the new constructor.
The corpus adapter reads both Racket's dotted atomic-type association pairs
and proper compound-type entries, with malformed-dot rejection controls; it
does not mistake the supplied environment type for a dot type constructor.
Site IDs are not minted by the binder: the original ordered Context/Vague sites
and their scope-indexed dependencies are traversed once per syntactic arm.
RR dependency traversal is structural provenance, not executable source factoring.

Typing checks R = Referents<T>, S : RefComp<R>, C1 : Content under x:R and
D : Discourse under read:RefComp<R>/o:ActOccurrence<Assertion>. No Unknown or
inference-gap result discharges the new Racket rule. The Lean rule has an
independent declarative judgment and actual checker completeness/soundness
bridges. Ordinary Perform (implicit and explicit role) also now has judgment
and bridge coverage; Racket validates and propagates the explicit role's
typing result. No prior proved rule was removed from the theorem domain.

## Source and population accounting

The eight semantic documents are unchanged from the released combined input.
Fences and candidate/RR/parse joins were moved by exact source content digest,
not paired by ordinal. One new core specimen is added; the previous final
five sample fences shift by one. The two affected current RR/parse pairs are
relocated, and their original bytes are preserved under `../history/pre-f01/`.
No RR or surface-lowering success is attributed to the new core specimen.

E02's reports, manifests, supplements, oracle and corpus are archived from
Git by `../shared/archive_pre_f01.py`. The old E02 migration generator now
reproduces that historical checkpoint without changing its population checks.
The separate `../shared/build_f01_migration.py` joins every old and current
term/environment pair, and records tag/cohort/oracle status on both sides.
At the current regenerated input, all 370 E02 inputs are retained exactly and
34 new inputs are added (404 total); the definition-parity cohort remains 192.
New negative controls are explicitly classified, never hidden by a denominator
or oracle-admission change. See `../shared/F01_MIGRATION.json` for each case.
All 32 existing A0 waivers retain their fields, findings and reasons; their
case IDs move only through exact corpus/lowering term-and-environment matches.
The four benchmark term/environment inputs were checked unchanged. Only the
baseline's corpus-digest link is transported: its original head, measurements,
runs, term count and thresholds are retained. The migration gate checks that
no performance measurement or threshold was changed.

The corpus now contains 96 fences, 79 specimen fences and 100 typed specimen
terms. L8.13 is an additional documentary mapping, not a newly executable
surface-factoring path: its uncovered #9 ledger entry preserves the existing
69-cited-rule ratchet. All existing equation bodies are retained; source ranges
and digests are rebased to the combined input. PerformSource is primitive and
lowering-only in the declaration inventory, with no equation to manufacture.

## Controls and verification

New Racket controls cover literal/omitted Host, force/arity/annotations, all
three scopes (including metadata), outer shadowing, nested forms, alpha and
capture-avoiding substitution, site ordering, whole-C1 preservation, and the
unchanged successful two-source outer-Bind route. Lean controls cover seven
positive typed/roundtrip paths, malformed and ill-typed paths, alpha/Host
identity, nested/collection-valued cases and exact n/n+1/n+2 site depths.
The M1 generator adds 64 arbitrary scoped three-arm serialization controls;
those deliberately ill-typed forms are not typing or model evidence.

Commands below passed on the implementation tree recorded by this checkpoint.

- `tools/check-smusni`: exit 0; 8 Python documentation controls and 3,531 Racket
  tests, including 65 focused F01 controls. The 404-case plumbing differential
  has zero differences/waivers. The independent A0/B1 comparison retains 114
  cases (78 corpus, 29 mechanisms, 7 lowering subterms), all 32 existing waivers,
  zero differences/stale waivers, and 81/81 witnessed rules. All 31 eligible
  lowering cases match/type-check; one pre-existing unresolved source case remains.
- `bash pilot/lean/check-m1.sh`: exit 0; 404 surface/text round trips, 67
  primitive-core decodes/canonical round trips, 287 pending-M2 and 50 out-of-slice
  inputs; 367 generated round trips (the old 303 plus 64 new scoped forms).
- `bash pilot/lean/check-m2.sh`: exit 0; 113 exporter assertions, 7 positive
  F01 typed/roundtrip paths and 26 rejections, P45 controls, all 18 production
  consumer mutations and both positive refinements pass. There are 111 typing
  rule records: 62 proved relation rules and 49 explicit exclusions. All 203
  successful outputs have proved typing (203/203). Across all 404 outcomes:
  42 unchanged, 161 expanded, 63 rejected, 48 pending M3, 6 blocked,
  1 input-unavailable and 83 outside the M2 slice. These are not the same
  partition as M1's raw input classification.
- Independent M2 parity is unchanged at **74/192**: 54 whole-A0 plus 20
  one-Assert bridge targets, 118 non-admissions. All 74 target terms/sites match,
  with zero differences. F01 success is not added to this oracle denominator.
- `python3 pilot/shared/build_f01_migration.py`, the historical E02 migration
  check, archive reproduction, documentation checks and `git diff --check` pass.

Local run logs: `/tmp/f01-root-checkpoint.0DOr6Y.log` and
`/tmp/f01-lean-env.Iwnrjx.log`; the durable results are recorded here and on #13.
The final report-anchor change uses generated source ranges and is additionally
checked with `lake build m2` and `lake exe m2`.
After a whitespace-only fixture cleanup, the corpus/source hashes were
regenerated and the 65 focused controls plus both full M1/M2 commands passed
again with identical counts (`/tmp/f01-final-metadata.2eMnJC.log`).

Limits/warnings: the existing report-only A0 size-growth trigger remains:
depths 16/32/64 took 61.457/334.342/1688.234 ms, ratios 5.440/5.049 against
the unchanged 4x limit. The four-term benchmark's other triggers pass; full-gate
wall time was not instrumented, so no full-wall comparison is claimed. Redex's
satisfying-generation facility remains unavailable for the existing pattern
(ellipses/context/side-condition limitation); fixture and mutation checks are
not relabelled as random generation. Lean emits existing lint warnings; there
are no project assumptions or proof holes. No baseline was reset.

## Explicit non-results

The code does not execute S, construct the shared source family/read pair,
allocate a Host occurrence, replay a failed-source fibre, compute acceptance,
or prove a run/event quotient model. Finiteness, total restriction, one
independently exportable source, legal sides/scopes and acyclic preparation
remain supplied semantic eligibility premises; RefComp typing and a count of
Refer nodes cannot certify them. Source-site preservation is not RR factoring.

Full failure-aware Comp/capture/quotient embedding, coupled EventOfContent
definedness (#10), general source factoring (#9), multisource failure, effectful
guards, other forces, accommodation/topic transitions and Presuppose F1
reconciliation remain outside this tranche. The auxiliary 236-check finite
model is not copied into this engine or counted as a full evaluator. The
closed A0 oracle is not widened to accept PerformSource contexts; successful
M2 typing of the direct form is not independent A0 or model parity.
