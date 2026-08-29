# Step 0 Rocq/QuickChick kill-test report

## Outcome

**FAIL.** QuickChick 2.2.0 derives a producer and `DecOpt` checker from the
actual packed, two-mode, record-valued relation without any rule-specific
generator. The corrected producer-only diagnostic covers every encoded rule
in checking mode but misses `A0-T-SelectExactly` in synthesis mode. The
required producer-plus-derived-checker path is not operational:
the synthesis run exhausts an 8 GiB virtual-memory bound before completing one
20,000-case result. Generic shrinking also fails scope preservation, and
derivation-preservation checking exhausts the same memory bound.

This does not admit Rocq to the full pilot slice. Producer-only numbers below
are diagnostic and are not presented as a passing validated run.

## Mechanism

`Step0.v` defines one mode-indexed relation:

```text
a0_type : env -> direction -> typed_case -> Prop
typed_case = (term, typing_record, rule trace)
typing_record = (type, effect set, obligation set)
```

The relation consumes its environment, expected type in checking mode,
recursive subderivations, computed compatibility, computed positive-count and
equality-domain premises, and the correlated child records. De Bruijn lookup
is a derived auxiliary relation. `Context` uses a recursive spine and therefore
handles any number of synthesized arguments; `SelectExactly` checks an
arbitrary count term at `Natural` before applying the computed positivity
predicate. Effects are duplicate-eliminating and canonicalized in the live
alphabetical order (`context`, `effectful-call`, `refer`). Obligations are
deduplicated, but this subset has no nonempty obligation origin; full canonical
obligation ordering is explicitly deferred rather than invented here.

QuickChick derives:

- the `env_lookup` producer/enumerator/checker;
- the `a0_type` producer and `DecOpt` checker;
- synthesis and expected-type-parameterized checking wrapper producers and
  checkers.

The run samples the expected type with the generic `ty` instance and then asks
the derived checking-mode producer for a case. It does not use a table of
checkable expected types. Failed expected-type requests are counted as
discards.

The public tuple-output command cannot express the three correlated outputs in
this toolchain: `TupleOutputProbe.v` reproducibly raises QuickChick's internal
`depDriver.ml` pattern-match anomaly. Packing the outputs is a general
representation workaround, demonstrated independently by
`RecordOutputProbe.v`; it does not introduce a second per-rule generator.

## Hand-authored component inventory

| Class | Component | Rule-specific? |
|---|---|---:|
| generic base | `purity`, bounded `ty`, `effect`, opaque `obligation`, `term`, equality/`Dec`, and QuickChick `Show`/`Arbitrary`/`Shrink`/`EnumSized` instances | no |
| generic base | canonical effect-set union and duplicate-eliminating obligation union | no |
| mode infrastructure | packed `typed_case`; manual record/case `Show`; structural term shrink that retains the correlated record and trace | no |
| mode infrastructure | `env_lookup`; mode-indexed `a0_type`; synthesis/checking wrappers; trace masks; scope/depth observers | no |
| rule-specific generator | none | n/a |

The rules themselves and their output clauses are hand-authored because they
are the relation being tested, not generator code. QuickChick generates the
producer and checker from those clauses. No constructor frequency or
per-rule sampler was supplied.

## Literal results

Final warm core compilation (`coqc Step0.v`) took 1.53 seconds with 514,744
KiB maximum RSS. The producer-only runner took 186.76 seconds wall time in
total, dominated by checking-mode discards. These build/runner figures are
kept separate from the per-checker elapsed times below.

### Required full validation path

Command:

```sh
./run-bounded.sh RunValidation.v
```

The script sets `ulimit -v 8388608` and a 300-second wall limit. Result:

```text
QuickChecking synth_generated
Time Elapsed: 14.266917s
Fatal error: out of memory
maxresident: 7,460,860 KiB
exit: 1 (native runner status 134 / SIGABRT)
```

The final fixed configuration is 20,000 successes, 100,000 maximum discards,
and maximum size 7.

The reviewer-requested low-fuel control also fails on the corrected head:

```sh
SMUSNI_STEP0_RSS_LIMIT_KIB=4194304 ./run-bounded.sh RunFuelProbe.v
```

At derived-checker fuel 8 and a 300-case budget it exhausts the 4 GiB bound in
15.988962 seconds (`maxresident: 3,712,544 KiB`, exit 1 / native status 134).

### Producer-only diagnostic

Command:

```sh
opam exec --switch smusni-pilot-rocq -- coqc RunGeneration.v 2>&1 | tee generation.log
python3 analyze.py generation.log
```

The literal analyzed run was:

| Metric | synthesis | checking |
|---|---:|---:|
| result | PASS | GAVE_UP |
| successes | 20,000 | 19,999 |
| discards | 0 | 100,000 |
| discard ratio | 0 | 0.833340 |
| maximum binder depth | 6 | 6 |
| elapsed | 13.750749 s | 170.967962 s |
| cases/minute | 87,267.97 | 7,018.51 |

Case coverage counts presence of a rule in a generated case's complete
recursive trace, not raw constructor occurrences:

| Manifest rule | synthesis cases | checking cases |
|---|---:|---:|
| `A0-Synth` | 20,000 | n/a |
| `A0-Check` | n/a | 19,999 |
| `A0-T-Natural` | 12,918 | 16,829 |
| `A0-T-Top` | 12,158 | 16,460 |
| `A0-T-Variable` | 375 | 754 |
| `A0-T-Lambda-Pure` | 8,417 | 15,824 |
| `A0-T-Lambda-Effectful` | 4,133 | 13,012 |
| `A0-T-Check-Synth` | 289 | 2,376 |
| `A0-T-Context` | 9,510 | 19,406 |
| `A0-T-SelectExactly` | 0 | 1 |
| `A0-T-SelectSome` | 3 | 11 |
| `A0-T-Bind-Reference` | 9,333 | 16,071 |
| `A0-T-Apply-Pure` | 1,143 | 4,853 |
| `A0-T-Apply-Effectful` | 289 | 1,624 |
| `A0-T-Equality` | 1,871 | 7,062 |

The producer reaches both expected-only selections in checking mode and
`SelectSome` under recursive synthesis through annotated `Bind`, without
per-rule weights. It fails to reach `SelectExactly` in synthesis mode at the
fixed budget, so complete per-mode manifest coverage fails.
The checking-mode outer generator misses the 20,000-success target by one case
at the disclosed discard ceiling.

### Shrinking

`RunScopeShrinking.v`, 2,000 requested successes per mode, maximum size 7:

| Property | Result | Literal stop |
|---|---|---:|
| synthesis scope preservation | FAIL | 76 tests, 0 discards |
| checking scope preservation | FAIL | 3 tests, 12 discards |

`./run-bounded.sh RunDerivationShrinking.v`:

```text
QuickChecking synth_derivation_preserving_shrinks
Time Elapsed: 13.388851s
Fatal error: out of memory
maxresident: 7,460,856 KiB
exit: 1
```

Therefore derivation-preserving shrinking is **FAIL**, not unmeasured success;
the derived checker cannot validate the generic structural shrinks within the
pilot's resource bound. No rule-specific shrinker was added.

### Negatives and representation probes

- Kernel examples construct a two-argument `Context` and a positive
  `SelectExactly` under annotated `Bind` on the general relation.
- Kernel proofs reject the wrong expected type, zero-count `SelectExactly`, an
  unbound de Bruijn variable, and plural-reference self-equality inside a
  closed lambda.
- A term-level mixed-effect regression proves that a source-order `refer` then
  `context` merge is recorded canonically as `[context, refer]`.
- `RecordOutputProbe.v` compiles, proving the packed-output producer derives on
  a recursive correlated relation.
- `check-tuple-probe.sh` passes only when the documented tuple-output command
  fails with the expected QuickChick `depDriver.ml` anomaly.

## Generality and explicit omissions

The general path handles unseen arbitrary compositions over the selected term
and type universe, not a fixture table. It reads every declared field in that
slice and computes its result record and trace from recursive inputs.

It does **not** claim full A0:

- the 40 rules in `MANIFEST.md` remain omitted;
- the selected `Apply` rules use the unary instance of live variadic
  application, so full application arity is not implemented here;
- the bounded compatibility universe implements equality, `Natural <:
  Number`, and unary `Fn <: EFn`, not every live A0 type constructor;
- no selected rule originates a nonempty obligation, so obligation propagation
  is represented but nonempty obligation generation is outside this subset;
  full nonempty obligations require the same canonical-set treatment as
  effects rather than the insertion-preserving deduplication used here;
- no valid relation-preserving shrinker was obtained.

These are limitations of the kill-test slice and are not counted as completed
full-rule migration.

## Gate disposition

- Relation-derived producer, no per-rule generator mirror: **PASS for the
  encoded slice**.
- Required producer-plus-derived-checker execution: **FAIL (memory)**.
- Checking-mode fixed success budget: **FAIL (19,999/20,000 at discard cap)**.
- Every encoded rule reached in producer-only diagnostics: **FAIL** because
  synthesis misses `A0-T-SelectExactly`; checking reaches every encoded rule.
- Scope-preserving shrinking: **FAIL**.
- Derivation-preserving shrinking: **FAIL (memory)**.
- Full Step 0 admission gate: **FAIL**.

## Repository verification

- `coqc Step0.v`: PASS, including the positive and negative kernel examples.
- `RecordOutputProbe.v`: PASS.
- `check-tuple-probe.sh`: PASS by reproducing the expected tool anomaly.
- corrected fuel-8/300-case control: expected FAIL at the 4 GiB bound.
- `tools/check-smusni`: PASS, 1,827 tests.
- `pilot/check-provisioning.sh`: PASS for all three pinned toolchains.
- `review/checks.py <worktree>`: links, balances, and pins PASS.
- `git diff --check`: PASS.
