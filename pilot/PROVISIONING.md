# Step −1 provisioning report

Scope: issue #74 pilot plan v2, Step −1 only. The normative documents and
`tools/smusni-redex/` are read-only inputs. These projects are provisioning
smokes, not semantic encodings and not evidence that a candidate passes the
later full slice.

## Host and repositories

- Host: Linux ARM64 VM; 105 GiB free before provisioning.
- opam: 2.3.0. Repositories, in priority order:
  `coq-released=https://coq.inria.fr/opam/released`, then
  `default=https://opam.ocaml.org`.
- Isabelle source: official Isabelle2025-2 ARM bundle from the Cambridge
  Isabelle mirror,
  `https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2025-2_linux_arm.tar.gz`.
  Published and verified SHA-256:
  `650a9669b4a087675afb34294d82ded2f0704d47d580dd9ed45cddc9f1764bdd`.

## Lean

Pinned files: `pilot/lean/lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`.

- Lean 4.33.1, commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Lake 5.0.0.
- Plausible commit
  `b7eb3304aeae834b12dda98993a37f6a41f6f0bb`. This is the newest Plausible
  commit pinned to the Lean 4.33 line before its 4.34.0-rc1 bump; its own
  toolchain names Lean 4.33.0, and it compiles under the installed 4.33.1 patch.
- No Mathlib dependency.

Mechanism: `Main.lean` defines an inductive `SmokeToken`, a decidable Boolean
predicate, evaluates it, runs Plausible on the supported built-in `Nat`
generator, and builds/runs a native executable.

Observed commands/times:

- `lake update`: 22.39 s wall (included Plausible clone and Lean component
  resolution).
- First dependency build: 4.17 s wall, failed only at the initial custom-type
  Plausible proposition because `deriving Arbitrary` did not by itself provide
  the quantified `Testable` instance.
- Corrected successful incremental build: 1.25 s; executable run: 0.22 s.
- Subsequent clean build with the dependency checkout present: 4.86 s.
- Output: Plausible reported no counterexample; executable printed
  `allowed=true; blocked=false`.

The custom-type generation boundary is recorded rather than filled with a
hand-written instance; Step −1 requires a Plausible run, not a general
custom-type generator.

## Rocq tuple

Pinned direct dependencies are in `smusni-pilot-rocq.opam`; the full installed
closure is in `.opam.locked`.

Joint constraint intersection consulted from the active package registries:

- `rocq-autosubst-ocaml.1.1+9.0`: OCaml `>=4.09,<4.15`, Rocq core
  `>=9.0,<9.1`;
- `rocq-equations.1.3.1+9.0`: Rocq runtime `>=9.0,<9.1`, stdlib and
  compatibility core;
- `coq-quickchick.2.2.0`: OCaml `>=4.07`, compatibility Coq `>=8.15~`;
- compatibility `coq.9.0.1`: core 9.0.1 and stdlib 9.0.0.

Thus the newest jointly supported maintained tuple is:

- OCaml 4.14.2;
- Rocq runtime/core 9.0.1 and stdlib 9.0.0;
- Coq compatibility packages 9.0.1 / stdlib 9.0.0;
- Equations 1.3.1+9.0;
- Autosubst-OCaml 1.1+9.0 (Autosubst 2 implementation);
- QuickChick 2.2.0.

Rocq 9.1 and 9.2 are not joint candidates because the published Autosubst
package excludes `>=9.1`; no version pin was patched around.

Provisioning times: opam initialization 7.90 s; OCaml 4.14.2 switch creation
61.98 s; 57-package tuple installation 229.23 s.

Composition smoke, one project:

1. `autosubst` consumes `SmokeSyntax.sig` and generates a genuinely scoped
   de Bruijn binder syntax plus renaming/substitution and lemmas. `Smoke.v`
   checks generated `subst_tm` and `idSubst_tm`.
2. Equations defines `smokeFlip`; the build checks its actual generated
   `smokeFlip_equation_1` and `smokeFlip_elim` induction principle.
3. QuickChick 2.2.0 uses the installed commands `QCDerive Show` and
   `QCDerive Arbitrary`; `QuickChick smokeChoiceTotal` passes 10,000 tests with
   zero discards in 0.005985 s. The initial plan-level `Derive Show` spelling
   failed and was corrected to the real API.
4. Rocq extraction emits `smoke_extract.ml`; OCaml compilation takes 0.02 s,
   and the runner prints `extractedSmoke(41)=42`.

The first combined Rocq build took 1.14 s and stopped at the unsupported
`Derive Show` command after Autosubst and Equations had already compiled. The
corrected `Smoke.v` build took 0.95 s. Deprecation warnings from QuickChick's
Coq namespace compatibility layer are retained in the log; they did not block
composition. A subsequent complete generated-source/Smoke/extraction build and
runner invocation took 1.44 s.

## Isabelle

- Isabelle2025-2 (January 2026), official ARM bundle; no external Nominal2.
- Installed outside the checkout at
  `/home/int19h.linux/.local/isabelle/Isabelle2025-2`.
- Download 128.96 s; archive extraction 12.39 s.

`Smoke.thy` defines a three-representative raw carrier with two quotient
classes, proves the equivalence relation, creates `quotient_type content`,
lifts `class_of`, proves the quotient is nontrivial, and runs Nitpick with
`expect = genuine` against the false one-class conjecture.

The first 4.96 s build exposed literal-Unicode source syntax; the second 6.19 s
build exposed two incomplete quotient proofs. After replacing source symbols
with Isabelle escapes and supplying the missing function-extensionality and
explicit witnesses, the successful build took 5.37 s. Bundled quotient/lifting
and Nitpick compose. `HOL-Nominal` was deliberately not tested, per the plan.

## Reproduction and limits

Run `./pilot/check-provisioning.sh` with the pinned external toolchains. The
script regenerates Autosubst output and diffs it byte-for-byte before compiling
the combined Rocq smoke. Its warm full three-platform run took 5.23 s.

Not done generally in Step −1:

- no platform encodes Smusni semantics yet;
- no shared S1–S7 artifacts are implemented here;
- no general Lean custom-type generator was added;
- no Rocq Step-0 typing relation or relation-derived generation was attempted;
- no Isabelle `HOL-Nominal` smoke or Step 0′ carrier screen was attempted;
- build/install timings are provisioning evidence, not later candidate runtime
  metrics.
