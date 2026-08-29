#!/usr/bin/env bash
set -euo pipefail

pilot_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
rocq_switch=${ROCQ_SWITCH:-smusni-pilot-rocq}
isabelle_bin=${ISABELLE_BIN:-}

if [[ -z "$isabelle_bin" ]]; then
  if command -v isabelle >/dev/null 2>&1; then
    isabelle_bin=$(command -v isabelle)
  else
    isabelle_bin=/home/int19h.linux/.local/isabelle/Isabelle2025-2/bin/isabelle
  fi
fi

echo "== Lean/Plausible =="
(
  cd "$pilot_root/lean"
  lean --version
  lake --version
  lake update
  lake build
  lake exe smoke
)

echo "== Rocq tuple/composition =="
opam exec --switch "$rocq_switch" -- rocq --version
rocq_tmp=$(mktemp -d /tmp/smusni-pilot-rocq-smoke-XXXXXX)
trap 'rm -rf -- "$rocq_tmp"' EXIT
opam exec --switch "$rocq_switch" -- \
  autosubst "$pilot_root/rocq/smoke/SmokeSyntax.sig" \
  -o "$rocq_tmp/Generated.v" -s rocq -f
diff -u "$pilot_root/rocq/smoke/core.v" "$rocq_tmp/core.v"
diff -u "$pilot_root/rocq/smoke/fintype.v" "$rocq_tmp/fintype.v"
diff -u "$pilot_root/rocq/smoke/Generated.v" "$rocq_tmp/Generated.v"
(
  cd "$pilot_root/rocq/smoke"
  opam exec --switch "$rocq_switch" -- coqc core.v
  opam exec --switch "$rocq_switch" -- coqc fintype.v
  opam exec --switch "$rocq_switch" -- coqc Generated.v
  opam exec --switch "$rocq_switch" -- coqc Smoke.v
  opam exec --switch "$rocq_switch" -- \
    ocamlc smoke_extract.mli smoke_extract.ml smoke_driver.ml -o smoke_driver
  ./smoke_driver
)

echo "== Isabelle quotient/lifting/Nitpick =="
"$isabelle_bin" version
"$isabelle_bin" build -D "$pilot_root/isabelle" -v

echo "provisioning smoke: ok"
