#!/usr/bin/env bash
set -euo pipefail

task_dir=$(cd "$(dirname "$0")" && pwd)
probe_log=$(mktemp)
trap 'rm -f "$probe_log"' EXIT

cd "$task_dir"
if opam exec --switch smusni-pilot-rocq -- \
    coqc TupleOutputProbe.v >"$probe_log" 2>&1; then
  echo "tuple-output probe unexpectedly derived" >&2
  exit 1
fi

if ! rg -q 'depDriver\.ml.*Pattern matching failed' "$probe_log"; then
  echo "tuple-output probe failed for an unexpected reason" >&2
  sed -n '1,160p' "$probe_log" >&2
  exit 1
fi

echo "tuple-output probe: expected QuickChick depDriver anomaly reproduced"
