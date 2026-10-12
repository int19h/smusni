#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build Smusni97
lake env lean Issue97Audit.lean
for prototype_fixture in StateSort DeadArgument ScrubExport ReviewedScrub OpaqueScrub; do
  if prototype_output=$(lake env lean "issue97-negative/$prototype_fixture.lean" 2>&1); then
    echo "FAIL issue97: accepted $prototype_fixture" >&2
    exit 1
  fi
  if ! [[ "$prototype_output" == *'Type mismatch'* || "$prototype_output" == *'Application type mismatch'* ]]; then
    echo "$prototype_output" >&2
    echo "FAIL issue97: unexpected failure in $prototype_fixture" >&2
    exit 1
  fi
  echo "PASS issue97 negative: $prototype_fixture"
done
