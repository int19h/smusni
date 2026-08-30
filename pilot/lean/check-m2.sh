#!/usr/bin/env bash
set -euo pipefail

task_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(cd "$task_dir/../.." && pwd)

cd "$repo_root"
python3 pilot/shared/build_m1_constructor_matrix.py
python3 pilot/shared/build_m1_s1_manifest.py
python3 pilot/lean/build_m1_inventory.py
python3 pilot/shared/build_m2_definition_manifest.py
python3 pilot/shared/build_m2_typing_manifest.py
python3 pilot/lean/build_m2_inventory.py

if rg -n '\b(sorry|axiom|admit)\b' pilot/lean -g '*.lean'; then
  echo "Lean M2 contains a forbidden assumption" >&2
  exit 1
fi

cd "$task_dir"
lake build m2
lake exe m2
