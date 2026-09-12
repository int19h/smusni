#!/usr/bin/env bash
# Isolated auxiliary target; run from any directory. No production suites.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build SmusniF02
lake env lean F02Audit.lean
# Identify precisely the source bytes checked, without storing generated baselines.
sha256sum SmusniF02.lean SmusniF02/*.lean F02Audit.lean check-f02.sh lakefile.toml lean-toolchain
