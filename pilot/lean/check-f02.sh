#!/usr/bin/env bash
# Isolated auxiliary target; run from any directory. No production suites.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build SmusniF02 F02AuditSupport
lake env lean F02Audit.lean
# Compile fixtures outside the regular library/build search path. Keep this
# bounded temporary directory for inspecting a failure; it contains no user data.
f02_audit_tmp=$(mktemp -d /tmp/smusni-f02-audit.XXXXXX)
mkdir "$f02_audit_tmp/SmusniF02"
f02_lean_path=$(lake env printenv LEAN_PATH)
for f02_fixture in UnsafeOpaque PrivateUnsafeOpaque SafeOpaque; do
  lake env lean --root=audit-fixtures \
    -o "$f02_audit_tmp/SmusniF02/$f02_fixture.olean" \
    "audit-fixtures/SmusniF02/$f02_fixture.lean"
done
lake env env LEAN_PATH="$f02_audit_tmp:$f02_lean_path" lean \
  audit-fixtures/AcceptSafeOpaque.lean
echo "PASS F02 positive audit: SafeOpaque accepted"
for f02_fixture in UnsafeOpaque PrivateUnsafeOpaque; do
  if f02_rejection=$(lake env env LEAN_PATH="$f02_audit_tmp:$f02_lean_path" lean \
      "audit-fixtures/Reject$f02_fixture.lean" 2>&1); then
    echo "FAIL F02: audit accepted $f02_fixture" >&2
    exit 1
  fi
  if ! [[ "$f02_rejection" == *'F02 has unsafe semantic declaration:'*'unsafeOpaque'* ]]; then
    echo "$f02_rejection" >&2
    echo "FAIL F02: $f02_fixture failed for an unexpected reason" >&2
    exit 1
  fi
  echo "PASS F02 negative audit: $f02_fixture rejected for unsafe declaration"
done
echo "F02 isolated audit fixtures: $f02_audit_tmp"
# Identify precisely the source bytes checked, without storing generated baselines.
sha256sum SmusniF02.lean SmusniF02/*.lean F02Audit.lean F02AuditSupport.lean \
  audit-fixtures/*.lean audit-fixtures/SmusniF02/*.lean check-f02.sh lakefile.toml lean-toolchain
