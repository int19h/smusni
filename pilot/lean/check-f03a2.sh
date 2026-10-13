#!/usr/bin/env bash
# A2 over the reviewed general A1 modules. No production suites.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build SmusniF03A2 F03A2AuditSupport
lake env lean F03A2Audit.lean
f03a2_audit_tmp=$(mktemp -d /tmp/smusni-f03a2-audit.XXXXXX)
mkdir "$f03a2_audit_tmp/SmusniF02"
f03a2_lean_path=$(lake env printenv LEAN_PATH)
for f03a2_fixture in UnsafeOpaque PrivateUnsafeOpaque SafeOpaque; do
  lake env lean --root=audit-fixtures \
    -o "$f03a2_audit_tmp/SmusniF02/$f03a2_fixture.olean" \
    "audit-fixtures/SmusniF02/$f03a2_fixture.lean"
done
lake env env LEAN_PATH="$f03a2_audit_tmp:$f03a2_lean_path" lean \
  f03a2-audit-fixtures/AcceptSafeOpaque.lean
echo "PASS F03-A2 positive audit: SafeOpaque accepted"
for f03a2_fixture in UnsafeOpaque PrivateUnsafeOpaque; do
  if f03a2_rejection=$(lake env env LEAN_PATH="$f03a2_audit_tmp:$f03a2_lean_path" lean \
      "f03a2-audit-fixtures/Reject$f03a2_fixture.lean" 2>&1); then
    echo "FAIL F03-A2: audit accepted $f03a2_fixture" >&2
    exit 1
  fi
  if ! [[ "$f03a2_rejection" == *'F03-A2 has unsafe semantic declaration:'*'unsafeOpaque'* ]]; then
    echo "$f03a2_rejection" >&2
    echo "FAIL F03-A2: $f03a2_fixture failed for an unexpected reason" >&2
    exit 1
  fi
  echo "PASS F03-A2 negative audit: $f03a2_fixture rejected for unsafe declaration"
done
echo "F03-A2 isolated audit fixtures: $f03a2_audit_tmp"
sha256sum SmusniF03A2.lean SmusniF03A2/*.lean F03A2Audit.lean F03A2AuditSupport.lean \
  f03a2-audit-fixtures/*.lean audit-fixtures/SmusniF02/*.lean check-f03a2.sh lakefile.toml lean-toolchain
