#!/usr/bin/env bash
# A1 only. No production suite, F03-B import, or A2 implementation.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build SmusniF03A1 F03A1AuditSupport
lake env lean F03A1Audit.lean
f03a1_audit_tmp=$(mktemp -d /tmp/smusni-f03a1-audit.XXXXXX)
mkdir "$f03a1_audit_tmp/SmusniF02"
f03a1_lean_path=$(lake env printenv LEAN_PATH)
for f03a1_fixture in UnsafeOpaque PrivateUnsafeOpaque SafeOpaque; do
  lake env lean --root=audit-fixtures \
    -o "$f03a1_audit_tmp/SmusniF02/$f03a1_fixture.olean" \
    "audit-fixtures/SmusniF02/$f03a1_fixture.lean"
done
lake env env LEAN_PATH="$f03a1_audit_tmp:$f03a1_lean_path" lean \
  f03a1-audit-fixtures/AcceptSafeOpaque.lean
echo "PASS F03-A1 positive audit: SafeOpaque accepted"
for f03a1_fixture in UnsafeOpaque PrivateUnsafeOpaque; do
  if f03a1_rejection=$(lake env env LEAN_PATH="$f03a1_audit_tmp:$f03a1_lean_path" lean \
      "f03a1-audit-fixtures/Reject$f03a1_fixture.lean" 2>&1); then
    echo "FAIL F03-A1: audit accepted $f03a1_fixture" >&2
    exit 1
  fi
  if ! [[ "$f03a1_rejection" == *'F03-A1 has unsafe semantic declaration:'*'unsafeOpaque'* ]]; then
    echo "$f03a1_rejection" >&2
    echo "FAIL F03-A1: $f03a1_fixture failed for an unexpected reason" >&2
    exit 1
  fi
  echo "PASS F03-A1 negative audit: $f03a1_fixture rejected for unsafe declaration"
done
echo "F03-A1 isolated audit fixtures: $f03a1_audit_tmp"
sha256sum SmusniF03A1.lean SmusniF03A1/*.lean F03A1Audit.lean F03A1AuditSupport.lean \
  f03a1-audit-fixtures/*.lean audit-fixtures/SmusniF02/*.lean check-f03a1.sh lakefile.toml lean-toolchain
