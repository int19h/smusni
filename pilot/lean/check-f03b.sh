#!/usr/bin/env bash
# Isolated F03-B proofs. The typing witness imports actual pilot judgments.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build SmusniF03B F03BAuditSupport
lake env lean F03BAudit.lean
# Reuse the existing F02 audit fixtures through the actual F03-B audit path.
# Keep the bounded temporary directory to support failure diagnosis.
f03b_audit_tmp=$(mktemp -d /tmp/smusni-f03b-audit.XXXXXX)
mkdir "$f03b_audit_tmp/SmusniF02"
f03b_lean_path=$(lake env printenv LEAN_PATH)
for f03b_fixture in UnsafeOpaque PrivateUnsafeOpaque SafeOpaque; do
  lake env lean --root=audit-fixtures \
    -o "$f03b_audit_tmp/SmusniF02/$f03b_fixture.olean" \
    "audit-fixtures/SmusniF02/$f03b_fixture.lean"
done
lake env env LEAN_PATH="$f03b_audit_tmp:$f03b_lean_path" lean \
  f03b-audit-fixtures/AcceptSafeOpaque.lean
echo "PASS F03-B positive audit: SafeOpaque accepted"
for f03b_fixture in UnsafeOpaque PrivateUnsafeOpaque; do
  if f03b_rejection=$(lake env env LEAN_PATH="$f03b_audit_tmp:$f03b_lean_path" lean \
      "f03b-audit-fixtures/Reject$f03b_fixture.lean" 2>&1); then
    echo "FAIL F03-B: audit accepted $f03b_fixture" >&2
    exit 1
  fi
  if ! [[ "$f03b_rejection" == *'F03-B has unsafe semantic declaration:'*'unsafeOpaque'* ]]; then
    echo "$f03b_rejection" >&2
    echo "FAIL F03-B: $f03b_fixture failed for an unexpected reason" >&2
    exit 1
  fi
  echo "PASS F03-B negative audit: $f03b_fixture rejected for unsafe declaration"
done
echo "F03-B isolated audit fixtures: $f03b_audit_tmp"
sha256sum SmusniF03B.lean SmusniF03B/*.lean F03BAudit.lean F03BAuditSupport.lean \
  f03b-audit-fixtures/*.lean audit-fixtures/SmusniF02/*.lean check-f03b.sh lakefile.toml lean-toolchain
