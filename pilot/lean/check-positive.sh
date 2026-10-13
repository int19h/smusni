#!/usr/bin/env bash
# Isolated positive experiment, with the existing audited foundation only.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build SmusniPositive PositiveAuditSupport
lake env lean PositiveAudit.lean
positive_audit_tmp=$(mktemp -d /tmp/smusni-positive-audit.XXXXXX)
mkdir "$positive_audit_tmp/SmusniF02"
positive_lean_path=$(lake env printenv LEAN_PATH)
for positive_fixture in UnsafeOpaque PrivateUnsafeOpaque SafeOpaque; do
  lake env lean --root=audit-fixtures \
    -o "$positive_audit_tmp/SmusniF02/$positive_fixture.olean" \
    "audit-fixtures/SmusniF02/$positive_fixture.lean"
done
lake env env LEAN_PATH="$positive_audit_tmp:$positive_lean_path" lean \
  positive-audit-fixtures/AcceptSafeOpaque.lean
echo "PASS positive model audit: SafeOpaque accepted"
for positive_fixture in UnsafeOpaque PrivateUnsafeOpaque; do
  if positive_rejection=$(lake env env LEAN_PATH="$positive_audit_tmp:$positive_lean_path" lean \
      "positive-audit-fixtures/Reject$positive_fixture.lean" 2>&1); then
    echo "FAIL positive model: audit accepted $positive_fixture" >&2
    exit 1
  fi
  if ! [[ "$positive_rejection" == *'Positive model has unsafe semantic declaration:'*'unsafeOpaque'* ]]; then
    echo "$positive_rejection" >&2
    echo "FAIL positive model: $positive_fixture failed for an unexpected reason" >&2
    exit 1
  fi
  echo "PASS positive model audit: $positive_fixture rejected for unsafe declaration"
done
echo "Positive model isolated audit fixtures: $positive_audit_tmp"
sha256sum SmusniPositive.lean SmusniPositive/*.lean PositiveAudit.lean PositiveAuditSupport.lean \
  positive-audit-fixtures/*.lean audit-fixtures/SmusniF02/*.lean check-positive.sh lakefile.toml lean-toolchain
