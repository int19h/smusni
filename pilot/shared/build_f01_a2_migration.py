#!/usr/bin/env python3
"""Audit the A2 non-admission correction against its immutable reviewed input.

No case IDs select a classification. Every current and prior record is compared;
available targets, cohort and corpus must be unchanged. Source-only failures
gain explicit evidence under schema 2, independently of target expansion.
"""
import argparse
from collections import Counter
import hashlib
import json
import subprocess

from build_m1_constructor_matrix import ROOT, field, parse_sexp, sha256

BASE = "8c14eaabdfca0866fefa253792b96fdf127b70b1"
ORACLE = "pilot/shared/M2_REDEX_ORACLE.sexp"
SOURCES = "pilot/shared/M2_ORACLE_SOURCES.sexp"
OUTPUT = ROOT / "pilot/shared/F01_A2_MIGRATION.json"


def before(path):
    return subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT).decode()


def records(text):
    root = parse_sexp(text)
    cases = next(e[1:] for e in root if isinstance(e, list) and e and e[0] == "cases")
    keyed = {field(case, "id"): case for case in cases}
    if len(keyed) != len(cases):
        raise ValueError("duplicate case ID")
    return root[1], keyed


def categories(rows):
    return dict(sorted(Counter("available" if field(row, "status") == "available"
                               else field(row, "category") for row in rows.values()).items()))


def build():
    _, old = records(before(ORACLE))
    _, new = records((ROOT / ORACLE).read_text())
    old_version, old_sources = records(before(SOURCES))
    new_version, new_sources = records((ROOT / SOURCES).read_text())
    if old.keys() != new.keys() or old_sources.keys() != new_sources.keys() or new.keys() != new_sources.keys():
        raise ValueError("A2 changed cohort/source IDs")
    if str(old_version) != "1" or str(new_version) != "2":
        raise ValueError("unexpected source-contract schema transition")
    changed = []
    available = 0
    source_failures = 0
    for identity in sorted(old):
        if field(old[identity], "status") != field(new[identity], "status"):
            raise ValueError("A2 changed oracle admission")
        if field(old[identity], "status") == "available":
            available += 1
            if old[identity] != new[identity]:
                raise ValueError("A2 changed an available target or its typing evidence")
        elif old[identity] != new[identity]:
            changed.append({"id": identity.strip('"'), "before": old[identity], "after": new[identity]})
        if field(old_sources[identity], "status") != field(new_sources[identity], "status"):
            raise ValueError("A2 changed source admission")
        if field(new_sources[identity], "status") == "unavailable":
            source_failures += 1
            for key in ("category", "stage", "reason"):
                if field(new_sources[identity], key) != field(new[identity], key):
                    raise ValueError("source-only failure evidence disagrees with the oracle's source rejection")
        elif old_sources[identity] != new_sources[identity]:
            raise ValueError("A2 changed independent source typing evidence")
    preserved = {}
    for path in ["tools/smusni-redex/inventory/port-corpus.sexp", "pilot/shared/M2_CASE_MANIFEST.json",
                 "tools/smusni-redex/inventory/port-baseline.sexp"]:
        if hashlib.sha256(before(path).encode()).hexdigest() != sha256(ROOT / path):
            raise ValueError("A2 changed a preserved input/baseline: " + path)
        preserved[path] = sha256(ROOT / path)
    return {"schema": "smusni-f01-a2-evidence-migration", "version": 1, "reviewed_base": BASE,
            "boundary": "Non-admission evidence correction only; no new independent oracle context or typed target.",
            "counts": {"cohort": len(new), "available_preserved": available,
                       "changed_non_admissions": len(changed), "source_failures_with_evidence": source_failures,
                       "before_categories": categories(old), "after_categories": categories(new)},
            "source_schema": {"before": old_version, "after": new_version},
            "preserved": preserved, "changes": changed}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = build()
    encoded = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.write:
        OUTPUT.write_text(encoded)
    elif not OUTPUT.exists() or OUTPUT.read_text() != encoded:
        raise SystemExit("stale F01_A2_MIGRATION.json")
    print("F01-A2 migration: " + json.dumps(result["counts"], sort_keys=True))


if __name__ == "__main__":
    main()
