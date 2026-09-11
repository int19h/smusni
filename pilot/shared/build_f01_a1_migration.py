#!/usr/bin/env python3
"""Retain every input at the reviewed F01 checkpoint through the A1 correction.

This is source/fixture transport evidence, not a semantic-output oracle. The
old erroneous rejection is preserved in Git and the review record, not used
as a current expected result. No source/term matching appears in the normalizer.
"""
import argparse
from collections import Counter
import json
import subprocess

from build_m1_constructor_matrix import ROOT, field, parse_sexp, sha256
from build_m1_s1_manifest import canonical_hash

BASE = "b706b4eac5b1c7244b02fefcf70cee8bb9d37bd2"
CORPUS = "tools/smusni-redex/inventory/port-corpus.sexp"
OUTPUT = ROOT / "pilot/shared/F01_A1_MIGRATION.json"


def old_text(path):
    return subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT).decode()


def rows(text):
    document = parse_sexp(text)
    cases = next(e[1:] for e in document if isinstance(e, list) and e and e[0] == "cases")
    result = {}
    for case in cases:
        term, env = field(case, "term"), field(case, "env")
        key = canonical_hash([term, env])
        if key in result:
            raise ValueError("ambiguous exact-input key")
        result[key] = {"id": field(case, "id").strip('"'), "term": term,
                       "environment": env, "provenance": field(case, "provenance")}
    return result


def build():
    before, after = rows(old_text(CORPUS)), rows((ROOT / CORPUS).read_text())
    if len(before) != 404 or not before.keys() <= after.keys():
        raise ValueError("A1 lost a reviewed F01 input")
    def memberships(text):
        return {identity: name for name, ids in json.loads(text)["cohorts"].items() for identity in ids}
    path = "pilot/shared/M2_CASE_MANIFEST.json"
    old_cohorts, new_cohorts = memberships(old_text(path)), memberships((ROOT / path).read_text())
    retained = [{"identity": key, "old": row, "current_id": after[key]["id"],
                 "old_cohort": old_cohorts[row["id"]], "current_cohort": new_cohorts[after[key]["id"]]}
                for key, row in sorted(before.items())]
    added = [{"identity": key, **row, "cohort": new_cohorts[row["id"]]}
             for key, row in sorted(after.items()) if key not in before]
    return {"schema": "smusni-f01-a1-input-transport", "version": 1, "reviewed_base": BASE,
            "source_input": "3e45db536c8523d023f70ae25878a3ecb9f79663",
            "finding": "F01-A1; msg_20260911T212401044741Z_c8f47942dc64432f80cd46c3f6a57b4b",
            "correction": "Act at expected Discourse is source notation for explicit performance, not subtyping. The old literal-Assert negative input is retained and its rejected expectation corrected; the review's Act-variable and typed nonliteral inputs are added.",
            "boundary": "Input/cohort identity only, not equivalent outputs. Deep typing evidence attaches to the returned canonical AST, not the unnormalized source.",
            "current_corpus_sha256": sha256(ROOT / CORPUS),
            "counts": {"old": len(before), "current": len(after), "retained": len(retained), "new": len(added),
                       "old_cohorts": dict(Counter(old_cohorts.values())), "current_cohorts": dict(Counter(new_cohorts.values()))},
            "retained": retained, "added": added}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = build()
    encoded = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.write:
        OUTPUT.write_text(encoded)
    elif not OUTPUT.exists() or OUTPUT.read_text() != encoded:
        raise SystemExit("stale F01_A1_MIGRATION.json")
    print("F01-A1 migration: " + json.dumps(result["counts"], sort_keys=True))


if __name__ == "__main__":
    main()
