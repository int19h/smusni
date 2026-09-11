#!/usr/bin/env python3
"""Account for every old/current input without treating source joins as parity.

Exact term AND environment equality is the only case transport used here.
Removed terms are retained as retired inputs, not silently paired by fence
ordinal or similarity. Definition/source changes are separate from identity.
"""
import argparse
from collections import Counter
import json
import subprocess

from build_m1_constructor_matrix import ROOT, field, parse_sexp, sha256
from build_m1_s1_manifest import canonical_hash

HISTORY = ROOT / "pilot/history/pre-e02"
OLD_CORPUS = ROOT / "tools/smusni-redex/inventory/history/pre-e01-port-corpus.sexp"
NEW_CORPUS = ROOT / "tools/smusni-redex/inventory/port-corpus.sexp"
OUTPUT = ROOT / "pilot/shared/M2_MIGRATION.json"

# Human-adopted equation changes, not inferred from case identifiers. The
# remaining selected old equation bodies were checked against 138259e, whose
# spec SHA-256 is recorded in the archived definition manifest.
CHANGED_DEFINITIONS = {
    "Massify": "spec.md:3974-3977: SelectExactly 1 replaced by reference-level Refer and existential canonical-group CoRef; not asserted equivalent",
    "Only": "spec.md:4267-4270: pure host plus Among exclusion replaces old focus equation; no effectful-host lift",
}


def corpus(path):
    root = parse_sexp(path.read_text())
    entries = next(node[1:] for node in root
                   if isinstance(node, list) and node and node[0] == "cases")
    result = []
    for entry in entries:
        term, environment = field(entry, "term"), field(entry, "env")
        result.append({"id": field(entry, "id").strip('"'),
                       "term": term, "environment": environment,
                       "term_environment_sha256": canonical_hash([term, environment]),
                       "provenance": field(entry, "provenance")})
    return result


def heads(term):
    if not isinstance(term, list):
        return set()
    return ({term[0]} if term and isinstance(term[0], str) else set()) | set().union(
        *(heads(child) for child in term))


def build():
    old, new = corpus(OLD_CORPUS), corpus(NEW_CORPUS)
    old_s1 = json.loads((HISTORY / "M1_S1_MANIFEST.json").read_text())
    new_s1 = json.loads((ROOT / "pilot/shared/M1_S1_MANIFEST.json").read_text())
    old_cohort = json.loads((HISTORY / "M2_CASE_MANIFEST.json").read_text())
    new_cohort = json.loads((ROOT / "pilot/shared/M2_CASE_MANIFEST.json").read_text())
    old_definitions = json.loads((HISTORY / "M2_DEFINITION_MANIFEST.json").read_text())
    new_definitions = json.loads((ROOT / "pilot/shared/M2_DEFINITION_MANIFEST.json").read_text())
    old_oracle = parse_sexp((HISTORY / "M2_REDEX_ORACLE.sexp").read_text())
    oracle_entries = next(node[1:] for node in old_oracle
                          if isinstance(node, list) and node and node[0] == "cases")
    old_oracles = {field(e, "id").strip('"'): field(e, "status") for e in oracle_entries}
    def index(rows):
        result = {}
        for row in rows:
            key = row["term_environment_sha256"]
            if key in result:
                raise ValueError("duplicate exact term/environment key; explicit many-to-one disposition needed")
            result[key] = row
        return result
    old_by_key, new_by_key = index(old), index(new)
    old_tags = {r["id"]: r["tag"] for r in old_s1["cases"]}
    new_tags = {r["id"]: r["tag"] for r in new_s1["cases"]}
    def memberships(manifest):
        return {case: name for name, ids in manifest["cohorts"].items() for case in ids}
    old_membership, new_membership = memberships(old_cohort), memberships(new_cohort)
    # Account for indirect changed dependencies even in out-of-slice inputs
    # (for example JoiGroup -> Massify), not only selected M2 definitions.
    all_dependencies = {}
    ledger = parse_sexp((ROOT / "tools/smusni-redex/inventory/definitions.sexp").read_text())
    for entry in ledger[2:]:
        if isinstance(entry, list) and entry and entry[0] == "definition":
            dependencies = next(node[1:] for node in entry[1:]
                                if isinstance(node, list) and node and node[0] == "dependencies")
            all_dependencies.setdefault(field(entry, "head"), set()).update(dependencies)
    for record in new_definitions["definitions"]:
        all_dependencies.setdefault(record["head"], set()).update(record["dependencies"])
    def changed_dependencies(term):
        observed = heads(term)
        # Compute defined dependency closure from the current catalog inputs.
        pending = list(observed)
        while pending:
            name = pending.pop()
            for dependency in all_dependencies.get(name, set()):
                if dependency not in observed:
                    observed.add(dependency)
                    pending.append(dependency)
        return sorted(observed & CHANGED_DEFINITIONS.keys())
    old_records = []
    for row in old:
        counterpart = new_by_key.get(row["term_environment_sha256"])
        changed = changed_dependencies(row["term"])
        disposition = "retired-term-environment" if counterpart is None else (
            "changed-definition-semantics" if changed else "identity-only")
        old_records.append({**row, "disposition": disposition,
                            "changed_definitions": changed,
                            "old_tag": old_tags[row["id"]],
                            "old_cohort": old_membership[row["id"]],
                            "old_oracle_status": old_oracles.get(row["id"]),
                            "current_id": counterpart["id"] if counterpart else None})
    new_records = []
    for row in new:
        counterpart = old_by_key.get(row["term_environment_sha256"])
        new_records.append({**row, "old_id": counterpart["id"] if counterpart else None,
                            "admission": "transported-input" if counterpart else "new-term-environment",
                            "current_tag": new_tags[row["id"]],
                            "current_cohort": new_membership[row["id"]],
                            "changed_definitions": changed_dependencies(row["term"])})
    old_catalog = {r["id"]: r for r in old_definitions["catalog"]}
    new_catalog = {r["id"]: r for r in new_definitions["catalog"]}
    definition_records = []
    for identity in sorted(old_catalog.keys() | new_catalog.keys()):
        before, after = old_catalog.get(identity), new_catalog.get(identity)
        head = (after or before)["head"]
        disposition = ("retired" if after is None else "newly-admitted" if before is None
                       else "changed-semantics" if head in CHANGED_DEFINITIONS
                       else "retained-definition")
        definition_records.append({"id": identity, "disposition": disposition,
                                   "old": before, "current": after,
                                   "semantic_change": CHANGED_DEFINITIONS.get(head)})
    old_typing = json.loads((HISTORY / "M2_TYPING_MANIFEST.json").read_text())
    new_typing = json.loads((ROOT / "pilot/shared/M2_TYPING_MANIFEST.json").read_text())
    old_source = subprocess.check_output([
        "git", "show", "a04cf29:tools/smusni-redex/port-a0.rkt"], cwd=ROOT)
    import hashlib
    if hashlib.sha256(old_source).hexdigest() != old_typing["sources"]["redex_sha256"]:
        raise ValueError("historical typing source revision does not match archived input")
    old_lines = old_source.decode().splitlines()
    new_lines = (ROOT / new_typing["sources"]["redex"]).read_text().splitlines()
    old_rules = {r["id"]: r for r in old_typing["rules"] if r["kind"] == "redex-rule"}
    rule_changes = []
    for rule in new_typing["rules"]:
        if rule["kind"] != "redex-rule":
            continue
        previous = old_rules.get(rule["id"])
        def rule_body(record, lines):
            return "\n".join(line for a, b in record["source_ranges"] for line in lines[a-1:b])
        before = rule_body(previous, old_lines) if previous else None
        after = rule_body(rule, new_lines)
        rule_changes.append({"id": rule["id"],
                             "disposition": "new-rule" if before is None else
                                 "source-rule-changed" if before != after else "body-identical-range-movement",
                             "old_body": before, "current_body": after})
    if len(old) != 337 or len(new) != 370 or len(old_oracles) != 160:
        raise ValueError("E02 frozen source populations drifted")
    return {
        "schema": "smusni-m2-source-migration", "version": 1,
        "input_revision": "18cd6267ad38abde8836a553f1531a4f05f339c6",
        "criterion": "pending-M2 AND nonempty defined-head set wholly contained in current a0/ported heads; unchanged from pre-E02",
        "transport_boundary": "exact term/environment equality only; identity transport is not semantic equivalence; source/index joins are not equivalence; changed equation dependencies override identity-only classification",
        "retirement_boundary": "retired term/environment means absent from the current input set, not retired language meaning; E01 source-sync records numerical/P2/P43/threshold and description changes; no guessed pairing of rewritten terms",
        "old_corpus_sha256": sha256(OLD_CORPUS), "current_corpus_sha256": sha256(NEW_CORPUS),
        "counts": {"old": len(old), "current": len(new),
                   "old_parity": old_cohort["counts"]["definition_parity"],
                   "current_parity": new_cohort["counts"]["definition_parity"],
                   "old_dispositions": dict(sorted(Counter(r["disposition"] for r in old_records).items())),
                   "current_admissions": dict(sorted(Counter(r["admission"] for r in new_records).items()))},
        "old_cases": old_records, "current_cases": new_records,
        "definitions": definition_records,
        "typing_rule_inputs": rule_changes,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = build()
    encoded = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.write:
        OUTPUT.write_text(encoded)
    elif not OUTPUT.exists() or OUTPUT.read_text() != encoded:
        raise SystemExit("stale M2_MIGRATION.json; regenerate with --write")
    print("M2 migration: " + json.dumps(result["counts"], sort_keys=True))


if __name__ == "__main__":
    main()
