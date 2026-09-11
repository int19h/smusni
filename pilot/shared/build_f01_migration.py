#!/usr/bin/env python3
"""Transport E02 inputs by exact term/environment, without parity assumptions.

The E02 migration is frozen separately. This live report accounts for every
input on both sides and independently records tag/cohort/oracle movements.
No numeric current-population reset and no fixture-number matching.
"""
import argparse
from collections import Counter
import json

from build_m1_constructor_matrix import ROOT, field, parse_sexp, sha256
from build_m2_migration import corpus

OLD = ROOT / "pilot/history/pre-f01"
NEW = ROOT / "pilot/shared"
CORPUS = ROOT / "tools/smusni-redex/inventory/port-corpus.sexp"
OUTPUT = NEW / "F01_MIGRATION.json"


def inputs(directory, corpus_path):
    rows = corpus(corpus_path)
    tags = {r["id"]: r["tag"] for r in json.loads((directory / "M1_S1_MANIFEST.json").read_text())["cases"]}
    cohorts = {identity: name for name, ids in json.loads((directory / "M2_CASE_MANIFEST.json").read_text())["cohorts"].items() for identity in ids}
    oracle = parse_sexp((directory / "M2_REDEX_ORACLE.sexp").read_text())
    oracle_cases = next(e[1:] for e in oracle if isinstance(e, list) and e and e[0] == "cases")
    statuses = {field(e, "id").strip('"'): field(e, "status") for e in oracle_cases}
    keyed = {}
    for row in rows:
        key = row["term_environment_sha256"]
        if key in keyed:
            raise ValueError("ambiguous term/environment identity")
        keyed[key] = {**row, "tag": tags[row["id"]], "cohort": cohorts[row["id"]],
                      "oracle_status": statuses.get(row["id"])}
    return keyed


def build():
    old, new = inputs(OLD, OLD / "port-corpus.sexp"), inputs(NEW, CORPUS)
    if len(old) != 370:
        raise ValueError("frozen E02 population changed")
    old_rows = [{"old": row, "current": new.get(key),
                 "disposition": "exact-input-retained" if key in new else "input-retired"}
                for key, row in sorted(old.items())]
    new_rows = [{"current": row, "old_id": old[key]["id"] if key in old else None,
                 "disposition": "exact-input-transport" if key in old else "new-input"}
                for key, row in sorted(new.items())]
    id_map = {row["id"]: new[key]["id"] for key, row in old.items() if key in new}
    def lowering_inputs(path):
        root = parse_sexp(path.read_text())
        outputs = next(e[1:] for e in root if isinstance(e, list) and e and e[0] == "outputs")
        result = {}
        for output in outputs:
            subterms = next(e[1:] for e in output if isinstance(e, list) and e and e[0] == "subterms")
            for term in subterms:
                result["b1-lowering-" + field(term, "id").strip('"')] = [field(term, "term"), field(term, "env")]
        return result
    old_lowering = lowering_inputs(OLD / "b1-lowering-subterms.sexp")
    new_lowering = lowering_inputs(ROOT / "tools/smusni-redex/inventory/b1-lowering-subterms.sexp")
    for identity, value in old_lowering.items():
        matches = [key for key, target in new_lowering.items() if target == value]
        if identity in matches:
            id_map[identity] = identity
        elif len(matches) == 1:
            id_map[identity] = matches[0]
        else:
            raise ValueError("missing/ambiguous lowering-input transport: " + identity)
    old_waivers = parse_sexp((OLD / "a0-waivers.sexp").read_text())
    current_waivers = parse_sexp((ROOT / "tools/smusni-redex/inventory/a0-waivers.sexp").read_text())
    def transport(value):
        if isinstance(value, list):
            if len(value) == 2 and value[0] == "case":
                identity = value[1].strip('"')
                return ["case", '"' + id_map.get(identity, identity) + '"']
            return [transport(item) for item in value]
        return value
    if transport(old_waivers) != current_waivers:
        raise ValueError("F01 changed waiver fields or failed exact-input transport")
    old_baseline = parse_sexp((OLD / "port-baseline.sexp").read_text())
    current_baseline = parse_sexp((ROOT / "tools/smusni-redex/inventory/port-baseline.sexp").read_text())
    def without_digest(baseline):
        return [entry for entry in baseline if not
                (isinstance(entry, list) and entry and entry[0] == "corpus-sha1")]
    if without_digest(old_baseline) != without_digest(current_baseline):
        raise ValueError("F01 changed performance measurements or triggers")
    current_corpus = parse_sexp(CORPUS.read_text())
    if field(current_baseline, "corpus-sha1") != field(current_corpus, "cases-sha1"):
        raise ValueError("performance baseline digest is not linked to current corpus")
    return {"schema": "smusni-f01-input-migration", "version": 1,
            "source_input": "3e45db536c8523d023f70ae25878a3ecb9f79663",
            "old_revision": "01759ba0042744fb8694c9214842c93aa1a684ff",
            "boundary": "Exact term and environment identity only, not equivalent denotation or oracle admission. F01 direct source form is outside the closed A0 oracle; old Perform role validation is corrected and corresponding Lean typing rules are proved. Full source/Host replay/event model remains outside this migration.",
            "historical_e02_migration": "pilot/history/pre-f01/M2_MIGRATION.json",
            "a0_waivers": {"old": len(old_waivers) - 2, "current": len(current_waivers) - 2,
                           "status": "exact input identity transport; no changed fields/findings/reasons"},
            "performance_baseline": {"status": "only corpus digest transported; all recorded timings and thresholds unchanged",
                                     "old": old_baseline, "current": current_baseline},
            "sources": {str(p.relative_to(ROOT)): sha256(p) for p in
                        [OLD / "port-corpus.sexp", CORPUS, NEW / "M1_S1_MANIFEST.json",
                         NEW / "M2_CASE_MANIFEST.json", NEW / "M2_REDEX_ORACLE.sexp"]},
            "counts": {"old": len(old), "current": len(new),
                       "old_dispositions": dict(Counter(r["disposition"] for r in old_rows)),
                       "current_dispositions": dict(Counter(r["disposition"] for r in new_rows)),
                       "old_cohorts": dict(Counter(r["cohort"] for r in old.values())),
                       "current_cohorts": dict(Counter(r["cohort"] for r in new.values()))},
            "old_cases": old_rows, "current_cases": new_rows}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    report = build()
    encoded = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.write:
        OUTPUT.write_text(encoded)
    elif not OUTPUT.exists() or OUTPUT.read_text() != encoded:
        raise SystemExit("stale F01_MIGRATION.json; regenerate with --write")
    print("F01 migration: " + json.dumps(report["counts"], sort_keys=True))


if __name__ == "__main__":
    main()
