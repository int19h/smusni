#!/usr/bin/env python3
"""Generate and verify the Lean-M2 definition-ID/case manifest."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from build_m1_constructor_matrix import ROOT, build_rows, field, parse_sexp, sha256


DEFINITIONS = ROOT / "tools/smusni-redex/inventory/definitions.sexp"
SPEC = ROOT / "spec.md"
SUPPLEMENT = ROOT / "pilot/shared/M2_RANGE_SUPPLEMENT.tsv"
DEPENDENCY_SUPPLEMENT = ROOT / "pilot/shared/M2_DEPENDENCY_SUPPLEMENT.tsv"
OUTPUT = ROOT / "pilot/shared/M2_DEFINITION_MANIFEST.json"
SELECTED_PORT_STATES = {"a0", "ported"}
EXTRA_IDS = {
    "D12.Grade",
    "D12.JaiRaise",
    "D5.3.Refer-member-lift",
}
REQUIRED_SUPPLEMENTS = {
    "D4.6.Close",
    "D12.Grade",
    "D5.3.Refer-member-lift",
    "D12.JaiPromote",
    "D12.JaiRaise",
    "D12.ActualClause",
    "D12.CanonicalAggregateAt",
    "D12.CoRef",
    "D4.9.CompleteGunmaAt",
    "D4.9.GunmaAt",
    "D4.6.DirectClause",
}


def values(entry: list[Any], name: str) -> list[Any]:
    for item in entry[1:]:
        if isinstance(item, list) and item and item[0] == name:
            return item[1:]
    raise KeyError(name)


def clean(value: str) -> str:
    if value.startswith("|") and value.endswith("|"):
        return value[1:-1]
    if value.startswith('"') and value.endswith('"'):
        return value[1:-1]
    return value


def parse_ranges(raw: Iterable[Any]) -> list[list[int]]:
    result: list[list[int]] = []
    for item in raw:
        if not isinstance(item, list) or len(item) != 2:
            raise ValueError(f"malformed source range: {item!r}")
        start, end = map(int, item)
        if start <= 0 or start > end:
            raise ValueError(f"invalid source range: {item!r}")
        result.append([start, end])
    return result


def parse_tsv_ranges(raw: str) -> list[list[int]]:
    if not raw:
        return []
    result = []
    for item in raw.split(","):
        start, end = item.split("-", 1)
        result.append([int(start), int(end)])
    return result


def line_digest(ranges: list[list[int]]) -> str | None:
    if not ranges:
        return None
    lines = SPEC.read_text(encoding="utf-8").splitlines()
    selected: list[str] = []
    for start, end in ranges:
        if end > len(lines):
            raise ValueError(f"source range {start}-{end} exceeds spec length")
        selected.extend(f"{line}:{lines[line - 1]}" for line in range(start, end + 1))
    return hashlib.sha256("\n".join(selected).encode()).hexdigest()


def nested_cases(value: Any) -> list[str]:
    found: list[str] = []
    if isinstance(value, list):
        if value and value[0] == "cases":
            found.extend(clean(str(item)) for item in value[1:])
        else:
            for item in value:
                found.extend(nested_cases(item))
    return found


@dataclass(frozen=True)
class Supplement:
    definition_id: str
    head: str
    kind: str
    spec_ranges: list[list[int]]
    equation_ranges: list[list[int]]
    case_names: list[str]
    reason: str


def load_supplements() -> dict[str, Supplement]:
    rows: dict[str, Supplement] = {}
    with SUPPLEMENT.open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            definition_id = row["definition_id"]
            if definition_id in rows:
                raise ValueError(f"duplicate M2 range supplement {definition_id}")
            rows[definition_id] = Supplement(
                definition_id=definition_id,
                head=row["head"],
                kind=row["kind"],
                spec_ranges=parse_tsv_ranges(row["spec_ranges"]),
                equation_ranges=parse_tsv_ranges(row["equation_ranges"]),
                case_names=[name for name in row["case_names"].split(",") if name],
                reason=row["reason"],
            )
    missing = REQUIRED_SUPPLEMENTS - rows.keys()
    extra = rows.keys() - REQUIRED_SUPPLEMENTS
    if missing or extra:
        raise ValueError(f"M2 range supplements mismatch: missing={sorted(missing)} extra={sorted(extra)}")
    return rows


def load_dependency_supplements() -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    with DEPENDENCY_SUPPLEMENT.open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            definition_id = row["definition_id"]
            dependency = row["additional_dependency"]
            ranges = parse_tsv_ranges(row["spec_ranges"])
            if not ranges or line_digest(ranges) is None:
                raise ValueError(f"dependency supplement {definition_id} lacks live ranges")
            if dependency in result.setdefault(definition_id, []):
                raise ValueError(f"duplicate dependency supplement {definition_id}/{dependency}")
            result[definition_id].append(dependency)
    if result != {"D4.6.Close": ["CoRef"]}:
        raise ValueError(f"unexpected M2 dependency supplements {result!r}")
    return result


def status_value(entry: list[Any]) -> dict[str, str | None]:
    raw = field(entry, "status")
    if isinstance(raw, list):
        if len(raw) != 2 or raw[0] != "blocked":
            raise ValueError(f"unsupported definition status {raw!r}")
        return {"kind": "blocked", "issue": clean(str(raw[1]))}
    return {"kind": clean(str(raw)), "issue": None}


def domain_record(raw: list[Any]) -> dict[str, Any]:
    if not raw or raw[0] != "domain":
        raise ValueError(f"malformed definition domain {raw!r}")
    return {
        "name": clean(str(raw[1])),
        "status": clean(" ".join(map(str, values(raw, "status")))),
        "port_state": clean(str(field(raw, "port-state"))),
        "reason": clean(str(field(raw, "reason"))),
    }


def build() -> dict[str, Any]:
    ledger = parse_sexp(DEFINITIONS.read_text(encoding="utf-8"))
    entries = [
        entry for entry in ledger[2:]
        if isinstance(entry, list) and entry and entry[0] == "definition"
    ]
    by_id: dict[str, list[Any]] = {}
    for entry in entries:
        definition_id = clean(str(field(entry, "id")))
        if definition_id in by_id:
            raise ValueError(f"duplicate definition id {definition_id}")
        by_id[definition_id] = entry

    supplements = load_supplements()
    dependency_supplements = load_dependency_supplements()

    def dependencies_for(definition_id: str, entry: list[Any]) -> list[str]:
        return [clean(str(item)) for item in values(entry, "dependencies")] + \
            dependency_supplements.get(definition_id, [])
    defined_heads = {
        key.split(":", 1)[1]
        for key, row in build_rows().items()
        if key.startswith("term:") and row.disposition == "defined-surface"
    }
    by_head: dict[str, list[str]] = {}
    for definition_id, entry in by_id.items():
        by_head.setdefault(clean(str(field(entry, "head"))), []).append(definition_id)

    initial_ids = {
        definition_id for definition_id, entry in by_id.items()
        if clean(str(field(entry, "port-state"))) in SELECTED_PORT_STATES
    } | EXTRA_IDS
    selected_ids = set(initial_ids)
    frontier = list(initial_ids)
    while frontier:
        definition_id = frontier.pop()
        entry = by_id[definition_id]
        for dependency in dependencies_for(definition_id, entry):
            if dependency not in defined_heads:
                continue
            candidates = by_head.get(dependency, [])
            if len(candidates) != 1:
                raise ValueError(
                    f"selected dependency {dependency} has definition IDs {candidates}"
                )
            candidate = candidates[0]
            if candidate not in selected_ids:
                selected_ids.add(candidate)
                frontier.append(candidate)

    selected: list[dict[str, Any]] = []
    port_selected = 0
    dependency_selected = 0
    for definition_id, entry in by_id.items():
        port_state = clean(str(field(entry, "port-state")))
        selection = None
        if port_state in SELECTED_PORT_STATES:
            selection = "definition-port-state"
            port_selected += 1
        elif definition_id in EXTRA_IDS:
            selection = "plan-v2-extra"
        elif definition_id in selected_ids:
            selection = "dependency-closure"
            dependency_selected += 1
        if selection is None:
            continue

        head = clean(str(field(entry, "head")))
        status = status_value(entry)
        if status["kind"] != "executable":
            raise ValueError(f"selected definition {definition_id} is not executable")
        supplement = supplements.get(definition_id)
        ledger_spec_ranges = parse_ranges(values(entry, "spec-source-ranges"))
        try:
            ledger_equation_ranges = parse_ranges(values(entry, "equation-ranges"))
            equation_sha1 = clean(str(field(entry, "equation-source-sha1")))
        except KeyError:
            ledger_equation_ranges = []
            equation_sha1 = "none"
        spec_ranges = ledger_spec_ranges or (supplement.spec_ranges if supplement else [])
        equation_ranges = ledger_equation_ranges or (
            supplement.equation_ranges if supplement else []
        )
        if not spec_ranges or not equation_ranges:
            raise ValueError(f"selected definition {definition_id} lacks reviewed ranges")

        implementations = values(entry, "implementations")
        cases = sorted(set(nested_cases(implementations)))
        if not cases and supplement:
            cases = supplement.case_names
        if not cases:
            raise ValueError(f"selected definition {definition_id} has no clause/domain cases")

        domains = [domain_record(raw) for raw in values(entry, "domains")]
        selected_domains = [
            domain for domain in domains
            if domain["port_state"] in SELECTED_PORT_STATES
        ]
        selected.append({
            "id": definition_id,
            "head": head,
            "selection": selection,
            "status": status,
            "port_state": port_state,
            "dependencies": dependencies_for(definition_id, entry),
            "cases": cases,
            "domains": domains,
            "selected_domains": selected_domains,
            "spec": {
                "ledger_sha1": clean(str(field(entry, "spec-source-sha1"))),
                "ranges": spec_ranges,
                "range_sha256": line_digest(spec_ranges),
            },
            "equation": {
                "ledger_sha1": equation_sha1,
                "ranges": equation_ranges,
                "range_sha256": line_digest(equation_ranges),
            },
            "supplement": None if supplement is None else {
                "kind": supplement.kind,
                "reason": supplement.reason,
            },
        })

    selected.sort(key=lambda row: row["id"])
    if port_selected != 19:
        raise ValueError(f"expected 19 a0/ported definition rows, found {port_selected}")
    if {row["id"] for row in selected if row["selection"] == "plan-v2-extra"} != EXTRA_IDS:
        raise ValueError("M2 extra definition selection drift")
    if dependency_selected != 6:
        raise ValueError(
            f"expected six dependency-closure definitions, found {dependency_selected}"
        )

    selected_domain_count = sum(len(row["selected_domains"]) for row in selected)
    if selected_domain_count != 1:
        raise ValueError(f"expected one selected definition domain, found {selected_domain_count}")

    catalog = []
    selected_set = {row["id"] for row in selected}
    for definition_id, entry in by_id.items():
        catalog.append({
            "id": definition_id,
            "head": clean(str(field(entry, "head"))),
            "status": status_value(entry),
            "port_state": clean(str(field(entry, "port-state"))),
            "selected": definition_id in selected_set,
            "reason": clean(str(field(entry, "reason"))),
        })
    catalog.sort(key=lambda row: row["id"])

    return {
        "schema": "smusni-lean-m2-definition-manifest",
        "version": 1,
        "sources": {
            "definitions": str(DEFINITIONS.relative_to(ROOT)),
            "definitions_sha256": sha256(DEFINITIONS),
            "spec": str(SPEC.relative_to(ROOT)),
            "spec_sha256": sha256(SPEC),
            "range_supplement": str(SUPPLEMENT.relative_to(ROOT)),
            "range_supplement_sha256": sha256(SUPPLEMENT),
            "dependency_supplement": str(DEPENDENCY_SUPPLEMENT.relative_to(ROOT)),
            "dependency_supplement_sha256": sha256(DEPENDENCY_SUPPLEMENT),
        },
        "counts": {
            "definition_port_state": port_selected,
            "plan_v2_extra": len(EXTRA_IDS),
            "dependency_closure": dependency_selected,
            "selected_definitions": len(selected),
            "selected_domains": selected_domain_count,
            "selected_clauses": sum(len(row["cases"]) for row in selected),
            "catalog_definitions": len(catalog),
        },
        "definitions": selected,
        "catalog": catalog,
    }


def encoded(manifest: dict[str, Any]) -> str:
    return json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = encoded(build())
    if args.write:
        OUTPUT.write_text(result, encoding="utf-8")
        print(f"wrote {OUTPUT.relative_to(ROOT)}")
        return 0
    if not OUTPUT.exists():
        raise SystemExit(f"missing {OUTPUT.relative_to(ROOT)}; run with --write")
    if OUTPUT.read_text(encoding="utf-8") != result:
        raise SystemExit(f"stale {OUTPUT.relative_to(ROOT)}; regenerate with --write")
    manifest = json.loads(result)
    counts = manifest["counts"]
    print("M2 definition manifest: ok " + " ".join(
        f"{key}={value}" for key, value in counts.items()
    ))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
