#!/usr/bin/env python3
"""Build the pinned S1 partition for Lean milestone 1."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from build_m1_constructor_matrix import (
    BASE_HEAD,
    ROOT,
    build_rows,
    parse_sexp,
    sha256,
)


CORPUS = ROOT / "tools/smusni-redex/inventory/port-corpus.sexp"
FIXTURES = ROOT / "tools/smusni-redex/inventory/fixtures.sexp"
RR_DIR = ROOT / "tools/smusni-redex/inventory/rr"
PARSE_DIR = ROOT / "tools/smusni-redex/inventory/parses"
OUTPUT = ROOT / "pilot/shared/M1_S1_MANIFEST.json"


def sexp_field(entry: list, name: str):
    for item in entry[1:]:
        if isinstance(item, list) and item and item[0] == name:
            if len(item) == 2:
                return item[1]
            return item[1:]
    raise KeyError(name)


def canonical_hash(value: Any) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, separators=(",", ":"), sort_keys=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def collect_term_heads(
    term: Any, known: dict[str, str], lexical_heads: set[str],
    data_names: set[str], free_names: set[str]
) -> set[str]:
    found: set[str] = set()

    def binder_names(value: Any) -> list[str]:
        if not isinstance(value, list) or not value:
            return []
        if isinstance(value[0], list):
            return [name for item in value for name in binder_names(item)]
        names = []
        for item in value:
            if item == "::":
                break
            if isinstance(item, str) and item.startswith("$"):
                names.append(item)
        return names

    def walk(
        value: Any, bound_names: set[str], check_undeclared_free: bool = True
    ) -> None:
        if isinstance(value, str):
            if value.startswith('"') and value.endswith('"'):
                found.add("$string")
                return
            raw = value.strip('"')
            if raw.isdigit():
                found.add("$natural")
            elif raw.startswith("$"):
                if raw in bound_names or raw in free_names:
                    found.add("$variable")
                elif not check_undeclared_free:
                    found.add("$variable")
                else:
                    found.add("$undeclared-free:" + raw)
            elif raw in {"λ", "Bind", "Context", "Vague"}:
                found.add("$malformed-structural:" + raw)
            elif raw.startswith(":") or raw in data_names:
                pass
            elif raw in lexical_heads:
                found.add("$lexical-predication")
            elif raw in known:
                found.add(raw)
            else:
                found.add("$unknown:" + raw)
            return
        if not isinstance(value, list) or not value:
            return
        first = value[0]
        if isinstance(first, list):
            found.add("$application")
            walk(first, bound_names, check_undeclared_free)
            for argument in value[1:]:
                walk(argument, bound_names, check_undeclared_free)
            return
        if not isinstance(first, str):
            return
        if len(value) >= 2 and value[1] == "::":
            # Binder or environment entry; its type belongs to the typed
            # record schema, not to the term-former partition.
            return
        if first == "λ" and len(value) != 3:
            found.add("$malformed-structural:λ")
            for nested in value[1:]:
                walk(nested, bound_names, check_undeclared_free)
            return
        if first == "Bind" and (len(value) < 4 or len(value) % 2 != 0):
            found.add("$malformed-structural:Bind")
            for nested in value[1:]:
                walk(nested, bound_names, check_undeclared_free)
            return
        if first == "Vague" and len(value) != 2:
            found.add("$malformed-structural:Vague")
            for nested in value[1:]:
                walk(nested, bound_names, check_undeclared_free)
            return
        if first in known and known[first] == "defined-surface":
            found.add(first)
            for nested in value[1:]:
                walk(nested, bound_names, False)
            return
        if first == "λ" and len(value) == 3:
            found.add(first)
            walk(
                value[2], bound_names | set(binder_names(value[1])),
                check_undeclared_free
            )
            return
        if first == "Bind" and len(value) >= 4:
            found.add(first)
            current_bound = set(bound_names)
            remaining = value[1:]
            while len(remaining) > 1:
                names = set(binder_names(remaining[0]))
                walk(remaining[1], current_bound, check_undeclared_free)
                current_bound |= names
                remaining = remaining[2:]
            if remaining:
                walk(remaining[0], current_bound, check_undeclared_free)
            return
        if first.startswith("$"):
            if first in bound_names or first in free_names:
                found.add("$application")
                found.add("$variable")
            elif not check_undeclared_free:
                found.add("$application")
                found.add("$variable")
            else:
                found.add("$undeclared-free:" + first)
            for nested in value[1:]:
                walk(nested, bound_names, check_undeclared_free)
            return
        if first in lexical_heads:
            found.add("$lexical-predication")
        elif first in known:
            found.add(first)
        elif first.startswith(":") or first in {"row", "fill"}:
            pass
        else:
            found.add("$unknown-head:" + first)
        for nested in value[1:]:
            walk(nested, bound_names, check_undeclared_free)

    walk(term, set())
    return found


def is_l530_provenance(value: Any) -> bool:
    if not isinstance(value, list):
        return False
    if len(value) >= 3 and value[0] == "fence":
        source = str(value[1]).strip('"')
        number = str(value[2]).strip('"')
        if source == "samples.md" and number in {"71", "72"}:
            return True
    return any(is_l530_provenance(item) for item in value)


def has_fence_kind(value: Any, wanted: str) -> bool:
    if not isinstance(value, list):
        return False
    if len(value) >= 4 and value[0] == "fence":
        if str(value[3]).strip('"') == wanted:
            return True
    return any(has_fence_kind(item, wanted) for item in value)


def has_variable_under_defined(
    term: Any, dispositions: dict[str, str]
) -> bool:
    def contains_variable(value: Any) -> bool:
        if isinstance(value, str):
            return not (value.startswith('"') and value.endswith('"')) and \
                value.startswith("$")
        return isinstance(value, list) and any(contains_variable(item) for item in value)

    if not isinstance(term, list) or not term:
        return False
    first = term[0]
    if isinstance(first, str) and dispositions.get(first) == "defined-surface":
        if any(contains_variable(item) for item in term[1:]):
            return True
    return any(
        has_variable_under_defined(item, dispositions) for item in term
        if isinstance(item, list)
    )


def build() -> dict[str, Any]:
    matrix = build_rows()
    term_dispositions = {
        key.split(":", 1)[1]: row.disposition
        for key, row in matrix.items()
        if key.startswith("term:")
    }
    data_names = {
        key.split(":", 1)[1]
        for key, row in matrix.items()
        if row.disposition == "type-index-data"
    }
    corpus = parse_sexp(CORPUS.read_text(encoding="utf-8"))
    fixture_inventory = parse_sexp(FIXTURES.read_text(encoding="utf-8"))
    lexical_heads = {
        entry[1]
        for entry in fixture_inventory[2:]
        if isinstance(entry, list) and entry and entry[0] == "row"
    }
    cases_node = next(item for item in corpus if isinstance(item, list) and item and item[0] == "cases")
    cases = []
    inventory_hashes: set[str] = set()
    counts = {"primitive-core": 0, "pending-milestone-2": 0, "out-of-slice": 0}
    l530_count = 0
    defined_payload_variable_cases = 0

    for entry in cases_node[1:]:
        case_id = sexp_field(entry, "id").strip('"')
        provenance = sexp_field(entry, "provenance")
        term = sexp_field(entry, "term")
        environment = sexp_field(entry, "env")
        free_names = {
            item[0]
            for item in environment
            if isinstance(item, list) and item and
            isinstance(item[0], str) and item[0].startswith("$")
        } if isinstance(environment, list) else set()
        inventory = sexp_field(entry, "inventory")
        if isinstance(inventory, str):
            inventory = [inventory]
        normalized_inventory = [item.strip('"') for item in inventory]
        inventory_hashes.update(normalized_inventory)
        heads = collect_term_heads(
            term, term_dispositions, lexical_heads, data_names, free_names
        )
        defined = sorted(
            head for head in heads
            if term_dispositions.get(head) == "defined-surface"
        )
        offending = sorted(
            head for head in heads
            if term_dispositions.get(head) in {"gap-prose-only", "tool-only"}
            or head not in term_dispositions
        )
        if has_fence_kind(provenance, "declaration"):
            offending.append("$nonterm:declaration")
        if offending:
            tag = "out-of-slice"
        elif defined:
            tag = "pending-milestone-2"
        else:
            tag = "primitive-core"
        counts[tag] += 1
        l530 = is_l530_provenance(provenance)
        l530_count += int(l530)
        defined_payload_variable_cases += int(
            has_variable_under_defined(term, term_dispositions)
        )
        cases.append(
            {
                "id": case_id,
                "tag": tag,
                "provenance": provenance,
                "term_sha256": canonical_hash(term),
                "heads": sorted(heads),
                "defined_heads": defined,
                "offending_heads": offending,
                "l5_30": l530,
            }
        )

    records = []
    for path in sorted(RR_DIR.glob("*.sexp")):
        records.append(
            {
                "path": str(path.relative_to(ROOT)),
                "schema": "RRFixture",
                "sha256": sha256(path),
            }
        )
    for path in sorted(PARSE_DIR.glob("*.json")):
        records.append(
            {
                "path": str(path.relative_to(ROOT)),
                "schema": "ParseFixture",
                "sha256": sha256(path),
                "skeleton_probe": path.name in {
                    "structural-probes.json",
                    "in-place-probes.json",
                },
            }
        )

    skeleton_count = sum(bool(item.get("skeleton_probe")) for item in records)
    if l530_count == 0:
        raise ValueError("S1 omitted all L5.30 fence cases")
    if skeleton_count != 2:
        raise ValueError(f"expected both skeleton probe records, got {skeleton_count}")

    return {
        "schema": "smusni-pilot-s1",
        "version": 1,
        "base_head": BASE_HEAD,
        "sources": {
            "port_corpus": str(CORPUS.relative_to(ROOT)),
            "port_corpus_sha256": sha256(CORPUS),
            "fixtures": str(FIXTURES.relative_to(ROOT)),
            "fixtures_sha256": sha256(FIXTURES),
            "constructor_matrix_sha256": sha256(
                ROOT / "pilot/shared/M1_CONSTRUCTOR_DISPOSITION.tsv"
            ),
            "inventory_hashes": sorted(inventory_hashes),
            "rr_syntax_normalization":
                "28 fixtures remove one ignored trailing ')' relative to base_head",
        },
        "counts": {
            "primitive_core": counts["primitive-core"],
            "pending_milestone_2": counts["pending-milestone-2"],
            "out_of_slice": counts["out-of-slice"],
            "total_cases": len(cases),
            "l5_30_cases": l530_count,
            "typed_records": len(records),
            "skeleton_probe_records": skeleton_count,
            "defined_payload_variable_cases": defined_payload_variable_cases,
        },
        "cases": sorted(cases, key=lambda item: item["id"]),
        "typed_records": records,
    }


def rendered() -> str:
    return json.dumps(build(), ensure_ascii=False, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    current = rendered()
    if args.write:
        OUTPUT.write_text(current, encoding="utf-8")
        print(f"wrote {OUTPUT.relative_to(ROOT)}")
        return 0
    if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != current:
        print(f"stale or missing {OUTPUT.relative_to(ROOT)}; run --write")
        return 1
    counts = build()["counts"]
    print("S1 manifest: ok " + " ".join(
        f"{key}={counts[key]}" for key in sorted(counts)
    ))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
