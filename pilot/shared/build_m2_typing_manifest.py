#!/usr/bin/env python3
"""Generate and verify the Lean-M2 Redex typing-rule manifest."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from pathlib import Path
from typing import Any

from build_m1_constructor_matrix import ROOT, field, parse_sexp, sha256


SOURCE = ROOT / "tools/smusni-redex/port-a0.rkt"
CORE = ROOT / "tools/smusni-redex/inventory/core.sexp"
FIXTURES = ROOT / "tools/smusni-redex/inventory/fixtures.sexp"
SUPPLEMENT = ROOT / "pilot/shared/M2_TYPING_SUPPLEMENT.tsv"
OUTPUT = ROOT / "pilot/shared/M2_TYPING_MANIFEST.json"


def line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def source_digest(lines: list[str], start: int, end: int) -> str:
    payload = "\n".join(
        f"{number}:{lines[number - 1]}" for number in range(start, end + 1)
    )
    return hashlib.sha256(payload.encode()).hexdigest()


def parse_ranges(raw: str) -> list[list[int]]:
    ranges: list[list[int]] = []
    for item in raw.split(","):
        start, stop = item.split("-", 1)
        ranges.append([int(start), int(stop)])
    return ranges


def range_digest(path: Path, ranges: list[list[int]]) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    selected: list[str] = []
    for start, stop in ranges:
        if start <= 0 or start > stop or stop > len(lines):
            raise ValueError(f"invalid {path.relative_to(ROOT)} range {start}-{stop}")
        selected.extend(f"{line}:{lines[line - 1]}" for line in range(start, stop + 1))
    return hashlib.sha256("\n".join(selected).encode()).hexdigest()


def clean(value: object) -> str:
    raw = str(value)
    if raw.startswith('"') and raw.endswith('"'):
        return raw[1:-1]
    if raw.startswith("|") and raw.endswith("|"):
        return raw[1:-1]
    return raw


def supplemental_rules() -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    with SUPPLEMENT.open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            source_path = row["source_path"].strip()
            path = ROOT / source_path
            ranges = parse_ranges(row["source_ranges"])
            records.append({
                "id": row["rule_id"],
                "kind": row["kind"],
                "subject": row["subject"],
                "anchor": row["anchor"],
                "source_path": source_path,
                "source_ranges": ranges,
                "source_sha256": range_digest(path, ranges),
                "conclusion": row["signature"],
                "reason": row["reason"],
            })
    ids = [record["id"] for record in records]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate M2 typing supplement rule")
    return records


def core_constants() -> list[dict[str, str]]:
    root = parse_sexp(CORE.read_text(encoding="utf-8"))
    records: list[dict[str, str]] = []
    for entry in root[2:]:
        if not isinstance(entry, list) or not entry or entry[0] != "constant":
            continue
        if len(entry) != 4:
            raise ValueError(f"malformed core constant {entry!r}")
        records.append({
            "name": clean(entry[1]),
            "type": clean(entry[2]) if not isinstance(entry[2], list)
                else "(" + " ".join(clean(item) for item in entry[2]) + ")",
            "anchor": clean(entry[3]),
        })
    return records


def lexical_rows() -> list[dict[str, Any]]:
    root = parse_sexp(FIXTURES.read_text(encoding="utf-8"))
    records: list[dict[str, Any]] = []
    for entry in root[2:]:
        if not isinstance(entry, list) or not entry or entry[0] != "row":
            continue
        if len(entry) != 5:
            raise ValueError(f"malformed lexical fixture row {entry!r}")
        records.append({
            "head": clean(entry[1]),
            "ordinary_arity": int(entry[2]),
            "event_mode": clean(entry[3]),
            "provenance": clean(entry[4]),
        })
    return records


def string_list_block(source: str, name: str) -> list[str]:
    marker = f"(define {name}"
    start = source.index(marker)
    next_section = source.find("\n\n", start)
    while next_section >= 0:
        candidate = source[start:next_section]
        if candidate.count("(") == candidate.count(")"):
            return re.findall(r'"([^"]+)"', candidate)
        next_section = source.find("\n\n", next_section + 2)
    raise ValueError(f"unterminated {name}")


def anchor_block(source: str) -> dict[str, str]:
    marker = "(define a0-rule-anchors"
    start = source.index(marker)
    end = source.index("\n\n", start)
    while source[start:end].count("(") != source[start:end].count(")"):
        end = source.index("\n\n", end + 2)
    pairs = re.findall(r'\("([^"]+)"\s+"([^"]+)"\)', source[start:end])
    anchors = dict(pairs)
    if len(anchors) != len(pairs):
        raise ValueError("duplicate A0 rule anchor")
    return anchors


def clause_spans(source: str) -> list[tuple[int, int]]:
    starts = [match.start() + 1 for match in re.finditer(r"\n  \[", source)]
    spans: list[tuple[int, int]] = []
    for index, start in enumerate(starts):
        end = starts[index + 1] if index + 1 < len(starts) else len(source)
        spans.append((start, end))
    return spans


def balanced_form(source: str, start: int) -> str:
    depth = 0
    in_string = False
    escaped = False
    for index in range(start, len(source)):
        char = source[index]
        if in_string:
            if char == '"' and not escaped:
                in_string = False
            escaped = char == "\\" and not escaped
            if char != "\\":
                escaped = False
            continue
        if char == '"':
            in_string = True
        elif char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                return source[start:index + 1]
    raise ValueError("unterminated typing conclusion")


def conclusion_after_label(clause: str, rule: str) -> str:
    label = f'"{rule}"'
    label_offset = clause.index(label) + len(label)
    matches = list(re.finditer(r"\((?:a0-type|a0-synth|a0-check)\b", clause[label_offset:]))
    if not matches:
        raise ValueError(f"typing rule {rule} has no judgment conclusion")
    start = label_offset + matches[0].start()
    return " ".join(balanced_form(clause, start).split())


def bracket_form_span(source: str, name: str) -> tuple[int, int, str]:
    marker = f"  [{name} "
    start = source.index(marker)
    depth = 0
    in_string = False
    escaped = False
    for index in range(start + 2, len(source)):
        char = source[index]
        if in_string:
            if char == '"' and not escaped:
                in_string = False
            escaped = char == "\\" and not escaped
            if char != "\\":
                escaped = False
            continue
        if char == '"':
            in_string = True
        elif char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                return start, index + 1, source[start:index + 1]
    raise ValueError(f"unterminated Redex grammar category {name}")


def build() -> dict[str, Any]:
    source = SOURCE.read_text(encoding="utf-8")
    lines = source.splitlines()
    required = string_list_block(source, "a0-required-rules")
    anchors = anchor_block(source)
    if len(required) != 78 or len(set(required)) != 78:
        raise ValueError(f"expected 78 unique required typing rules, got {len(required)}")
    if set(required) != anchors.keys():
        raise ValueError(
            f"typing rule/anchor mismatch: missing={sorted(set(required)-anchors.keys())} "
            f"extra={sorted(anchors.keys()-set(required))}"
        )

    spans = clause_spans(source)
    records = []
    for rule in required:
        label = f'"{rule}"'
        positions = [
            match.start() for match in
            re.finditer(r"-{10,}\s+" + re.escape(label), source)
        ]
        clause_matches = [
            (start, end) for start, end in spans
            if any(start <= position < end for position in positions)
        ]
        if len(clause_matches) != 1:
            raise ValueError(f"typing rule {rule} clause count {len(clause_matches)}")
        start_offset, end_offset = clause_matches[0]
        clause = source[start_offset:end_offset].rstrip()
        for marker in ("\n\n(define-judgment-form", "\n\n;;", "\n\n(define "):
            clause = clause.split(marker, 1)[0].rstrip()
        start_line = line_number(source, start_offset)
        end_line = start_line + clause.count("\n")
        records.append({
            "id": rule,
            "kind": "redex-rule",
            "subject": rule,
            "anchor": anchors[rule],
            "source_path": str(SOURCE.relative_to(ROOT)),
            "source_ranges": [[start_line, end_line]],
            "source_sha256": source_digest(lines, start_line, end_line),
            "conclusion": conclusion_after_label(clause, rule),
            "reason": "Generated from the frozen A0/B1 typing judgment.",
        })

    grammar = {}
    for name in ("τ", "direction", "R", "t", "ρdecl", "dep", "role"):
        start, end, raw = bracket_form_span(source, name)
        start_line = line_number(source, start)
        end_line = line_number(source, end - 1)
        grammar[name] = {
            "source_range": [start_line, end_line],
            "source_sha256": source_digest(lines, start_line, end_line),
            "source": " ".join(raw.split()),
        }

    supplements = supplemental_rules()
    all_records = records + supplements
    if len({record["id"] for record in all_records}) != len(all_records):
        raise ValueError("duplicate combined M2 typing rule id")
    return {
        "schema": "smusni-lean-m2-typing-manifest",
        "version": 2,
        "sources": {
            "redex": str(SOURCE.relative_to(ROOT)),
            "redex_sha256": sha256(SOURCE),
            "core": str(CORE.relative_to(ROOT)),
            "core_sha256": sha256(CORE),
            "fixtures": str(FIXTURES.relative_to(ROOT)),
            "fixtures_sha256": sha256(FIXTURES),
            "supplement": str(SUPPLEMENT.relative_to(ROOT)),
            "supplement_sha256": sha256(SUPPLEMENT),
        },
        "counts": {
            "required_redex_rules": len(records),
            "supplemental_rules": len(supplements),
            "required_rules": len(all_records),
            "supported_rules": len(all_records),
            "unsupported_rules": 0,
            "grammar_categories": len(grammar),
            "core_constants": len(core_constants()),
            "lexical_rows": len(lexical_rows()),
        },
        "grammar": grammar,
        "rules": all_records,
        "constants": core_constants(),
        "lexical_rows": lexical_rows(),
        "unsupported": [],
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
    counts = json.loads(result)["counts"]
    print("M2 typing manifest: ok " + " ".join(
        f"{key}={value}" for key, value in counts.items()
    ))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
