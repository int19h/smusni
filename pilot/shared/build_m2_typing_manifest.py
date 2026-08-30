#!/usr/bin/env python3
"""Generate and verify the Lean-M2 Redex typing-rule manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any

from build_m1_constructor_matrix import ROOT, sha256


SOURCE = ROOT / "tools/smusni-redex/port-a0.rkt"
OUTPUT = ROOT / "pilot/shared/M2_TYPING_MANIFEST.json"


def line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def source_digest(lines: list[str], start: int, end: int) -> str:
    payload = "\n".join(
        f"{number}:{lines[number - 1]}" for number in range(start, end + 1)
    )
    return hashlib.sha256(payload.encode()).hexdigest()


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
            "anchor": anchors[rule],
            "source_range": [start_line, end_line],
            "source_sha256": source_digest(lines, start_line, end_line),
            "conclusion": conclusion_after_label(clause, rule),
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

    return {
        "schema": "smusni-lean-m2-typing-manifest",
        "version": 1,
        "source": str(SOURCE.relative_to(ROOT)),
        "source_sha256": sha256(SOURCE),
        "counts": {
            "required_rules": len(records),
            "supported_rules": len(records),
            "unsupported_rules": 0,
            "grammar_categories": len(grammar),
        },
        "grammar": grammar,
        "rules": records,
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
