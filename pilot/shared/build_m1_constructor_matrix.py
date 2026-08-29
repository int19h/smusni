#!/usr/bin/env python3
"""Build and verify the Lean-M1 constructor disposition matrix.

The matrix is fixed before CoreTerm constructors are written.  It joins the
tracked core inventory, definition ledger, live A0 grammar, and the normative
kernel appendix.  Source changes make the checked-in matrix stale rather than
silently changing the constructor set.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterator


ROOT = Path(__file__).resolve().parents[2]
CORE = ROOT / "tools/smusni-redex/inventory/core.sexp"
DEFINITIONS = ROOT / "tools/smusni-redex/inventory/definitions.sexp"
A0 = ROOT / "tools/smusni-redex/port-a0.rkt"
SPEC = ROOT / "spec.md"
OUTPUT = ROOT / "pilot/shared/M1_CONSTRUCTOR_DISPOSITION.tsv"

PRIMITIVE = "primitive-core"
DEFINED = "defined-surface"
DATA = "type-index-data"
GAP = "gap-prose-only"
TOOL = "tool-only"
DISPOSITIONS = {PRIMITIVE, DEFINED, DATA, GAP, TOOL}


# The appendix is prose, so its named additions are explicit and reviewed.
# Rows already present in core.sexp gain a second source; rows missing from the
# current inventory are still dispositioned rather than silently lost.
SPEC_PRIMITIVES = {
    "$application",
    "$lexical-predication",
    "ActContent",
    "Deictic",
    "During",
    "EnumerationOrdinal",
    "InContext",
    "InnatelyCapable",
    "InterpretAct",
    "MotionVector",
    "NewTopic",
    "QuestionOf",
    "RealizedAct",
    "RealizedDiscourse",
    "Resume",
    "ShiftedGround",
    "TopicAdmissible",
    "×",
    "÷",
    "<",
    "≤",
}

SPEC_DEFINED = {
    "⊤",
    "ClauseIff",
    "ClauseImp",
    "ClauseXor",
    "DemonstratedClause",
    "MePred",
    "RoiClause",
    "That",
    "This",
    "Topic",
    "UnrealizedClause",
    "UnitSet",
    "Yonder",
}

SPEC_DATA = {
    "BasisKind",
    "ClauseContent",
    "Content",
    "DefectKind",
    "Direction",
    "Discourse",
    "EnumerationLevel",
    "Force",
    "GenericMode",
    "Intensity",
    "OccurrenceRole",
    "Proximity",
    "ScalarMode",
    "Target",
    "ThresholdKind",
    "TopicResolution",
}

SPEC_NON_TERM = {
    "family:Select": "primitive family label; concrete Select constructors are separate",
    "metatheory:bind": "carrier sequencing operation denoted by term:Bind",
}

# Core inventory structural rows need an explicit semantic disposition.
STRUCTURAL_OVERRIDES = {
    "λ": PRIMITIVE,
    "Bind": PRIMITIVE,
    "Let": DEFINED,
    "GroupBasisConstraint": DATA,
}

# Grammar-only nodes are adapters or metadata, not object-language formers.
GRAMMAR_TOOL_ONLY = {
    "CloseWith",
    "Quote",
    "Site",
    "SiteValue",
    "Syntax",
    "bound",
    "context",
    "deps",
    "found",
    "member",
    "ok",
    "outer",
    "presuppose",
    "refusal",
    "row",
    "site",
    "sites",
    "typing",
    "vague",
    "values",
    "when-positive",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def clean_symbol(token: str) -> str:
    if token.startswith("|") and token.endswith("|"):
        return token[1:-1]
    return token


def tokens(source: str) -> Iterator[str]:
    i = 0
    while i < len(source):
        char = source[i]
        if char.isspace():
            i += 1
        elif char == ";":
            newline = source.find("\n", i)
            i = len(source) if newline < 0 else newline + 1
        elif char in "()":
            yield char
            i += 1
        elif char == '"':
            j = i + 1
            escaped = False
            while j < len(source):
                if source[j] == '"' and not escaped:
                    break
                escaped = source[j] == "\\" and not escaped
                if source[j] != "\\":
                    escaped = False
                j += 1
            if j >= len(source):
                raise ValueError("unterminated string")
            yield source[i : j + 1]
            i = j + 1
        elif char == "|":
            j = source.find("|", i + 1)
            if j < 0:
                raise ValueError("unterminated bar symbol")
            yield source[i : j + 1]
            i = j + 1
        else:
            j = i
            while j < len(source) and not source[j].isspace() and source[j] not in "();":
                j += 1
            yield source[i:j]
            i = j


def parse_sexp(source: str) -> list:
    stream = iter(tokens(source))

    def one(token: str):
        if token != "(":
            return clean_symbol(token)
        result = []
        for nested in stream:
            if nested == ")":
                return result
            result.append(one(nested))
        raise ValueError("unterminated list")

    first = next(stream)
    value = one(first)
    try:
        extra = next(stream)
    except StopIteration:
        return value
    raise ValueError(f"extra token after root: {extra}")


def bracket_rule(source: str, name: str) -> list:
    marker = f"  [{name} "
    start = source.index(marker)
    depth = 0
    end = None
    for index in range(start + 2, len(source)):
        if source[index] == "[":
            depth += 1
        elif source[index] == "]":
            depth -= 1
            if depth == 0:
                end = index + 1
                break
    if end is None:
        raise ValueError(f"unterminated grammar rule {name}")
    return parse_sexp(source[start:end].replace("[", "(").replace("]", ")"))


@dataclass
class Row:
    head: str
    disposition: str
    sources: set[str] = field(default_factory=set)
    evidence: set[str] = field(default_factory=set)


def add(rows: dict[str, Row], head: str, disposition: str,
        source: str, evidence: str) -> None:
    head = clean_symbol(head)
    if disposition not in DISPOSITIONS:
        raise ValueError(f"bad disposition {disposition} for {head}")
    if head in rows and rows[head].disposition != disposition:
        raise ValueError(
            f"conflicting dispositions for {head}: "
            f"{rows[head].disposition} vs {disposition} ({source})"
        )
    row = rows.setdefault(head, Row(head, disposition))
    row.sources.add(source)
    row.evidence.add(evidence)


def field(entry: list, name: str):
    for item in entry[1:]:
        if isinstance(item, list) and item and item[0] == name:
            return item[1] if len(item) == 2 else item[1:]
    raise KeyError(name)


def build_rows() -> dict[str, Row]:
    rows: dict[str, Row] = {}
    core = parse_sexp(CORE.read_text(encoding="utf-8"))
    definitions = parse_sexp(DEFINITIONS.read_text(encoding="utf-8"))

    for entry in core[2:]:
        if not isinstance(entry, list) or not entry:
            continue
        kind = entry[0]
        if kind == "sort":
            add(rows, f"sort:{entry[1]}", DATA, "core", entry[-1].strip('"'))
        elif kind == "type-form":
            add(rows, f"type-form:{entry[1]}", DATA, "core", entry[-1].strip('"'))
        elif kind == "constant":
            add(rows, f"term:{entry[1]}", PRIMITIVE, "core", entry[-1].strip('"'))
        elif kind == "form":
            head, status = entry[1], entry[2]
            disposition = {
                "primitive": PRIMITIVE,
                "defined": DEFINED,
                "structural": STRUCTURAL_OVERRIDES.get(head),
            }[status]
            if disposition is None:
                raise ValueError(f"unclassified structural core form {head}")
            add(rows, f"term:{head}", disposition, "core", entry[-1].strip('"'))

    for entry in definitions[2:]:
        if not isinstance(entry, list) or not entry or entry[0] != "definition":
            continue
        head = field(entry, "head")
        status = field(entry, "status")
        if isinstance(status, list):
            disposition = GAP
            status_text = " ".join(status)
        elif status == "executable":
            disposition = DEFINED
            status_text = status
        else:
            disposition = GAP
            status_text = status
        key = f"term:{head}"
        if key in rows:
            rows[key].sources.add("definitions")
            rows[key].evidence.add(f"definition status {status_text}")
        else:
            add(rows, key, disposition, "definitions",
                f"definition status {status_text}")

    grammar = A0.read_text(encoding="utf-8")
    term_rule = bracket_rule(grammar, "t")
    constant_rule = bracket_rule(grammar, "constant")
    type_rule = bracket_rule(grammar, "τ")

    for pattern in term_rule[1:]:
        if isinstance(pattern, list):
            head = pattern[0]
            if head == "t":
                head = "$application"
            key = f"term:{head}"
            if key in rows:
                rows[key].sources.add("a0-grammar")
                rows[key].evidence.add("SmusniA0 t grammar")
            elif head == "$application":
                add(rows, key, PRIMITIVE, "a0-grammar",
                    "SmusniA0 generic application grammar")
            elif head in GRAMMAR_TOOL_ONLY:
                add(rows, key, TOOL, "a0-grammar", "SmusniA0 adapter grammar")
            else:
                raise ValueError(f"unclassified A0 term head {head}")

    add(rows, "term:$variable", PRIMITIVE, "a0-grammar", "SmusniA0 atom x")
    add(rows, "term:$natural", PRIMITIVE, "a0-grammar", "SmusniA0 atom n")
    for constant in constant_rule[1:]:
        disposition = DEFINED if constant == "⊤" else PRIMITIVE
        key = f"term:{constant}"
        if key in rows:
            if constant in SPEC_DEFINED:
                rows[key].disposition = DEFINED
            rows[key].sources.add("a0-grammar")
            rows[key].evidence.add("SmusniA0 constant grammar")
        else:
            add(rows, key, disposition, "a0-grammar",
                "SmusniA0 constant grammar")

    for pattern in type_rule[1:]:
        head = pattern[0] if isinstance(pattern, list) else pattern
        candidates = [
            key for key, row in rows.items()
            if row.disposition == DATA and key.split(":", 1)[-1] == head
        ]
        if candidates:
            for key in candidates:
                rows[key].sources.add("a0-grammar")
                rows[key].evidence.add("SmusniA0 type grammar")
        else:
            add(rows, f"type:{head}", DATA, "a0-grammar", "SmusniA0 type grammar")

    for head in SPEC_PRIMITIVES:
        key = f"term:{head}"
        if key in rows:
            if rows[key].disposition != PRIMITIVE:
                raise ValueError(f"kernel says primitive but matrix says {rows[key].disposition}: {head}")
            rows[key].sources.add("spec-appendix")
            rows[key].evidence.add("spec Appendix: the kernel")
        else:
            add(rows, key, PRIMITIVE, "spec-appendix", "spec Appendix: the kernel")
    for head in SPEC_DEFINED:
        key = f"term:{head}"
        if key in rows:
            rows[key].disposition = DEFINED
            rows[key].sources.add("spec-appendix")
            rows[key].evidence.add("spec Appendix: defined forms")
        else:
            add(rows, key, DEFINED, "spec-appendix", "spec Appendix: defined forms")
    for head in SPEC_DATA:
        candidates = [
            key for key, row in rows.items()
            if row.disposition == DATA and key.split(":", 1)[-1] == head
        ]
        if candidates:
            for key in candidates:
                rows[key].sources.add("spec-3.4-3.5")
                rows[key].evidence.add("spec §3.4–§3.5")
        else:
            add(rows, f"type:{head}", DATA, "spec-3.4-3.5", "spec §3.4–§3.5")
    for key, reason in SPEC_NON_TERM.items():
        add(rows, key, GAP, "spec-appendix", reason)

    return rows


def render(rows: dict[str, Row]) -> str:
    base_head = subprocess.check_output(
        ["git", "rev-parse", "origin/main"], cwd=ROOT, text=True
    ).strip()
    header = [
        f"# base_head\t{base_head}",
        f"# core_sha256\t{sha256(CORE)}",
        f"# definitions_sha256\t{sha256(DEFINITIONS)}",
        f"# a0_sha256\t{sha256(A0)}",
        f"# spec_sha256\t{sha256(SPEC)}",
        "head\tdisposition\tsources\tevidence",
    ]
    body = []
    for head in sorted(rows, key=lambda item: item.casefold()):
        row = rows[head]
        body.append(
            "\t".join(
                [
                    row.head,
                    row.disposition,
                    ",".join(sorted(row.sources)),
                    " | ".join(sorted(row.evidence)),
                ]
            )
        )
    return "\n".join(header + body) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    rendered = render(build_rows())
    if args.write:
        OUTPUT.write_text(rendered, encoding="utf-8")
        print(f"wrote {OUTPUT.relative_to(ROOT)}")
        return 0
    if not OUTPUT.exists():
        print(f"missing {OUTPUT.relative_to(ROOT)}")
        return 1
    if OUTPUT.read_text(encoding="utf-8") != rendered:
        print(f"stale {OUTPUT.relative_to(ROOT)}; run --write")
        return 1
    counts: dict[str, int] = {item: 0 for item in DISPOSITIONS}
    for row in build_rows().values():
        counts[row.disposition] += 1
    print("constructor matrix: ok " + " ".join(
        f"{key}={counts[key]}" for key in sorted(counts)
    ))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
