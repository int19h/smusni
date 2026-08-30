#!/usr/bin/env python3
"""Generate Lean M2 definition and typing inventory constants."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
DEFINITIONS = ROOT / "pilot/shared/M2_DEFINITION_MANIFEST.json"
TYPING = ROOT / "pilot/shared/M2_TYPING_MANIFEST.json"
OUTPUT = ROOT / "pilot/lean/SmusniPilot/M2Inventory.lean"


def lower_camel(parts: list[str]) -> str:
    first, *rest = parts
    return first[:1].lower() + first[1:] + "".join(
        part[:1].upper() + part[1:] for part in rest
    )


def lean_name(raw: str) -> str:
    special = {
        "τ": "type",
        "ρdecl": "rowDeclaration",
        "Γ": "environment",
    }
    if raw in special:
        return special[raw]
    parts = re.findall(r"[A-Za-z0-9]+", raw)
    if not parts:
        raise ValueError(f"cannot derive Lean name from {raw!r}")
    name = lower_camel(parts)
    if name[0].isdigit():
        name = "n" + name
    return name


def q(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def string_list(values: list[str]) -> str:
    return "[" + ", ".join(q(value) for value in values) + "]"


def range_list(values: list[list[int]]) -> str:
    return "[" + ", ".join(
        f"{{ start := {start}, stop := {stop} }}" for start, stop in values
    ) + "]"


def render_enum(name: str, rows: list[tuple[str, str]]) -> str:
    constructors = "\n".join(f"  | {constructor}" for constructor, _ in rows)
    names = "\n".join(
        f"  | .{constructor} => {q(raw)}" for constructor, raw in rows
    )
    all_values = "\n".join(f"  .{constructor}," for constructor, _ in rows)
    return f"""inductive {name} where
{constructors}
  deriving Repr, DecidableEq, BEq

def {name}.name : {name} → String
{names}

def {name}.all : List {name} := [
{all_values}
]

"""


def render() -> str:
    definitions = json.loads(DEFINITIONS.read_text(encoding="utf-8"))
    typing = json.loads(TYPING.read_text(encoding="utf-8"))

    definition_rows = [
        (lean_name(row["id"]), row["id"]) for row in definitions["definitions"]
    ]
    clause_rows: list[tuple[str, str]] = []
    clause_by_definition: dict[str, list[str]] = {}
    definition_by_clause: dict[str, str] = {}
    for row in definitions["definitions"]:
        clauses = []
        for case in row["cases"]:
            raw = f"{row['id']}/{case}"
            constructor = lean_name(f"{row['id']}_{case}")
            clause_rows.append((constructor, raw))
            clauses.append(constructor)
            definition_by_clause[constructor] = lean_name(row["id"])
        clause_by_definition[row["id"]] = clauses

    typing_rows = [
        (lean_name(rule["id"]), rule["id"]) for rule in typing["rules"]
    ]
    grammar_rows = [
        (lean_name(name), name) for name in typing["grammar"]
    ]
    for label, rows in (
        ("definitions", definition_rows),
        ("clauses", clause_rows),
        ("typing rules", typing_rows),
        ("grammar categories", grammar_rows),
    ):
        names = [name for name, _ in rows]
        duplicates = sorted({name for name in names if names.count(name) > 1})
        if duplicates:
            raise ValueError(f"duplicate Lean names in {label}: {duplicates}")

    records = []
    for row in definitions["definitions"]:
        constructor = lean_name(row["id"])
        selection = {
            "definition-port-state": ".definitionPortState",
            "plan-v2-extra": ".planV2Extra",
            "dependency-closure": ".dependencyClosure",
        }[row["selection"]]
        supplement = row["supplement"]
        supplement_kind = (
            "none" if supplement is None
            else f"some {q(supplement['kind'])}"
        )
        clauses = "[" + ", ".join(
            f".{name}" for name in clause_by_definition[row["id"]]
        ) + "]"
        domains = string_list(
            [domain["name"] for domain in row["selected_domains"]]
        )
        records.append(f"""  | .{constructor} => {{
      id := .{constructor}
      head := {q(row['head'])}
      selection := {selection}
      portState := {q(row['port_state'])}
      dependencies := {string_list(row['dependencies'])}
      clauses := {clauses}
      selectedDomains := {domains}
      specRanges := {range_list(row['spec']['ranges'])}
      equationRanges := {range_list(row['equation']['ranges'])}
      specDigest := {q(row['spec']['range_sha256'])}
      equationDigest := {q(row['equation']['range_sha256'])}
      supplementKind := {supplement_kind}
    }}""")

    typing_records = []
    for rule in typing["rules"]:
        constructor = lean_name(rule["id"])
        ranges = rule["source_ranges"]
        typing_records.append(f"""  | .{constructor} => {{
      id := .{constructor}
      kind := {q(rule['kind'])}
      subject := {q(rule['subject'])}
      anchor := {q(rule['anchor'])}
      sourcePath := {q(rule['source_path'])}
      sourceRanges := {range_list(ranges)}
      sourceDigest := {q(rule['source_sha256'])}
      conclusion := {q(rule['conclusion'])}
      reason := {q(rule['reason'])}
    }}""")

    grammar_records = []
    for name, record in typing["grammar"].items():
        constructor = lean_name(name)
        start, stop = record["source_range"]
        grammar_records.append(f"""  | .{constructor} => {{
      category := .{constructor}
      sourceRange := {{ start := {start}, stop := {stop} }}
      sourceDigest := {q(record['source_sha256'])}
      source := {q(record['source'])}
    }}""")

    constant_records = ",\n".join(
        "  { name := " + q(record["name"]) +
        ", typeSource := " + q(record["type"]) +
        ", anchor := " + q(record["anchor"]) + " }"
        for record in typing["constants"]
    )
    lexical_records = ",\n".join(
        "  { head := " + q(record["head"]) +
        ", ordinaryArity := " + str(record["ordinary_arity"]) +
        ", eventMode := " +
        (".directEvent" if record["event_mode"] == "direct-event"
         else ".holdingState") +
        ", provenance := " + q(record["provenance"]) + " }"
        for record in typing["lexical_rows"]
    )
    disposition_records = ",\n".join(
        "  { id := " + q(record["id"]) +
        ", head := " + q(record["head"]) +
        ", status := " + q(record["status"]["kind"]) +
        ", issue := " + ("none" if record["status"]["issue"] is None
                           else "some " + q(record["status"]["issue"])) +
        ", portState := " + q(record["port_state"]) +
        ", selected := " + ("true" if record["selected"] else "false") +
        ", reason := " + q(record["reason"]) + " }"
        for record in definitions["catalog"]
    )

    body = render_enum("M2DefinitionId", definition_rows)
    body += render_enum("M2ClauseId", clause_rows)
    body += "def M2ClauseId.definition : M2ClauseId → M2DefinitionId\n" + "\n".join(
        f"  | .{clause} => .{definition}"
        for clause, definition in definition_by_clause.items()
    ) + "\n\n"
    body += render_enum("M2TypingRuleId", typing_rows)
    body += render_enum("M2GrammarCategory", grammar_rows)
    return f"""-- Generated by build_m2_inventory.py from the pinned M2 manifests.
-- Do not edit by hand.

namespace SmusniPilot

{body}structure SourceRange where
  start : Nat
  stop : Nat
  deriving Repr, DecidableEq, BEq

inductive M2DefinitionSelection where
  | definitionPortState
  | planV2Extra
  | dependencyClosure
  deriving Repr, DecidableEq, BEq

structure M2DefinitionRecord where
  id : M2DefinitionId
  head : String
  selection : M2DefinitionSelection
  portState : String
  dependencies : List String
  clauses : List M2ClauseId
  selectedDomains : List String
  specRanges : List SourceRange
  equationRanges : List SourceRange
  specDigest : String
  equationDigest : String
  supplementKind : Option String
  deriving Repr, DecidableEq, BEq

def M2DefinitionId.record : M2DefinitionId → M2DefinitionRecord
{chr(10).join(records)}

def m2DefinitionRecords : List M2DefinitionRecord :=
  M2DefinitionId.all.map M2DefinitionId.record

structure M2DefinitionDispositionRecord where
  id : String
  head : String
  status : String
  issue : Option String
  portState : String
  selected : Bool
  reason : String
  deriving Repr, DecidableEq, BEq

def m2DefinitionDispositionRecords : List M2DefinitionDispositionRecord := [
{disposition_records}
]

structure M2TypingRuleRecord where
  id : M2TypingRuleId
  kind : String
  subject : String
  anchor : String
  sourcePath : String
  sourceRanges : List SourceRange
  sourceDigest : String
  conclusion : String
  reason : String
  deriving Repr, DecidableEq, BEq

def M2TypingRuleId.record : M2TypingRuleId → M2TypingRuleRecord
{chr(10).join(typing_records)}

def m2TypingRuleRecords : List M2TypingRuleRecord :=
  M2TypingRuleId.all.map M2TypingRuleId.record

structure M2CoreConstantRecord where
  name : String
  typeSource : String
  anchor : String
  deriving Repr, DecidableEq, BEq

def m2CoreConstantRecords : List M2CoreConstantRecord := [
{constant_records}
]

inductive M2LexicalEventMode where
  | holdingState
  | directEvent
  deriving Repr, DecidableEq, BEq

structure M2LexicalRowRecord where
  head : String
  ordinaryArity : Nat
  eventMode : M2LexicalEventMode
  provenance : String
  deriving Repr, DecidableEq, BEq

def m2LexicalRowRecords : List M2LexicalRowRecord := [
{lexical_records}
]

structure M2GrammarRecord where
  category : M2GrammarCategory
  sourceRange : SourceRange
  sourceDigest : String
  source : String
  deriving Repr, DecidableEq, BEq

def M2GrammarCategory.record : M2GrammarCategory → M2GrammarRecord
{chr(10).join(grammar_records)}

def m2GrammarRecords : List M2GrammarRecord :=
  M2GrammarCategory.all.map M2GrammarCategory.record

def m2DefinitionManifestDigest : String :=
  {q(definitions['sources']['definitions_sha256'])}

def m2TypingManifestDigest : String :=
  {q(typing['sources']['redex_sha256'])}

end SmusniPilot
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = render()
    if args.write:
        OUTPUT.write_text(result, encoding="utf-8")
        print(f"wrote {OUTPUT.relative_to(ROOT)}")
        return 0
    if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != result:
        print(f"stale or missing {OUTPUT.relative_to(ROOT)}; run --write")
        return 1
    definitions = json.loads(DEFINITIONS.read_text(encoding="utf-8"))
    typing = json.loads(TYPING.read_text(encoding="utf-8"))
    print(
        "Lean M2 inventory: ok "
        f"definitions={definitions['counts']['selected_definitions']} "
        f"clauses={definitions['counts']['selected_clauses']} "
        f"typing-rules={typing['counts']['required_rules']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
