#!/usr/bin/env python3
"""Generate the all-S1 M2 cohort manifest without fixture-keyed outputs."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from build_m1_constructor_matrix import ROOT, sha256


S1 = ROOT / "pilot/shared/M1_S1_MANIFEST.json"
DEFINITIONS = ROOT / "pilot/shared/M2_DEFINITION_MANIFEST.json"
OUTPUT = ROOT / "pilot/shared/M2_CASE_MANIFEST.json"


def build() -> dict[str, Any]:
    s1 = json.loads(S1.read_text(encoding="utf-8"))
    definitions = json.loads(DEFINITIONS.read_text(encoding="utf-8"))
    parity_heads = {
        row["head"] for row in definitions["definitions"]
        if row["selection"] == "definition-port-state"
    }
    if len(parity_heads) != 19:
        raise ValueError(f"expected 19 generated parity heads, got {len(parity_heads)}")

    parity: list[str] = []
    extras: list[str] = []
    primitive: list[str] = []
    residual_pending: list[str] = []
    out_of_slice: list[str] = []
    for case in s1["cases"]:
        defined = set(case["defined_heads"])
        if case["tag"] == "primitive-core":
            primitive.append(case["id"])
        elif case["tag"] == "out-of-slice":
            out_of_slice.append(case["id"])
        elif defined and defined <= parity_heads:
            parity.append(case["id"])
        elif defined & {"Grade", "JaiRaise"}:
            extras.append(case["id"])
        else:
            residual_pending.append(case["id"])

    if len(parity) != 160:
        raise ValueError(f"expected generated parity cohort 160, got {len(parity)}")
    if len(extras) != 3:
        raise ValueError(f"expected Grade/Jai corpus extras 3, got {len(extras)}")
    if len(primitive) != 50 or len(out_of_slice) != 31:
        raise ValueError("S1 primitive/out-of-slice cohort drift")
    if len(parity) + len(extras) + len(primitive) + len(residual_pending) + \
            len(out_of_slice) != s1["counts"]["total_cases"]:
        raise ValueError("M2 cohorts do not partition all S1 cases")

    return {
        "schema": "smusni-lean-m2-case-manifest",
        "version": 1,
        "sources": {
            "s1": str(S1.relative_to(ROOT)),
            "s1_sha256": sha256(S1),
            "definitions": str(DEFINITIONS.relative_to(ROOT)),
            "definitions_sha256": sha256(DEFINITIONS),
        },
        "parity_heads": sorted(parity_heads),
        "counts": {
            "total": s1["counts"]["total_cases"],
            "definition_parity": len(parity),
            "plan_corpus_extras": len(extras),
            "primitive_baseline": len(primitive),
            "residual_pending": len(residual_pending),
            "out_of_slice": len(out_of_slice),
        },
        "cohorts": {
            "definition_parity": sorted(parity),
            "plan_corpus_extras": sorted(extras),
            "primitive_baseline": sorted(primitive),
            "residual_pending": sorted(residual_pending),
            "out_of_slice": sorted(out_of_slice),
        },
    }


def encoded(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = encoded(build())
    if args.write:
        OUTPUT.write_text(result, encoding="utf-8")
        print(f"wrote {OUTPUT.relative_to(ROOT)}")
        return 0
    if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != result:
        raise SystemExit(f"stale {OUTPUT.relative_to(ROOT)}; regenerate with --write")
    counts = json.loads(result)["counts"]
    print("M2 case manifest: ok " + " ".join(
        f"{key}={value}" for key, value in counts.items()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
