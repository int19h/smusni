#!/usr/bin/env python3
"""Reproduce the immutable pre-E02 pilot inputs and reported results from Git.

This is a historical export, not a current validation run. Never archives the
working tree or replaces an existing snapshot with different bytes.
"""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[2]
REVISION = "18cd6267ad38abde8836a553f1531a4f05f339c6"
DESTINATION = ROOT / "pilot/history/pre-e02"
PATHS = [
    "pilot/shared/M1_CONSTRUCTOR_DISPOSITION.tsv",
    "pilot/shared/M1_S1_MANIFEST.json",
    "pilot/shared/M1_INPUTS.md",
    "pilot/shared/M2_CASE_MANIFEST.json",
    "pilot/shared/M2_DEFINITION_MANIFEST.json",
    "pilot/shared/M2_TYPING_MANIFEST.json",
    "pilot/shared/M2_REDEX_ORACLE.sexp",
    "pilot/shared/M2_RANGE_SUPPLEMENT.tsv",
    "pilot/shared/M2_DEPENDENCY_SUPPLEMENT.tsv",
    "pilot/shared/M2_TYPING_SUPPLEMENT.tsv",
    "pilot/lean/M1_REPORT.md",
    "pilot/lean/M2_REPORT.md",
]


def main():
    records = []
    for name in PATHS:
        data = subprocess.check_output(["git", "show", f"{REVISION}:{name}"], cwd=ROOT)
        target = DESTINATION / Path(name).name
        if target.exists() and target.read_bytes() != data:
            raise SystemExit(f"refusing to replace historical snapshot {target}")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        records.append({"source": name, "snapshot": target.name,
                        "sha256": hashlib.sha256(data).hexdigest()})
    manifest = {"source_revision": REVISION,
                "status": "historical inputs and reported results, not current validation",
                "corpus": "tools/smusni-redex/inventory/history/pre-e01-port-corpus.sexp",
                "files": records}
    data = (json.dumps(manifest, indent=2) + "\n").encode()
    target = DESTINATION / "ARCHIVE.json"
    if target.exists() and target.read_bytes() != data:
        raise SystemExit("refusing to replace historical archive manifest")
    target.write_bytes(data)
    print(f"pre-E02 archive verified: {len(records)} files from {REVISION}")


if __name__ == "__main__":
    main()
