#!/usr/bin/env python3
"""Export the immutable merged E02 checkpoint before F01 input migration."""
import archive_pre_e02 as archive

archive.REVISION = "01759ba0042744fb8694c9214842c93aa1a684ff"
archive.DESTINATION = archive.ROOT / "pilot/history/pre-f01"
archive.PATHS += [
    "pilot/shared/M2_MIGRATION.json",
    "pilot/shared/M2_ORACLE_SOURCES.sexp",
    "tools/smusni-redex/inventory/port-corpus.sexp",
    "pilot/lean/E02_ASSERT_BRIDGE.md",
    "pilot/lean/E02_CONSUMER_BATCH01.md",
    "pilot/lean/E02_NEGATION_FIDELITY.md",
]

if __name__ == "__main__":
    archive.main(corpus="pilot/history/pre-f01/port-corpus.sexp", label="pre-F01")
