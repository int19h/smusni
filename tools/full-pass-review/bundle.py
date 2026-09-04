#!/usr/bin/env python3
"""Build a manifest-bearing bundle for one conventionally labelled full pass."""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_DOCS = ["brief.md", "spec.md", "rationale.md", "samples.md", "primer.md"]


def positive_generation(value: str) -> int:
    """Parse a strictly positive full-pass generation label."""
    try:
        generation = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("generation must be an integer") from error
    if generation <= 0:
        raise argparse.ArgumentTypeError("generation must be positive")
    return generation


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generation", required=True, type=positive_generation)
    parser.add_argument("--docs", nargs="+", default=DEFAULT_DOCS)
    args = parser.parse_args()

    output_directory = ROOT / "review" / "bundle"
    output_directory.mkdir(parents=True, exist_ok=True)
    output_path = output_directory / f"full-pass-{args.generation}.md"
    rows: list[tuple[str, int, str]] = []
    parts: list[str] = []
    for name in args.docs:
        path = ROOT / name
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        lines = data.count(b"\n")
        rows.append((name, lines, digest))
        parts.append(
            f"\n\n<!-- ===== BEGIN {name} lines={lines} sha256={digest} ===== -->\n\n"
            + data.decode("utf-8")
            + f"\n\n<!-- ===== END {name} ===== -->\n"
        )

    manifest = "\n".join(
        f"| `{name}` | {lines} | `{digest}` |" for name, lines, digest in rows
    )
    header = (
        f"# Full-pass review bundle, generation {args.generation}\n\n"
        "Read every document below in full. Before reviewing, attest by echoing\n"
        "each document's line count and SHA-256 from the text you loaded; if you\n"
        "cannot hold the whole bundle, say so instead of reviewing a part.\n\n"
        "| document | lines | sha256 |\n|---|---|---|\n"
        + manifest
        + "\n"
    )
    output_path.write_text(header + "".join(parts))
    print(output_path)
    print(header)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
