#!/usr/bin/env python3
"""Generate the full-pass review bundle: the in-scope documents concatenated in
order, each preceded by its name, line count, and SHA-256, with a manifest.

Usage: python3 tools/review-exchange/bundle.py [--docs a.md b.md ...]
Writes review/bundle/full-pass-<generation>.md (ignored) and prints its path
and the manifest so the same numbers can be quoted in the launch instruction.
"""
from __future__ import annotations

import argparse
import hashlib
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_DOCS = ["brief.md", "spec.md", "rationale.md", "samples.md", "primer.md"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--docs", nargs="+", default=DEFAULT_DOCS)
    a = ap.parse_args()
    reg = tomllib.loads((ROOT / "tools" / "review-exchange" / "participants.toml").read_text())
    gen = int(reg.get("generation", 1))
    out_dir = ROOT / "review" / "bundle"
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / f"full-pass-{gen}.md"
    rows, parts = [], []
    for name in a.docs:
        path = ROOT / name
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        lines = data.count(b"\n")
        rows.append((name, lines, digest))
        parts.append(f"\n\n<!-- ===== BEGIN {name} lines={lines} sha256={digest} ===== -->\n\n"
                     + data.decode("utf-8") + f"\n\n<!-- ===== END {name} ===== -->\n")
    manifest = "\n".join(f"| `{n}` | {l} | `{d}` |" for n, l, d in rows)
    head = (f"# Full-pass review bundle, generation {gen}\n\n"
            "Read every document below in full. Before reviewing, attest by echoing\n"
            "each document's line count and SHA-256 from the text you loaded; if you\n"
            "cannot hold the whole bundle, say so instead of reviewing a part.\n\n"
            "| document | lines | sha256 |\n|---|---|---|\n" + manifest + "\n")
    out.write_text(head + "".join(parts))
    print(out)
    print(head)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
