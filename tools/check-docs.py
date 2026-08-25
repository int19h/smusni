#!/usr/bin/env python3
"""Tracked read-only consistency checks for the documentation corpus."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


CORPUS = [
    "brief.md",
    "primer.md",
    "spec.md",
    "catalog.md",
    "cmavo.md",
    "samples.md",
    "rationale.md",
]


def missing_links(root: Path) -> list[tuple[Path, int, str]]:
    failures: list[tuple[Path, int, str]] = []
    link_re = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
    for path in root.glob("*.md"):
        source = path.read_text()
        for match in link_re.finditer(source):
            target = match.group(1).split("#", 1)[0]
            if not target or "://" in target or target.startswith("mailto:"):
                continue
            if not (path.parent / target).exists():
                failures.append(
                    (path, source.count("\n", 0, match.start()) + 1, match.group(1))
                )
    return failures


def missing_pins(root: Path) -> list[int]:
    pins = {int(value) for value in re.findall(r"\bP(\d+)\b", (root / "spec.md").read_text())}
    return sorted(set(range(1, 38)) - pins)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", nargs="?", default=".")
    args = parser.parse_args()
    root = Path(args.root).resolve()

    missing_files = [name for name in CORPUS if not (root / name).is_file()]
    links = [] if missing_files else missing_links(root)
    pins = [] if missing_files else missing_pins(root)

    print(f"documentation_files_missing={missing_files}")
    print(f"relative_links_missing={len(links)}")
    for path, line, target in links:
        print(f"  {path.relative_to(root)}:{line}: missing {target}")
    print(f"pins_missing={pins}")
    return int(bool(missing_files or links or pins))


if __name__ == "__main__":
    raise SystemExit(main())

