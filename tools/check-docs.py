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


def lisp_balance(root: Path) -> list[tuple[Path, int, str]]:
    """Check paired delimiters outside strings/comments in every Lisp fence."""
    failures: list[tuple[Path, int, str]] = []
    for name in CORPUS:
        path = root / name
        stack: list[tuple[str, int]] = []
        in_fence = False
        in_string = escaped = False
        start = 0
        for line_number, line in enumerate(path.read_text().splitlines(), 1):
            if not in_fence:
                if re.fullmatch(r"\s*```lisp\s*", line):
                    in_fence, start = True, line_number
                    stack = []
                    in_string = escaped = False
                continue
            if re.fullmatch(r"\s*```\s*", line):
                for opening, location in stack:
                    failures.append((path, location, f"unclosed {opening}"))
                if in_string:
                    failures.append((path, start, "unclosed string"))
                in_fence = False
                continue
            for char in line:
                if in_string:
                    if escaped:
                        escaped = False
                    elif char == "\\":
                        escaped = True
                    elif char == '"':
                        in_string = False
                    continue
                if char == ";":
                    break
                if char == '"':
                    in_string = True
                elif char in "([{":
                    stack.append((char, line_number))
                elif char in ")]}":
                    expected = dict(zip(")]}", "([{"))[char]
                    if not stack or stack[-1][0] != expected:
                        failures.append((path, line_number, f"unmatched {char}"))
                    else:
                        stack.pop()
            # A backslash before the physical newline escapes that newline.
            escaped = False
        if in_fence:
            failures.append((path, start, "unclosed Lisp fence"))
    return failures


def agents_is_standalone(root: Path) -> bool:
    agents = root / "AGENTS.md"
    if not agents.is_file():
        return False
    text = agents.read_text()
    return not any((root / name).read_text().strip() in text
                   for name in CORPUS if (root / name).read_text().strip())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", nargs="?", default=".")
    args = parser.parse_args()
    root = Path(args.root).resolve()

    missing_files = [name for name in CORPUS if not (root / name).is_file()]
    links = [] if missing_files else missing_links(root)
    pins = [] if missing_files else missing_pins(root)
    balance = [] if missing_files else lisp_balance(root)
    standalone = False if missing_files else agents_is_standalone(root)

    print(f"documentation_files_missing={missing_files}")
    print(f"relative_links_missing={len(links)}")
    for path, line, target in links:
        print(f"  {path.relative_to(root)}:{line}: missing {target}")
    print(f"pins_missing={pins}")
    print(f"lisp_balance_failures={len(balance)}")
    for path, line, problem in balance:
        print(f"  {path.relative_to(root)}:{line}: {problem}")
    print(f"agents_is_standalone={standalone}")
    return int(bool(missing_files or links or pins or balance or not standalone))


if __name__ == "__main__":
    raise SystemExit(main())
