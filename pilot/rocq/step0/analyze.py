#!/usr/bin/env python3
"""Summarize Step 0 QuickChick trace-mask distributions."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass, field
from pathlib import Path


RULE_BITS = {
    "A0-Synth": 1,
    "A0-Check": 2,
    "A0-T-Natural": 4,
    "A0-T-Top": 8,
    "A0-T-Variable": 16,
    "A0-T-Lambda-Pure": 32,
    "A0-T-Lambda-Effectful": 64,
    "A0-T-Check-Synth": 128,
    "A0-T-Context": 256,
    "A0-T-SelectExactly": 512,
    "A0-T-SelectSome": 1024,
    "A0-T-Bind-Reference": 2048,
    "A0-T-Apply-Pure": 4096,
    "A0-T-Apply-Effectful": 8192,
    "A0-T-Equality": 16384,
}

HEADER_RE = re.compile(
    r"^QuickChecking "
    r"(synth_generated|check_generated|synth_generation_only|check_generation_only)$"
)
BUCKET_RE = re.compile(r"^(\d+) : \((\d+), (\d+)\)$")
PASS_RE = re.compile(r"^\+\+\+ Passed (\d+) tests \((\d+) discards\)$")
GAVE_UP_RE = re.compile(r"^\*\*\* Gave up! Passed only (\d+) tests$")
DISCARDED_RE = re.compile(r"^Discarded: (\d+)$")
TIME_RE = re.compile(r"^Time Elapsed: ([0-9.]+)s$")


@dataclass
class Measurement:
    label: str
    buckets: list[tuple[int, int, int]] = field(default_factory=list)
    result: str | None = None
    cases: int | None = None
    discards: int | None = None
    seconds: float | None = None

    def finish(self) -> None:
        if self.cases is None or self.discards is None or self.seconds is None:
            raise ValueError(f"incomplete measurement for {self.label}")
        bucket_cases = sum(count for count, _, _ in self.buckets)
        if bucket_cases != self.cases:
            raise ValueError(
                f"{self.label}: buckets total {bucket_cases}, report says {self.cases}"
            )


def parse(path: Path) -> dict[str, Measurement]:
    measurements: dict[str, Measurement] = {}
    current: Measurement | None = None
    pending_give_up = False

    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if match := HEADER_RE.match(line):
            current = Measurement(match.group(1))
            measurements[current.label] = current
            pending_give_up = False
            continue
        if current is None:
            continue
        if match := BUCKET_RE.match(line):
            current.buckets.append(tuple(map(int, match.groups())))
        elif match := PASS_RE.match(line):
            current.result = "PASS"
            current.cases = int(match.group(1))
            current.discards = int(match.group(2))
        elif match := GAVE_UP_RE.match(line):
            current.result = "GAVE_UP"
            current.cases = int(match.group(1))
            pending_give_up = True
        elif pending_give_up and (match := DISCARDED_RE.match(line)):
            current.discards = int(match.group(1))
            pending_give_up = False
        elif match := TIME_RE.match(line):
            current.seconds = float(match.group(1))
            current.finish()
            current = None

    has_validated = {"synth_generated", "check_generated"} <= measurements.keys()
    has_generation = {
        "synth_generation_only",
        "check_generation_only",
    } <= measurements.keys()
    if not (has_validated or has_generation):
        raise ValueError("missing a complete synthesis/checking measurement pair")
    return measurements


def report(measurement: Measurement) -> None:
    assert measurement.cases is not None
    assert measurement.discards is not None
    assert measurement.seconds is not None
    max_depth = max(depth for _, _, depth in measurement.buckets)
    attempts = measurement.cases + measurement.discards
    discard_ratio = measurement.discards / attempts if attempts else 0.0
    per_minute = measurement.cases / measurement.seconds * 60

    print(f"## {measurement.label}")
    print(f"result: {measurement.result}")
    print(f"cases: {measurement.cases}")
    print(f"discards: {measurement.discards}")
    print(f"discard_ratio: {discard_ratio:.6f}")
    print(f"max_binder_depth: {max_depth}")
    print(f"elapsed_seconds: {measurement.seconds:.6f}")
    print(f"cases_per_minute: {per_minute:.2f}")
    print("rule_case_coverage:")
    for rule, bit in RULE_BITS.items():
        count = sum(
            bucket_count
            for bucket_count, mask, _ in measurement.buckets
            if mask & bit
        )
        print(f"  {rule}: {count}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("log", type=Path)
    args = parser.parse_args()
    measurements = parse(args.log)
    if "synth_generated" in measurements:
        synth_label = "synth_generated"
        check_label = "check_generated"
    else:
        synth_label = "synth_generation_only"
        check_label = "check_generation_only"
    report(measurements[synth_label])
    print()
    report(measurements[check_label])


if __name__ == "__main__":
    main()
