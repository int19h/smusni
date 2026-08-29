#!/usr/bin/env python3
"""Fail-closed provisioning pin verification and negative self-tests."""

from __future__ import annotations

import argparse
import hashlib
import re
import shutil
import subprocess
import tempfile
import tomllib
from pathlib import Path


class PinError(RuntimeError):
    pass


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run(*args: str, cwd: Path | None = None) -> str:
    completed = subprocess.run(
        args,
        cwd=cwd,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return completed.stdout.strip()


def load_toml(path: Path) -> dict:
    with path.open("rb") as stream:
        return tomllib.load(stream)


def verify_lean(pilot_root: Path, toolchain_path: Path | None = None) -> None:
    lean_dir = pilot_root / "lean"
    lock = load_toml(lean_dir / "toolchain-lock.toml")
    toolchain_path = toolchain_path or lean_dir / "lean-toolchain"
    actual_toolchain = toolchain_path.read_text(encoding="utf-8").strip()
    if actual_toolchain != lock["toolchain"]:
        raise PinError(
            f"Lean toolchain mismatch: {actual_toolchain!r} != {lock['toolchain']!r}"
        )
    lean_binary = shutil.which("lean")
    elan_binary = shutil.which("elan")
    if (
        not lean_binary
        or not elan_binary
        or Path(lean_binary).resolve() != Path(elan_binary).resolve()
    ):
        raise PinError("Lean is not being selected through the elan proxy")
    lean_output = run("lean", "--version", cwd=lean_dir)
    if f"version {lock['lean_version']}" not in lean_output:
        raise PinError(f"Lean version mismatch: {lean_output}")
    if f"commit {lock['lean_commit']}" not in lean_output:
        raise PinError(f"Lean commit mismatch: {lean_output}")
    lake_output = run("lake", "--version", cwd=lean_dir)
    if f"Lake version {lock['lake_version_prefix']}" not in lake_output:
        raise PinError(f"Lake version mismatch: {lake_output}")
    manifest = lean_dir / "lake-manifest.json"
    if sha256(manifest) != lock["manifest_sha256"]:
        raise PinError("lake-manifest.json digest differs from toolchain-lock.toml")
    manifest_text = manifest.read_text(encoding="utf-8")
    if lock["plausible_revision"] not in manifest_text:
        raise PinError("Plausible revision is absent from lake-manifest.json")


LOCK_DEPENDENCY = re.compile(r'^\s*"([^"]+)"\s*\{=\s*"([^"]+)"\}\s*$')


def parse_locked_closure(path: Path) -> dict[str, str]:
    closure: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        match = LOCK_DEPENDENCY.match(line)
        if match:
            name, version = match.groups()
            if name in closure:
                raise PinError(f"duplicate package in opam lock: {name}")
            closure[name] = version
    if not closure:
        raise PinError("opam lock contains no exact dependencies")
    return closure


def installed_closure(switch: str) -> dict[str, str]:
    output = run(
        "opam",
        "list",
        "--switch",
        switch,
        "--installed",
        "--short",
        "--columns=name,version",
        "--separator==",
        "--color=never",
    )
    result: dict[str, str] = {}
    for line in output.splitlines():
        name, separator, version = line.partition("=")
        if not separator:
            raise PinError(f"unparseable opam list row: {line!r}")
        result[name.strip()] = version.strip()
    return result


def verify_rocq(
    pilot_root: Path, switch: str, lock_path: Path | None = None
) -> None:
    rocq_dir = pilot_root / "rocq"
    lock_path = lock_path or rocq_dir / "smusni-pilot-rocq.opam.locked"
    expected = parse_locked_closure(lock_path)
    actual = installed_closure(switch)
    if expected != actual:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        changed = sorted(
            name
            for name in set(expected) & set(actual)
            if expected[name] != actual[name]
        )
        raise PinError(
            f"opam closure mismatch: missing={missing} extra={extra} changed={changed}"
        )
    snapshot = load_toml(rocq_dir / "repository-snapshot.toml")
    opam_root = Path(run("opam", "var", "root"))
    repos_config = opam_root / "repo" / "repos-config"
    if sha256(repos_config) != snapshot["repos_config_sha256"]:
        raise PinError("opam repository configuration differs from snapshot")
    for package in snapshot["packages"]:
        opam_file = (
            opam_root
            / "repo"
            / package["repository"]
            / "packages"
            / package["name"]
            / f"{package['name']}.{package['version']}"
            / "opam"
        )
        if not opam_file.is_file():
            raise PinError(f"snapshot package metadata is absent: {opam_file}")
        if sha256(opam_file) != package["opam_sha256"]:
            raise PinError(f"package metadata changed: {package['name']}")


def verify_isabelle(
    pilot_root: Path, isabelle_bin: str, bundle_path: Path | None = None
) -> None:
    bundle_path = bundle_path or pilot_root / "isabelle" / "bundle.toml"
    bundle = load_toml(bundle_path)
    actual = run(isabelle_bin, "version").strip()
    if actual != bundle["release"]:
        raise PinError(f"Isabelle release mismatch: {actual!r} != {bundle['release']!r}")


def expect_failure(label: str, action) -> None:
    try:
        action()
    except PinError:
        return
    raise PinError(f"negative self-test did not fail: {label}")


def self_test(pilot_root: Path, switch: str, isabelle_bin: str) -> None:
    with tempfile.TemporaryDirectory(prefix="smusni-pin-selftest-") as directory:
        temporary = Path(directory)
        wrong_toolchain = temporary / "lean-toolchain"
        wrong_toolchain.write_text("leanprover/lean4:v0.0.0\n", encoding="utf-8")
        expect_failure(
            "Lean toolchain",
            lambda: verify_lean(pilot_root, wrong_toolchain),
        )

        lock_source = pilot_root / "rocq" / "smusni-pilot-rocq.opam.locked"
        wrong_lock = temporary / "wrong.opam.locked"
        lock_text = lock_source.read_text(encoding="utf-8")
        wrong_lock.write_text(
            lock_text.replace('"angstrom" {= "0.16.1"}', '"angstrom" {= "0.0.0"}', 1),
            encoding="utf-8",
        )
        expect_failure(
            "opam closure",
            lambda: verify_rocq(pilot_root, switch, wrong_lock),
        )

        wrong_bundle = temporary / "bundle.toml"
        bundle_text = (pilot_root / "isabelle" / "bundle.toml").read_text(
            encoding="utf-8"
        )
        wrong_bundle.write_text(
            bundle_text.replace('release = "Isabelle2025-2"', 'release = "Wrong"', 1),
            encoding="utf-8",
        )
        expect_failure(
            "Isabelle release",
            lambda: verify_isabelle(pilot_root, isabelle_bin, wrong_bundle),
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pilot-root", type=Path, required=True)
    parser.add_argument("--rocq-switch", default="smusni-pilot-rocq")
    parser.add_argument("--isabelle-bin", required=True)
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    pilot_root = arguments.pilot_root.resolve()
    verify_lean(pilot_root)
    verify_rocq(pilot_root, arguments.rocq_switch)
    verify_isabelle(pilot_root, arguments.isabelle_bin)
    if arguments.self_test:
        self_test(pilot_root, arguments.rocq_switch, arguments.isabelle_bin)
    print("provisioning pins: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
