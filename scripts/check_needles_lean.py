#!/usr/bin/env python3
"""Build-check the repo-local SixBirdsMetaMath Lean project.

Runs:

1. Structural prechecks: required files exist; no forbidden Lean
   tokens (sorry, admit, axiom, opaque, constant); no external path
   references in active source files.
2. Python validators chain: extract inventory, audit
   foundations deps (skip-validation/skip-probe by default), check
   provenance, semantic alignment, paper inventories,
   imported-foundations canary.
3. `lake build` in `lean/`.

Use --skip-prechecks to run only the lake build (e.g. inside a
top-level verifier). Use --skip-build to run only the prechecks
(e.g. when `lake` isn't available in PATH).
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "lean"
VENDOR_DIR = ROOT / "vendor" / "foundations"

STATIC_BUILD_ARTIFACTS = (
    LEAN_DIR / ".lake",
    LEAN_DIR / "lake-manifest.json",
    VENDOR_DIR / "six-birds-theory" / "formal" / ".lake",
    VENDOR_DIR / "six-birds-theory" / "formal" / "lake-manifest.json",
    VENDOR_DIR / "six-birds-foundations-ii" / "lean" / "full" / ".lake",
    VENDOR_DIR / "six-birds-foundations-ii" / "lean" / "full" / "lake-manifest.json",
    VENDOR_DIR / "six-birds-foundations-iii" / "lean" / "full" / ".lake",
    VENDOR_DIR / "six-birds-foundations-iii" / "lean" / "full" / "lake-manifest.json",
)
FORBIDDEN_LEAN_TOKENS = re.compile(r"\b(sorry|admit|axiom|opaque|constant)\b")
LEGACY_TRUST_REGISTER = LEAN_DIR / "manifests" / "legacy_obligations.toml"
DECLARATION_TOKEN_RE = re.compile(r"^\s*(axiom|opaque|constant)\s+([A-Za-z0-9_']+)")
FORBIDDEN_EXTERNAL_REFS = (
    "../" + "six-birds-",
    "/home" + "/repos/",
)
PACKAGE_DEPENDENCY_PATHS = {
    "SixBirdsNeedles": "../" + "../" + "six-birds-needles/lean",
    "SixBirdsDualityConfinement": "../" + "../" + "six-birds-duality-confinement/lean",
    "SixBirdsHiddenness": "../" + "../" + "six-birds-hiddenness/lean",
}


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def run(command: list[str], *, cwd: Path) -> tuple[int, str]:
    result = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return result.returncode, result.stdout


def build_artifacts() -> list[Path]:
    artifacts = list(STATIC_BUILD_ARTIFACTS)
    artifacts.extend(LEAN_DIR.glob("**/*.olean"))
    artifacts.extend(LEAN_DIR.glob("**/*.ilean"))
    return sorted({path for path in artifacts if path.exists()})


def cleanup() -> None:
    for artifact in build_artifacts():
        if artifact.is_dir():
            shutil.rmtree(artifact)
        elif artifact.exists():
            artifact.unlink()


REQUIRED_FILES = [
    LEAN_DIR / "lean-toolchain",
    LEGACY_TRUST_REGISTER,
    LEAN_DIR / "lakefile.toml",
    LEAN_DIR / "README.md",
    LEAN_DIR / "SixBirdsMetaMath.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "ImportedFoundations.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "FoundationsICompat.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Terminology.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Main.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Main" / "LegalQuotient.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Main" / "XiInterface.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Main" / "PredictiveNative.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Main" / "LayerDissolving.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Main" / "DualityConfinement.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Main" / "CriticalPair.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Main" / "AllSix.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Xi.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Xi" / "StandingHypotheses.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Xi" / "Currency.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Xi" / "AdequacyResidual.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Xi" / "Projection.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Xi" / "OptimalResidual.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Xi" / "Promotion.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Xi" / "StrictExtension.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Xi" / "DataProcessing.lean",
    LEAN_DIR / "SixBirdsMetaMath" / "Xi" / "Obstruction.lean",
]


def check_required_files() -> list[str]:
    return [f"missing {rel(path)}" for path in REQUIRED_FILES if not path.exists()]


def lean_source_files() -> list[Path]:
    files: list[Path] = []
    files.extend(sorted((LEAN_DIR / "SixBirdsMetaMath").rglob("*.lean")))
    files.append(LEAN_DIR / "SixBirdsMetaMath.lean")
    return [path for path in files if path.exists()]


def active_source_files() -> list[Path]:
    files = lean_source_files() + [
        LEAN_DIR / "lakefile.toml",
        LEAN_DIR / "lean-toolchain",
        ROOT / "scripts" / "check_needles_lean.py",
        ROOT / "scripts" / "extract_latex_inventory.py",
        ROOT / "scripts" / "audit_foundations_dependencies.py",
        ROOT / "scripts" / "check_foundations_provenance.py",
        ROOT / "scripts" / "check_semantic_alignment.py",
        ROOT / "scripts" / "build_paper_inventories.py",
        ROOT / "scripts" / "generate_imported_foundations.py",
        ROOT / "scripts" / "check_manifests.py",
        ROOT / "scripts" / "test_check_manifests.py",
        LEAN_DIR / "manifests" / "section_module_map.toml",
        # Operational runbooks and prompt-generation helpers are not part of the
        # public validation surface scanned for external path references.
    ]
    return [path for path in files if path.exists()]


BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)


def mask_lean_comments(text: str) -> str:
    """Mask Lean comments so token scans skip prose.

    Non-newline characters inside `/- ... -/` block comments (including
    `/-! ... -/` doc comments) become spaces so line/column positions
    are preserved for error reporting. Line comments (`-- ...`) are
    stripped per-line by the caller.

    The regex is non-nested. Lean supports nested block comments, but
    for the validator's purpose a nested block containing a forbidden
    token will still be flagged — that's a conservative false positive
    we accept.
    """
    def _mask(match: re.Match[str]) -> str:
        return "".join(ch if ch == "\n" else " " for ch in match.group(0))
    return BLOCK_COMMENT_RE.sub(_mask, text)


def check_no_forbidden_lean_tokens() -> list[str]:
    errors: list[str] = []
    if not LEGACY_TRUST_REGISTER.exists():
        return [f"missing {rel(LEGACY_TRUST_REGISTER)}"]
    try:
        records = tomllib.loads(LEGACY_TRUST_REGISTER.read_text()).get("declaration", [])
    except tomllib.TOMLDecodeError as exc:
        return [f"{rel(LEGACY_TRUST_REGISTER)} is invalid TOML: {exc}"]
    registered: set[tuple[str, str, str]] = set()
    for record in records:
        key = (record.get("path"), record.get("kind"), record.get("name"))
        if not all(isinstance(value, str) and value for value in key):
            errors.append(f"{rel(LEGACY_TRUST_REGISTER)} has an incomplete declaration")
            continue
        if key in registered:
            errors.append(f"{rel(LEGACY_TRUST_REGISTER)} duplicates {key}")
        if key[1] not in {"axiom", "opaque", "constant"}:
            errors.append(f"{rel(LEGACY_TRUST_REGISTER)} has invalid kind {key[1]}")
        if key[0].startswith(("lean/SixBirdsMetaMath/RHNavier/",
                              "lean/SixBirdsMetaMath/RHNavierPvNP/")):
            errors.append(f"{rel(LEGACY_TRUST_REGISTER)} cannot exempt a joint analytic module")
        if record.get("role") not in {
            "open_metatheory_obligation", "external_foundations_iv_obligation",
            "uninterpreted_legacy_interface",
        }:
            errors.append(f"{rel(LEGACY_TRUST_REGISTER)} has invalid role for {key}")
        registered.add(key)
    seen: set[tuple[str, str, str]] = set()
    for path in lean_source_files():
        raw = path.read_text(encoding="utf-8")
        masked = mask_lean_comments(raw)
        for lineno, line in enumerate(masked.splitlines(), start=1):
            stripped = line.split("--", 1)[0]
            match = FORBIDDEN_LEAN_TOKENS.search(stripped)
            if not match:
                continue
            declaration = DECLARATION_TOKEN_RE.match(stripped)
            if declaration is None or declaration.group(1) != match.group(1):
                errors.append(f"{rel(path)}:{lineno}: forbidden Lean token `{match.group(1)}`")
                continue
            key = (rel(path), declaration.group(1), declaration.group(2))
            if key not in registered:
                errors.append(f"{rel(path)}:{lineno}: unregistered Lean declaration `{key[1]} {key[2]}`")
            else:
                seen.add(key)
    for key in sorted(registered - seen):
        errors.append(f"{rel(LEGACY_TRUST_REGISTER)} has stale declaration {key}")
    return errors


def check_no_external_refs() -> list[str]:
    errors: list[str] = []
    for path in active_source_files():
        text = path.read_text(encoding="utf-8")
        if path == LEAN_DIR / "lakefile.toml":
            try:
                requirements = tomllib.loads(text).get("require", [])
            except tomllib.TOMLDecodeError as exc:
                errors.append(f"{rel(path)} is invalid TOML: {exc}")
                continue
            for requirement in requirements:
                name = requirement.get("name")
                expected = PACKAGE_DEPENDENCY_PATHS.get(name)
                if expected is not None and requirement.get("path") == expected:
                    text = text.replace(f'path = "{expected}"', "", 1)
        for ref in FORBIDDEN_EXTERNAL_REFS:
            if ref in text:
                errors.append(f"{rel(path)} contains forbidden external reference `{ref}`")
    return errors


# Lean files whose namespace declaration deliberately differs from their
# file-path-derived name. The alignment trio declares aliases in the
# umbrella `SixBirdsMetaMath` namespace (matching SAU's pattern). Umbrella
# files (top-level + axis umbrellas + ImportedFoundations) have no
# namespace declaration; they are import-only.
_UMBRELLA_NAMESPACE_FILES = {
    "SixBirdsMetaMath/FoundationsICompat.lean": "SixBirdsMetaMath",
    "SixBirdsMetaMath/Terminology.lean": "SixBirdsMetaMath",
}
_NO_NAMESPACE_FILES = {
    "SixBirdsMetaMath.lean",
    "SixBirdsMetaMath/Main.lean",
    "SixBirdsMetaMath/Xi.lean",
    "SixBirdsMetaMath/NS.lean",
    "SixBirdsMetaMath/RHNavier.lean",
    "SixBirdsMetaMath/RHNavierPvNP.lean",
    "SixBirdsMetaMath/ImportedFoundations.lean",
}
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+(\S+)\s*$", re.MULTILINE)
_END_RE = re.compile(r"^\s*end\s+(\S+)\s*$", re.MULTILINE)


def _file_path_namespace(rel_path: str) -> str:
    """Derive the expected namespace from a `SixBirdsMetaMath/...` relative path."""
    without_ext = rel_path[: -len(".lean")] if rel_path.endswith(".lean") else rel_path
    return without_ext.replace("/", ".")


def check_lean_namespaces() -> list[str]:
    """Each Lean module under lean/SixBirdsMetaMath/ must declare a namespace
    matching its file path, or be one of the documented exceptions
    (umbrella imports / alignment-trio alias hubs)."""
    errors: list[str] = []
    for path in lean_source_files():
        rel_to_lean = path.resolve().relative_to(LEAN_DIR).as_posix()
        text = path.read_text(encoding="utf-8")
        ns_decls = _NAMESPACE_RE.findall(text)
        end_decls = _END_RE.findall(text)

        if rel_to_lean in _NO_NAMESPACE_FILES:
            if ns_decls or end_decls:
                errors.append(
                    f"{rel(path)}: umbrella file must have no `namespace` / `end` declaration "
                    f"(got namespaces={ns_decls}, ends={end_decls})"
                )
            continue

        expected = _UMBRELLA_NAMESPACE_FILES.get(rel_to_lean) or _file_path_namespace(rel_to_lean)
        if expected not in ns_decls:
            errors.append(
                f"{rel(path)}: expected `namespace {expected}` declaration "
                f"(got {ns_decls})"
            )
        if expected not in end_decls:
            errors.append(
                f"{rel(path)}: expected matching `end {expected}` declaration "
                f"(got {end_decls})"
            )
        if len(ns_decls) > 1 or len(end_decls) > 1:
            errors.append(
                f"{rel(path)}: multiple namespace/end pairs not supported "
                f"(namespaces={ns_decls}, ends={end_decls})"
            )
    return errors


def validator_chain(skip_probe: bool) -> list[list[str]]:
    """Phase A + Phase C validators, in chain order.

    `skip_probe` is forwarded only to validators that accept it (audit
    foundations deps, check manifests). The other validators are
    probe-free.
    """
    audit_args = ["scripts/audit_foundations_dependencies.py", "--check", "--skip-validation"]
    if skip_probe:
        audit_args.append("--skip-probe")
    manifests_args = ["scripts/check_manifests.py", "--check"]
    if skip_probe:
        manifests_args.append("--skip-probe")
    # The inherited XI/AOR/Main/NS extractor describes papers owned by
    # Needles, not current metatheory manuscripts. Validate this repository's
    # two live paper axes through their dedicated statement registries.
    return [
        audit_args,
        ["scripts/check_foundations_provenance.py", "--check"],
        ["scripts/check_semantic_alignment.py", "--check"],
        ["scripts/check_statements_of_record_meta_math.py"],
        ["scripts/check_statements_of_record_foundations_iv.py"],
        ["scripts/generate_imported_foundations.py", "--check"],
        manifests_args,
    ]


def run_validator_chain(skip_probe: bool) -> int:
    for args in validator_chain(skip_probe):
        code, output = run([sys.executable] + args, cwd=ROOT)
        if code != 0:
            print(output, end="")
            return code
    return 0


def check(
    *, clean: bool, skip_prechecks: bool, skip_build: bool, skip_probe: bool
) -> int:
    errors = check_required_files()
    errors.extend(check_no_forbidden_lean_tokens())
    errors.extend(check_no_external_refs())
    errors.extend(check_lean_namespaces())
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    if not skip_prechecks:
        # If --skip-build is set we assume no Lean toolchain; force --skip-probe
        # too so the validator chain doesn't try to invoke `lake`.
        effective_skip_probe = skip_probe or skip_build
        code = run_validator_chain(effective_skip_probe)
        if code != 0:
            return code

    if not skip_build:
        code, output = run(["lake", "build"], cwd=LEAN_DIR)
        print(output, end="")
        if clean:
            cleanup()
            remaining = build_artifacts()
            if remaining:
                for artifact in remaining:
                    print(f"ERROR: cleanup left build artifact {rel(artifact)}", file=sys.stderr)
                return 1
        if code != 0:
            return code

    print("SixBirdsMetaMath Lean build passed" if not skip_build else "SixBirdsMetaMath Lean prechecks passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cleanup", action="store_true", help="remove local Lake build artifacts after checking")
    parser.add_argument(
        "--skip-prechecks",
        action="store_true",
        help="skip the Phase A+C python validator chain (run only structural checks + lake build)",
    )
    parser.add_argument(
        "--skip-build",
        action="store_true",
        help="skip `lake build` (useful when the Lean toolchain isn't installed). Implies --skip-probe.",
    )
    parser.add_argument(
        "--skip-probe",
        action="store_true",
        help="forward to audit and manifest validators: skip lake env lean probes",
    )
    args = parser.parse_args()
    return check(
        clean=args.cleanup,
        skip_prechecks=args.skip_prechecks,
        skip_build=args.skip_build,
        skip_probe=args.skip_probe,
    )


if __name__ == "__main__":
    raise SystemExit(main())
