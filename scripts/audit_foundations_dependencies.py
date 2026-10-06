#!/usr/bin/env python3
"""Audit reusable Lean declarations from the three Foundations repos.

Adapted for six-birds-needles from six-birds-math-usefulness. Records
which Foundations declarations are available for later import/wrapping
and validates a curated map from needles dependency concepts to canonical
Lean names. Vendored foundations live under `vendor/foundations/`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
INVENTORY_DIR = ROOT / "formalization" / "inventory"
VENDOR_FOUNDATIONS = ROOT / "vendor" / "foundations"
SOURCE_ITEMS = INVENTORY_DIR / "source_items.jsonl"
FOUNDATIONS_DECLARATIONS = INVENTORY_DIR / "foundations_declarations.jsonl"
IMPORTED_FOUNDATIONS = INVENTORY_DIR / "imported_foundations.yml"
AUDIT_MD = INVENTORY_DIR / "foundations_dependency_audit.md"

DECL_KINDS = {
    "abbrev": "definition",
    "axiom": "axiom",
    "class": "structure",
    "def": "definition",
    "inductive": "inductive",
    "lemma": "lemma",
    "structure": "structure",
    "theorem": "theorem",
}
LABEL_PREFIXES = ("def:", "thm:", "prop:", "lem:", "cor:", "rmk:", "rem:", "obl:", "warn:", "nonclaim:")
NORMALIZED_CONSUMER_FIELDS = {"needles_label_consumers", "needles_lean_consumers"}
NEEDLES_AXES = {"main", "xi", "ns", "both"}
LEAN_CONSUMER_PREFIX = "SixBirdsMetaMath."
LOAD_BEARING_USE_CLASSIFICATIONS = {
    "substantive_theorem_use",
    "definition_host",
    "record_schema",
    "status_family",
}


@dataclass(frozen=True)
class Foundation:
    foundation_id: str
    repo_path: Path
    lake_project: Path
    root_module: str
    manifest_path: Path | None
    validation_command: str


FOUNDATIONS = [
    Foundation(
        foundation_id="foundations_i",
        repo_path=(VENDOR_FOUNDATIONS / "six-birds-theory").resolve(),
        lake_project=(VENDOR_FOUNDATIONS / "six-birds-theory" / "formal").resolve(),
        root_module="ClosureLadder",
        manifest_path=None,
        validation_command="bash scripts/check_lean.sh",
    ),
    Foundation(
        foundation_id="foundations_ii",
        repo_path=(VENDOR_FOUNDATIONS / "six-birds-foundations-ii").resolve(),
        lake_project=(VENDOR_FOUNDATIONS / "six-birds-foundations-ii" / "lean" / "full").resolve(),
        root_module="SixBirds",
        manifest_path=(VENDOR_FOUNDATIONS / "six-birds-foundations-ii" / "lean" / "manifest.toml").resolve(),
        validation_command="./scripts/validate_lean.sh --tier full --require-full",
    ),
    Foundation(
        foundation_id="foundations_iii",
        repo_path=(VENDOR_FOUNDATIONS / "six-birds-foundations-iii").resolve(),
        lake_project=(VENDOR_FOUNDATIONS / "six-birds-foundations-iii" / "lean" / "full").resolve(),
        root_module="SixBirdsIII",
        manifest_path=(VENDOR_FOUNDATIONS / "six-birds-foundations-iii" / "lean" / "manifest.toml").resolve(),
        validation_command="./scripts/validate_lean.sh --tier full --require-full",
    ),
]


# Default imported-foundations entries. Bootstrapped from the SAU set; needles
# consumers (label and Lean) are intentionally empty and will be populated by
# hand in Phase A.9 as cross-walk is curated for the two needles paper axes.
DEFAULT_IMPORTED_FOUNDATIONS = [
    {
        "dependency_concept": "closure operator",
        "dependency_role": "definition_host",
        "use_classification": "alias_or_adapter",
        "needles_paper_axis": "both",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_i",
        "source_label": "",
        "module": "ClosureLadder",
        "lean_decl": "ClosureOp",
        "match_basis": "name_match",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "closure ladder strict extension",
        "dependency_role": "record_schema",
        "use_classification": "alias_or_adapter",
        "needles_paper_axis": "both",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_i",
        "source_label": "",
        "module": "ClosureLadder",
        "lean_decl": "ClosureLadder",
        "match_basis": "name_match",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "idempotent endomap",
        "dependency_role": "definition_host",
        "use_classification": "alias_or_adapter",
        "needles_paper_axis": "both",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_i",
        "source_label": "",
        "module": "ClosureLadder",
        "lean_decl": "ClosureLadder.IdempotentEndo",
        "match_basis": "name_match",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "quotient packaging",
        "dependency_role": "definition_host",
        "use_classification": "alias_or_adapter",
        "needles_paper_axis": "both",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_i",
        "source_label": "",
        "module": "ClosureLadder",
        "lean_decl": "ClosureLadder.MetaPackaging.pack",
        "match_basis": "name_match",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "primitive roles",
        "dependency_role": "definition_host",
        "use_classification": "definition_host",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_ii",
        "source_label": "def:primitive-roles",
        "module": "SixBirds",
        "lean_decl": "SixBirds.Role",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "FATCD host",
        "dependency_role": "definition_host",
        "use_classification": "definition_host",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_ii",
        "source_label": "def:fatcd",
        "module": "SixBirds",
        "lean_decl": "SixBirds.FATCD",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "Foundations II channel status",
        "dependency_role": "status_family",
        "use_classification": "status_family",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_ii",
        "source_label": "def:channel-status",
        "module": "SixBirds",
        "lean_decl": "SixBirds.ChannelStatus",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "scoped exact six",
        "dependency_role": "theorem_used",
        "use_classification": "alias_or_adapter",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_ii",
        "source_label": "thm:scoped-exact-six",
        "module": "SixBirds",
        "lean_decl": "SixBirds.scoped_exact_six",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "typed non collapse",
        "dependency_role": "theorem_used",
        "use_classification": "alias_or_adapter",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_ii",
        "source_label": "prop:typed-non-collapse",
        "module": "SixBirds",
        "lean_decl": "SixBirds.typed_non_collapse",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "BirdInt audited finite calculus",
        "dependency_role": "definition_host",
        "use_classification": "alias_or_adapter",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_iii",
        "source_label": "def:birdint-domain",
        "module": "SixBirdsIII",
        "lean_decl": "SixBirdsIII.BirdIntDomain",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "Foundations III primitive labels",
        "dependency_role": "definition_host",
        "use_classification": "definition_host",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_iii",
        "source_label": "def:primitive-labels",
        "module": "SixBirdsIII",
        "lean_decl": "SixBirdsIII.Primitive",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "promotion status family",
        "dependency_role": "status_family",
        "use_classification": "status_family",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_iii",
        "source_label": "def:promotion-status",
        "module": "SixBirdsIII",
        "lean_decl": "SixBirdsIII.PromotionStatus",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "claim status family",
        "dependency_role": "status_family",
        "use_classification": "status_family",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_iii",
        "source_label": "def:claim-status",
        "module": "SixBirdsIII",
        "lean_decl": "SixBirdsIII.ClaimStatus",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "gate status family",
        "dependency_role": "status_family",
        "use_classification": "status_family",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_iii",
        "source_label": "def:gate-status",
        "module": "SixBirdsIII",
        "lean_decl": "SixBirdsIII.GateStatus",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "promotion bridge record",
        "dependency_role": "record_schema",
        "use_classification": "record_schema",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_iii",
        "source_label": "def:promotion-bridge-record",
        "module": "SixBirdsIII",
        "lean_decl": "SixBirdsIII.PromotionBridgeRecord",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "claim record",
        "dependency_role": "record_schema",
        "use_classification": "record_schema",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_iii",
        "source_label": "def:claim-record",
        "module": "SixBirdsIII",
        "lean_decl": "SixBirdsIII.ClaimRecord",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
    {
        "dependency_concept": "defect record",
        "dependency_role": "record_schema",
        "use_classification": "record_schema",
        "needles_paper_axis": "main",
        "needles_label_consumers": "",
        "needles_lean_consumers": "",
        "foundation_id": "foundations_iii",
        "source_label": "def:defect-record",
        "module": "SixBirdsIII",
        "lean_decl": "SixBirdsIII.DefectRecord",
        "match_basis": "manifest_label",
        "import_policy": "reuse_canonical",
    },
]


def rel(path: Path) -> str:
    return Path(os.path.relpath(path.resolve(), ROOT)).as_posix()


def read_jsonl(path: Path) -> list[dict[str, object]]:
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write_jsonl(path: Path, records: Iterable[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True))
            handle.write("\n")


def lean_toolchain(foundation: Foundation) -> str:
    path = foundation.lake_project / "lean-toolchain"
    return path.read_text(encoding="utf-8").strip() if path.exists() else "unknown"


def lean_module_file(lake_project: Path, module: str) -> Path:
    return lake_project / (module.replace(".", "/") + ".lean")


def module_name(lake_project: Path, path: Path) -> str:
    return path.relative_to(lake_project).with_suffix("").as_posix().replace("/", ".")


def local_imports(path: Path) -> list[str]:
    imports: list[str] = []
    import_re = re.compile(r"^\s*import\s+([A-Za-z0-9_.'/.]+)\s*$")
    for line in path.read_text(encoding="utf-8").splitlines():
        match = import_re.match(line)
        if match:
            imports.append(match.group(1).replace("/", "."))
    return imports


def reachable_lean_files(foundation: Foundation) -> list[Path]:
    root = lean_module_file(foundation.lake_project, foundation.root_module)
    seen_modules: set[str] = set()
    seen_files: set[Path] = set()
    ordered: list[Path] = []

    def visit(module: str) -> None:
        if module in seen_modules:
            return
        seen_modules.add(module)
        path = lean_module_file(foundation.lake_project, module)
        if not path.exists():
            return
        resolved = path.resolve()
        if resolved in seen_files:
            return
        seen_files.add(resolved)
        ordered.append(path)
        for imported in local_imports(path):
            if lean_module_file(foundation.lake_project, imported).exists():
                visit(imported)

    if root.exists():
        visit(foundation.root_module)
    return ordered


def scan_lean_declarations(foundation: Foundation) -> dict[str, dict[str, object]]:
    decls: dict[str, dict[str, object]] = {}
    decl_re = re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)?"
        r"(?P<kind>abbrev|axiom|class|def|inductive|lemma|structure|theorem)\s+"
        r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
    )
    namespace_re = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
    end_re = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")

    for path in reachable_lean_files(foundation):
        namespaces: list[str] = []
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            namespace_match = namespace_re.match(line)
            if namespace_match:
                namespaces.append(namespace_match.group(1))
                continue

            end_match = end_re.match(line)
            if end_match and namespaces:
                name = end_match.group(1)
                if name is not None and (name == namespaces[-1] or name == namespaces[-1].split(".")[-1]):
                    namespaces.pop()
                continue

            decl_match = decl_re.match(line)
            if not decl_match:
                continue
            raw_kind = decl_match.group("kind")
            name = decl_match.group("name")
            prefix = ".".join(namespaces)
            full_name = f"{prefix}.{name}" if prefix else name
            decls[full_name] = {
                "foundation_id": foundation.foundation_id,
                "repo_path": rel(foundation.repo_path),
                "lake_project": rel(foundation.lake_project),
                "root_module": foundation.root_module,
                "module": module_name(foundation.lake_project, path),
                "lean_decl": full_name,
                "kind": DECL_KINDS[raw_kind],
                "source_label": "",
                "source_file": rel(path),
                "line_start": line_no,
                "description": "",
                "toolchain": lean_toolchain(foundation),
                "validation_command": foundation.validation_command,
                "validation_status": "not_run",
            }
    return decls


def parse_manifest(path: Path) -> list[dict[str, object]]:
    """Parse the small TOML subset used by the Foundations manifests."""
    records: list[dict[str, object]] = []
    current: dict[str, object] | None = None
    current_table = ""
    table_re = re.compile(r"^\s*\[\[(?P<table>[A-Za-z0-9_-]+)\]\]\s*$")
    kv_re = re.compile(r"^\s*(?P<key>[A-Za-z0-9_-]+)\s*=\s*(?P<value>.*)\s*$")
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        table_match = table_re.match(line)
        if table_match:
            if current is not None:
                records.append(current)
            current_table = table_match.group("table")
            current = {"manifest_table": current_table}
            continue
        kv_match = kv_re.match(line)
        if kv_match and current is not None:
            key = kv_match.group("key")
            value = kv_match.group("value").strip()
            if value.startswith('"') and value.endswith('"'):
                current[key] = json.loads(value)
            elif re.fullmatch(r"\d+", value):
                current[key] = int(value)
            else:
                current[key] = value
    if current is not None:
        records.append(current)
    return records


def manifest_records(foundation: Foundation, scanned: dict[str, dict[str, object]]) -> list[dict[str, object]]:
    assert foundation.manifest_path is not None
    out: list[dict[str, object]] = []
    for entry in parse_manifest(foundation.manifest_path):
        lean_decl = str(entry.get("lean_decl", ""))
        source = dict(scanned.get(lean_decl, {}))
        if not source:
            source = {
                "source_file": "",
                "line_start": 0,
                "module": str(entry.get("lean_module", foundation.root_module)),
                "kind": "theorem" if entry.get("manifest_table") == "claim" else "definition",
            }
        raw_kind = str(entry.get("kind") or entry.get("manifest_table") or source.get("kind", "definition"))
        if raw_kind == "claim":
            raw_kind = "theorem"
        record = {
            "foundation_id": foundation.foundation_id,
            "repo_path": rel(foundation.repo_path),
            "lake_project": rel(foundation.lake_project),
            "root_module": foundation.root_module,
            "module": str(entry.get("lean_module") or source.get("module") or foundation.root_module),
            "lean_decl": lean_decl,
            "kind": str(source.get("kind") or raw_kind),
            "source_label": str(entry.get("paper_label", "")),
            "source_file": str(source.get("source_file", "")),
            "line_start": int(source.get("line_start", 0) or 0),
            "description": str(entry.get("description", "")),
            "toolchain": lean_toolchain(foundation),
            "validation_command": foundation.validation_command,
            "validation_status": "not_run",
        }
        out.append(record)
    return out


def validation_statuses(run_validation: bool) -> dict[str, str]:
    statuses: dict[str, str] = {}
    for foundation in FOUNDATIONS:
        if not foundation.repo_path.exists() or not foundation.lake_project.exists():
            statuses[foundation.foundation_id] = "missing"
            continue
        if not run_validation:
            statuses[foundation.foundation_id] = "not_run"
            continue
        result = subprocess.run(
            foundation.validation_command,
            cwd=foundation.repo_path,
            shell=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        statuses[foundation.foundation_id] = "pass" if result.returncode == 0 else "fail"
    return statuses


def collect_declarations(run_validation: bool) -> tuple[list[dict[str, object]], list[str]]:
    errors: list[str] = []
    statuses = validation_statuses(run_validation)
    records: list[dict[str, object]] = []

    for foundation in FOUNDATIONS:
        if not foundation.repo_path.exists():
            errors.append(f"missing Foundations repo {rel(foundation.repo_path)}")
            continue
        if not foundation.lake_project.exists():
            errors.append(f"missing Lean project {rel(foundation.lake_project)}")
            continue
        scanned = scan_lean_declarations(foundation)
        if foundation.manifest_path is None:
            foundation_records = list(scanned.values())
        elif foundation.manifest_path.exists():
            foundation_records = manifest_records(foundation, scanned)
        else:
            errors.append(f"missing manifest {rel(foundation.manifest_path)}")
            foundation_records = []
        for record in foundation_records:
            record["validation_status"] = statuses[foundation.foundation_id]
        records.extend(foundation_records)

    records.sort(key=lambda r: (str(r["foundation_id"]), str(r["lean_decl"])))
    return records, errors


def shell_quote_lean_name(name: str) -> str:
    return name


def probe_declarations(records: list[dict[str, object]]) -> list[str]:
    errors: list[str] = []
    by_foundation = {f.foundation_id: f for f in FOUNDATIONS}
    grouped: dict[str, list[str]] = {}
    for record in records:
        grouped.setdefault(str(record["foundation_id"]), []).append(str(record["lean_decl"]))

    for foundation_id, decls in grouped.items():
        foundation = by_foundation[foundation_id]
        if not decls:
            continue
        build = subprocess.run(
            ["lake", "build"],
            cwd=foundation.lake_project,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if build.returncode != 0:
            errors.append(
                f"Lean build failed before declaration probe for {foundation_id}: "
                f"cd {rel(foundation.lake_project)} && lake build"
            )
            for line in build.stdout.splitlines()[:80]:
                errors.append(f"  {line}")
            continue
        probe = "import " + foundation.root_module + "\n\n" + "\n".join(
            f"#check {shell_quote_lean_name(decl)}" for decl in sorted(set(decls))
        )
        with tempfile.NamedTemporaryFile("w", suffix=".lean", encoding="utf-8", delete=False) as handle:
            handle.write(probe)
            probe_path = Path(handle.name)
        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(probe_path)],
                cwd=foundation.lake_project,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
            )
        finally:
            probe_path.unlink(missing_ok=True)
        if result.returncode != 0:
            errors.append(
                f"Lean probe failed for {foundation_id} declarations: "
                f"cd {rel(foundation.lake_project)} && lake env lean <probe>"
            )
            for line in result.stdout.splitlines()[:40]:
                errors.append(f"  {line}")
    return errors


def yaml_value(value: object) -> str:
    if value is None:
        return '""'
    text = str(value)
    return json.dumps(text)


def write_imported_foundations_if_missing() -> None:
    if IMPORTED_FOUNDATIONS.exists():
        return
    lines = [
        "# Curated map from needles dependency concepts to canonical Foundations Lean declarations.",
        "# This file is validated by scripts/audit_foundations_dependencies.py --check.",
        "imports:",
    ]
    for entry in DEFAULT_IMPORTED_FOUNDATIONS:
        first = True
        for key in (
            "dependency_concept",
            "dependency_role",
            "use_classification",
            "needles_paper_axis",
            "needles_label_consumers",
            "needles_lean_consumers",
            "foundation_id",
            "source_label",
            "module",
            "lean_decl",
            "match_basis",
            "import_policy",
        ):
            value = entry.get(key, "")
            prefix = "  -" if first else "   "
            lines.append(f"{prefix} {key}: {yaml_value(value)}")
            first = False
    IMPORTED_FOUNDATIONS.parent.mkdir(parents=True, exist_ok=True)
    IMPORTED_FOUNDATIONS.write_text("\n".join(lines) + "\n", encoding="utf-8")


def split_csv(value: str) -> list[str]:
    return [token.strip() for token in value.split(",") if token.strip()]


def parse_imported_foundations() -> list[dict[str, str]]:
    if not IMPORTED_FOUNDATIONS.exists():
        return []
    entries: list[dict[str, str]] = []
    current: dict[str, str] | None = None
    field_re = re.compile(r"^\s{4}(?P<key>[A-Za-z0-9_]+):\s*(?P<value>.*)\s*$")
    first_re = re.compile(r"^\s{2}-\s+(?P<key>[A-Za-z0-9_]+):\s*(?P<value>.*)\s*$")
    for line in IMPORTED_FOUNDATIONS.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.lstrip().startswith("#") or line.strip() == "imports:":
            continue
        first = first_re.match(line)
        if first:
            if current is not None:
                entries.append(current)
            current = {first.group("key"): parse_yaml_scalar(first.group("value"))}
            continue
        field = field_re.match(line)
        if field and current is not None:
            current[field.group("key")] = parse_yaml_scalar(field.group("value"))
    if current is not None:
        entries.append(current)
    return entries


def parse_yaml_scalar(value: str) -> str:
    value = value.strip()
    if value.startswith('"') and value.endswith('"'):
        return str(json.loads(value))
    return value


def validate_imported_foundations(
    declarations: list[dict[str, object]],
    source_items: list[dict[str, object]],
) -> list[str]:
    errors: list[str] = []
    entries = parse_imported_foundations()
    if not entries:
        return [f"missing or empty {rel(IMPORTED_FOUNDATIONS)}"]

    declaration_keys = {(str(r["foundation_id"]), str(r["lean_decl"])) for r in declarations}
    label_keys = {(str(r["foundation_id"]), str(r["source_label"])) for r in declarations if r.get("source_label")}
    source_labels = {str(r["latex_label"]) for r in source_items}
    foundation_ids = {f.foundation_id for f in FOUNDATIONS}

    for index, entry in enumerate(entries, start=1):
        foundation_id = entry.get("foundation_id", "")
        lean_decl = entry.get("lean_decl", "")
        source_label = entry.get("source_label", "")
        import_policy = entry.get("import_policy", "")
        paper_axis = entry.get("needles_paper_axis", "")
        if foundation_id not in foundation_ids:
            errors.append(f"import entry {index} has unknown foundation_id {foundation_id!r}")
        if paper_axis and paper_axis not in NEEDLES_AXES:
            errors.append(f"import entry {index} has invalid needles_paper_axis {paper_axis!r}")
        if import_policy == "reuse_canonical" and not lean_decl:
            errors.append(f"import entry {index} reuse_canonical lacks lean_decl")
        if lean_decl and (foundation_id, lean_decl) not in declaration_keys:
            errors.append(f"import entry {index} points to missing declaration {foundation_id}:{lean_decl}")
        if source_label and (foundation_id, source_label) not in label_keys:
            errors.append(f"import entry {index} points to missing source_label {foundation_id}:{source_label}")
        missing_consumer_fields = sorted(NORMALIZED_CONSUMER_FIELDS - set(entry))
        if missing_consumer_fields:
            errors.append(
                f"import entry {index} is missing normalized consumer fields: "
                + ", ".join(missing_consumer_fields)
            )
        if entry.get("dependency_role") == "theorem_used" and entry.get("use_classification") == "smoke_check":
            errors.append(f"import entry {index} is theorem_used but classified as smoke_check")
        label_consumers = split_csv(entry.get("needles_label_consumers", ""))
        lean_consumers = split_csv(entry.get("needles_lean_consumers", ""))
        load_bearing = (
            entry.get("use_classification") in LOAD_BEARING_USE_CLASSIFICATIONS
            or entry.get("dependency_role") == "theorem_used"
        )
        # During Phase A consumers may be empty across all entries; the
        # validator does not yet error on missing consumers. Phase E (after
        # mechanization begins) will tighten this gate.
        for consumer in label_consumers:
            if consumer not in source_labels:
                errors.append(f"import entry {index} references missing needles consumer label {consumer}")
        for consumer in lean_consumers:
            if not consumer.startswith(LEAN_CONSUMER_PREFIX):
                errors.append(f"import entry {index} has invalid Lean consumer {consumer!r}")
    return errors


def imported_use_classification_counts(import_entries: list[dict[str, str]]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for entry in import_entries:
        use_classification = entry.get("use_classification", "")
        counts[use_classification] = counts.get(use_classification, 0) + 1
    return counts


def audit_markdown_text(declarations: list[dict[str, object]], import_entries: list[dict[str, str]]) -> str:
    counts: dict[str, int] = {}
    statuses: dict[str, str] = {}
    toolchains: dict[str, str] = {}
    for record in declarations:
        fid = str(record["foundation_id"])
        counts[fid] = counts.get(fid, 0) + 1
        statuses[fid] = str(record["validation_status"])
        toolchains[fid] = str(record["toolchain"])

    policy_counts: dict[str, int] = {}
    role_counts: dict[str, int] = {}
    for entry in import_entries:
        policy_counts[entry.get("import_policy", "")] = policy_counts.get(entry.get("import_policy", ""), 0) + 1
        role_counts[entry.get("dependency_role", "")] = role_counts.get(entry.get("dependency_role", ""), 0) + 1
    use_counts = imported_use_classification_counts(import_entries)

    lines = [
        "# Foundations dependency audit",
        "",
        "This report is generated by `scripts/audit_foundations_dependencies.py`.",
        "",
        "## Canonical declaration inventory",
        "",
        "| Foundation | Root module | Toolchain | Declarations | Validation |",
        "| --- | --- | --- | ---: | --- |",
    ]
    for foundation in FOUNDATIONS:
        lines.append(
            f"| {foundation.foundation_id} | `{foundation.root_module}` | "
            f"`{toolchains.get(foundation.foundation_id, 'unknown')}` | "
            f"{counts.get(foundation.foundation_id, 0)} | "
            f"`{statuses.get(foundation.foundation_id, 'not_run')}` |"
        )

    lines.extend(
        [
            "",
            "## Curated import map",
            "",
            f"- Import entries: {len(import_entries)}",
            "- Import policies: "
            + ", ".join(f"`{key}`={value}" for key, value in sorted(policy_counts.items()) if key),
            "- Dependency roles: "
            + ", ".join(f"`{key}`={value}" for key, value in sorted(role_counts.items()) if key),
            "- Use classifications: "
            + ", ".join(f"`{key}`={value}" for key, value in sorted(use_counts.items()) if key),
            "",
            "## Vendored Foundations status",
            "",
            "- The required Foundations Lean assets are vendored under `vendor/foundations/`.",
            "- Foundations I is locally adapted to Lean `v4.28.0` and imported by local Lake path dependency.",
            "- Foundations II currently uses Lean `v4.28.0` and is imported by local Lake path dependency.",
            "- Foundations III currently uses Lean `v4.28.0` and is imported by local Lake path dependency.",
        ]
    )
    return "\n".join(lines) + "\n"


def write_audit_markdown(declarations: list[dict[str, object]], import_entries: list[dict[str, str]]) -> None:
    AUDIT_MD.write_text(audit_markdown_text(declarations, import_entries), encoding="utf-8")


def generate(args: argparse.Namespace) -> int:
    INVENTORY_DIR.mkdir(parents=True, exist_ok=True)
    write_imported_foundations_if_missing()

    declarations, errors = collect_declarations(run_validation=not args.skip_validation)
    write_jsonl(FOUNDATIONS_DECLARATIONS, declarations)
    import_entries = parse_imported_foundations()
    write_audit_markdown(declarations, import_entries)

    errors.extend(validate_imported_foundations(declarations, read_jsonl(SOURCE_ITEMS)))
    if not args.skip_validation:
        for foundation in FOUNDATIONS:
            if any(
                str(record["foundation_id"]) == foundation.foundation_id
                and record["validation_status"] == "fail"
                for record in declarations
            ):
                errors.append(
                    f"validation command failed for {foundation.foundation_id}: "
                    f"{foundation.validation_command}"
                )
    if not args.skip_probe:
        errors.extend(probe_declarations(declarations))

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    print(f"wrote {len(declarations)} declarations to {rel(FOUNDATIONS_DECLARATIONS)}")
    print(f"validated {len(import_entries)} import-map entries in {rel(IMPORTED_FOUNDATIONS)}")
    print(f"wrote {rel(AUDIT_MD)}")
    return 0


def check(skip_validation: bool = False, skip_probe: bool = False) -> int:
    errors: list[str] = []
    write_imported_foundations_if_missing()
    declarations, collect_errors = collect_declarations(run_validation=not skip_validation)
    errors.extend(collect_errors)
    import_entries = parse_imported_foundations()

    if not skip_validation:
        validation_errors = [
            f"validation command failed for {foundation.foundation_id}: {foundation.validation_command}"
            for foundation in FOUNDATIONS
            if any(
                str(r["foundation_id"]) == foundation.foundation_id and r["validation_status"] == "fail"
                for r in declarations
            )
        ]
        if validation_errors:
            for error in errors + validation_errors:
                print(f"ERROR: {error}", file=sys.stderr)
            return 1

    if FOUNDATIONS_DECLARATIONS.exists():
        committed = read_jsonl(FOUNDATIONS_DECLARATIONS)
        if committed != declarations:
            errors.append(f"{rel(FOUNDATIONS_DECLARATIONS)} is stale; rerun foundations audit")
    else:
        errors.append(f"missing {rel(FOUNDATIONS_DECLARATIONS)}")

    old_audit = AUDIT_MD.read_text(encoding="utf-8") if AUDIT_MD.exists() else None
    expected_md = audit_markdown_text(declarations, import_entries)
    if old_audit is None:
        errors.append(f"missing {rel(AUDIT_MD)}")
    elif old_audit != expected_md:
        errors.append(f"{rel(AUDIT_MD)} is stale; rerun foundations audit")

    errors.extend(validate_imported_foundations(declarations, read_jsonl(SOURCE_ITEMS)))
    if not skip_probe:
        errors.extend(probe_declarations(declarations))

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(f"foundations audit check passed: {len(declarations)} declarations, {len(import_entries)} import mappings")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate committed audit artifacts")
    parser.add_argument(
        "--skip-validation",
        action="store_true",
        help="generate with validation_status=not_run instead of running native foundation validators",
    )
    parser.add_argument("--skip-probe", action="store_true", help="skip Lean #check declaration probes")
    args = parser.parse_args()
    if args.check:
        return check(skip_validation=args.skip_validation, skip_probe=args.skip_probe)
    return generate(args)


if __name__ == "__main__":
    raise SystemExit(main())
