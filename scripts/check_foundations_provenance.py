#!/usr/bin/env python3
"""Validate vendored Foundations provenance and import-use classifications.

Adapted for six-birds-needles from six-birds-math-usefulness. Reads
`vendor/foundations/vendor_provenance.yml` (already shipped with the
vendored tree) and `formalization/inventory/imported_foundations.yml`
(the needles cross-walk).
"""

from __future__ import annotations

import argparse
import collections
import fnmatch
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# audit_foundations_dependencies is a sibling module in this scripts/ dir.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import audit_foundations_dependencies as audit  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]
VENDOR_DIR = ROOT / "vendor" / "foundations"
PROVENANCE_YML = VENDOR_DIR / "vendor_provenance.yml"
FOUNDATIONS_I_NOTICE = VENDOR_DIR / "foundations-i-adaptation.md"
IMPORTED_FOUNDATIONS = ROOT / "formalization" / "inventory" / "imported_foundations.yml"
FOUNDATIONS_DECLARATIONS = ROOT / "formalization" / "inventory" / "foundations_declarations.jsonl"
SOURCE_ITEMS = ROOT / "formalization" / "inventory" / "source_items.jsonl"
SUMMARY_MD = ROOT / "formalization" / "inventory" / "foundations_provenance_summary.md"

ALLOWED_USE_CLASSIFICATIONS = {
    "substantive_theorem_use",
    "definition_host",
    "record_schema",
    "status_family",
    "alias_or_adapter",
    "smoke_check",
    "provenance_only",
}
LOAD_BEARING_USE_CLASSIFICATIONS = {
    "substantive_theorem_use",
    "definition_host",
    "record_schema",
    "status_family",
}
CANONICAL_VENDOR_STATUSES = {"vendored_canonical"}
UPSTREAM_DIFF_POLICIES = {
    "full_tree",
    "unpublished_lean_track",
    "not_applicable_locally_adapted",
}
LABEL_PREFIXES = ("def:", "thm:", "prop:", "lem:", "cor:", "rmk:", "rem:", "obl:", "warn:", "nonclaim:")
LEAN_CONSUMER_PREFIX = "SixBirdsMetaMath."
REQUIRED_PROVENANCE_FIELDS = {
    "foundation_id",
    "local_path",
    "lake_project",
    "root_module",
    "toolchain",
    "validation_command",
    "upstream_identity",
    "vendor_status",
    "proof_role",
    "adaptation_summary",
    "compare_notice",
}
GIT_SHA_RE = re.compile(r"^[0-9a-f]{40}$")
UPSTREAM_REPO_RE = re.compile(r"^https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
UPSTREAM_DIFF_IGNORES = {
    ".git",
    ".lake",
    ".validate-logs",
    "lake-manifest.json",
    "*.olean",
    "*.ilean",
}


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def parse_scalar(raw: str) -> str:
    value = raw.strip()
    if value.startswith('"') and value.endswith('"'):
        return str(json.loads(value))
    return value


def consumer_summary(entry: dict[str, str]) -> str:
    labels = str(entry.get("needles_label_consumers", "")).strip()
    lean = str(entry.get("needles_lean_consumers", "")).strip()
    parts = [f"labels: {labels}"]
    if lean:
        parts.append(f"Lean: {lean}")
    return "; ".join(parts)


def parse_foundations_provenance() -> tuple[list[dict[str, str]], list[str]]:
    errors: list[str] = []
    if not PROVENANCE_YML.exists():
        return [], [f"missing {rel(PROVENANCE_YML)}"]
    entries: list[dict[str, str]] = []
    current: dict[str, str] | None = None
    first_re = re.compile(r"^\s{2}-\s+(?P<key>[A-Za-z0-9_]+):\s*(?P<value>.*)\s*$")
    field_re = re.compile(r"^\s{4}(?P<key>[A-Za-z0-9_]+):\s*(?P<value>.*)\s*$")
    for lineno, line in enumerate(PROVENANCE_YML.read_text(encoding="utf-8").splitlines(), start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#") or stripped == "foundations:":
            continue
        first = first_re.match(line)
        if first:
            if current is not None:
                entries.append(current)
            current = {first.group("key"): parse_scalar(first.group("value"))}
            continue
        field = field_re.match(line)
        if field and current is not None:
            current[field.group("key")] = parse_scalar(field.group("value"))
            continue
        errors.append(f"{rel(PROVENANCE_YML)}:{lineno}: invalid provenance syntax")
    if current is not None:
        entries.append(current)
    return entries, errors


def read_jsonl(path: Path) -> list[dict[str, object]]:
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def consumer_tokens(entry: dict[str, str]) -> list[str]:
    return label_consumer_tokens(entry) + lean_consumer_tokens(entry)


def label_consumer_tokens(entry: dict[str, str]) -> list[str]:
    return [token.strip() for token in entry.get("needles_label_consumers", "").split(",") if token.strip()]


def lean_consumer_tokens(entry: dict[str, str]) -> list[str]:
    return [token.strip() for token in entry.get("needles_lean_consumers", "").split(",") if token.strip()]


def validate_provenance(entries: list[dict[str, str]]) -> list[str]:
    errors: list[str] = []
    seen: set[str] = set()
    expected_ids = {foundation.foundation_id for foundation in audit.FOUNDATIONS}
    for index, entry in enumerate(entries, start=1):
        missing = sorted(REQUIRED_PROVENANCE_FIELDS - set(entry))
        if missing:
            errors.append(f"provenance entry {index} missing fields: {', '.join(missing)}")
            continue
        foundation_id = entry["foundation_id"]
        seen.add(foundation_id)
        local_path = ROOT / entry["local_path"]
        lake_project = ROOT / entry["lake_project"]
        toolchain_path = lake_project / "lean-toolchain"
        if not local_path.exists():
            errors.append(f"{foundation_id} local_path does not exist: {entry['local_path']}")
        if not lake_project.exists():
            errors.append(f"{foundation_id} lake_project does not exist: {entry['lake_project']}")
        if not toolchain_path.exists():
            errors.append(f"{foundation_id} missing lean-toolchain at {rel(toolchain_path)}")
        elif toolchain_path.read_text(encoding="utf-8").strip() != entry["toolchain"]:
            errors.append(f"{foundation_id} toolchain does not match provenance record")
        root_module_file = lake_project / (entry["root_module"].replace(".", "/") + ".lean")
        if not root_module_file.exists():
            errors.append(f"{foundation_id} root module file is missing: {rel(root_module_file)}")
        if entry.get("vendor_status") in CANONICAL_VENDOR_STATUSES:
            upstream_repo = entry.get("upstream_repo", "")
            upstream_commit = entry.get("upstream_commit", "")
            upstream_tag = entry.get("upstream_tag", "")
            if not upstream_repo:
                errors.append(f"{foundation_id} canonical vendor entry lacks upstream_repo")
            elif not UPSTREAM_REPO_RE.fullmatch(upstream_repo):
                errors.append(f"{foundation_id} upstream_repo is not an auditable GitHub URL")
            if not upstream_commit and not upstream_tag:
                errors.append(f"{foundation_id} canonical vendor entry lacks upstream_commit or upstream_tag")
            if upstream_commit and not GIT_SHA_RE.fullmatch(upstream_commit):
                errors.append(f"{foundation_id} upstream_commit is not a 40-character git SHA")
        policy = entry.get("upstream_diff_policy", "not_applicable_locally_adapted")
        if policy not in UPSTREAM_DIFF_POLICIES:
            errors.append(f"{foundation_id} has invalid upstream_diff_policy {policy!r}")
        if entry.get("vendor_status") in CANONICAL_VENDOR_STATUSES and policy != "full_tree":
            errors.append(f"{foundation_id} canonical vendor entry must use upstream_diff_policy: full_tree")
        if entry.get("vendor_status") == "local_prepublication_snapshot" and policy != "unpublished_lean_track":
            errors.append(f"{foundation_id} prepublication snapshot must use upstream_diff_policy: unpublished_lean_track")
    missing_ids = sorted(expected_ids - seen)
    extra_ids = sorted(seen - expected_ids)
    if missing_ids:
        errors.append(f"provenance file missing foundation ids: {', '.join(missing_ids)}")
    if extra_ids:
        errors.append(f"provenance file has unknown foundation ids: {', '.join(extra_ids)}")
    return errors


def validate_foundations_i_notice() -> list[str]:
    if not FOUNDATIONS_I_NOTICE.exists():
        return [f"missing {rel(FOUNDATIONS_I_NOTICE)}"]
    text = FOUNDATIONS_I_NOTICE.read_text(encoding="utf-8")
    required_phrases = [
        "v4.28.0",
        "ClosureLadder",
    ]
    return [
        f"{rel(FOUNDATIONS_I_NOTICE)} must mention `{phrase}`"
        for phrase in required_phrases
        if phrase not in text
    ]


def validate_import_use_classifications() -> tuple[list[str], collections.Counter[str]]:
    errors: list[str] = []
    counts: collections.Counter[str] = collections.Counter()
    declarations = read_jsonl(FOUNDATIONS_DECLARATIONS)
    declaration_keys = {(str(row["foundation_id"]), str(row["lean_decl"])) for row in declarations}
    source_labels = {str(row["latex_label"]) for row in read_jsonl(SOURCE_ITEMS)}

    for index, entry in enumerate(audit.parse_imported_foundations(), start=1):
        classification = entry.get("use_classification", "")
        counts[classification] += 1
        if classification not in ALLOWED_USE_CLASSIFICATIONS:
            errors.append(f"import entry {index} has invalid use_classification {classification!r}")
        key = (entry.get("foundation_id", ""), entry.get("lean_decl", ""))
        if key not in declaration_keys:
            errors.append(f"import entry {index} points to missing declaration {key[0]}:{key[1]}")
        consumers = consumer_tokens(entry)
        if "needles_label_consumers" not in entry or "needles_lean_consumers" not in entry:
            errors.append(f"import entry {index} is missing normalized consumer fields")
        load_bearing = (
            classification in LOAD_BEARING_USE_CLASSIFICATIONS
            or entry.get("dependency_role") == "theorem_used"
        )
        # During Phase A consumers may be empty (alignment is curated in A.9);
        # we don't yet error on missing consumers.
        if classification == "substantive_theorem_use" and entry.get("dependency_role") != "theorem_used":
            errors.append(f"import entry {index} is substantive theorem use but dependency_role is not theorem_used")
        if classification == "smoke_check" and entry.get("dependency_role") == "theorem_used":
            errors.append(f"import entry {index} is theorem_used but classified as smoke_check")
        if classification in {"smoke_check", "provenance_only"} and consumers:
            errors.append(f"import entry {index} is {classification} but lists needles consumers")
        for consumer in label_consumer_tokens(entry):
            if consumer not in source_labels:
                errors.append(f"import entry {index} references missing needles consumer label {consumer}")
        for consumer in lean_consumer_tokens(entry):
            if not consumer.startswith(LEAN_CONSUMER_PREFIX):
                errors.append(f"import entry {index} has unrecognized consumer token {consumer!r}")
    return errors, counts


def summary_text(provenance_entries: list[dict[str, str]], use_counts: collections.Counter[str]) -> str:
    import_entries = audit.parse_imported_foundations()
    substantive_theorems = [
        entry for entry in import_entries if entry.get("use_classification") == "substantive_theorem_use"
    ]
    load_bearing_definitions = [
        entry
        for entry in import_entries
        if entry.get("use_classification") in {"definition_host", "record_schema", "status_family"}
    ]
    non_load_bearing = [
        entry
        for entry in import_entries
        if entry.get("use_classification") in {"alias_or_adapter", "smoke_check", "provenance_only"}
    ]
    lines = [
        "# Foundations Provenance Summary",
        "",
        "Generated by `scripts/check_foundations_provenance.py`.",
        "",
        "## Vendored Tracks",
        "",
        "| Foundation | Root module | Toolchain | Vendor status | Upstream pin | Diff policy | Proof role |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for entry in provenance_entries:
        pin = entry.get("upstream_commit") or entry.get("upstream_tag") or ""
        lines.append(
            f"| {entry.get('foundation_id', '')} | `{entry.get('root_module', '')}` | "
            f"`{entry.get('toolchain', '')}` | `{entry.get('vendor_status', '')}` | "
            f"`{pin}` | "
            f"`{entry.get('upstream_diff_policy', 'not_applicable_locally_adapted')}` | "
            f"`{entry.get('proof_role', '')}` |"
        )
    lines.extend(
        [
            "",
            "## Import Use Classifications",
            "",
        ]
    )
    for classification, count in sorted(use_counts.items()):
        lines.append(f"- `{classification}`: {count}")
    lines.extend(
        [
            "",
            "## Substantive Imported Theorem Use",
            "",
        ]
    )
    if substantive_theorems:
        for entry in substantive_theorems:
            lines.append(
                f"- `{entry.get('lean_decl', '')}` -> "
                f"{consumer_summary(entry)}"
            )
    else:
        lines.append("- None currently declared. Imported theorem entries are smoke/adapter records, not needles theorem coverage.")
    lines.extend(
        [
            "",
            "## Load-Bearing Imported Definition/Schema/Status Use",
            "",
        ]
    )
    for entry in load_bearing_definitions:
        lines.append(
            f"- `{entry.get('lean_decl', '')}` (`{entry.get('use_classification', '')}`) -> "
            f"{consumer_summary(entry)}"
        )
    lines.extend(
        [
            "",
            "## Non-Load-Bearing Imports",
            "",
        ]
    )
    for entry in non_load_bearing:
        lines.append(
            f"- `{entry.get('lean_decl', '')}` (`{entry.get('use_classification', '')}`)"
        )
    return "\n".join(lines) + "\n"


def write_summary(provenance_entries: list[dict[str, str]], use_counts: collections.Counter[str]) -> None:
    SUMMARY_MD.parent.mkdir(parents=True, exist_ok=True)
    SUMMARY_MD.write_text(summary_text(provenance_entries, use_counts), encoding="utf-8")


def run(check: bool) -> int:
    provenance_entries, errors = parse_foundations_provenance()
    errors.extend(validate_provenance(provenance_entries))
    errors.extend(validate_foundations_i_notice())
    import_errors, use_counts = validate_import_use_classifications()
    errors.extend(import_errors)

    expected = summary_text(provenance_entries, use_counts)
    if check:
        if not SUMMARY_MD.exists():
            errors.append(f"missing {rel(SUMMARY_MD)}")
        elif SUMMARY_MD.read_text(encoding="utf-8") != expected:
            errors.append(f"{rel(SUMMARY_MD)} is stale; rerun foundations provenance check")
    else:
        write_summary(provenance_entries, use_counts)

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(
        f"foundations provenance check passed: {len(provenance_entries)} vendored tracks, "
        f"{sum(use_counts.values())} import-use entries"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate committed provenance artifacts")
    args = parser.parse_args()
    return run(check=args.check)


if __name__ == "__main__":
    raise SystemExit(main())
