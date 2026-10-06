#!/usr/bin/env python3
"""Validate the semantic alignment audit between needles LaTeX claims and Lean declarations.

Adapted for six-birds-needles from six-birds-math-usefulness. Phase A
runs this trivially because no Lean exists yet — `needles_items.jsonl`
is absent/empty and the validator exits clean. Phase B onward builds
out the alignment records as Lean coverage grows.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TRACEABILITY_DIR = ROOT / "formalization" / "traceability"
NEEDLES_ITEMS = TRACEABILITY_DIR / "needles_items.jsonl"
ALIGNMENT = TRACEABILITY_DIR / "semantic_alignment.yml"
SUMMARY = TRACEABILITY_DIR / "semantic_alignment_summary.md"
LEAN_ROOT = ROOT / "lean"

THEOREM_COVERAGE = {
    "direct_proof",
    "computational_proof",
    "definitional_proof",
    "projection_over_record",
    "imported_foundation_statement",
}
ALLOWED_STATUSES = {
    "faithful",
    "lean_stronger",
    "projection_packaged",
    "narrowed_surrogate",
    "weakened_genericized",
    "misaligned",
    "needs_strengthening",
}
ALLOWED_ACTIONS = {
    "no_action",
    "strengthen_statement",
    "replace_projection_with_derivation",
    "retain_record_packaging",
    "revise_boundary",
    "open_obligation",
}
UNRESOLVED_STATUSES = {
    "projection_packaged",
    "narrowed_surrogate",
    "weakened_genericized",
    "misaligned",
    "needs_strengthening",
}
DECL_START_RE = re.compile(
    r"^(?:protected\s+|private\s+)?"
    r"(?:theorem|lemma|def|abbrev)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def read_jsonl(path: Path) -> list[dict[str, object]]:
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def scalar(value: object) -> str:
    return json.dumps(str(value), ensure_ascii=False)


def parse_scalar(raw: str) -> str:
    value = raw.strip()
    if value.startswith('"') and value.endswith('"'):
        return str(json.loads(value))
    return value


def theorem_items() -> list[dict[str, object]]:
    items = read_jsonl(NEEDLES_ITEMS)
    return [
        record
        for record in items
        if str(record.get("category", "")) not in {"lean_definition", "prose_only"}
        and str(record.get("coverage", "")) in THEOREM_COVERAGE
    ]


def default_entry(record: dict[str, object]) -> dict[str, str]:
    label = str(record["latex_label"])
    if str(record.get("coverage", "")) == "projection_over_record":
        status = "projection_packaged"
        action = "replace_projection_with_derivation"
        notes = (
            "Lean declaration is a checked projection from an explicit proof-carrying record; "
            "it packages the paper claim but is not yet a direct derivation."
        )
    else:
        status = "needs_strengthening"
        action = "open_obligation"
        notes = "Semantic relation has not been manually strengthened beyond proof-shape validation."
    return {
        "latex_label": label,
        "statement_hash": str(record["statement_hash"]),
        "source_file": str(record["source_file"]),
        "lean_decl": str(record["lean_decl"]),
        "module": str(record["module"]),
        "coverage": str(record["coverage"]),
        "alignment_status": status,
        "resolution_action": action,
        "notes": notes,
    }


def alignment_text(records: list[dict[str, str]]) -> str:
    lines = [
        "# Semantic alignment audit for theorem-like needles Lean coverage.",
        "# Generated/updated by scripts/check_semantic_alignment.py; edit statuses deliberately.",
        "items:",
    ]
    for record in records:
        lines.append(f"  - latex_label: {scalar(record['latex_label'])}")
        for key in [
            "statement_hash",
            "source_file",
            "lean_decl",
            "module",
            "coverage",
            "alignment_status",
            "resolution_action",
            "notes",
        ]:
            lines.append(f"    {key}: {scalar(record[key])}")
    lines.append("")
    return "\n".join(lines)


def parse_alignment() -> tuple[dict[str, dict[str, str]], list[str]]:
    errors: list[str] = []
    if not ALIGNMENT.exists():
        return {}, []
    entries: dict[str, dict[str, str]] = {}
    current: dict[str, str] | None = None
    field_re = re.compile(r"^([A-Za-z0-9_]+):\s*(.*)$")
    for lineno, line in enumerate(ALIGNMENT.read_text(encoding="utf-8").splitlines(), start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#") or stripped == "items:":
            continue
        if line.startswith("  - "):
            current = {}
            rest = line[4:].strip()
            if rest:
                match = field_re.match(rest)
                if not match:
                    errors.append(f"{rel(ALIGNMENT)}:{lineno}: invalid alignment field")
                    continue
                current[match.group(1)] = parse_scalar(match.group(2))
            label = current.get("latex_label")
            if label:
                if label in entries:
                    errors.append(f"{rel(ALIGNMENT)}:{lineno}: duplicate alignment label {label}")
                entries[label] = current
            continue
        if line.startswith("    ") and current is not None:
            match = field_re.match(stripped)
            if not match:
                errors.append(f"{rel(ALIGNMENT)}:{lineno}: invalid alignment field")
                continue
            current[match.group(1)] = parse_scalar(match.group(2))
            label = current.get("latex_label")
            if label:
                if label in entries and entries[label] is not current:
                    errors.append(f"{rel(ALIGNMENT)}:{lineno}: duplicate alignment label {label}")
                entries[label] = current
            continue
        errors.append(f"{rel(ALIGNMENT)}:{lineno}: invalid alignment syntax")

    required = {
        "latex_label",
        "statement_hash",
        "source_file",
        "lean_decl",
        "module",
        "coverage",
        "alignment_status",
        "resolution_action",
        "notes",
    }
    for label, entry in entries.items():
        missing = sorted(required - set(entry))
        if missing:
            errors.append(f"{label} alignment entry is missing fields: {', '.join(missing)}")
    return entries, errors


def module_path(module: str) -> Path:
    if not module.startswith("SixBirdsMetaMath"):
        return ROOT / "__missing_module__.lean"
    suffix = module.removeprefix("SixBirdsMetaMath").lstrip(".")
    if not suffix:
        return LEAN_ROOT / "SixBirdsMetaMath.lean"
    return LEAN_ROOT / "SixBirdsMetaMath" / Path(*suffix.split(".")).with_suffix(".lean")


def lean_decl_exists(module: str, lean_decl: str) -> bool:
    path = module_path(module)
    if not path.exists():
        return False
    short_name = lean_decl.split(".")[-1]
    for line in path.read_text(encoding="utf-8").splitlines():
        match = DECL_START_RE.match(line)
        if match and match.group("name") == short_name:
            return True
    return False


def validate(entries: dict[str, dict[str, str]]) -> list[str]:
    errors: list[str] = []
    expected = theorem_items()
    expected_by_label = {str(record["latex_label"]): record for record in expected}

    for record in expected:
        label = str(record["latex_label"])
        entry = entries.get(label)
        if entry is None:
            errors.append(f"{label} is missing from {rel(ALIGNMENT)}")
            continue
        for key in ["statement_hash", "source_file", "lean_decl", "module", "coverage"]:
            if entry.get(key) != str(record[key]):
                errors.append(f"{label} alignment {key} is stale")
        status = entry.get("alignment_status", "")
        action = entry.get("resolution_action", "")
        if status not in ALLOWED_STATUSES:
            errors.append(f"{label} has invalid alignment_status {status!r}")
        if action not in ALLOWED_ACTIONS:
            errors.append(f"{label} has invalid resolution_action {action!r}")
        if status in {"faithful", "lean_stronger"} and action != "no_action":
            errors.append(f"{label} is marked {status} but has unresolved action {action!r}")
        if status in UNRESOLVED_STATUSES and action == "no_action":
            errors.append(f"{label} is unresolved status {status} but has no resolution action")
        if status == "projection_packaged" and str(record["coverage"]) != "projection_over_record":
            errors.append(f"{label} is projection_packaged but coverage is {record['coverage']}")
        if str(record["coverage"]) == "projection_over_record" and status != "projection_packaged":
            errors.append(f"{label} has projection_over_record coverage but status {status}")
        if not lean_decl_exists(str(record["module"]), str(record["lean_decl"])):
            errors.append(f"{label} Lean declaration {record['lean_decl']} not found in {record['module']}")

    for label in sorted(set(entries) - set(expected_by_label)):
        errors.append(f"{rel(ALIGNMENT)} references non-theorem or missing label {label}")

    return errors


def summary_text(entries: dict[str, dict[str, str]], errors: list[str]) -> str:
    expected = theorem_items()
    by_label = {str(record["latex_label"]): record for record in expected}
    status_counts = collections.Counter(entry.get("alignment_status", "") for entry in entries.values())
    action_counts = collections.Counter(entry.get("resolution_action", "") for entry in entries.values())
    coverage_counts = collections.Counter(str(record["coverage"]) for record in expected)
    unresolved = [
        entries[label]
        for label in sorted(by_label)
        if label in entries and entries[label].get("alignment_status") in UNRESOLVED_STATUSES
    ]
    lines = [
        "# Needles Semantic Alignment Summary",
        "",
        "Generated by `scripts/check_semantic_alignment.py`.",
        "",
        "This audit records whether each theorem-like Lean declaration has the same",
        "mathematical content as its LaTeX source, or whether it is still a surrogate,",
        "projection-packaged claim, or strengthening obligation.",
        "",
        "## Counts",
        "",
        f"- Theorem-like audited items: {len(expected)}",
        f"- Unresolved / packaged / strengthening items: {len(unresolved)}",
        "",
        "## Coverage",
        "",
    ]
    for coverage, count in sorted(coverage_counts.items()):
        lines.append(f"- `{coverage}`: {count}")
    lines.extend(["", "## Alignment Status", ""])
    for status, count in sorted(status_counts.items()):
        lines.append(f"- `{status}`: {count}")
    lines.extend(["", "## Resolution Actions", ""])
    for action, count in sorted(action_counts.items()):
        lines.append(f"- `{action}`: {count}")
    lines.extend(["", "## Unresolved Items", ""])
    if unresolved:
        for entry in unresolved:
            lines.append(
                "- "
                + f"`{entry['latex_label']}`: `{entry['alignment_status']}` / "
                + f"`{entry['resolution_action']}` -> `{entry['lean_decl']}`"
            )
    else:
        lines.append("- None.")
    lines.extend(["", "## Check Errors", ""])
    if errors:
        for error in errors:
            lines.append(f"- {error}")
    else:
        lines.append("- None.")
    lines.append("")
    return "\n".join(lines)


def write_default_alignment() -> None:
    records = [default_entry(record) for record in theorem_items()]
    records.sort(key=lambda record: record["latex_label"])
    ALIGNMENT.parent.mkdir(parents=True, exist_ok=True)
    ALIGNMENT.write_text(alignment_text(records), encoding="utf-8")


def check_or_generate(*, check: bool) -> tuple[list[str], str]:
    expected = theorem_items()
    # Phase A: no Lean yet, no needles_items.jsonl, so expected is empty
    # and alignment is trivially complete. Skip file creation.
    if not expected:
        return [], "# Needles Semantic Alignment Summary\n\nNo theorem-like Lean items to audit yet (Phase A).\n"
    if not ALIGNMENT.exists():
        if check:
            return [f"missing {rel(ALIGNMENT)}; rerun scripts/check_semantic_alignment.py"], ""
        write_default_alignment()
    entries, parse_errors = parse_alignment()
    errors = list(parse_errors)
    if not parse_errors:
        errors.extend(validate(entries))
    rendered_summary = summary_text(entries, errors)
    if SUMMARY.exists():
        if SUMMARY.read_text(encoding="utf-8") != rendered_summary:
            if check:
                errors.append(f"{rel(SUMMARY)} is stale; rerun scripts/check_semantic_alignment.py")
            else:
                SUMMARY.write_text(rendered_summary, encoding="utf-8")
    elif check:
        errors.append(f"missing {rel(SUMMARY)}; rerun scripts/check_semantic_alignment.py")
    else:
        SUMMARY.parent.mkdir(parents=True, exist_ok=True)
        SUMMARY.write_text(rendered_summary, encoding="utf-8")
    return errors, rendered_summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate semantic alignment audit")
    args = parser.parse_args()
    errors, _ = check_or_generate(check=args.check)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    if args.check:
        print("semantic alignment check passed")
    else:
        print("semantic alignment write passed (Phase A: no Lean items yet)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
