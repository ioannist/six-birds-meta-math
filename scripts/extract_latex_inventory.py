#!/usr/bin/env python3
"""Extract and validate the LaTeX theorem inventory for Lean planning.

Adapted for six-birds-needles from six-birds-math-usefulness. Two paper
axes are scanned: paper/main/formed_layer_membrane.tex (Main axis) and
paper/xi/xi_companion.tex (Xi axis). All theorem-like environments must
carry a `\\label{}` from the needles naming scheme
`<kind>:<axis>:<short-name>`.

The script is intentionally dependency-free. It emits JSONL inventory
files and validates the curated formalization-boundary overlay used by
later Lean work.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
INVENTORY_DIR = ROOT / "formalization" / "inventory"
SOURCE_ITEMS = INVENTORY_DIR / "source_items.jsonl"
DEPENDENCY_ITEMS = INVENTORY_DIR / "dependency_items.jsonl"
TERMINOLOGY_SNAPSHOT = INVENTORY_DIR / "terminology_snapshot.json"
BOUNDARY_FILE = INVENTORY_DIR / "formalization_boundary.yml"

# Needles-specific paper sources, one per axis.
PAPER_AXES = {
    "main": ROOT / "paper" / "main" / "formed_layer_membrane.tex",
    "xi": ROOT / "paper" / "xi" / "xi_companion.tex",
    "ns": ROOT / "paper" / "ns" / "needles_ns.tex",
    "aor": ROOT / "paper" / "aor" / "aor_paper.tex",
}

THEOREM_ENVS = (
    "definition",
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "remark",
    "warning",
    "obligation",
    "nonclaim",
)
FORMALIZATION_CATEGORIES = {
    "lean_definition",
    "fully_formal_math",
    "schema_theorem",
    "sourced_assumption",
    "prose_only",
}

# Mapping from env_kind to the required label kind prefix(es). Some envs
# accept multiple kind prefixes; see `nonclaim` (which we model as
# kind=nonclaim with a leading "nonclaim:" prefix).
LABEL_KIND_PREFIXES = {
    "definition": {"def"},
    "theorem": {"thm"},
    "lemma": {"lem"},
    "proposition": {"prop"},
    "corollary": {"cor"},
    "remark": {"rmk", "rem"},
    "warning": {"warn"},
    "obligation": {"obl"},
    "nonclaim": {"nonclaim"},
}
PAPER_AXES_SET = {"main", "xi", "ns", "aor"}
LABEL_SHORT_NAME_RE = re.compile(r"^[a-z0-9][a-z0-9-]*[a-z0-9]$")

BEGIN_RE = re.compile(
    r"\\begin\{(?P<kind>definition|theorem|lemma|proposition|corollary|remark|warning|obligation|nonclaim)\}"
    r"(?:\[(?P<title>.*?)\])?"
)
REF_RE = re.compile(r"\\(?:ref|Cref|cref|eqref)\{([^}]+)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")


@dataclass(frozen=True)
class EnvItem:
    source_file: Path
    paper_axis: str
    line_start: int
    line_end: int
    env_kind: str
    display_title: str
    raw_body: str
    latex_label: str | None
    refs: list[str]


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def strip_latex_comments(line: str) -> str:
    """Remove unescaped LaTeX comments from a single line."""
    escaped = False
    out: list[str] = []
    for ch in line:
        if ch == "%" and not escaped:
            break
        out.append(ch)
        escaped = ch == "\\" and not escaped
        if ch != "\\":
            escaped = False
    return "".join(out)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def target_files() -> list[tuple[str, Path]]:
    """Return (axis, path) for each needles paper axis."""
    out: list[tuple[str, Path]] = []
    for axis, path in PAPER_AXES.items():
        if path.exists():
            out.append((axis, path))
    return out


def extract_refs(raw: str) -> list[str]:
    refs: list[str] = []
    seen: set[str] = set()
    for match in REF_RE.finditer(raw):
        for part in match.group(1).split(","):
            label = part.strip()
            if label and label not in seen:
                seen.add(label)
                refs.append(label)
    return refs


def normalize_statement(raw: str) -> str:
    lines = []
    for line in raw.splitlines():
        without_comments = strip_latex_comments(line)
        without_label = LABEL_RE.sub("", without_comments)
        if without_label.strip():
            lines.append(without_label.strip())
    return re.sub(r"\s+", " ", " ".join(lines)).strip()


def extract_items(axis: str, path: Path) -> tuple[list[EnvItem], list[EnvItem]]:
    lines = read_text(path).splitlines()
    labeled: list[EnvItem] = []
    unlabeled: list[EnvItem] = []
    i = 0
    while i < len(lines):
        begin_match = BEGIN_RE.search(strip_latex_comments(lines[i]))
        if not begin_match:
            i += 1
            continue
        kind = begin_match.group("kind")
        title = (begin_match.group("title") or "").strip()
        start = i
        end = i
        end_re = re.compile(rf"\\end\{{{re.escape(kind)}\}}")
        while end < len(lines) and not end_re.search(lines[end]):
            end += 1
        if end >= len(lines):
            end = len(lines) - 1
        raw = "\n".join(lines[start : end + 1])
        labels = LABEL_RE.findall(raw)
        item = EnvItem(
            source_file=path,
            paper_axis=axis,
            line_start=start + 1,
            line_end=end + 1,
            env_kind=kind,
            display_title=title,
            raw_body=raw,
            latex_label=labels[0] if labels else None,
            refs=extract_refs(raw),
        )
        if item.latex_label:
            labeled.append(item)
        else:
            unlabeled.append(item)
        i = end + 1
    return labeled, unlabeled


def item_record(item: EnvItem, corpus: str) -> dict[str, object]:
    normalized = normalize_statement(item.raw_body)
    return {
        "corpus": corpus,
        "paper_axis": item.paper_axis,
        "source_file": rel(item.source_file),
        "line_start": item.line_start,
        "line_end": item.line_end,
        "env_kind": item.env_kind,
        "latex_label": item.latex_label,
        "display_title": item.display_title,
        "raw_body": item.raw_body,
        "normalized_statement": normalized,
        "statement_hash": sha256_text(normalized),
        "body_hash": sha256_text(item.raw_body),
        "dependencies": item.refs,
    }


def write_jsonl(path: Path, records: Iterable[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True))
            handle.write("\n")


def terminology_record() -> dict[str, object]:
    path = ROOT / "paper" / "notation_and_terminology.md"
    content = read_text(path) if path.exists() else ""
    return {
        "source_file": rel(path) if path.exists() else "paper/notation_and_terminology.md",
        "body_hash": sha256_text(content),
        "line_count": len(content.splitlines()),
        "role": "terminology_source",
    }


def write_terminology_snapshot() -> None:
    TERMINOLOGY_SNAPSHOT.parent.mkdir(parents=True, exist_ok=True)
    TERMINOLOGY_SNAPSHOT.write_text(
        json.dumps(terminology_record(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def collect_records() -> tuple[list[dict[str, object]], list[dict[str, object]], list[EnvItem]]:
    target_records: list[dict[str, object]] = []
    dependency_records: list[dict[str, object]] = []
    unlabeled_target_items: list[EnvItem] = []

    for axis, path in target_files():
        labeled, unlabeled = extract_items(axis, path)
        unlabeled_target_items.extend(unlabeled)
        target_records.extend(item_record(item, "target") for item in labeled)

    return target_records, dependency_records, unlabeled_target_items


def default_category(record: dict[str, object]) -> str:
    kind = str(record["env_kind"])
    if kind == "definition":
        return "lean_definition"
    if kind in ("remark", "nonclaim"):
        return "prose_only"
    if kind == "obligation":
        return "sourced_assumption"
    if kind == "warning":
        return "prose_only"
    # theorem | lemma | proposition | corollary
    text = f"{record.get('display_title', '')} {record.get('normalized_statement', '')}".lower()
    schema_words = (
        "all-six",
        "exact-six",
        "audit",
        "record",
        "accepted",
        "transfer",
        "promotion",
    )
    if any(word in text for word in schema_words):
        return "schema_theorem"
    return "fully_formal_math"


def quote_yaml_key(key: str) -> str:
    return json.dumps(key)


def write_boundary(records: list[dict[str, object]], overwrite: bool = False) -> None:
    existing = parse_boundary() if BOUNDARY_FILE.exists() else {}
    if BOUNDARY_FILE.exists() and not overwrite:
        boundary = dict(existing)
    else:
        boundary = {}

    for record in sorted(records, key=lambda r: str(r["latex_label"])):
        label = str(record["latex_label"])
        old = boundary.get(label, {})
        boundary[label] = {
            "category": old.get("category") or default_category(record),
            "source_file": str(record["source_file"]),
            "statement_hash": str(record["statement_hash"]),
        }

    lines = [
        "# Formalization boundary overlay for the Lean 4 inventory.",
        "# Categories: lean_definition, fully_formal_math, schema_theorem, sourced_assumption, prose_only.",
        "# This file is curated. The extractor updates missing entries but preserves existing categories.",
        "items:",
    ]
    for label in sorted(boundary):
        entry = boundary[label]
        lines.extend(
            [
                f"  {quote_yaml_key(label)}:",
                f"    category: {entry.get('category', '')}",
                f"    source_file: {entry.get('source_file', '')}",
                f"    statement_hash: {entry.get('statement_hash', '')}",
            ]
        )
    BOUNDARY_FILE.parent.mkdir(parents=True, exist_ok=True)
    BOUNDARY_FILE.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_boundary() -> dict[str, dict[str, str]]:
    if not BOUNDARY_FILE.exists():
        return {}
    entries: dict[str, dict[str, str]] = {}
    current: str | None = None
    key_re = re.compile(r'^\s{2}"(?P<label>(?:[^"\\]|\\.)+)":\s*$')
    field_re = re.compile(r"^\s{4}(?P<key>[A-Za-z_]+):\s*(?P<value>.*)\s*$")
    for line in BOUNDARY_FILE.read_text(encoding="utf-8").splitlines():
        key_match = key_re.match(line)
        if key_match:
            current = json.loads(f'"{key_match.group("label")}"')
            entries[current] = {}
            continue
        field_match = field_re.match(line)
        if field_match and current is not None:
            entries[current][field_match.group("key")] = field_match.group("value").strip()
    return entries


def validate(
    records: list[dict[str, object]],
    unlabeled_target_items: list[EnvItem],
    *,
    require_boundary: bool,
) -> list[str]:
    errors: list[str] = []

    if unlabeled_target_items:
        for item in unlabeled_target_items:
            errors.append(
                "unlabeled target environment: "
                f"{rel(item.source_file)}:{item.line_start} {item.env_kind}"
                + (f" [{item.display_title}]" if item.display_title else "")
            )

    by_label: dict[str, list[dict[str, object]]] = {}
    for record in records:
        by_label.setdefault(str(record["latex_label"]), []).append(record)
    for label, matches in sorted(by_label.items()):
        if len(matches) > 1:
            locations = ", ".join(f"{m['source_file']}:{m['line_start']}" for m in matches)
            errors.append(f"duplicate target label {label}: {locations}")

    # Enforce the `<kind>:<axis>:<short-name>` label scheme: every label
    # must have three colon-separated parts; the kind must match the
    # env_kind; the axis must match the paper_axis; the short-name must
    # be kebab-case alphanumeric.
    for record in records:
        label = str(record["latex_label"])
        env_kind = str(record["env_kind"])
        axis = str(record["paper_axis"])
        location = f"{record['source_file']}:{record['line_start']}"
        parts = label.split(":")
        if len(parts) != 3:
            errors.append(
                f"label {label!r} at {location} does not match `<kind>:<axis>:<short-name>` "
                f"(expected exactly 3 colon-separated parts, got {len(parts)})"
            )
            continue
        kind_prefix, label_axis, short_name = parts
        allowed_kinds = LABEL_KIND_PREFIXES.get(env_kind, set())
        if kind_prefix not in allowed_kinds:
            errors.append(
                f"label {label!r} at {location} has kind prefix {kind_prefix!r} "
                f"but env_kind is {env_kind!r} (allowed: {sorted(allowed_kinds)})"
            )
        if label_axis not in PAPER_AXES_SET:
            errors.append(
                f"label {label!r} at {location} has axis {label_axis!r} not in {sorted(PAPER_AXES_SET)}"
            )
        elif label_axis != axis:
            errors.append(
                f"label {label!r} at {location} has axis {label_axis!r} but the env lives in axis {axis!r}"
            )
        if not LABEL_SHORT_NAME_RE.fullmatch(short_name):
            errors.append(
                f"label {label!r} at {location} short-name {short_name!r} is not kebab-case alphanumeric"
            )

    if require_boundary:
        boundary = parse_boundary()
        record_by_label = {str(record["latex_label"]): record for record in records}
        for label in sorted(record_by_label):
            entry = boundary.get(label)
            if not entry:
                errors.append(f"missing boundary category for target label {label}")
                continue
            category = entry.get("category", "")
            if category not in FORMALIZATION_CATEGORIES:
                errors.append(f"invalid category for {label}: {category!r}")
            expected_hash = str(record_by_label[label]["statement_hash"])
            if entry.get("statement_hash") != expected_hash:
                errors.append(
                    f"stale statement hash for {label}: "
                    f"boundary={entry.get('statement_hash')} current={expected_hash}"
                )
        for label in sorted(boundary):
            if label not in record_by_label:
                errors.append(f"boundary references missing target label {label}")

    return errors


def generate(args: argparse.Namespace) -> int:
    target_records, dependency_records, unlabeled = collect_records()
    INVENTORY_DIR.mkdir(parents=True, exist_ok=True)
    write_jsonl(SOURCE_ITEMS, target_records)
    write_jsonl(DEPENDENCY_ITEMS, dependency_records)
    write_terminology_snapshot()
    if args.init_boundary or args.overwrite_boundary or not BOUNDARY_FILE.exists():
        write_boundary(target_records, overwrite=args.overwrite_boundary)
    errors = validate(target_records, unlabeled, require_boundary=True)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(f"wrote {len(target_records)} target records to {rel(SOURCE_ITEMS)}")
    print(f"wrote {len(dependency_records)} dependency records to {rel(DEPENDENCY_ITEMS)}")
    print(f"validated {rel(BOUNDARY_FILE)}")
    return 0


def check() -> int:
    target_records, dependency_records, unlabeled = collect_records()
    errors = validate(target_records, unlabeled, require_boundary=True)

    if SOURCE_ITEMS.exists():
        committed = [
            json.loads(line)
            for line in SOURCE_ITEMS.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        current = target_records
        if committed != current:
            errors.append(f"{rel(SOURCE_ITEMS)} is stale; rerun extractor")
    else:
        errors.append(f"missing {rel(SOURCE_ITEMS)}")

    if DEPENDENCY_ITEMS.exists():
        committed_dependency = [
            json.loads(line)
            for line in DEPENDENCY_ITEMS.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        if committed_dependency != dependency_records:
            errors.append(f"{rel(DEPENDENCY_ITEMS)} is stale; rerun extractor")
    else:
        errors.append(f"missing {rel(DEPENDENCY_ITEMS)}")

    if TERMINOLOGY_SNAPSHOT.exists():
        committed_terminology = json.loads(TERMINOLOGY_SNAPSHOT.read_text(encoding="utf-8"))
        if committed_terminology != terminology_record():
            errors.append(f"{rel(TERMINOLOGY_SNAPSHOT)} is stale; rerun extractor")
    else:
        errors.append(f"missing {rel(TERMINOLOGY_SNAPSHOT)}")

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(f"inventory check passed: {len(target_records)} target records")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate committed inventory and boundary")
    parser.add_argument("--init-boundary", action="store_true", help="add missing boundary entries")
    parser.add_argument("--overwrite-boundary", action="store_true", help="rewrite boundary categories from defaults")
    args = parser.parse_args()
    if args.check:
        return check()
    return generate(args)


if __name__ == "__main__":
    raise SystemExit(main())
