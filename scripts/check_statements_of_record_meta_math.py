#!/usr/bin/env python3
"""Validate the meta-math statements-of-record registry.

The registry at
``paper/meta_math/notes/statements-of-record.yml`` binds every
paper-facing label for the meta-math paper to its target
destination, proof-presentation mode, Lean coverage, and Lean
declaration. This validator cross-checks that registry against
``lean/manifests/meta_math_manifest.toml`` and
``paper/meta_math/paper_inventory.toml`` so drafting cannot drift
from the mechanized state or the Phase 0 source inventory.

Distinct from ``scripts/check_statements_of_record.py`` (which
covers the needles paper axes); shares no inventory or manifest.
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter
from pathlib import Path

try:  # Python 3.11+
    import tomllib  # type: ignore[import-not-found]
except ModuleNotFoundError:  # older Python
    import tomli as tomllib  # type: ignore[no-redef]

import yaml


ROOT = Path(__file__).resolve().parents[1]
STATEMENTS = ROOT / "paper" / "meta_math" / "notes" / "statements-of-record.yml"
MANIFEST = ROOT / "lean" / "manifests" / "meta_math_manifest.toml"
INVENTORY = ROOT / "paper" / "meta_math" / "paper_inventory.toml"
TRUST_BASE = ROOT / "lean" / "manifests" / "trust_base.txt"


TOP_LEVEL_KEYS = {
    "schema_version",
    "status",
    "rows",
    "total_rows",
    "target_destination_counts",
    "target_part_counts",
    "lean_coverage_counts",
    "proof_presentation_counts",
    "semantic_alignment_counts",
}

ROW_FIELDS = {
    "paper_label",
    "env_kind",
    "source_file",
    "source_section",
    "source_lines",
    "theorem_title",
    "target_destination",
    "target_part",
    "target_section_hint",
    "proof_presentation",
    "lean_coverage",
    "lean_decl",
    "semantic_alignment",
    "obligation_guard",
    "substrate_cite",
    "notes",
}

ALLOWED_DESTINATIONS = {
    "body", "appendix", "source_only", "evidence_pack_only", "nonclaim",
}
ALLOWED_PARTS = {
    "I", "II", "III", "Apparatus", "Validation", "Audit", "Predictions",
    "Scope", "Conclusion",
}
ALLOWED_PROOF_PRESENTATIONS = {
    "body_full",
    "body_sketch",
    "appendix_only",
    "lean_substantive",
    "lean_traceability_only",
    "standard_reference",
    "definition_entry",
    "obligation_disclosure",
    "validation_citation",
    "nonclaim_statement",
}
ALLOWED_LEAN_COVERAGE = {
    "theorem",
    "partial",
    "obligation",
    "substrate_pending",
    "definition",
    "not_mechanized",
    "not_applicable",
}
ALLOWED_SEMANTIC_ALIGNMENTS = {
    "faithful",
    "narrowed_surrogate",
    "weakened_genericized",
    "needs_strengthening",
    "projection_packaged",
    "opacity_guarded",
    "not_applicable",
}
ALLOWED_ENV_KINDS = {
    "definition",
    "theorem",
    "lemma",
    "corollary",
    "proposition",
    "remark",
    "warning",
    "nonclaim",
    "obligation",
    "support_only",
    "validation",
}


def _load_yaml(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as fh:
        return yaml.safe_load(fh)


def _load_toml(path: Path) -> dict:
    with path.open("rb") as fh:
        return tomllib.load(fh)


def _validate_rows(rows: list[dict], manifest_decls: set[str],
                   inventory_labels: set[str], trust_base_lines: set[str]) -> list[str]:
    errors: list[str] = []
    seen_labels: set[str] = set()
    counts: dict[str, Counter] = {
        "target_destination": Counter(),
        "target_part": Counter(),
        "lean_coverage": Counter(),
        "proof_presentation": Counter(),
        "semantic_alignment": Counter(),
    }

    for i, row in enumerate(rows):
        label = row.get("paper_label", f"<row {i}>")

        # Field schema
        missing = ROW_FIELDS - row.keys()
        extra = row.keys() - ROW_FIELDS
        if missing:
            errors.append(f"{label}: missing fields {sorted(missing)}")
        if extra:
            errors.append(f"{label}: unexpected fields {sorted(extra)}")

        if label in seen_labels:
            errors.append(f"{label}: duplicate paper_label")
        seen_labels.add(label)

        # Vocabulary checks
        env_kind = row.get("env_kind")
        if env_kind not in ALLOWED_ENV_KINDS:
            errors.append(f"{label}: invalid env_kind '{env_kind}'")

        dest = row.get("target_destination")
        if dest not in ALLOWED_DESTINATIONS:
            errors.append(f"{label}: invalid target_destination '{dest}'")
        else:
            counts["target_destination"][dest] += 1

        part = row.get("target_part")
        if part not in ALLOWED_PARTS:
            errors.append(f"{label}: invalid target_part '{part}'")
        else:
            counts["target_part"][part] += 1

        pp = row.get("proof_presentation")
        if pp not in ALLOWED_PROOF_PRESENTATIONS:
            errors.append(f"{label}: invalid proof_presentation '{pp}'")
        else:
            counts["proof_presentation"][pp] += 1

        lc = row.get("lean_coverage")
        if lc not in ALLOWED_LEAN_COVERAGE:
            errors.append(f"{label}: invalid lean_coverage '{lc}'")
        else:
            counts["lean_coverage"][lc] += 1

        sa = row.get("semantic_alignment")
        if sa not in ALLOWED_SEMANTIC_ALIGNMENTS:
            errors.append(f"{label}: invalid semantic_alignment '{sa}'")
        else:
            counts["semantic_alignment"][sa] += 1

        # Lean decl cross-check (skip placeholders)
        lean_decl = row.get("lean_decl", "")
        if lc not in {"not_mechanized", "not_applicable"} and lean_decl != "not_applicable":
            # A row may bundle multiple decls in a brace-set; split by comma after stripping
            decls_to_check: list[str] = []
            if "{" in lean_decl and "}" in lean_decl:
                prefix, rest = lean_decl.split("{", 1)
                inner, _ = rest.split("}", 1)
                for piece in (p.strip() for p in inner.split(",")):
                    decls_to_check.append(prefix + piece)
            else:
                decls_to_check.append(lean_decl)
            for d in decls_to_check:
                if d not in manifest_decls:
                    errors.append(
                        f"{label}: lean_decl '{d}' not in meta-math manifest"
                    )

        # Obligation rows must have an obligation_guard and lean_decl in trust_base
        if lc == "obligation":
            guard = row.get("obligation_guard", "")
            if not guard:
                errors.append(f"{label}: obligation row missing obligation_guard")
            # The lean_decl should be in trust_base.txt (as a meta-math obligation line)
            if lean_decl and lean_decl != "not_applicable" and lean_decl not in trust_base_lines:
                errors.append(
                    f"{label}: obligation lean_decl '{lean_decl}' not in trust_base.txt"
                )

        # Validation rows must have a substrate_cite
        if env_kind == "validation":
            cite = row.get("substrate_cite", "")
            if not cite:
                errors.append(f"{label}: validation row missing substrate_cite")

        # Nonclaim rows must use nonclaim_statement presentation + nonclaim destination
        if env_kind == "nonclaim":
            if pp != "nonclaim_statement":
                errors.append(
                    f"{label}: nonclaim row must use proof_presentation=nonclaim_statement"
                )
            if dest != "nonclaim":
                errors.append(
                    f"{label}: nonclaim row must use target_destination=nonclaim"
                )

    # Cross-check inventory T-labels appear at least once
    inventory_t_labels = {lab for lab in inventory_labels if lab.startswith("T")}
    used_t_labels = {lab for lab in seen_labels if lab.startswith("T") and "-" not in lab}
    missing_t = inventory_t_labels - used_t_labels
    if missing_t:
        errors.append(
            f"inventory T-labels missing primary SOR row: {sorted(missing_t)}"
        )

    return errors


def _extract_manifest_decls(manifest: dict) -> set[str]:
    out: set[str] = set()
    for e in manifest.get("entries", []):
        out.add(e["lean_decl"])
    return out


def _extract_inventory_labels(inventory: dict) -> set[str]:
    return {e["paper_label"] for e in inventory.get("entry", [])}


def _extract_trust_base_lines(text: str) -> set[str]:
    out: set[str] = set()
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        out.add(line)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--statements", type=Path, default=STATEMENTS)
    parser.add_argument("--manifest", type=Path, default=MANIFEST)
    parser.add_argument("--inventory", type=Path, default=INVENTORY)
    parser.add_argument("--trust-base", type=Path, default=TRUST_BASE)
    args = parser.parse_args(argv)

    if not args.statements.exists():
        print(f"missing: {args.statements}", file=sys.stderr)
        return 2
    data = _load_yaml(args.statements)
    if not isinstance(data, dict):
        print("statements-of-record.yml: top-level must be a mapping", file=sys.stderr)
        return 2

    top_extra = data.keys() - TOP_LEVEL_KEYS
    if top_extra:
        print(f"unexpected top-level keys: {sorted(top_extra)}", file=sys.stderr)
        return 2

    rows = data.get("rows", [])
    if not isinstance(rows, list) or not rows:
        print("statements-of-record.yml: rows must be a non-empty list", file=sys.stderr)
        return 2

    manifest = _load_toml(args.manifest)
    manifest_decls = _extract_manifest_decls(manifest)

    inventory = _load_toml(args.inventory)
    inventory_labels = _extract_inventory_labels(inventory)

    trust_base_text = args.trust_base.read_text(encoding="utf-8")
    trust_base_lines = _extract_trust_base_lines(trust_base_text)

    errors = _validate_rows(rows, manifest_decls, inventory_labels, trust_base_lines)
    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        return 1

    print(
        f"ok: {len(rows)} rows; "
        f"{len(manifest_decls)} manifest decls cross-checked; "
        f"{len(inventory_labels)} inventory labels matched."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
