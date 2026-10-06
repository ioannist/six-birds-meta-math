#!/usr/bin/env python3
"""Build per-axis paper inventory TOMLs and mechanization queue CSVs.

Reads source_items.jsonl plus an inlined status mapping (curated below)
and emits, for each axis in {main, xi, ns}:
- formalization/inventory/<axis>_paper_inventory.toml
- formalization/traceability/queue_<axis>.csv

Run with `--check` to validate that the committed files match what
the script would generate (used by Phase A's seal step and any
downstream CI).

Status field allowlist:
  mechanize_now, obligation, out_of_scope_rh, out_of_scope_ns,
  support_only, nonclaim
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INVENTORY_DIR = ROOT / "formalization" / "inventory"
TRACEABILITY_DIR = ROOT / "formalization" / "traceability"
SOURCE_ITEMS = INVENTORY_DIR / "source_items.jsonl"

MAIN_TOML = INVENTORY_DIR / "main_paper_inventory.toml"
XI_TOML = INVENTORY_DIR / "xi_paper_inventory.toml"
NS_TOML = INVENTORY_DIR / "ns_paper_inventory.toml"
AOR_TOML = INVENTORY_DIR / "aor_paper_inventory.toml"
QUEUE_MAIN = TRACEABILITY_DIR / "queue_main.csv"
QUEUE_XI = TRACEABILITY_DIR / "queue_xi.csv"
QUEUE_NS = TRACEABILITY_DIR / "queue_ns.csv"
QUEUE_AOR = TRACEABILITY_DIR / "queue_aor.csv"

AXES = ("main", "xi", "ns", "aor")

AXIS_TOML = {
    "main": MAIN_TOML,
    "xi": XI_TOML,
    "ns": NS_TOML,
    "aor": AOR_TOML,
}
AXIS_QUEUE = {
    "main": QUEUE_MAIN,
    "xi": QUEUE_XI,
    "ns": QUEUE_NS,
    "aor": QUEUE_AOR,
}


MAIN_SECTIONS = [
    (52, 70, "Landing: formed-layer membrane theory"),
    (71, 115, "Legal quotient and native currency"),
    (116, 130, "Schur squares and lawful witnesses"),
    (131, 169, "The Xi companion interface"),
    (170, 202, "Predictive native membranes"),
    (203, 249, "Layer-dissolving membrane endpoint theorem"),
    (250, 495, "Duality-confinement membrane theorem"),
    (496, 512, "Critical-pair completion and strict extension"),
    (513, 532, "All-six records, transfer, and taxonomy"),
    (533, 557, "Root-composite RH obligation"),
    (558, 572, "Navier adequacy demonstration"),
    (573, 9999, "Conclusion"),
]
XI_SECTIONS = [
    (48, 66, "Purpose and scope"),
    (67, 88, "Standing hypotheses: the legal energy quotient"),
    (89, 119, "Currency and minimum spend"),
    (120, 156, "Definition of the adequacy residual"),
    (157, 184, "Projection theorem"),
    (185, 222, "Optimal residual and exact adequacy"),
    (223, 248, "Promotion from native membrane to dissolving membrane"),
    (249, 288, "Strict native extension"),
    (289, 348, "Data processing and transfer"),
    (349, 379, "Obstruction and repair calculus"),
    (380, 407, "Predictive adequacy ladders"),
    (408, 424, "Examples and application templates"),
    (425, 428, "Nonclaims"),
    (429, 9999, "Conclusion"),
]
NS_SECTIONS = [
    (63, 98, "The Navier-Stokes carrier and the BG/BKM dissolving readout"),
    (99, 147, "Literature imports"),
    (148, 166, "Criterion-native equality and physical-native gap"),
    (167, 185, "The physical-native adequacy cascade"),
    (186, 229, "Framework-derived no-go theorems (NG2-NG10)"),
    (230, 289, "Gevrey radius-window branch and LP-transport rescue"),
    (290, 312, "Six Birds closure records R1-R9"),
    (313, 322, "Main theorem under Six Birds closure"),
    (323, 359, "NS as an AOR instance"),
    (360, 9999, "Status, limitations, and external interpretation"),
]
AOR_SECTIONS = [
    (88, 147, "PreSB carriers and the AOR full subcategory"),
    (148, 191, "The closure-completion functor Cl_SB"),
    (192, 281, "The structural defect Xi_SB and its 8 strata"),
    (282, 356, "The Sigma_residual atlas"),
    (357, 393, "AOR-8 statuses and discharge"),
    (394, 488, "Discharge cascades over Sigma_residual"),
    (489, 600, "Refinement chains, colimits, and asymptotic discharge"),
    (601, 9999, "Status, scope, and nonclaim boundary"),
]

AXIS_SECTIONS = {
    "main": MAIN_SECTIONS,
    "xi": XI_SECTIONS,
    "ns": NS_SECTIONS,
    "aor": AOR_SECTIONS,
}


# Curated intended_status per paper_label. Defaults applied by kind below for any
# label not listed here.
STATUS_OVERRIDES = {
    # Main paper RH-specific obligations
    "obl:main:explicit-formula-domination": "out_of_scope_rh",
    "obl:main:character-source-coercivity": "out_of_scope_rh",
    # Main paper duality-confinement remarks / warnings: nonclaim scope
    "warn:main:defect-paid-version": "nonclaim",
    # NS PDE imports: realized as Lean structures, but boundary category is
    # sourced_assumption (provenance). They remain mechanize_now under the
    # inventory status assignment.
    # No override needed; default for def → mechanize_now.
    # NS framework-deliverable T10: kept mechanize_now with manifest
    # status = partial / projection-packaged. No override needed.
}


def find_section(axis: str, line: int) -> str:
    sections = AXIS_SECTIONS.get(axis)
    if sections is None:
        return "<unknown-axis>"
    for start, end, name in sections:
        if start <= line <= end:
            return name
    return "<unknown>"


def default_status(env_kind: str) -> str:
    if env_kind == "nonclaim":
        return "nonclaim"
    if env_kind == "remark":
        return "nonclaim"
    if env_kind == "warning":
        return "nonclaim"
    if env_kind == "obligation":
        return "obligation"
    return "mechanize_now"


def intended_status(label: str, env_kind: str) -> str:
    if label in STATUS_OVERRIDES:
        return STATUS_OVERRIDES[label]
    return default_status(env_kind)


def toml_string(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def render_toml(axis: str, entries: list[dict]) -> str:
    lines = [
        f"# Per-axis paper inventory for the {axis} paper.",
        "# Generated by scripts/build_paper_inventories.py from source_items.jsonl.",
        "#",
        "# intended_status: mechanize_now | obligation | out_of_scope_rh | out_of_scope_ns | support_only | nonclaim",
        "",
    ]
    for entry in entries:
        lines.append("[[entry]]")
        lines.append(f"paper_label = {toml_string(entry['paper_label'])}")
        lines.append(f"kind = {toml_string(entry['kind'])}")
        lines.append(f"section = {toml_string(entry['section'])}")
        lines.append(f"intended_status = {toml_string(entry['intended_status'])}")
        lines.append(f"required = {'true' if entry['required'] else 'false'}")
        lines.append(f"line_start = {entry['line_start']}")
        lines.append(f"line_end = {entry['line_end']}")
        lines.append(f"source_file = {toml_string(entry['source_file'])}")
        lines.append(f"statement_hash = {toml_string(entry['statement_hash'])}")
        lines.append(f"duplicate_of = {toml_string('')}")
        lines.append("")
    return "\n".join(lines)


def write_toml(path: Path, axis: str, entries: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(render_toml(axis, entries), encoding="utf-8")


def render_queue(entries: list[dict]) -> str:
    queue_entries = [e for e in entries if e["intended_status"] == "mechanize_now"]
    buffer = io.StringIO()
    writer = csv.writer(buffer, lineterminator="\n")
    writer.writerow(["order", "paper_label", "kind", "section", "line_start", "source_file"])
    for order, entry in enumerate(queue_entries, start=1):
        writer.writerow(
            [
                order,
                entry["paper_label"],
                entry["kind"],
                entry["section"],
                entry["line_start"],
                entry["source_file"],
            ]
        )
    return buffer.getvalue()


def write_queue(path: Path, entries: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(render_queue(entries), encoding="utf-8")


def collect_entries() -> dict[str, list[dict]]:
    records = [
        json.loads(line)
        for line in SOURCE_ITEMS.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    entries_by_axis: dict[str, list[dict]] = {axis: [] for axis in AXES}
    for record in sorted(records, key=lambda r: (r["paper_axis"], r["line_start"])):
        label = str(record["latex_label"])
        kind = str(record["env_kind"])
        axis = str(record["paper_axis"])
        line = int(record["line_start"])
        entry = {
            "paper_label": label,
            "kind": kind,
            "section": find_section(axis, line),
            "intended_status": intended_status(label, kind),
            "required": True,
            "line_start": line,
            "line_end": int(record["line_end"]),
            "source_file": str(record["source_file"]),
            "statement_hash": str(record["statement_hash"]),
        }
        if axis in entries_by_axis:
            entries_by_axis[axis].append(entry)
        else:
            raise SystemExit(f"unknown paper_axis {axis!r} in {label}; update AXES in build_paper_inventories")
    return entries_by_axis


def check() -> int:
    """Validate the committed inventory TOMLs and queue CSVs match what we
    would generate from the current source_items.jsonl."""
    errors: list[str] = []
    entries_by_axis = collect_entries()
    for axis in AXES:
        entries = entries_by_axis[axis]
        path = AXIS_TOML[axis]
        if not path.exists():
            errors.append(f"missing {path.relative_to(ROOT)}; rerun build_paper_inventories")
        else:
            expected = render_toml(axis, entries)
            if path.read_text(encoding="utf-8") != expected:
                errors.append(f"{path.relative_to(ROOT)} is stale; rerun build_paper_inventories")
        queue_path = AXIS_QUEUE[axis]
        if not queue_path.exists():
            errors.append(f"missing {queue_path.relative_to(ROOT)}; rerun build_paper_inventories")
        else:
            expected_queue = render_queue(entries)
            if queue_path.read_text(encoding="utf-8") != expected_queue:
                errors.append(f"{queue_path.relative_to(ROOT)} is stale; rerun build_paper_inventories")
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("paper inventories and queues are current")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate committed inventory TOMLs and queue CSVs against current source_items.jsonl",
    )
    args = parser.parse_args()
    if args.check:
        return check()

    entries_by_axis = collect_entries()
    for axis in AXES:
        entries = entries_by_axis[axis]
        write_toml(AXIS_TOML[axis], axis, entries)
        write_queue(AXIS_QUEUE[axis], entries)
        mech_count = sum(1 for e in entries if e["intended_status"] == "mechanize_now")
        print(f"wrote {len(entries)} {axis} entries → {AXIS_TOML[axis].relative_to(ROOT)}")
        print(f"wrote {axis} queue ({mech_count} items) → {AXIS_QUEUE[axis].relative_to(ROOT)}")

    print()
    print("Status breakdown:")
    for axis in AXES:
        entries = entries_by_axis[axis]
        counts: dict[str, int] = {}
        for e in entries:
            counts[e["intended_status"]] = counts.get(e["intended_status"], 0) + 1
        print(f"  {axis}: " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
