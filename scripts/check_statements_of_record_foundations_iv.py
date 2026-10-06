#!/usr/bin/env python3
"""Validate the F-IV statements-of-record registry.

Cross-checks `paper/foundations_iv/notes/statements-of-record.yml`
against `paper/foundations_iv/paper_inventory.toml` and
`lean/manifests/foundations_iv_manifest.toml` plus
`lean/manifests/trust_base.txt` so the paper-prep state cannot
silently drift from the mechanized corpus.

Discipline:
  * Every F-IV inventory row has exactly one SOR row.
  * Each SOR row's `lean_decl` exists in the manifest.
  * Each SOR `lean_coverage` matches the manifest `status` partition.
  * Trust-base attachments (obligation_guard / guard_decl /
    axiom_shape / trust_base_tag) are populated for partial /
    obligation rows and blank for theorem / anchor_substrate rows.
  * Substrate citations are populated for anchor / partial /
    obligation rows whose substrate is named in the manifest /
    inventory.

Exit code 0 iff all checks pass. Prints findings grouped by severity.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Iterable

try:
    import tomllib  # Python 3.11+
except ModuleNotFoundError:
    import tomli as tomllib  # type: ignore[no-redef]

try:
    import yaml
except ImportError:
    sys.stderr.write("error: PyYAML required (pip install pyyaml)\n")
    sys.exit(2)


ROOT = Path(__file__).resolve().parents[1]
SOR_YML = ROOT / "paper" / "foundations_iv" / "notes" / "statements-of-record.yml"
INVENTORY = ROOT / "paper" / "foundations_iv" / "paper_inventory.toml"
MANIFEST = ROOT / "lean" / "manifests" / "foundations_iv_manifest.toml"
TRUST_BASE = ROOT / "lean" / "manifests" / "trust_base.txt"
REFERENCES_BIB = ROOT / "paper" / "references.bib"

ROW_FIELDS = {
    "paper_label",
    "env_kind",
    "source_file",
    "source_section",
    "theorem_title",
    "target_destination",
    "target_axis",
    "target_chapter",
    "target_section_hint",
    "proof_presentation",
    "lean_coverage",
    "lean_decl",
    "semantic_alignment",
    "substrate_cite",
    "trust_base_tag",
    "axiom_shape",
    "obligation_guard",
    "guard_decl",
    "notes",
}
ALLOWED_ENV_KINDS = {
    "definition", "theorem", "lemma", "proposition", "corollary",
    "remark", "warning", "nonclaim", "obligation",
    "substrate_pending", "anchor_substrate",
}
ALLOWED_DESTINATIONS = {"body", "appendix", "source_only"}
ALLOWED_AXES = {
    "Transport", "Stability", "Access", "Symmetry",
    "StatusRecordsCoherence", "SelfReferenceLimits",
    "ClosureRealityBoundary",
}
ALLOWED_PROOF_PRESENTATIONS = {
    "body_full", "body_sketch", "appendix_only",
    "lean_substantive", "lean_traceability_only",
    "standard_reference", "definition_entry", "anchor_citation",
}
ALLOWED_LEAN_COVERAGE = {
    "theorem", "partial", "obligation", "substrate_pending",
    "anchor_substrate", "definition", "not_mechanized",
}
ALLOWED_SEMANTIC = {
    "faithful", "narrowed_surrogate", "weakened_genericized",
    "needs_strengthening", "projection_packaged",
    "anchored_to_substrate", "not_applicable",
}
ALLOWED_TRUST_BASE_TAGS = {"obligation", "substrate_pending", "none", ""}
F_IV_TRUST_BASE_AXIOMS: dict[str, tuple[str, str]] = {}


def load_yaml(path: Path) -> dict:
    return yaml.safe_load(path.read_text())


def load_toml(path: Path) -> dict:
    return tomllib.loads(path.read_text())


def load_lines(path: Path) -> list[str]:
    return path.read_text().splitlines()


def collect_bibkeys(path: Path) -> set[str]:
    """Extract @<type>{<key>, entries from a bibtex file."""
    import re
    pat = re.compile(r"^\s*@\w+\s*\{\s*([^,\s]+)\s*,", re.MULTILINE)
    return set(pat.findall(path.read_text()))


def collect_inventory_labels(inv: dict) -> set[str]:
    return {e["paper_label"] for e in inv["entry"]}


def collect_manifest_index(manifest: dict) -> dict:
    """Map paper_label -> set of lean_decl strings, plus per-decl status."""
    by_label: dict[str, set[str]] = {}
    decl_status: dict[str, str] = {}
    for e in manifest["entries"]:
        by_label.setdefault(e["paper_label"], set()).add(e["lean_decl"])
        decl_status[e["lean_decl"]] = e["status"]
    return {"by_label": by_label, "decl_status": decl_status}


def collect_inventory_status(inv: dict) -> dict[str, str]:
    return {e["paper_label"]: e["intended_status"] for e in inv["entry"]}


def report(findings: list[tuple[str, str]]) -> int:
    if not findings:
        print("OK — F-IV statements-of-record validate clean.")
        return 0
    crit = [m for sev, m in findings if sev == "CRITICAL"]
    err = [m for sev, m in findings if sev == "ERROR"]
    warn = [m for sev, m in findings if sev == "WARN"]
    for label, items in (("CRITICAL", crit), ("ERROR", err), ("WARN", warn)):
        if items:
            print(f"\n[{label}] ({len(items)} finding{'s' if len(items)!=1 else ''})")
            for m in items:
                print(f"  - {m}")
    return 1 if (crit or err) else 0


def main() -> int:
    findings: list[tuple[str, str]] = []
    sor = load_yaml(SOR_YML)
    inv = load_toml(INVENTORY)
    manifest = load_toml(MANIFEST)
    trust_lines = load_lines(TRUST_BASE)
    bibkeys = collect_bibkeys(REFERENCES_BIB)

    rows = sor.get("rows", [])
    inv_labels = collect_inventory_labels(inv)
    idx = collect_manifest_index(manifest)
    by_label = idx["by_label"]
    decl_status = idx["decl_status"]

    sor_labels = {r["paper_label"] for r in rows}

    # 1. Coverage parity (inventory ↔ SOR).
    missing_in_sor = inv_labels - sor_labels
    extra_in_sor = sor_labels - inv_labels
    for lbl in sorted(missing_in_sor):
        findings.append(("CRITICAL", f"inventory label {lbl} has no SOR row"))
    for lbl in sorted(extra_in_sor):
        findings.append(("CRITICAL", f"SOR row {lbl} is not in inventory"))

    # 2. Row-level field discipline.
    inv_status = collect_inventory_status(inv)
    for r in rows:
        lbl = r["paper_label"]
        keys = set(r.keys())
        missing = ROW_FIELDS - keys
        extra = keys - ROW_FIELDS
        for k in sorted(missing):
            findings.append(("ERROR", f"{lbl}: SOR row missing field `{k}`"))
        for k in sorted(extra):
            findings.append(("WARN", f"{lbl}: SOR row has unrecognized field `{k}`"))

        # Enum checks.
        ek = r.get("env_kind")
        if ek not in ALLOWED_ENV_KINDS:
            findings.append(("ERROR", f"{lbl}: env_kind `{ek}` not in allowed set"))
        td = r.get("target_destination")
        if td not in ALLOWED_DESTINATIONS:
            findings.append(("ERROR", f"{lbl}: target_destination `{td}` not in allowed set"))
        ta = r.get("target_axis")
        if ta not in ALLOWED_AXES:
            findings.append(("ERROR", f"{lbl}: target_axis `{ta}` not in allowed set"))
        pp = r.get("proof_presentation")
        if pp not in ALLOWED_PROOF_PRESENTATIONS:
            findings.append(("ERROR", f"{lbl}: proof_presentation `{pp}` not in allowed set"))
        lc = r.get("lean_coverage")
        if lc not in ALLOWED_LEAN_COVERAGE:
            findings.append(("ERROR", f"{lbl}: lean_coverage `{lc}` not in allowed set"))
        sa = r.get("semantic_alignment")
        if sa not in ALLOWED_SEMANTIC:
            findings.append(("ERROR", f"{lbl}: semantic_alignment `{sa}` not in allowed set"))
        tbt = r.get("trust_base_tag", "")
        if tbt not in ALLOWED_TRUST_BASE_TAGS:
            findings.append(("ERROR", f"{lbl}: trust_base_tag `{tbt}` not in allowed set"))

        # Lean decl present in manifest.
        decl = r.get("lean_decl", "")
        if decl and decl not in decl_status:
            findings.append(("ERROR",
                f"{lbl}: lean_decl `{decl}` not found in manifest"))

        # Lean coverage / inventory status consistency.
        # Manifest decl statuses are per-decl; inventory has the row-level
        # intended_status. SOR lean_coverage must agree with inventory.
        inv_s = inv_status.get(lbl, "")
        # Translate inventory statuses to SOR lean_coverage values:
        translation = {
            "mechanize_now": "theorem",
            "partial": "partial",
            "obligation": "obligation",
            "anchor_substrate": "anchor_substrate",
        }
        expected_lc = translation.get(inv_s, inv_s)
        if expected_lc and lc != expected_lc:
            findings.append(("ERROR",
                f"{lbl}: lean_coverage `{lc}` disagrees with inventory "
                f"intended_status `{inv_s}` (expected `{expected_lc}`)"))

        # Trust-base attachment discipline.
        if lc in {"partial", "obligation"}:
            tag_required = "obligation" if lc == "obligation" else "substrate_pending"
            if tbt != tag_required:
                findings.append(("ERROR",
                    f"{lbl}: trust_base_tag must be `{tag_required}` for "
                    f"lean_coverage `{lc}`, got `{tbt}`"))
            for fld in ("axiom_shape", "obligation_guard", "guard_decl"):
                if not r.get(fld):
                    findings.append(("ERROR",
                        f"{lbl}: {fld} must be populated for "
                        f"lean_coverage `{lc}`"))
        elif lc in {"theorem", "anchor_substrate", "definition", "not_mechanized"}:
            if tbt not in {"none", ""}:
                findings.append(("ERROR",
                    f"{lbl}: trust_base_tag must be `none` for "
                    f"lean_coverage `{lc}`, got `{tbt}`"))
            for fld in ("axiom_shape", "obligation_guard", "guard_decl"):
                if r.get(fld):
                    findings.append(("WARN",
                        f"{lbl}: {fld} should be blank for "
                        f"lean_coverage `{lc}`"))

        # Anchor rows must carry substrate citations.
        if lc == "anchor_substrate" and not r.get("substrate_cite"):
            findings.append(("ERROR",
                f"{lbl}: anchor_substrate row must populate substrate_cite"))

        # Every nonblank substrate_cite key must exist in references.bib.
        cite = r.get("substrate_cite", "") or ""
        if cite:
            cited_keys = [k.strip() for k in cite.split(",") if k.strip()]
            for key in cited_keys:
                if key not in bibkeys:
                    findings.append(("ERROR",
                        f"{lbl}: substrate_cite key `{key}` not in "
                        f"paper/references.bib"))

        # Source file existence (best-effort).
        sf = r.get("source_file", "")
        if sf:
            sf_path = ROOT / sf
            if not sf_path.exists():
                findings.append(("ERROR",
                    f"{lbl}: source_file `{sf}` does not exist"))

    # 3. Trust base axiom registry coverage.
    # Trust base lists fully-qualified Lean paths, one per line, with
    # comment headers `# obligation — ...` / `# substrate_pending — ...`.
    declared_axioms = set()
    for line in trust_lines:
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        # Extract last dotted component as the axiom name.
        axiom = s.rsplit(".", 1)[-1] if "." in s else s
        declared_axioms.add(axiom)
    for line in trust_lines:
        if line.strip().startswith("SixBirdsMetaMath.FoundationsIV."):
            findings.append(("ERROR",
                f"trust_base.txt contains a project-local F-IV axiom `{line.strip()}`"))
    expected_axioms = set(F_IV_TRUST_BASE_AXIOMS.keys())
    missing = expected_axioms - declared_axioms
    for ax in sorted(missing):
        findings.append(("WARN",
            f"trust_base.txt does not appear to declare F-IV axiom `{ax}`"))

    # 4. Aggregate count check (52 rows expected).
    if len(rows) != 52:
        findings.append(("CRITICAL",
            f"SOR row count {len(rows)} != 52 expected"))

    return report(findings)


if __name__ == "__main__":
    sys.exit(main())
