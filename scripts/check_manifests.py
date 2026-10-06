#!/usr/bin/env python3
"""Per-axis manifest validator for the SixBirdsMetaMath Lean project.

Reads each axis's manifest and paper inventory; cross-references them;
verifies the Lean module file exists for every manifest entry; and
(unless --skip-probe is set) probes every declaration with
`lake env lean` and checks the axiom closure of each theorem against
the trust base.

Empty manifests pass trivially. As entries are added, the validator
exercises more checks per entry.

Schema:
- Manifests live at lean/manifests/*_manifest.toml.
- Each entry is in a `[[definition]]` or `[[claim]]` array table.
- Trust base lives at lean/manifests/trust_base.txt (one axiom per
  line, comments allowed).
- Paper inventories live at
  formalization/inventory/{main,xi}_paper_inventory.toml in `[[entry]]`
  arrays.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import audit_foundations_dependencies as audit  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "lean"
LEAN_LIB_DIR = LEAN_DIR / "SixBirdsMetaMath"
MANIFESTS_DIR = LEAN_DIR / "manifests"
TRUST_BASE = MANIFESTS_DIR / "trust_base.txt"
SECTION_MODULE_MAP = MANIFESTS_DIR / "section_module_map.toml"
INVENTORY_DIR = ROOT / "formalization" / "inventory"

AXES = [
    ("main", "main_manifest.toml", "main_paper_inventory.toml"),
    ("xi", "xi_manifest.toml", "xi_paper_inventory.toml"),
    ("ns", "ns_manifest.toml", "ns_paper_inventory.toml"),
    ("aor", "aor_manifest.toml", "aor_paper_inventory.toml"),
]
PAPER_AXES = [axis for axis, _, _ in AXES]

ALLOWED_STATUSES = {"definition", "theorem", "axiomatic", "partial", "unformalized"}
# `axiomatic` is documented in legacy manifest headers for parity with F2/F3,
# but manifest rows should expose project-local obligations through the
# trust-base-audited `partial` / `obligation` path instead.
FORBIDDEN_STATUSES = {"axiomatic"}
DEFINITION_KINDS = {"definition"}
THEOREM_KINDS = {"theorem", "lemma", "proposition", "corollary"}
# Every manifest entry must carry all these fields (empty string allowed for
# free-form text fields; `lean_subproject` is constrained below).
REQUIRED_FIELDS = {
    "paper_label",
    "paper_section",
    "description",
    "status",
    "lean_subproject",
    "lean_module",
    "lean_decl",
    "notes",
}
# This repository is a single Lake project; lean_subproject must be ".". F2/F3
# use the same convention; we enforce it strictly so manifests cannot silently
# drift.
EXPECTED_LEAN_SUBPROJECT = "."

MANIFEST_TABLES = {"definition", "claim"}
INVENTORY_TABLES = {"entry"}


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def parse_section_module_map() -> dict[str, dict[str, str]]:
    """Parse the simple `[axis]` / `"section" = "module"` TOML format.

    Returns {axis: {section_title: module_path}}. Empty dict if the
    file is missing (the caller flags that as an error).
    """
    if not SECTION_MODULE_MAP.exists():
        return {}
    out: dict[str, dict[str, str]] = {}
    current: str | None = None
    table_re = re.compile(r"^\s*\[(?P<name>[A-Za-z0-9_]+)\]\s*$")
    kv_re = re.compile(r'^\s*"(?P<key>[^"]+)"\s*=\s*"(?P<value>[^"]+)"\s*$')
    for line in SECTION_MODULE_MAP.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        table_match = table_re.match(line)
        if table_match:
            current = table_match.group("name")
            out.setdefault(current, {})
            continue
        kv_match = kv_re.match(line)
        if kv_match and current is not None:
            out[current][kv_match.group("key")] = kv_match.group("value")
    return out


def check_section_module_map() -> list[str]:
    """Validate section_module_map.toml against the per-axis inventories.

    For every axis: every section that appears in the paper inventory's
    `mechanize_now` entries must have a map entry; every mapped module
    path must resolve to an existing `.lean` file. Sections that exist
    in the map but not in the inventory's mechanize_now set are
    allowed (stubs like StandingHypotheses).
    """
    errors: list[str] = []
    if not SECTION_MODULE_MAP.exists():
        return [f"missing {rel(SECTION_MODULE_MAP)}"]
    mapping = parse_section_module_map()
    for axis, _manifest_name, inventory_name in AXES:
        inventory_path = INVENTORY_DIR / inventory_name
        if not inventory_path.exists():
            errors.append(f"section_module_map check: missing {rel(inventory_path)}")
            continue
        ientries = inventory_entries(inventory_path)
        # Sections that the queue (mechanize_now items) actually visits.
        queue_sections = {
            str(e.get("section", ""))
            for e in ientries
            if e.get("intended_status") == "mechanize_now"
        }
        axis_map = mapping.get(axis, {})
        missing_in_map = sorted(queue_sections - set(axis_map))
        for section in missing_in_map:
            errors.append(
                f"section_module_map: axis {axis!r} is missing an entry for section "
                f"{section!r} (queued in {axis} paper inventory)"
            )
        # Module file existence for all mapped modules.
        for section, module in axis_map.items():
            module_path = lean_module_to_file(module)
            if module_path is None:
                errors.append(
                    f"section_module_map: axis {axis!r} section {section!r} maps to "
                    f"{module!r} which does not start with SixBirdsMetaMath"
                )
                continue
            if not module_path.exists():
                errors.append(
                    f"section_module_map: axis {axis!r} section {section!r} maps to "
                    f"module {module!r} whose file {rel(module_path)} does not exist"
                )
    # Reject axes in the map that aren't actual axes.
    for axis_in_map in sorted(set(mapping) - set(PAPER_AXES)):
        errors.append(
            f"section_module_map: unknown axis table [{axis_in_map}] (allowed: {PAPER_AXES})"
        )
    return errors


def parse_trust_base() -> set[str]:
    if not TRUST_BASE.exists():
        return set()
    out: set[str] = set()
    for line in TRUST_BASE.read_text(encoding="utf-8").splitlines():
        stripped = line.split("#", 1)[0].strip()
        if stripped:
            out.add(stripped)
    return out


def manifest_entries(path: Path) -> list[dict]:
    return [
        r
        for r in audit.parse_manifest(path)
        if r.get("manifest_table") in MANIFEST_TABLES
    ]


def inventory_entries(path: Path) -> list[dict]:
    return [
        r
        for r in audit.parse_manifest(path)
        if r.get("manifest_table") in INVENTORY_TABLES
    ]


def expected_status_for_kind(kind: str) -> str | None:
    if kind in DEFINITION_KINDS:
        return "definition"
    if kind in THEOREM_KINDS:
        return "theorem"
    return None


def lean_module_to_file(module: str) -> Path | None:
    if not module.startswith("SixBirdsMetaMath"):
        return None
    suffix = module.removeprefix("SixBirdsMetaMath").lstrip(".")
    if not suffix:
        return LEAN_DIR / "SixBirdsMetaMath.lean"
    return LEAN_LIB_DIR / Path(*suffix.split(".")).with_suffix(".lean")


def check_schema(axis: str, entries: list[dict]) -> list[str]:
    errors: list[str] = []
    for index, entry in enumerate(entries, start=1):
        label = entry.get("paper_label", f"<unlabeled entry #{index}>")
        missing = sorted(REQUIRED_FIELDS - set(entry))
        if missing:
            errors.append(
                f"{axis} manifest entry {label}: missing required fields: {', '.join(missing)}"
            )
            continue
        status = entry.get("status", "")
        if status not in ALLOWED_STATUSES:
            errors.append(
                f"{axis} manifest entry {label}: invalid status {status!r} "
                f"(allowed: {sorted(ALLOWED_STATUSES)})"
            )
        if status in FORBIDDEN_STATUSES:
            errors.append(
                f"{axis} manifest entry {label}: status {status!r} is forbidden; "
                "use the trust-base-audited obligation path for project-local assumptions"
            )
        subproject = str(entry.get("lean_subproject", ""))
        if subproject != EXPECTED_LEAN_SUBPROJECT:
            errors.append(
                f"{axis} manifest entry {label}: lean_subproject must be "
                f"{EXPECTED_LEAN_SUBPROJECT!r} (got {subproject!r}); "
                "this repository is a single Lake project"
            )
    return errors


def cross_reference(
    axis: str, mentries: list[dict], ientries: list[dict]
) -> list[str]:
    errors: list[str] = []
    inv_by_label = {str(e.get("paper_label", "")): e for e in ientries if e.get("paper_label")}
    seen_labels: set[str] = set()
    for entry in mentries:
        label = str(entry.get("paper_label", ""))
        if not label:
            continue
        if label in seen_labels:
            errors.append(f"{axis} manifest entry: duplicate paper_label {label}")
            continue
        seen_labels.add(label)
        inv = inv_by_label.get(label)
        if not inv:
            errors.append(
                f"{axis} manifest references paper_label {label!r} not in {axis} paper inventory"
            )
            continue
        # The manifest is only for mechanized items. Nonclaims, RH/NS
        # out-of-scope obligations, and support_only items must not
        # appear here.
        inv_intended_status = str(inv.get("intended_status", ""))
        if inv_intended_status != "mechanize_now":
            errors.append(
                f"{axis} manifest entry {label}: paper inventory intended_status is "
                f"{inv_intended_status!r}; only `mechanize_now` items belong in the manifest"
            )
            continue
        inv_kind = str(inv.get("kind", ""))
        manifest_status = str(entry.get("status", ""))
        expected = expected_status_for_kind(inv_kind)
        # Status fidelity only enforced when the manifest status is a
        # "real" status (definition/theorem). `partial`/`unformalized`
        # are allowed regardless of kind during Phase E in-progress.
        if expected and manifest_status in {"definition", "theorem"}:
            if manifest_status != expected:
                errors.append(
                    f"{axis} manifest entry {label}: status {manifest_status!r} "
                    f"does not match paper kind {inv_kind!r} (expected status {expected!r})"
                )
    return errors


def lean_module_check(axis: str, mentries: list[dict]) -> list[str]:
    errors: list[str] = []
    for entry in mentries:
        label = entry.get("paper_label", "<unlabeled>")
        module = str(entry.get("lean_module", ""))
        if not module:
            continue
        path = lean_module_to_file(module)
        if path is None:
            errors.append(
                f"{axis} manifest entry {label}: lean_module {module!r} must start with SixBirdsMetaMath"
            )
            continue
        if not path.exists():
            errors.append(
                f"{axis} manifest entry {label}: lean_module file {rel(path)} does not exist"
            )
    return errors


_AXIOM_TOKEN_STRIP = re.compile(r"[\[\],]")


def _split_axioms_payload(payload: str) -> list[str]:
    """Tokenize the axiom-list payload after `depends on axioms:`.

    Lean 4.28.0 emits a bracketed comma-separated list:
        depends on axioms: [propext, Classical.choice, Quot.sound]
    Older Lean versions emit a whitespace-separated list:
        depends on axioms: propext Classical.choice Quot.sound
    This tokenizer handles both: strip `[`/`]`/`,` then split on
    whitespace, dropping empty tokens.
    """
    cleaned = _AXIOM_TOKEN_STRIP.sub(" ", payload)
    return [tok for tok in cleaned.split() if tok]


def parse_print_axioms_output(text: str) -> dict[str, list[str]]:
    """Map each declaration name to its declared axioms.

    `#print axioms d` outputs one of:
      "'d' does not depend on any axioms"
      "'d' depends on axioms: [ax1, ax2, ...]"        (Lean 4.28.0+)
      "'d' depends on axioms: ax1 ax2 ..."             (older Lean)
    The axiom list may wrap across lines (indented continuations).
    """
    out: dict[str, list[str]] = {}
    pattern = re.compile(
        r"^'(?P<name>[^']+)' (?:does not depend on any axioms|depends on axioms:(?P<rest>.*))$"
    )
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        match = pattern.match(lines[i].strip())
        if not match:
            i += 1
            continue
        name = match.group("name")
        rest = match.group("rest")
        if rest is None:
            # "does not depend on any axioms" branch
            out[name] = []
            i += 1
            continue
        # Collect any indented continuation lines. Lean's `#print
        # axioms` formats multi-axiom outputs by line-wrapping with
        # single-space indentation (not two-space). Detect any line that
        # starts with a space and isn't itself the start of a new
        # `'name' depends on...` record.
        i += 1
        while i < len(lines):
            line = lines[i]
            if not line.startswith(" "):
                break
            if pattern.match(line.strip()):
                break
            rest += " " + line.strip()
            i += 1
        out[name] = _split_axioms_payload(rest)
    return out


def lake_probe(
    axis: str, mentries: list[dict], trust: set[str]
) -> list[str]:
    if not mentries:
        return []
    errors: list[str] = []
    lines = []
    modules = sorted({str(e["lean_module"]) for e in mentries if e.get("lean_module")})
    for module in modules:
        lines.append(f"import {module}")
    lines.append("")
    # Only probe entries with a non-empty lean_decl. Fresh
    # `unformalized` entries seed `lean_decl = ""`; skipping them here
    # keeps the probe quiet while still
    # auditing every real declaration.
    probed_entries = [e for e in mentries if str(e.get("lean_decl", "")).strip()]
    for entry in probed_entries:
        lines.append(f"#check @{entry['lean_decl']}")
    # Audit the axiom closure of every entry whose Lean declaration is
    # a propositional content carrier — both fully realized theorems
    # AND `partial` declarations (which are still real Lean theorems,
    # just narrower than the paper claim). `definition` entries do not
    # have an axiom closure to audit; `unformalized` has no Lean decl.
    audited_entries = [
        e for e in probed_entries if e.get("status") in {"theorem", "partial"}
    ]
    for entry in audited_entries:
        lines.append(f"#print axioms {entry['lean_decl']}")
    probe = "\n".join(lines) + "\n"

    with tempfile.NamedTemporaryFile("w", suffix=".lean", encoding="utf-8", delete=False) as handle:
        handle.write(probe)
        probe_path = Path(handle.name)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(probe_path)],
            cwd=LEAN_DIR,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    except FileNotFoundError:
        probe_path.unlink(missing_ok=True)
        return [f"{axis} lake probe: `lake` not found in PATH (use --skip-probe to bypass)"]
    finally:
        probe_path.unlink(missing_ok=True)

    if result.returncode != 0:
        errors.append(f"{axis} lake probe failed (manifest declarations did not type-check):")
        for line in result.stdout.splitlines()[:40]:
            errors.append(f"  {line}")
        return errors

    if audited_entries:
        axioms_by_decl = parse_print_axioms_output(result.stdout)
        for entry in audited_entries:
            decl = str(entry["lean_decl"])
            if decl not in axioms_by_decl:
                errors.append(
                    f"{axis} manifest entry {entry['paper_label']}: "
                    f"`#print axioms {decl}` output not found"
                )
                continue
            extras = sorted(set(axioms_by_decl[decl]) - trust)
            if extras:
                errors.append(
                    f"{axis} manifest entry {entry['paper_label']}: declaration {decl} "
                    f"depends on out-of-trust axioms: {', '.join(extras)}"
                )
    return errors


def run_axis(
    axis: str, manifest_name: str, inventory_name: str, *, skip_probe: bool, trust: set[str]
) -> tuple[int, list[str]]:
    """Returns (entry_count, errors) for one axis."""
    errors: list[str] = []
    manifest_path = MANIFESTS_DIR / manifest_name
    inventory_path = INVENTORY_DIR / inventory_name
    if not manifest_path.exists():
        errors.append(f"missing {rel(manifest_path)}")
        return 0, errors
    if not inventory_path.exists():
        errors.append(f"missing {rel(inventory_path)}")
        return 0, errors

    mentries = manifest_entries(manifest_path)
    ientries = inventory_entries(inventory_path)

    errors.extend(check_schema(axis, mentries))
    if errors:
        return len(mentries), errors

    errors.extend(cross_reference(axis, mentries, ientries))
    errors.extend(lean_module_check(axis, mentries))
    if errors:
        return len(mentries), errors

    if not skip_probe:
        errors.extend(lake_probe(axis, mentries, trust))

    return len(mentries), errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="accepted for consistency with other validators; same behavior as default",
    )
    parser.add_argument(
        "--skip-probe",
        action="store_true",
        help="skip `lake env lean` probes and axiom audits (use in CI without a Lean toolchain)",
    )
    args = parser.parse_args()

    if not TRUST_BASE.exists():
        print(f"ERROR: missing {rel(TRUST_BASE)}", file=sys.stderr)
        return 1
    trust = parse_trust_base()

    all_errors: list[str] = []
    counts: dict[str, int] = {}
    all_errors.extend(check_section_module_map())
    for axis, manifest_name, inventory_name in AXES:
        count, errors = run_axis(
            axis, manifest_name, inventory_name, skip_probe=args.skip_probe, trust=trust
        )
        counts[axis] = count
        all_errors.extend(errors)

    if all_errors:
        for error in all_errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    summary = ", ".join(f"{axis}={count} entries" for axis, count in counts.items())
    probe_note = " (probe skipped)" if args.skip_probe else ""
    print(
        f"manifest check passed: {summary}, trust_base={len(trust)} axioms, "
        f"section_module_map covers every queued section{probe_note}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
