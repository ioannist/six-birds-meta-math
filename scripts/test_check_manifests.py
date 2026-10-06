#!/usr/bin/env python3
"""Regression tests for scripts/check_manifests.py.

These exercise the code paths that empty manifests don't cover. Run
once after any check_manifests.py edit:

    python3 scripts/test_check_manifests.py

Exits 0 on success, 1 on any assertion failure.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_manifests as cm  # noqa: E402


def test_split_axioms_payload_bracketed_csv() -> None:
    # Lean 4.28.0 format
    payload = " [propext, Classical.choice, Quot.sound]"
    assert cm._split_axioms_payload(payload) == [
        "propext",
        "Classical.choice",
        "Quot.sound",
    ], cm._split_axioms_payload(payload)


def test_split_axioms_payload_whitespace_only() -> None:
    # Older Lean format
    payload = " propext Classical.choice Quot.sound"
    assert cm._split_axioms_payload(payload) == [
        "propext",
        "Classical.choice",
        "Quot.sound",
    ]


def test_split_axioms_payload_empty() -> None:
    assert cm._split_axioms_payload("") == []
    assert cm._split_axioms_payload("[]") == []


def test_parse_print_axioms_lean428_format() -> None:
    sample = (
        "'foo_no_axioms' does not depend on any axioms\n"
        "'foo_with_classical' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
    )
    out = cm.parse_print_axioms_output(sample)
    assert out == {
        "foo_no_axioms": [],
        "foo_with_classical": ["propext", "Classical.choice", "Quot.sound"],
    }, out


def test_parse_print_axioms_continuation() -> None:
    # Synthetic case: long axiom list wrapped across lines
    sample = (
        "'foo' depends on axioms: [propext,\n"
        "  Classical.choice, Quot.sound,\n"
        "  funext]\n"
    )
    out = cm.parse_print_axioms_output(sample)
    assert out == {
        "foo": ["propext", "Classical.choice", "Quot.sound", "funext"],
    }, out


def test_parse_print_axioms_single_space_continuation() -> None:
    # Real Lean 4.28.0 output: multi-axiom lists wrap with SINGLE-space
    # indentation, not two-space. This regression test covers a bug
    # where parse_print_axioms_output truncated the axiom list at the
    # first continuation line.
    sample = (
        "'SixBirdsMetaMath.Main.LegalQuotient.probeFamilyCurrency' depends on axioms: [propext,\n"
        " Classical.choice,\n"
        " Lean.ofReduceBool,\n"
        " Lean.trustCompiler,\n"
        " Quot.sound]\n"
    )
    out = cm.parse_print_axioms_output(sample)
    assert out == {
        "SixBirdsMetaMath.Main.LegalQuotient.probeFamilyCurrency": [
            "propext",
            "Classical.choice",
            "Lean.ofReduceBool",
            "Lean.trustCompiler",
            "Quot.sound",
        ],
    }, out


def test_partial_entries_are_audited() -> None:
    """Per the post-§1 review: `partial` Lean declarations are still
    real Lean theorems and must respect the trust policy. Verify the
    lake-probe code path constructs a probe that includes `#print
    axioms` lines for partial entries, not just theorem entries.
    """
    # Inspect the `lake_probe` function's source to verify the audit
    # filter widens to `{"theorem", "partial"}`.
    import inspect
    source = inspect.getsource(cm.lake_probe)
    assert 'status") in {"theorem", "partial"}' in source, (
        "lake_probe should audit both theorem and partial entries"
    )


def test_parse_print_axioms_multiple_decls_single_space() -> None:
    # Two declarations, each with multi-line single-space continuation.
    sample = (
        "'foo' depends on axioms: [propext,\n"
        " Classical.choice]\n"
        "'bar' depends on axioms: [Quot.sound,\n"
        " funext]\n"
    )
    out = cm.parse_print_axioms_output(sample)
    assert out == {
        "foo": ["propext", "Classical.choice"],
        "bar": ["Quot.sound", "funext"],
    }, out


def test_trust_base_matches_lean_output() -> None:
    """End-to-end: real `Classical.em` use → axioms reported → diff against trust."""
    trust = cm.parse_trust_base()
    sample = (
        "'foo_with_classical' depends on axioms: [propext, Classical.choice, Quot.sound]"
    )
    parsed = cm.parse_print_axioms_output(sample)
    extras = sorted(set(parsed["foo_with_classical"]) - trust)
    assert extras == [], (
        f"trust base must accept Lean 4.28.0 Classical.em closure; got extras {extras}"
    )


def test_check_schema_missing_field() -> None:
    bad = [
        {
            "manifest_table": "definition",
            "paper_label": "def:main:foo",
            # missing paper_section, description, status, lean_*, notes
        }
    ]
    errors = cm.check_schema("main", bad)
    assert any("missing required fields" in e for e in errors), errors
    # Make sure the missing list mentions specifically the new requirements
    joined = " ".join(errors)
    for field in ("paper_section", "description", "notes", "status", "lean_module"):
        assert field in joined, f"missing field {field!r} should appear in error: {errors}"


def test_check_schema_wrong_subproject() -> None:
    bad = [
        {
            "manifest_table": "definition",
            "paper_label": "def:main:foo",
            "paper_section": "Section",
            "description": "desc",
            "status": "definition",
            "lean_subproject": "foo",  # wrong; needles requires "."
            "lean_module": "SixBirdsMetaMath.Main.LegalQuotient",
            "lean_decl": "SixBirdsMetaMath.Main.LegalQuotient.foo",
            "notes": "",
        }
    ]
    errors = cm.check_schema("main", bad)
    assert any("lean_subproject" in e for e in errors), errors


def test_check_schema_forbidden_status() -> None:
    bad = [
        {
            "manifest_table": "definition",
            "paper_label": "def:main:foo",
            "paper_section": "Section",
            "description": "desc",
            "status": "axiomatic",
            "lean_subproject": ".",
            "lean_module": "SixBirdsMetaMath.Main.LegalQuotient",
            "lean_decl": "SixBirdsMetaMath.Main.LegalQuotient.foo",
            "notes": "",
        }
    ]
    errors = cm.check_schema("main", bad)
    assert any("forbidden in needles" in e for e in errors), errors


def test_cross_reference_rejects_nonclaim_label() -> None:
    # Build a fake inventory entry with intended_status=nonclaim
    inventory = [
        {
            "manifest_table": "entry",
            "paper_label": "nonclaim:main:closure-only-scope",
            "kind": "nonclaim",
            "intended_status": "nonclaim",
            "section": "Landing",
            "required": "true",
        }
    ]
    manifest = [
        {
            "manifest_table": "definition",
            "paper_label": "nonclaim:main:closure-only-scope",
            "paper_section": "Landing",
            "description": "wrong",
            "status": "definition",
            "lean_subproject": ".",
            "lean_module": "SixBirdsMetaMath.Main.LegalQuotient",
            "lean_decl": "SixBirdsMetaMath.Main.LegalQuotient.foo",
            "notes": "",
        }
    ]
    errors = cm.cross_reference("main", manifest, inventory)
    assert any("intended_status" in e and "mechanize_now" in e for e in errors), errors


def test_cross_reference_rejects_out_of_scope_rh() -> None:
    inventory = [
        {
            "manifest_table": "entry",
            "paper_label": "obl:main:explicit-formula-domination",
            "kind": "obligation",
            "intended_status": "out_of_scope_rh",
            "section": "Root-composite RH obligation",
            "required": "true",
        }
    ]
    manifest = [
        {
            "manifest_table": "definition",
            "paper_label": "obl:main:explicit-formula-domination",
            "paper_section": "RH",
            "description": "wrong",
            "status": "definition",
            "lean_subproject": ".",
            "lean_module": "SixBirdsMetaMath.Main.LegalQuotient",
            "lean_decl": "SixBirdsMetaMath.Main.LegalQuotient.foo",
            "notes": "",
        }
    ]
    errors = cm.cross_reference("main", manifest, inventory)
    assert any("out_of_scope_rh" in e for e in errors), errors


def test_parse_section_module_map_real_file() -> None:
    """Smoke-test the parser against the committed section_module_map.toml."""
    mapping = cm.parse_section_module_map()
    assert set(mapping) == {"main", "xi"}, mapping
    # Spot-check a few well-known entries.
    assert mapping["main"]["Legal quotient and native currency"] == \
        "SixBirdsMetaMath.Main.LegalQuotient", mapping["main"]
    assert mapping["xi"]["Currency and minimum spend"] == \
        "SixBirdsMetaMath.Xi.Currency", mapping["xi"]


def test_section_module_map_check_passes_on_current_state() -> None:
    """Integration test: the current map covers every queued section and
    every mapped module exists in the Lean tree."""
    errors = cm.check_section_module_map()
    assert errors == [], errors


def test_cross_reference_accepts_mechanize_now() -> None:
    inventory = [
        {
            "manifest_table": "entry",
            "paper_label": "def:main:packaged-currency",
            "kind": "definition",
            "intended_status": "mechanize_now",
            "section": "Legal quotient and native currency",
            "required": "true",
        }
    ]
    manifest = [
        {
            "manifest_table": "definition",
            "paper_label": "def:main:packaged-currency",
            "paper_section": "Legal quotient",
            "description": "Packaged native currency",
            "status": "definition",
            "lean_subproject": ".",
            "lean_module": "SixBirdsMetaMath.Main.LegalQuotient",
            "lean_decl": "SixBirdsMetaMath.Main.LegalQuotient.packagedCurrency",
            "notes": "",
        }
    ]
    errors = cm.cross_reference("main", manifest, inventory)
    assert errors == [], errors


def main() -> int:
    tests = [
        (name, fn)
        for name, fn in sorted(globals().items())
        if name.startswith("test_") and callable(fn)
    ]
    failed = 0
    for name, fn in tests:
        try:
            fn()
        except AssertionError as exc:
            print(f"FAIL {name}: {exc}", file=sys.stderr)
            failed += 1
        else:
            print(f"PASS {name}")
    if failed:
        print(f"\n{failed} test(s) failed", file=sys.stderr)
        return 1
    print(f"\nAll {len(tests)} test(s) passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
