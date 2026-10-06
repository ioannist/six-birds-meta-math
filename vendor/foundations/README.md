# Vendored Foundations Lean assets

This directory makes the SAU formalization self-contained with respect to the
Six Birds Foundations repositories.

Only the assets needed by the current SAU Lean skeleton and validation scripts
are copied here:

- `six-birds-theory/formal`: Foundations I `ClosureLadder` Lean project,
  adapted locally to Lean `v4.28.0` and a self-contained closure interface.
- `six-birds-foundations-ii/lean`: Foundations II full Lean project, manifest,
  trust base, and paper sections required by its validator.
- `six-birds-foundations-iii/lean`: Foundations III full Lean project, manifest,
  paper inventory, trust base, and validator.

The SAU project imports Foundations I, II, and III from this local vendor tree.

Foundations I notice: this vendored copy is not a byte-identical mirror of the
original Foundations I Lean repo. Its mathlib-backed implementation has been
replaced by a local Lean `v4.28.0` `ClosureLadder` interface so this repository
can remain self-contained and use one Lean toolchain for SAU verification.

See `foundations-i-adaptation.md` for the reviewer-facing comparison notice and
`vendor_provenance.yml` for the checked machine-readable provenance record.

The default provenance check is offline:

```bash
python scripts/check_foundations_provenance.py --check
```

For maintainers with network access, the optional upstream-diff check compares
vendored tracks whose `upstream_diff_policy` is `full_tree` against the recorded
GitHub pin:

```bash
python scripts/check_foundations_provenance.py --check --verify-upstream
```

At present this full upstream diff applies to Foundations II. Foundations III is
recorded as a `local_prepublication_snapshot` because the public upstream
repository does not yet contain the Lean track vendored here; that policy should
be changed to `full_tree` once the Lean track is published upstream.
