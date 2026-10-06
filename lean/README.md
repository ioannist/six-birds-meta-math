# Six Birds Meta-Math Lean Project

This directory holds the Lean 4 formalization support for the Six Birds
meta-math repository. The active public axes are tracked under
`SixBirdsMetaMath/MetaMath/` and `SixBirdsMetaMath/FoundationsIV/`.
Legacy support axes for Main, Xi, NS, and AOR remain available under
the same namespace because the validator and manifest checks still use
their inventories.

The alignment trio (`ImportedFoundations`, `FoundationsICompat`,
`Terminology`) sits at the top of the namespace and pulls in the
vendored Foundations I/II/III material.

## Toolchain

Pinned to `leanprover/lean4:v4.28.0` in `lean-toolchain`. Matches the
three vendored foundations under `../vendor/foundations/`. No version
drift across the project.

## No mathlib

The Lean project is deliberately mathlib-free, matching the foundations
stack. Finite-dimensional linear
algebra used by the membrane theory (matrices, Schur complements,
pseudoinverses, Loewner order, trace, anti-linear involutions) is
defined locally as mechanization proceeds. See
`../paper/notation_and_terminology.md` for the governance contract.

## Build

```bash
cd lean
lake build
```

This builds the umbrella `SixBirdsMetaMath`, which transitively builds
the alignment trio and all formalization support modules.

## Public Checks

From the repo root:

```bash
make paper-preflight
```

This builds and lints the active papers, validates the statements of
record, and runs the manifest checks. To build the Lean support modules
directly:

```bash
cd lean
lake build
```

## Lean Boundary Discipline

Executable Lean source should not use `sorry` or `admit`. Deliberate
paper-boundary obligations are disclosed through the statements of
record, inventories, manifests, and `manifests/trust_base.txt`.
`scripts/check_manifests.py --check` audits theorem axiom closures
against that trust base.

## Pointers

- Cross-walk to canonical Foundations names:
  `../formalization/inventory/imported_foundations.yml`
- Generated drift canary:
  `SixBirdsMetaMath/ImportedFoundations.lean`
  (regenerate with `scripts/generate_imported_foundations.py`)
- Notation/terminology governance: `../paper/notation_and_terminology.md`
- Public statement inventories: `../paper/*/paper_inventory.toml`
- Statements of record: `../paper/*/notes/statements-of-record.yml`
- Lean manifests: `manifests/*.toml`
