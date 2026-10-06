# Formalization Boundary

This inventory defines the source contract for the needles Lean 4
mechanization. The authoritative target corpus is the set of theorem-like
environments in:

- `paper/main/formed_layer_membrane.tex` (Main axis: formed-layer
  membrane theory, including the absorbed duality-confinement framework
  from step 69)
- `paper/xi/xi_companion.tex` (Xi axis: adequacy residual calculus)

There are no external dependency papers in this repository. Foundations
I/II/III declarations are not source items; they are tracked separately
via `imported_foundations.yml` and the vendored trees under
`vendor/foundations/`.

## What "Same As The LaTeX Source" Means

Lean declarations cannot be textually identical to LaTeX theorem
statements. For this project, source equality means traceable semantic
correspondence:

- every Lean declaration must cite the LaTeX `\label`;
- every Lean declaration must carry the committed `statement_hash`;
- if the LaTeX statement changes, the hash changes and the Lean mapping
  is stale until reviewed;
- prose-only remarks are inventoried for context but do not create Lean
  theorem obligations unless manually promoted in
  `formalization_boundary.yml`.

## Boundary Categories

- `lean_definition`: definitions intended to become Lean structures,
  predicates, enums, notation, or named constants.
- `fully_formal_math`: mathematical facts intended to receive direct Lean
  proofs.
- `schema_theorem`: conditional framework results over formal records
  (typically theorems that consume the all-six channel records or audit
  packages).
- `sourced_assumption`: named domain facts or premises to isolate as
  assumptions before deeper formalization (used for obligations such as
  the RH-specific explicit-formula domination claim).
- `prose_only`: remarks, warnings, or nonclaims with no Lean theorem
  obligation.

## Intended Status (axis-level scope, orthogonal to category)

The per-axis inventory TOMLs (`main_paper_inventory.toml`,
`xi_paper_inventory.toml`) assign a second field `intended_status` that
governs whether the entry enters the mechanization queue:

- `mechanize_now`: full Lean realization required during this project.
- `obligation`: stated as a Lean `def` shape; no proof attempted.
- `out_of_scope_rh`: excluded by project scope (RH-specific).
- `out_of_scope_ns`: excluded by project scope (Navier-specific).
- `support_only`: diagnostic / counterexample, not a proof gate.
- `nonclaim`: explicitly negated in the paper.

`category` and `intended_status` are orthogonal axes: a `lean_definition`
can be `mechanize_now` or `out_of_scope_ns`; a `sourced_assumption` can
be `obligation` or `out_of_scope_rh`. The mechanization queue (Phase E)
filters on `intended_status == "mechanize_now"`.

## Validation Contract

Run:

```sh
python scripts/extract_latex_inventory.py --check
```

The check fails if a target theorem-like environment is unlabeled,
labels are duplicated, a boundary category is missing or invalid, the
boundary references a missing label, or a committed statement hash is
stale.
