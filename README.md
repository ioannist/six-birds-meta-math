# Six Birds Meta-Math

Companion repository for two papers:

> **Three Conditional Clay-Problem Closures: A Shared Gaussian Observation and a Common Vocabulary**
> Ioannis Tsiokos. Version 4, 1 October 2026 (Versions 1–3 were titled *One Meta-Theory, Three
> Clay-Problem Closures*).
> DOI (v4): [10.5281/zenodo.23086999](https://doi.org/10.5281/zenodo.23086999);
> v1 (17 June 2026): [10.5281/zenodo.20713144](https://doi.org/10.5281/zenodo.20713144)

> **Six Birds Foundations IV: A Catalog of Layer-Agnostic Structural Laws**
> Ioannis Tsiokos. Version 3, 1 October 2026.
> DOI (v3): [10.5281/zenodo.23087000](https://doi.org/10.5281/zenodo.23087000);
> v1 (17 June 2026): [10.5281/zenodo.20713187](https://doi.org/10.5281/zenodo.20713187)

Each paper's version-history appendix records the changes between versions.

## Layout

```
paper/meta_math/       LaTeX sources of the Clay-problem paper
paper/foundations_iv/  LaTeX sources of Foundations IV
paper/references.bib   shared bibliography
lean/                  Lean 4 formalization (SixBirdsMetaMath namespace), manifests and trust base
formalization/         paper inventories
review/                Lean audit outputs and mathematical reviews of the October 2026 versions
vendor/foundations/    vendored Six Birds Foundations I-III Lean material
scripts/               validators, inventory builders, paper sync and Zenodo citation tooling
```

## Build

Papers (requires `latexmk` and a TeX distribution):

```bash
make paper-build                  # both papers
make paper-build-meta_math        # paper/meta_math/build/main.pdf
make paper-build-foundations_iv   # paper/foundations_iv/build/main.pdf
```

Build output under `paper/*/build/` is not tracked; the released PDFs are on Zenodo.

Lean (toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.28.0`):

```bash
cd lean && lake build
```

See `lean/README.md` for the formalization layout and validators.

## License

The manuscripts are distributed under CC-BY 4.0, as stated on their first pages.
