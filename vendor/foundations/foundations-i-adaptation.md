# Foundations I Adaptation Notice

This repository vendors the Foundations I `ClosureLadder` Lean track so the needles
formalization is self-contained.  The local copy is intentionally adapted; it is
not a byte-identical mirror of the upstream Foundations I Lean project.

## What Changed

- The local toolchain is `leanprover/lean4:v4.28.0`, matching the needles,
  Foundations II, and Foundations III Lean tracks.
- The upstream mathlib dependency was removed.
- The mathlib-backed closure-operator infrastructure was replaced by local
  self-contained order/closure interfaces.
- The needles-facing declaration names used by the import map are preserved:
  `ClosureOp`, `ClosureLadder`, `ClosureLadder.IdempotentEndo`, and
  `ClosureLadder.MetaPackaging.pack`.

## How To Compare

Reviewers comparing this directory to the original Foundations I repository
should not expect identical Lean internals.  The intended invariant is stable
paper-facing meaning and stable needles dependency names, not byte-for-byte source
compatibility.

The local validation contract is:

```bash
cd vendor/foundations/six-birds-theory
bash scripts/check_lean.sh
```

The one-shot needles verifier runs this through the Foundations dependency audit.
