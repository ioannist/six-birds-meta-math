import ClosureLadder.Basic

/-!
# Local closure-operator order lemmas

The upstream Foundations I file used mathlib's `ClosureOperator`. In this
vendored SAU copy, the corresponding facts target the local `ClosureOp`.
-/

namespace ClosureOp

theorem le_def {α : Type u} {c d : ClosureOp α} :
    le c d ↔ ∀ x, IsClosed d x → IsClosed c x :=
  Iff.rfl

end ClosureOp
