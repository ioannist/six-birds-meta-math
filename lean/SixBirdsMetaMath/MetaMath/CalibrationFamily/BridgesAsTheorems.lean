import SixBirdsMetaMath.MetaMath.CalibrationFamily.Structure

namespace SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgesAsTheorems

open SixBirdsMetaMath.MetaMath.CalibrationFamily.Structure

/-!
T13 Bridges-as-Theorems.

Calibration bridges are typed objects with content.  The observed PvNP
bridge graph (Component A, Component B, isolated `R_E`, and the failed
vobs / `I_alg` theorem gap) is evidence for this typing; the theorem below
records the core two-kind dichotomy.
-/

/-- A calibration bridge is either a free typed dictionary or typed theorem content. -/
inductive BridgeKind where
  | basisChange
  | substantive
  deriving DecidableEq, Repr

/-- A typed transport bridge between two calibrations. -/
structure TypedBridge where
  source : Calibration
  target : Calibration
  kind : BridgeKind
  deriving Repr

/-- Every typed bridge is either a basis-change dictionary or a substantive theorem. -/
theorem bridges_as_theorems (b : TypedBridge) :
    b.kind = BridgeKind.basisChange ∨ b.kind = BridgeKind.substantive := by
  cases b.kind with
  | basisChange => exact Or.inl rfl
  | substantive => exact Or.inr rfl

end SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgesAsTheorems
