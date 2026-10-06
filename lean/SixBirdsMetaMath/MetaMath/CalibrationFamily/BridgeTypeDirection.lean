import SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgesAsTheorems

namespace SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgeTypeDirection

open SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgesAsTheorems

/-!
T14 Bridge Type-Direction.

The source/target fields of a typed bridge encode direction.  Reversing a
bridge swaps these fields while preserving bridge kind; equality with the
reverse is therefore possible only when the source and target coincide.
-/

/-- The reverse-direction bridge swaps source and target with the same kind. -/
def TypedBridge.reverse (b : TypedBridge) : TypedBridge where
  source := b.target
  target := b.source
  kind := b.kind

/-- A typed bridge is symmetric under reversal exactly when its endpoints coincide. -/
theorem bridge_type_direction (b : TypedBridge) :
    b = TypedBridge.reverse b ↔ b.source = b.target := by
  constructor
  · intro h
    simpa [TypedBridge.reverse] using congrArg TypedBridge.source h
  · intro h
    cases b with
    | mk source target kind =>
        dsimp at h
        cases h
        rfl

end SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgeTypeDirection
