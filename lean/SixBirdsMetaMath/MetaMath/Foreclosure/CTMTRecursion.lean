import SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy

namespace SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion

open SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy

/-!
T6 CTMT Recursion.

This module records the depth-indexed structure behind nested
matrix-element terminality.  The concrete operator-algebra reduction from
one carrier-native matrix family to a deeper one is kept abstract as a
semantics relation; the theorem proves the base-case identification and
the iterative tower step from the constructors.
-/

variable {language : ClaimLanguage.{u}}

/--
Abstract reduction relation: carrier `C` reduces the CTMT decision problem
for target `X` to a deeper carrier-native matrix-element family represented
by `Cdeeper`.
-/
def cascadeReducesToDeeperFamily
    (semantics : language.Claim → TypedPrimaryCarrier language → TypedPrimaryCarrier language → Prop)
    (X : language.Claim) (C Cdeeper : TypedPrimaryCarrier language) : Prop :=
  semantics X C Cdeeper

/--
Depth-indexed CTMT tower.

Depth `1` is exactly the ordinary T1 `creCTMT` state.  A step from a
deeper positive-depth tower records one further operator-algebra reduction
from the current carrier to the deeper carrier.
-/
inductive CTMTTower
    (semantics : language.Claim → TypedPrimaryCarrier language → TypedPrimaryCarrier language → Prop)
    (X : language.Claim) : TypedPrimaryCarrier language → Nat → Prop where
  | base {C : TypedPrimaryCarrier language} (h : creCTMT X C) :
      CTMTTower semantics X C 1
  | step {C Cdeeper : TypedPrimaryCarrier language} (n : Nat)
      (htower : CTMTTower semantics X Cdeeper (n + 1))
      (hreduces : cascadeReducesToDeeperFamily semantics X C Cdeeper) :
      CTMTTower semantics X C (n + 2)

/--
CTMT recursion: depth-1 towers are exactly plain CTMT, and any positive-depth
deeper tower can be lifted one level through a cascade reduction.
-/
theorem ctmt_recursion :
    (∀ (semantics : language.Claim → TypedPrimaryCarrier language → TypedPrimaryCarrier language → Prop)
        (X : language.Claim) (C : TypedPrimaryCarrier language),
        CTMTTower semantics X C 1 ↔ creCTMT X C) ∧
    (∀ (semantics : language.Claim → TypedPrimaryCarrier language → TypedPrimaryCarrier language → Prop)
        (X : language.Claim) (C Cdeeper : TypedPrimaryCarrier language) (n : Nat),
        CTMTTower semantics X Cdeeper (n + 1) →
          cascadeReducesToDeeperFamily semantics X C Cdeeper →
            CTMTTower semantics X C (n + 2)) := by
  constructor
  · intro semantics X C
    constructor
    · intro htower
      cases htower with
      | base h => exact h
    · intro hctmt
      exact CTMTTower.base hctmt
  · intro semantics X C Cdeeper n htower hreduces
    exact CTMTTower.step n htower hreduces

end SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion
