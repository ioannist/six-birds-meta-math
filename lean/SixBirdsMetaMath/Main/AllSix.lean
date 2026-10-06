import SixBirdsMetaMath.Main.LegalQuotient

open SixBirdsMetaMath.Main.LegalQuotient

namespace SixBirdsMetaMath.Main.AllSix

/-!
Main paper §9 "All-six records, transfer, and taxonomy".

This module gives a finite-rank structural encoding of adequacy-aware
transfer records.  The paper theorem is qualitative; the Lean theorem
below records the required components and unfolds the exact/defective
bridge cases without deriving a new quantitative operator inequality.
-/

/--
A lawful membrane-transfer record.  It carries source and target audit,
native-probe, dissolving-probe, and adequacy-residual transport data in
the finite rational matrix model.
-/
structure LawfulMembraneTransfer
    (e e_t y y_t z z_t : Nat) where
  C : Mat e e
  L : Mat y e
  D : Mat z e
  KLLdagger : Mat y y
  ThetaY : Mat y y
  OmegaZ : Mat z z
  C_t : Mat e_t e_t
  L_t : Mat y_t e_t
  D_t : Mat z_t e_t
  KLLdagger_t : Mat y_t y_t
  ThetaY_t : Mat y_t y_t
  OmegaZ_t : Mat z_t z_t
  S_energy : Mat e_t e
  S_native : Mat y_t y
  S_dissolving : Mat z_t z
  S_residual : Mat z_t z

/-- Exact bridge: native and dissolving budgets transfer by congruence. -/
def IsExactBridge {e e_t y y_t z z_t : Nat}
    (T : LawfulMembraneTransfer e e_t y y_t z z_t) : Prop :=
  T.ThetaY_t = matMul (matMul T.S_native T.ThetaY) (transpose T.S_native) ∧
  T.OmegaZ_t = matMul (matMul T.S_dissolving T.OmegaZ) (transpose T.S_dissolving)

/-- Defective bridge: target budgets include declared PSD residual currencies. -/
def IsDefectiveBridge {e e_t y y_t z z_t : Nat}
    (T : LawfulMembraneTransfer e e_t y y_t z z_t)
    (E_native_defect : Mat y_t y_t) (E_residual_defect : Mat z_t z_t) : Prop :=
  PositiveSemidefinite E_native_defect ∧
  PositiveSemidefinite E_residual_defect ∧
  T.ThetaY_t =
    matAdd (matMul (matMul T.S_native T.ThetaY) (transpose T.S_native))
      E_native_defect ∧
  T.OmegaZ_t =
    matAdd (matMul (matMul T.S_dissolving T.OmegaZ) (transpose T.S_dissolving))
      E_residual_defect

/--
Adequacy-aware transfer, finite-rank structural form.  A lawful transfer
record carries the four transport maps by construction; exact and
defective bridge certificates unfold to the corresponding congruence or
paid-defect budget clauses.
-/
theorem adequacyAwareTransfer
    {e e_t y y_t z z_t : Nat}
    (T : LawfulMembraneTransfer e e_t y y_t z z_t) :
    (∃ Se : Mat e_t e, Se = T.S_energy) ∧
    (∃ Sn : Mat y_t y, Sn = T.S_native) ∧
    (∃ Sd : Mat z_t z, Sd = T.S_dissolving) ∧
    (∃ Sr : Mat z_t z, Sr = T.S_residual) ∧
    (IsExactBridge T →
      T.ThetaY_t = matMul (matMul T.S_native T.ThetaY) (transpose T.S_native) ∧
      T.OmegaZ_t =
        matMul (matMul T.S_dissolving T.OmegaZ) (transpose T.S_dissolving)) ∧
    (∀ E_native_defect E_residual_defect,
      IsDefectiveBridge T E_native_defect E_residual_defect →
        PositiveSemidefinite E_native_defect ∧
        PositiveSemidefinite E_residual_defect ∧
        T.ThetaY_t =
          matAdd (matMul (matMul T.S_native T.ThetaY) (transpose T.S_native))
            E_native_defect ∧
        T.OmegaZ_t =
          matAdd (matMul (matMul T.S_dissolving T.OmegaZ) (transpose T.S_dissolving))
            E_residual_defect) := by
  refine ⟨⟨T.S_energy, rfl⟩, ⟨T.S_native, rfl⟩, ⟨T.S_dissolving, rfl⟩,
    ⟨T.S_residual, rfl⟩, ?_, ?_⟩
  · intro hExact
    exact hExact
  · intro E_native_defect E_residual_defect hDefective
    exact hDefective

end SixBirdsMetaMath.Main.AllSix
