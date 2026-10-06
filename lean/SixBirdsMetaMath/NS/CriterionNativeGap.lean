import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.NS.Carrier
import SixBirdsMetaMath.Xi.AdequacyResidual

open SixBirdsMetaMath.Main.LegalQuotient
open SixBirdsMetaMath.Xi.AdequacyResidual

namespace SixBirdsMetaMath.NS.CriterionNativeGap

/-!
NS paper §3 "Criterion-native equality and physical-native gap".

Two labeled environments split the original T3:
- `thm:ns:criterion-native-equality` — trivial algebraic equality
  `Ξ_C(D^{BG} ∣ L^{BG}) = 0` when `L^{BG} := D^{BG}`. Provable by
  direct substitution into the Schur-complement definition; the
  equality is uninformative and does not establish physical-native
  adequacy.
- `thm:ns:no-go-criterion-native` (= NG1 in `ns_no_go_theorem_ledger.csv`)
  — the criterion-native equality does **not** promote to a
  physical-native bound `Ξ_C(D^{BG} ∣ L^{phys}) ≼ Ω^{BG}`. A concrete
  two-coordinate rational counterexample has criterion residual zero
  and physical-native residual one.
-/

/--
Criterion-native equality.

When the criterion-native family is just the BG readout, `L^{BG} := D^{BG}`,
the residual is the Schur complement of `K_DD` against itself.  On the
legal quotient this is zero once the exposed Moore--Penrose support
identity `K_DD K_DD† K_DD = K_DD` is supplied.
-/
theorem criterionNativeEquality {e z : Nat}
    (C_J_t : Mat e e) (D_BG : Mat z e) (KDDdagger : Mat z z)
    (hSchur :
      matMul (matMul (blockCurrencyDD C_J_t D_BG) KDDdagger)
          (blockCurrencyDD C_J_t D_BG) =
        blockCurrencyDD C_J_t D_BG) :
    adequacyResidual C_J_t D_BG D_BG KDDdagger = zeroMat z z := by
  change
    matSub (blockCurrencyDD C_J_t D_BG)
        (matMul (matMul (blockCurrencyDD C_J_t D_BG) KDDdagger)
          (blockCurrencyDD C_J_t D_BG)) =
      zeroMat z z
  rw [hSchur]
  exact matSub_self_eq_zero (blockCurrencyDD C_J_t D_BG)

/--
No-go NG1: criterion-native circularity.

The criterion-native identity leaves the physical-native family
`L^{phys}` untouched.  The finite witness below has `C = I_2`,
`D^{BG} = [1,0]`, `L^{phys} = [0,1]`, and one-dimensional identity
pseudoinverses.  The criterion-native residual vanishes, but the
physical-native residual is the nonzero `1x1` matrix.
-/
theorem noGoCriterionNative :
    ∃ (e y z : Nat) (C : Mat e e) (D_BG : Mat z e) (Lphys : Mat y e)
      (KDDdagger : Mat z z) (KLLphysDag : Mat y y),
      adequacyResidual C D_BG D_BG KDDdagger = zeroMat z z ∧
        adequacyResidual C Lphys D_BG KLLphysDag ≠ zeroMat z z := by
  let D_BG : Mat 1 2 := fun _ j => if j.val = 0 then 1 else 0
  let Lphys : Mat 1 2 := fun _ j => if j.val = 0 then 0 else 1
  refine ⟨2, 1, 1, identityMat 2, D_BG, Lphys, identityMat 1, identityMat 1, ?_, ?_⟩
  · funext i j
    have hi : i = 0 := Subsingleton.elim i 0
    have hj : j = 0 := Subsingleton.elim j 0
    subst i
    subst j
    unfold adequacyResidual blockCurrencyDD blockCurrencyDL blockCurrencyLD
      identityMat diagonalPseudoInverse transpose matMul matSub zeroMat
    dsimp [D_BG]
    simp [sumFin, Rat.inv_def]
    rw [show Rat.divInt 1 1 = (1 : Rat) by rfl]
    grind
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    unfold adequacyResidual blockCurrencyDD blockCurrencyDL blockCurrencyLD
      identityMat diagonalPseudoInverse transpose matMul matSub zeroMat at h00
    dsimp [D_BG, Lphys] at h00
    simp [sumFin, Rat.inv_def] at h00
    rw [show Rat.divInt 1 1 = (1 : Rat) by rfl] at h00
    grind

end SixBirdsMetaMath.NS.CriterionNativeGap
