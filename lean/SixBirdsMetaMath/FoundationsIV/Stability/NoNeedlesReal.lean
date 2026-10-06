import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel

/-!
F6 No-Needles Stability for Mathlib matrices over an ordered field.

The order is the quadratic-form preorder, without symmetry requirements on
the budgets. The cross-block symmetry, supplied-inverse symmetry, and block
projection identity give the algebraic decomposition; congruence and addition
then transport the two source budgets to the endpoint budget.
-/

namespace SixBirdsMetaMath.FoundationsIV.Stability.NoNeedlesReal

open Matrix
open scoped Matrix

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Quadratic-form comparison, without assuming either matrix is symmetric. -/
def loewnerLE {n : ℕ} (A B : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ v : Fin n → 𝕜, 0 ≤ v ⬝ᵥ ((B - A) *ᵥ v)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The quadratic form of a rectangular congruence is the source form
evaluated on the transposed pullback vector. -/
theorem quadratic_congruence {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) 𝕜)
    (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin m → 𝕜) :
    v ⬝ᵥ ((M * A * Mᵀ) *ᵥ v) =
      (Mᵀ *ᵥ v) ⬝ᵥ (A *ᵥ (Mᵀ *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  rw [← mulVec_transpose]

omit [IsStrictOrderedRing 𝕜] in
/-- Quadratic-form comparison is preserved by any rectangular congruence. -/
theorem loewnerLE_congruence {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) 𝕜)
    (A B : Matrix (Fin n) (Fin n) 𝕜) (h : loewnerLE A B) :
    loewnerLE (M * A * Mᵀ) (M * B * Mᵀ) := by
  intro v
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, quadratic_congruence]
  exact h (Mᵀ *ᵥ v)

/-- Adding two quadratic-form comparisons preserves comparison. -/
theorem loewnerLE_add_mono {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) 𝕜)
    (hAB : loewnerLE A B) (hCD : loewnerLE C D) :
    loewnerLE (A + C) (B + D) := by
  intro v
  have h : B + D - (A + C) = (B - A) + (D - C) := by abel
  rw [h, add_mulVec, dotProduct_add]
  exact add_nonneg (hAB v) (hCD v)

/-- Transitivity of the quadratic-form preorder. -/
theorem loewnerLE_trans {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) 𝕜)
    (hAB : loewnerLE A B) (hBC : loewnerLE B C) :
    loewnerLE A C := by
  intro v
  have h : C - A = (B - A) + (C - B) := by abel
  rw [h, add_mulVec, dotProduct_add]
  exact add_nonneg (hAB v) (hBC v)

/-- The native explanation `Ê = K_DL K_LL†`. -/
def nativeExplanation {y z : ℕ}
    (KDL : Matrix (Fin z) (Fin y) 𝕜)
    (KLLdagger : Matrix (Fin y) (Fin y) 𝕜) :
    Matrix (Fin z) (Fin y) 𝕜 := KDL * KLLdagger

/-- The Schur residual `Ξ = K_DD - K_DL K_LL† K_LD`. -/
def blockResidual {y z : ℕ}
    (KLD : Matrix (Fin y) (Fin z) 𝕜)
    (KDL : Matrix (Fin z) (Fin y) 𝕜)
    (KDD : Matrix (Fin z) (Fin z) 𝕜)
    (KLLdagger : Matrix (Fin y) (Fin y) 𝕜) :
    Matrix (Fin z) (Fin z) 𝕜 := KDD - KDL * KLLdagger * KLD

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The displayed symmetry and projection hypotheses give the decomposition
`K_DD = Ê K_LL Êᵀ + Ξ`, without positivity assumptions on the blocks. -/
theorem block_schur_decomposition {y z : ℕ}
    (KLL : Matrix (Fin y) (Fin y) 𝕜)
    (KLD : Matrix (Fin y) (Fin z) 𝕜)
    (KDL : Matrix (Fin z) (Fin y) 𝕜)
    (KDD : Matrix (Fin z) (Fin z) 𝕜)
    (KLLdagger : Matrix (Fin y) (Fin y) 𝕜)
    (hKDL : KDL = KLDᵀ) (hdagger : KLLdagger = KLLdaggerᵀ)
    (hprojection : KLL * KLLdagger * KLD = KLD) :
    KDD = nativeExplanation KDL KLLdagger * KLL *
        (nativeExplanation KDL KLLdagger)ᵀ +
      blockResidual KLD KDL KDD KLLdagger := by
  have htranspose : KDLᵀ = KLD := by rw [hKDL, transpose_transpose]
  have hterm : nativeExplanation KDL KLLdagger * KLL *
      (nativeExplanation KDL KLLdagger)ᵀ = KDL * KLLdagger * KLD := by
    unfold nativeExplanation
    rw [transpose_mul, ← hdagger, htranspose]
    calc
      KDL * KLLdagger * KLL * (KLLdagger * KLD) =
          (KDL * KLLdagger) * ((KLL * KLLdagger) * KLD) := by
            simp only [Matrix.mul_assoc]
      _ = KDL * KLLdagger * KLD := by rw [hprojection]
  rw [hterm]
  unfold blockResidual
  abel

/-- F6 over any ordered field, with precisely the cross-block symmetry,
supplied-inverse symmetry, projection identity, and three budget hypotheses. -/
theorem no_needles_stability_ordered_field {y z d : ℕ}
    (KLL : Matrix (Fin y) (Fin y) 𝕜)
    (KLD : Matrix (Fin y) (Fin z) 𝕜)
    (KDL : Matrix (Fin z) (Fin y) 𝕜)
    (KDD : Matrix (Fin z) (Fin z) 𝕜)
    (KLLdagger : Matrix (Fin y) (Fin y) 𝕜)
    (ThetaY : Matrix (Fin y) (Fin y) 𝕜)
    (OmegaZ : Matrix (Fin z) (Fin z) 𝕜)
    (ThetaD : Matrix (Fin d) (Fin d) 𝕜)
    (S : Matrix (Fin d) (Fin z) 𝕜)
    (hKDL : KDL = KLDᵀ) (hdagger : KLLdagger = KLLdaggerᵀ)
    (hprojection : KLL * KLLdagger * KLD = KLD)
    (hnative : loewnerLE KLL ThetaY)
    (hresidual : loewnerLE (blockResidual KLD KDL KDD KLLdagger) OmegaZ)
    (htransport : loewnerLE
      (S * (nativeExplanation KDL KLLdagger * ThetaY *
        (nativeExplanation KDL KLLdagger)ᵀ + OmegaZ) * Sᵀ) ThetaD) :
    loewnerLE (S * KDD * Sᵀ) ThetaD := by
  have hdecomp := block_schur_decomposition KLL KLD KDL KDD KLLdagger
    hKDL hdagger hprojection
  have hbound : loewnerLE KDD
      (nativeExplanation KDL KLLdagger * ThetaY *
        (nativeExplanation KDL KLLdagger)ᵀ + OmegaZ) := by
    conv_lhs => rw [hdecomp]
    exact loewnerLE_add_mono _ _ _ _
      (loewnerLE_congruence (nativeExplanation KDL KLLdagger) KLL ThetaY hnative)
      hresidual
  exact loewnerLE_trans _ _ _ (loewnerLE_congruence S _ _ hbound) htransport

/-- F6 for real block matrices. No symmetry is assumed on any budget. -/
theorem no_needles_stability_real {y z d : ℕ}
    (KLL : Matrix (Fin y) (Fin y) ℝ)
    (KLD : Matrix (Fin y) (Fin z) ℝ)
    (KDL : Matrix (Fin z) (Fin y) ℝ)
    (KDD : Matrix (Fin z) (Fin z) ℝ)
    (KLLdagger : Matrix (Fin y) (Fin y) ℝ)
    (ThetaY : Matrix (Fin y) (Fin y) ℝ)
    (OmegaZ : Matrix (Fin z) (Fin z) ℝ)
    (ThetaD : Matrix (Fin d) (Fin d) ℝ)
    (S : Matrix (Fin d) (Fin z) ℝ)
    (hKDL : KDL = KLDᵀ) (hdagger : KLLdagger = KLLdaggerᵀ)
    (hprojection : KLL * KLLdagger * KLD = KLD)
    (hnative : loewnerLE KLL ThetaY)
    (hresidual : loewnerLE (blockResidual KLD KDL KDD KLLdagger) OmegaZ)
    (htransport : loewnerLE
      (S * (nativeExplanation KDL KLLdagger * ThetaY *
        (nativeExplanation KDL KLLdagger)ᵀ + OmegaZ) * Sᵀ) ThetaD) :
    loewnerLE (S * KDD * Sᵀ) ThetaD :=
  no_needles_stability_ordered_field KLL KLD KDL KDD KLLdagger
    ThetaY OmegaZ ThetaD S hKDL hdagger hprojection hnative hresidual htransport

end SixBirdsMetaMath.FoundationsIV.Stability.NoNeedlesReal
