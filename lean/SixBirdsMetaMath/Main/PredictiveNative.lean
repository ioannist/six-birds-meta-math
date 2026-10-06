import SixBirdsMetaMath.Main.LegalQuotient

open SixBirdsMetaMath.Main.LegalQuotient

namespace SixBirdsMetaMath.Main.PredictiveNative

/-!
Main paper §5 "Predictive native membranes".

The first theorem is the exact Loewner/no-witness duality for accepted
predictive stages.  The second theorem records the finite propagation
scheme using the public Loewner arithmetic library; the infinite
product/sum machinery is deferred in the manifest.
-/

/-- Predictive currency `K̂ = R · K_{C,Γ}(L) · R^T`. -/
def predictiveCurrency {e a y : Nat}
    (R : Mat y y) (C : Mat e e) (Gamma : Mat e a) (L : Mat y e) : Mat y y :=
  matMul (matMul R (packagedCurrency C Gamma L)) (transpose R)

/-- A native predictive membrane with budget `Theta` across accepted stages. -/
def nativePredictiveMembrane {y : Nat}
    (Khat : Nat → Mat y y) (Theta : Mat y y) (accepted : Nat → Prop) : Prop :=
  ∀ j, accepted j → loewnerLE (Khat j) Theta

/-- No accepted stage contains a native recombination critical-pair witness. -/
def noPredictiveCriticalPair {y : Nat}
    (Khat : Nat → Mat y y) (Theta : Mat y y) (accepted : Nat → Prop) : Prop :=
  ¬ ∃ j, ∃ nativeRecombination,
    accepted j ∧ 0 < quad (matSub (Khat j) Theta) nativeRecombination

/--
Predictive native membrane: the accepted-stage Loewner budget is
equivalent to absence of an accepted native recombination witness.
-/
theorem predictiveNativeMembrane {y : Nat}
    (Khat : Nat → Mat y y) (Theta : Mat y y) (accepted : Nat → Prop) :
    nativePredictiveMembrane Khat Theta accepted ↔
      noPredictiveCriticalPair Khat Theta accepted := by
  unfold nativePredictiveMembrane noPredictiveCriticalPair loewnerLE
  constructor
  · intro hMembrane hWitness
    cases hWitness with
    | intro j hStage =>
        cases hStage with
        | intro nativeRecombination hWitnessAtStage =>
            exact hMembrane j hWitnessAtStage.left nativeRecombination hWitnessAtStage.right
  · intro hNoWitness j hAccepted nativeRecombination hPositive
    exact hNoWitness ⟨j, nativeRecombination, hAccepted, hPositive⟩

/-- Finite product `∏_{j < k} (1 + eps j)`, folded from the right. -/
def productOneEps (eps : Nat → Rat) : Nat → Rat
  | 0 => 1
  | k + 1 => (1 + eps k) * productOneEps eps k

/-- Finite matrix sum `Σ_{j < k} D_j`, folded from the right. -/
def sumD {m : Nat} (D : Nat → Mat m m) : Nat → Mat m m
  | 0 => zeroMat m m
  | k + 1 => matAdd (D k) (sumD D k)

/-- The finite product/sum envelope used in the propagation induction. -/
def predictiveEnvelope {y : Nat}
    (Khat : Nat → Mat y y) (eps : Nat → Rat) (D : Nat → Mat y y) (k : Nat) :
    Mat y y :=
  matScale (productOneEps eps k) (matAdd (Khat 0) (sumD D k))

/--
Summable predictive propagation, finite conditional form.  The proof
iterates the per-stage bound through the public Loewner-arithmetic
library, then applies the supplied finite product/sum envelope bound.
-/
theorem summablePredictivePropagation {y : Nat}
    (Khat : Nat → Mat y y) (eps : Nat → Rat) (D : Nat → Mat y y)
    (Pinfty : Rat) (Dinfty : Mat y y) (n : Nat)
    (hStep : ∀ j, j < n →
      loewnerLE (Khat (j + 1))
        (matAdd (matScale (1 + eps j) (Khat j)) (D j)))
    (hFactorNonneg : ∀ j, j < n → 0 ≤ 1 + eps j)
    (hEnvelopeStep : ∀ j, j < n →
      loewnerLE
        (matAdd (matScale (1 + eps j) (predictiveEnvelope Khat eps D j)) (D j))
        (predictiveEnvelope Khat eps D (j + 1)))
    (hPbound : ∀ k, k ≤ n →
      loewnerLE (predictiveEnvelope Khat eps D k)
        (matScale Pinfty (matAdd (Khat 0) Dinfty))) :
    loewnerLE (Khat n) (matScale Pinfty (matAdd (Khat 0) Dinfty)) := by
  have hIter : ∀ k, k ≤ n → loewnerLE (Khat k) (predictiveEnvelope Khat eps D k) := by
    intro k
    induction k with
    | zero =>
        intro _hZero
        unfold predictiveEnvelope productOneEps sumD
        rw [matAdd_zero_right, matScale_one]
        exact loewnerLE_refl (Khat 0)
    | succ k ih =>
        intro hkSucc
        have hkLt : k < n := Nat.lt_of_succ_le hkSucc
        have hkLe : k ≤ n := Nat.le_trans (Nat.le_succ k) hkSucc
        have hCurrent : loewnerLE (Khat k) (predictiveEnvelope Khat eps D k) := ih hkLe
        have hScaled :
            loewnerLE (matScale (1 + eps k) (Khat k))
              (matScale (1 + eps k) (predictiveEnvelope Khat eps D k)) :=
          loewnerLE_scale_nonneg (1 + eps k) (Khat k) (predictiveEnvelope Khat eps D k)
            (hFactorNonneg k hkLt) hCurrent
        have hDefect : loewnerLE (D k) (D k) := loewnerLE_refl (D k)
        have hWithDefect :
            loewnerLE
              (matAdd (matScale (1 + eps k) (Khat k)) (D k))
              (matAdd (matScale (1 + eps k) (predictiveEnvelope Khat eps D k)) (D k)) :=
          loewnerLE_add_mono (matScale (1 + eps k) (Khat k))
            (matScale (1 + eps k) (predictiveEnvelope Khat eps D k))
            (D k) (D k) hScaled hDefect
        have hStageToEnvelope :
            loewnerLE (Khat (k + 1)) (predictiveEnvelope Khat eps D (k + 1)) :=
          loewnerLE_trans (Khat (k + 1))
            (matAdd (matScale (1 + eps k) (Khat k)) (D k))
            (predictiveEnvelope Khat eps D (k + 1))
            (hStep k hkLt)
            (loewnerLE_trans
              (matAdd (matScale (1 + eps k) (Khat k)) (D k))
              (matAdd (matScale (1 + eps k) (predictiveEnvelope Khat eps D k)) (D k))
              (predictiveEnvelope Khat eps D (k + 1))
              hWithDefect
              (hEnvelopeStep k hkLt))
        exact hStageToEnvelope
  exact loewnerLE_trans (Khat n) (predictiveEnvelope Khat eps D n)
    (matScale Pinfty (matAdd (Khat 0) Dinfty))
    (hIter n (Nat.le_refl n))
    (hPbound n (Nat.le_refl n))

end SixBirdsMetaMath.Main.PredictiveNative
