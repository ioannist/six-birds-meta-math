import SixBirdsMetaMath.RHNavierPvNP.SATXiCurrency
import SixBirdsMetaMath.RHNavier.JointSixBirdsObservationReturn

/-!
The RH zero-window and SAT assignment XI analyses use the same
constant-vector finite Hilbert probe. Their native states have
different readouts: RH reflection cancels the signed displacement
sum, while SAT's nonnegative indicator sum counts witnesses.
-/

noncomputable section
open scoped InnerProductSpace
namespace SixBirdsMetaMath.RHNavierPvNP.ConstantProbeComparison

open SixBirdsMetaMath.RHNavierPvNP.SATXiCurrency
open SixBirdsDualityConfinement.RH.ClassicalZeroLedger
open SixBirdsDualityConfinement.RH.FiniteZeroWindows
open SixBirdsDualityConfinement.RH.ActualInvolution
open SixBirdsNeedles.XiCore

/-- The common finite constant-vector probe, independent of the
application's index type. -/
def finiteConstantProbe (I : Type*) [Fintype I] :
    EuclideanSpace ℝ I →L[ℝ] ℝ := by
  classical
  exact innerSL ℝ (WithLp.toLp 2 (fun _ : I => (1 : ℝ)))

theorem satMeanProbe_eq_common (n : Nat) :
    satMeanProbe n = finiteConstantProbe (SixBirdsHiddenness.PvNP.CNFSemantics.Assignment n) := by
  rfl

theorem rhInvariantProbe_eq_common (W : Finset NontrivialZero) :
    invariantProbe W = finiteConstantProbe {ρ // ρ ∈ W} := by
  rfl

/-- The shared probe has sharply different native effects on the
two concrete states. RH's reflection-symmetric signed displacement
is annihilated; SAT's nonnegative indicator has positive readout
precisely for the actual encoded SAT language. This exposes why the
two strong source conditions cannot simply be identified. -/
theorem rh_sat_constant_probe_readouts
    (m : NontrivialZero → ℕ)
    (hm : ∀ ρ, m (J_zero ρ) = m ρ)
    (W : Finset NontrivialZero) (hW : JReflectedWindow W)
    {n : Nat} (φ : SixBirdsHiddenness.PvNP.CNFSemantics.Formula n) :
    finiteConstantProbe {ρ // ρ ∈ W} (displacementVector m W) = 0 ∧
      (0 < finiteConstantProbe
          (SixBirdsHiddenness.PvNP.CNFSemantics.Assignment n)
          (satState φ) ↔
        (SixBirdsHiddenness.PvNP.StandardSATBridge.toExternalFormula φ).encode ∈
          SAT.L_SAT) := by
  constructor
  · rw [← rhInvariantProbe_eq_common]
    exact invariantProbe_displacement_zero_J m hm W hW
  · rw [← satMeanProbe_eq_common]
    exact satMeanProbe_pos_iff_encoded_L_SAT φ

/-- Reflection symmetry puts the actual RH displacement state
entirely in the hidden XI kernel of the constant-vector probe. The
SAT theorem `satState_not_fully_hidden_of_sat` proves the opposite
for every satisfiable indicator state. -/
theorem rh_reflected_state_fully_hidden
    (m : NontrivialZero → ℕ)
    (hm : ∀ ρ, m (J_zero ρ) = m ρ)
    (W : Finset NontrivialZero) (hW : JReflectedWindow W) :
    hilbertKernelXi (invariantProbe W) (displacementVector m W) =
      displacementVector m W := by
  apply (Submodule.starProjection_eq_self_iff).mpr
  exact invariantProbe_displacement_zero_J m hm W hW

end SixBirdsMetaMath.RHNavierPvNP.ConstantProbeComparison
