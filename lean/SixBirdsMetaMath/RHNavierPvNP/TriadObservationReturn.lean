import SixBirdsMetaMath.RHNavierPvNP.ConstantProbeComparison

/-!
A concrete RH–Navier–PvNP observation span. Both application readouts
use the same actual local nonlinear Navier frame and its Duhamel
correction; the RH and SAT Hilbert states use the same finite
constant-vector probe shape and maintained XI operator. Their native
states, source costs, and target returns remain distinct.
-/

noncomputable section
open scoped NNReal RealInnerProductSpace InnerProductSpace
namespace SixBirdsMetaMath.RHNavierPvNP.TriadObservationReturn

open SixBirdsNeedles.XiCore
open SixBirdsNeedles.NSCore
open SixBirdsNeedles.NSCore.ComplexGaussianObservations
open SixBirdsDualityConfinement.RH.ClassicalZeroLedger
open SixBirdsDualityConfinement.RH.FiniteZeroWindows
open SixBirdsDualityConfinement.RH.ActualInvolution
open SixBirdsMetaMath.RHNavier.JointSixBirdsObservationReturn
open SixBirdsMetaMath.RHNavier.ComplexGaussianNavierRHBridge
open SixBirdsMetaMath.RHNavierPvNP.FiniteSATGaussianObservation
open SixBirdsMetaMath.RHNavierPvNP.SATXiCurrency
open SixBirdsMetaMath.RHNavierPvNP.ConstantProbeComparison
open SixBirdsHiddenness.PvNP.CNFSemantics

/-- At one actual local nonlinear Navier frame, the RH zero-window
excess is its retained XI charge, and the SAT-filtered frame with its
Duhamel correction detects the combined SAT native/XI energy. The
finite constant probe is *definitionally the same construction* on
both index types, but RH reflection cancels it whereas SAT positivity
counts witnesses. Adding a concrete SAT clause also has an exact
failure-residual transport through this same nonlinear frame and its
Duhamel term. An actual unit-branch mask on the SAT state obeys the
maintained XI native/hidden commutator law. This theorem neither pays
RH/Navier/PvNP source premises nor bounds the exponential SAT readout
cost. -/
theorem concrete_triad_gaussian_xi_span
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a)
    (ρ : NontrivialZero)
    (W : Finset NontrivialZero) (hW : JReflectedWindow W)
    (hρ : ρ ∈ W)
    {n : Nat} (φ : Formula n) (clause : Clause n)
    (i : Fin n) (choice : Bool) :
    let t := τ.toNNReal + t₀
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    (nonlinearFrameWindowExcess γ hγ ν t₀ hν ht₀ τ a W =
      (a * b / (a + b)) *
        ‖hilbertKernelXi (invariantProbe W)
          (displacementVector unitWeights W)‖ ^ 2) ∧
    (finiteConstantProbe {ρ // ρ ∈ W}
      (displacementVector unitWeights W) = 0) ∧
    ((satFrameTrace φ binarySATCoordinate a
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      satFrameTrace φ binarySATCoordinate a
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) ≠ 0) ↔
      0 < (‖hilbertNativeCurrency (satMeanProbe n) (satState φ)‖ ^ 2 +
        ‖hilbertKernelXi (satMeanProbe n) (satState φ)‖ ^ 2)) ∧
    (0 < finiteConstantProbe (Assignment n) (satState φ) ↔
      (SixBirdsHiddenness.PvNP.StandardSATBridge.toExternalFormula φ).encode ∈
        SAT.L_SAT) ∧
    (satFrameTrace (φ ++ [clause]) binarySATCoordinate a
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      satFrameTrace (φ ++ [clause]) binarySATCoordinate a
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) =
      (satFrameTrace φ binarySATCoordinate a
          (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
        satFrameTrace φ binarySATCoordinate a
          (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ)) -
        (clauseFailureFrameTrace φ clause binarySATCoordinate a
          (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
        clauseFailureFrameTrace φ clause binarySATCoordinate a
          (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ))) ∧
    (satState (φ ++ [unitClause i choice]) =
      satUnitMask i choice (satState φ)) ∧
    (hilbertKernelXi (satMeanProbe n)
        (satUnitMask i choice (satState φ)) -
      satUnitMask i choice
        (hilbertKernelXi (satMeanProbe n) (satState φ)) =
      satUnitMask i choice
        (hilbertNativeCurrency (satMeanProbe n) (satState φ)) -
      hilbertNativeCurrency (satMeanProbe n)
        (satUnitMask i choice (satState φ))) := by
  dsimp only
  have hRH := nonlinear_frame_actual_zero_xi_return
    γ hγ ν t₀ hν ht₀ τ hτ hmem a ha ρ W hW hρ
  have hProbes := rh_sat_constant_probe_readouts
    unitWeights (fun _ => rfl) W hW φ
  exact ⟨hRH.2.1, hProbes.1,
    actual_navier_sat_xi_energy_return
      φ γ hγ ν t₀ hν ht₀ τ hτ hmem a ha,
    hProbes.2,
    actual_navier_clause_residual_return φ clause binarySATCoordinate
      γ hγ ν t₀ hν ht₀ τ a,
    satState_append_unit_eq_mask φ i choice,
    satUnitMask_xi_commutator φ i choice⟩

end SixBirdsMetaMath.RHNavierPvNP.TriadObservationReturn
