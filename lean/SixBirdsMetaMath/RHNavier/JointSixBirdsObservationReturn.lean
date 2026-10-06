import SixBirdsMetaMath.RHNavier.ComplexGaussianNavierRHBridge
import SixBirdsNeedles.NSCore.ClosurePhysicalReturn
import SixBirdsNeedles.NSCore.PhysicalClassicalReturn

/-!
The joint theorem uses the *same* complex directional Gaussian family on
actual completed-zeta zeros and on an actual local maximal Navier mild path.
Its two exact returns retain their different information: the RH field
reads a zero-window XI charge; the Navier field retains the projected
Duhamel source. No closure payment is asserted by this theorem.

The two conditional endpoints below deliberately expose different
premises. The RH zero-excess premise is exactly RH-strength; the Navier
two-channel residual closure is a separate dynamical assumption.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory Laplacian
open scoped NNReal InnerProduct InnerProductSpace
namespace SixBirdsMetaMath.RHNavier.JointSixBirdsObservationReturn

open SixBirdsMetaMath.RHNavier.ComplexGaussianNavierRHBridge
open SixBirdsNeedles.NSCore.ComplexGaussianObservations
open SixBirdsNeedles.NSCore
open SixBirdsDualityConfinement.RH.ClassicalZeroLedger
open SixBirdsDualityConfinement.RH.ArithmeticJensenWindows
open SixBirdsDualityConfinement.RH.ActualInvolution
open SixBirdsDualityConfinement.RH.FiniteZeroWindows
open SixBirdsDualityConfinement.RH.ComplexGaussianObservation

/-- One checked Gaussian observation and source-return theorem on both
actual carriers at the same positive Navier observation time. The second
field is an exact equation, not an estimate on the Duhamel source. -/
theorem joint_actual_zero_xi_and_navier_source_return
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν : ℝ≥0) (hν : 0 < ν) (g₀ : FourierEnergy)
    (t : ℝ) (ht : t ∈ admissibleMildTimes γ hγ ν hν g₀)
    (htpos : 0 < t)
    (a : ℝ) (ha : 0 < a)
    (ρ : NontrivialZero)
    (m : NontrivialZero → ℕ) (hm : ∀ ρ, m (J_zero ρ) = m ρ)
    (W : Finset NontrivialZero) (hW : JReflectedWindow W)
    (hρ : ρ ∈ W) :
    (navierHeatWindowExcess a ν t.toNNReal m W =
      (a * (4 * Real.pi ^ 2 * (ν : ℝ) * (t.toNNReal : ℝ)) /
        (a + 4 * Real.pi ^ 2 * (ν : ℝ) * (t.toNNReal : ℝ))) *
        ‖SixBirdsNeedles.XiCore.hilbertKernelXi
          (invariantProbe W) (displacementVector m W)‖ ^ 2) ∧
    (navierComplexWindowReadout a ν t.toNNReal
        (spectralCoordinate ρ.val) =
      (((Real.pi : ℂ) /
        ((a + 4 * Real.pi ^ 2 * (ν : ℝ) * (t.toNNReal : ℝ) : ℝ) : ℂ)) ^
          ((Module.finrank ℝ Space3 : ℂ) / 2)) *
        spectralGaussian
          (a * (4 * Real.pi ^ 2 * (ν : ℝ) * (t.toNNReal : ℝ)) /
            (a + 4 * Real.pi ^ 2 * (ν : ℝ) * (t.toNNReal : ℝ))) ρ.val) ∧
    (complexDirectionalStateReadout a thetaAxis (spectralCoordinate ρ.val)
        (maximalMildValue γ hγ ν hν g₀ t) +
      complexDirectionalStateReadout a thetaAxis (spectralCoordinate ρ.val)
        (nonlinearHeatDuhamel γ hγ ν hν
          (maximalMildValue γ hγ ν hν g₀) t) =
      complexDirectionalStateReadout a thetaAxis (spectralCoordinate ρ.val)
        (heatEnergy ν t.toNNReal g₀)) ∧
    ((m ρ : ℝ) * displacement ρ ^ 2 ≤
      ‖SixBirdsNeedles.XiCore.hilbertKernelXi
        (invariantProbe W) (displacementVector m W)‖ ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact navierHeatWindowExcess_eq_rh_xi a ν t.toNNReal ha hν
      (Real.toNNReal_pos.mpr htpos) m hm W hW
  · exact actual_zero_gaussian_eq_navier_heat_readout
      a ν t.toNNReal ha hν (Real.toNNReal_pos.mpr htpos) ρ
  · exact maximalMildValue_complex_directional_return
      γ hγ ν hν g₀ t ht a ha thetaAxis (spectralCoordinate ρ.val)
  · have hw : windowGaussianLogExcess 1 m W = windowEnergy m W := by
      simpa using windowGaussianLogExcess_eq_windowEnergy 1 m W
    have hx : windowGaussianLogExcess 1 m W =
        ‖SixBirdsNeedles.XiCore.hilbertKernelXi
          (invariantProbe W) (displacementVector m W)‖ ^ 2 := by
      simpa using windowGaussianLogExcess_eq_xi 1 m hm W hW
    calc
      (m ρ : ℝ) * displacement ρ ^ 2 ≤ windowEnergy m W :=
        term_le_window m W ρ hρ
      _ = windowGaussianLogExcess 1 m W := hw.symm
      _ = _ := hx

/-- The genuinely nonlinear theta-frame return and the RH XI window
identity in one theorem. The three Navier paths and their Duhamel terms
are actual local mild solutions; the zero window contains actual
completed-zeta zeros. The equality itself supplies neither closure. -/
theorem nonlinear_frame_actual_zero_xi_return
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a)
    (ρ : NontrivialZero)
    (W : Finset NontrivialZero) (hW : JReflectedWindow W)
    (hρ : ρ ∈ W) :
    let t := τ.toNNReal + t₀
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    (complexFrameTrace a (spectralCoordinate ρ.val)
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      complexFrameTrace a (spectralCoordinate ρ.val)
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) =
      ((((Real.pi : ℂ) / ((a + b : ℝ) : ℂ)) ^
        ((Module.finrank ℝ Space3 : ℂ) / 2)) *
        spectralGaussian (a * b / (a + b)) ρ.val) • (2 : ℂ)) ∧
    (nonlinearFrameWindowExcess γ hγ ν t₀ hν ht₀ τ a W =
      (a * b / (a + b)) *
        ‖SixBirdsNeedles.XiCore.hilbertKernelXi
          (invariantProbe W) (displacementVector unitWeights W)‖ ^ 2) ∧
    (displacement ρ ^ 2 ≤
      ‖SixBirdsNeedles.XiCore.hilbertKernelXi
        (invariantProbe W) (displacementVector unitWeights W)‖ ^ 2) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact complex_nonlinear_frame_return_at_actual_zero
      γ hγ ν t₀ hν ht₀ τ hτ hmem a ha ρ
  · rw [nonlinearFrameWindowExcess_eq_navierHeatWindowExcess
      γ hγ ν t₀ hν ht₀ τ hτ hmem a ha W]
    exact navierHeatWindowExcess_eq_rh_xi
      a ν (τ.toNNReal + t₀) ha hν (by positivity)
      unitWeights (fun _ => rfl) W hW
  · have hw : windowGaussianLogExcess 1 unitWeights W =
        windowEnergy unitWeights W := by
      simpa using windowGaussianLogExcess_eq_windowEnergy 1 unitWeights W
    have hx : windowGaussianLogExcess 1 unitWeights W =
        ‖SixBirdsNeedles.XiCore.hilbertKernelXi
          (invariantProbe W) (displacementVector unitWeights W)‖ ^ 2 := by
      simpa using windowGaussianLogExcess_eq_xi 1 unitWeights
        (fun _ => rfl) W hW
    have hle := term_le_window unitWeights W ρ hρ
    simp only [unitWeights, Nat.cast_one, one_mul] at hle
    calc
      displacement ρ ^ 2 ≤ windowEnergy unitWeights W := hle
      _ = windowGaussianLogExcess 1 unitWeights W := hw.symm
      _ = _ := hx

/-- The same observation also applies *after* the actual Navier
high-frequency Hilbert XI projection. The projected Duhamel term stays in
the equation, so this does not bound that residual. -/
theorem actual_navier_xi_source_step_at_zero_coordinate
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν : ℝ≥0) (hν : 0 < ν) (g₀ : FourierEnergy)
    (N : ℕ) (t : ℝ)
    (ht : t ∈ admissibleMildTimes γ hγ ν hν g₀)
    (htpos : 0 < t)
    (a : ℝ) (ha : 0 < a) (ρ : NontrivialZero) :
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t.toNNReal : ℝ)
    let X := SixBirdsNeedles.XiCore.hilbertKernelXi (kineticCutoff N)
    complexDirectionalStateReadout a thetaAxis (spectralCoordinate ρ.val)
        (X (maximalMildValue γ hγ ν hν g₀ t)) +
      complexDirectionalStateReadout a thetaAxis (spectralCoordinate ρ.val)
        (X (nonlinearHeatDuhamel γ hγ ν hν
          (maximalMildValue γ hγ ν hν g₀) t)) =
      Complex.exp (-(↑(a * b / (a + b)) : ℂ) *
        (spectralCoordinate ρ.val) ^ 2 * (‖thetaAxis‖ ^ 2 : ℂ)) •
        complexDirectionalStateReadout (a + b) thetaAxis
          ((↑(a / (a + b)) : ℂ) * spectralCoordinate ρ.val) (X g₀) :=
  maximalMildValue_complex_directional_xi_source_step
    γ hγ ν hν g₀ N t ht htpos a ha thetaAxis
      (spectralCoordinate ρ.val)

/-- Explicit RH-side observation premise. This is an equivalence
calibration, not an independently proved prime-side source law. -/
def ArithmeticZeroWindowClosure (a : ℝ) (ν t : ℝ≥0) : Prop :=
  ∀ n : ℕ, navierHeatWindowExcess a ν t unitWeights
    (canonicalJensenWindow n) = 0

theorem arithmetic_zero_window_closure_iff_rh
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t) :
    ArithmeticZeroWindowClosure a ν t ↔ RiemannHypothesis :=
  canonical_navierHeatWindowExcess_zero_iff_riemannHypothesis
    a ν t ha hν ht

/-- Conditional full classical RH. The antecedent is disclosed by the
equivalence above to have exactly RH strength; no prime-side proof of it
is part of this joint observation theorem. -/
theorem riemannHypothesis_of_arithmetic_zero_window_closure
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t)
    (hc : ArithmeticZeroWindowClosure a ν t) :
    RiemannHypothesis :=
  (arithmetic_zero_window_closure_iff_rh a ν t ha hν ht).mp hc

/-- The Navier premise remains the actual, separate two-channel residual
condition. It returns a global mild solution with its Duhamel PDE equation. -/
theorem navier_global_mild_of_two_channel_closure
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν : ℝ≥0) (hν : 0 < ν) (g₀ : FourierEnergy)
    (ha₀ : AdmissibleEnergy γ (by linarith) g₀)
    (hc : TwoChannelResidualClosure γ hγ ν hν g₀) :
    ∃ u : ℝ → FourierEnergy, ContinuousOn u (Ici 0) ∧ u 0 = g₀ ∧
      (∀ t ≥ 0, AdmissibleEnergy γ (by linarith) (u t)) ∧
      (∀ t ≥ 0,
        u t = heatEnergy ν t.toNNReal g₀ - nonlinearHeatDuhamel γ hγ ν hν u t) :=
  exists_global_admissible_mild_of_twoChannel_closure
    γ hγ ν hν g₀ ha₀ hc

/-- The same Navier closure also returns the global lifespan and the
pressure-restored physical PDE, almost everywhere in space at every
positive time. This is the PDE endpoint, not merely an abstract lifespan
predicate. -/
theorem navier_global_physical_pde_of_two_channel_closure
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν : ℝ≥0) (hν : 0 < ν) (g₀ : FourierEnergy)
    (ha₀ : AdmissibleEnergy γ (by linarith) g₀)
    (hc : TwoChannelResidualClosure γ hγ ν hν g₀) :
    admissibleMildTimes γ hγ ν hν g₀ = Ici 0 ∧
      (∀ t : ℝ, 0 < t →
        ((deriv (fun s => realInverseFourierEnergy
          (kineticSynthesis γ (by linarith)
            (maximalMildValue γ hγ ν hν g₀ s))) t : PhysicalVelocityL2) :
          Space3 → Space3) =ᵐ[volume]
          (fun x => realInverseFourierEnergy
              (kineticDiffusion γ (by linarith) ν
                (maximalMildValue γ hγ ν hν g₀ t)) x -
            spatialConvection
              (realSobolevField γ (by linarith)
                (maximalMildValue γ hγ ν hν g₀ t))
              (realSobolevField γ (by linarith)
                (maximalMildValue γ hγ ν hν g₀ t)) x -
            realScalarGradient
              (sobolevPressure γ hγ
                (maximalMildValue γ hγ ν hν g₀ t)
                (maximalMildValue γ hγ ν hν g₀ t)) x)) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x : Space3,
        realSpatialDivergence
          (realSobolevField γ (by linarith)
            (maximalMildValue γ hγ ν hν g₀ t)) x = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact maximalMildValue_global_of_twoChannel_closure
      γ hγ ν hν g₀ ha₀ hc
  · intro t ht
    exact closure_global_physical_pressure_ae
      γ hγ ν hν g₀ ha₀ hc ht
  · intro t ht x
    exact closure_global_real_divergence
      γ hγ ν hν g₀ ha₀ hc ht x

/-- The principal spectral Navier closure reaches the pointwise physical PDE
for real divergence-free initial data. The RH arithmetic premise above is
separate and supplies no part of this dynamical closure. -/
theorem navier_pointwise_physical_pde_of_hilbert_xi_closure
    (γ : ℝ) (hγ : 5 / 2 < γ) (ν : ℝ≥0) (hν : 0 < ν)
    (u₀ : PhysicalVelocityL2)
    (hf : MemLp (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (γ / 2) •
      fourierOfRealVelocity u₀ ξ) 2 volume)
    (v : Space3 → Space3) (hv : Differentiable ℝ v)
    (hv₀ : v =ᵐ[volume] (u₀ : Space3 → Space3))
    (hdiv : ∀ x : Space3, realSpatialDivergence v x = 0)
    (hc : HilbertXiStrongClosure γ hγ ν hν
      (energyOfWeightedAmplitude γ (fourierOfRealVelocity u₀ : Space3 → Velocity3) hf)) :
    let g₀ := energyOfWeightedAmplitude γ
      (fourierOfRealVelocity u₀ : Space3 → Velocity3) hf
    admissibleMildTimes γ hγ ν hν g₀ = Ici 0 ∧
    (∀ t > 0, ∀ x : Space3,
      let g := maximalMildValue γ hγ ν hν g₀ t
      let u := realSobolevField γ (by linarith) g
      deriv (fun r => realSobolevField γ (by linarith)
        (maximalMildValue γ hγ ν hν g₀ r) x) t -
        (ν : ℝ) • (Δ u) x + spatialConvection u u x +
        realScalarGradient (sobolevPressure γ hγ g g) x = 0) := by
  have h := physical_representative_global_navier_endpoint
    γ hγ ν hν u₀ hf v hv hv₀ hdiv hc
  dsimp only at h ⊢
  rcases h with ⟨hglobal, _, _, _, _, _, _, _, _, hpde, _⟩
  exact ⟨hglobal, hpde⟩

#print axioms joint_actual_zero_xi_and_navier_source_return
#print axioms nonlinear_frame_actual_zero_xi_return
#print axioms actual_navier_xi_source_step_at_zero_coordinate
#print axioms arithmetic_zero_window_closure_iff_rh
#print axioms riemannHypothesis_of_arithmetic_zero_window_closure
#print axioms navier_global_mild_of_two_channel_closure
#print axioms navier_global_physical_pde_of_two_channel_closure
#print axioms navier_pointwise_physical_pde_of_hilbert_xi_closure

end SixBirdsMetaMath.RHNavier.JointSixBirdsObservationReturn
