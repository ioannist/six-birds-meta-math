import SixBirdsNeedles.NSCore.ComplexGaussianObservations
import SixBirdsDualityConfinement.RH.ComplexGaussianObservation
import SixBirdsDualityConfinement.RH.ArithmeticJensenWindows
import SixBirdsDualityConfinement.RH.FullClassicalRHBridge

/-! Arithmetic specializations of the maintained Navier complex Gaussian observation. -/
noncomputable section
open MeasureTheory Real
open scoped NNReal RealInnerProductSpace InnerProductSpace
namespace SixBirdsMetaMath.RHNavier.ComplexGaussianNavierRHBridge

open SixBirdsNeedles.NSCore
open SixBirdsNeedles.NSCore.ComplexGaussianObservations
open SixBirdsDualityConfinement.RH.ComplexGaussianObservation
open SixBirdsDualityConfinement.RH.ArithmeticJensenWindows
open SixBirdsDualityConfinement.RH.FiniteZeroWindows
open SixBirdsDualityConfinement.RH.FullClassicalRHBridge
open SixBirdsDualityConfinement.RH.ClassicalZeroLedger

/-- This complex Gaussian identity holds at every complex point. Sampling
at an actual zeta zero supplies no further arithmetic information here. -/
theorem spectral_gaussian_eq_complex_navier_integral
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    complexAxialHeatIntegral a b (spectralCoordinate s) =
      (((Real.pi : ℂ) / (↑(a + b) : ℂ)) ^
        ((Module.finrank ℝ Space3 : ℂ) / 2)) *
        spectralGaussian (a * b / (a + b)) s := by
  rw [complexAxialHeatIntegral_formula a b ha hb]
  rfl

/-- Specialization of the pointwise Gaussian identity to an actual zero. -/
theorem actual_zero_gaussian_eq_complex_navier_integral
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ρ : SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero) :
    complexAxialHeatIntegral a b (spectralCoordinate ρ.val) =
      (((Real.pi : ℂ) / (↑(a + b) : ℂ)) ^
        ((Module.finrank ℝ Space3 : ℂ) / 2)) *
        spectralGaussian (a * b / (a + b)) ρ.val :=
  spectral_gaussian_eq_complex_navier_integral a b ha hb ρ.val

/-- The free Navier heat readout equals the spectral Gaussian at every
complex point; the identity does not use a zeta-zero hypothesis. -/
theorem spectral_gaussian_eq_navier_heat_readout
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t)
    (s : ℂ) :
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    navierComplexWindowReadout a ν t (spectralCoordinate s) =
      (((Real.pi : ℂ) / (↑(a + b) : ℂ)) ^
        ((Module.finrank ℝ Space3 : ℂ) / 2)) *
        spectralGaussian (a * b / (a + b)) s := by
  dsimp only
  have hb : 0 < 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ) := by positivity
  rw [navierComplexWindowReadout_eq_axial_integral]
  exact spectral_gaussian_eq_complex_navier_integral a _ ha hb s

/-- Specialization of the pointwise heat readout to an actual zero. -/
theorem actual_zero_gaussian_eq_navier_heat_readout
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t)
    (ρ : SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero) :
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    navierComplexWindowReadout a ν t (spectralCoordinate ρ.val) =
      (((Real.pi : ℂ) / (↑(a + b) : ℂ)) ^
        ((Module.finrank ℝ Space3 : ℂ) / 2)) *
        spectralGaussian (a * b / (a + b)) ρ.val :=
  spectral_gaussian_eq_navier_heat_readout a ν t ha hν ht ρ.val

/-- The source-corrected nonlinear theta frame returns the same spectral
Gaussian at every complex point. Zeta-zero status enters only when the
points are later selected into an arithmetic divisor window. -/
theorem complex_nonlinear_frame_return_at_point
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a)
    (s : ℂ) :
    let t := τ.toNNReal + t₀
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    complexFrameTrace a (spectralCoordinate s)
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      complexFrameTrace a (spectralCoordinate s)
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) =
      ((((Real.pi : ℂ) / (↑(a + b) : ℂ)) ^
        ((Module.finrank ℝ Space3 : ℂ) / 2)) *
        spectralGaussian (a * b / (a + b)) s) • (2 : ℂ) := by
  dsimp only
  have ht : 0 < τ.toNNReal + t₀ := by positivity
  rw [complex_nonlinear_theta_frame_return γ hγ ν t₀ hν ht₀ τ hτ hmem a ha]
  rw [spectral_gaussian_eq_navier_heat_readout a ν
    (τ.toNNReal + t₀) ha hν ht s]

/-- Specialization of the nonlinear frame return to an actual zero. -/
theorem complex_nonlinear_frame_return_at_actual_zero
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a)
    (ρ : SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero) :
    let t := τ.toNNReal + t₀
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    complexFrameTrace a (spectralCoordinate ρ.val)
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      complexFrameTrace a (spectralCoordinate ρ.val)
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) =
      ((((Real.pi : ℂ) / (↑(a + b) : ℂ)) ^
        ((Module.finrank ℝ Space3 : ℂ) / 2)) *
        spectralGaussian (a * b / (a + b)) ρ.val) • (2 : ℂ) :=
  complex_nonlinear_frame_return_at_point γ hγ ν t₀ hν ht₀ τ hτ hmem a ha ρ.val

def gaussianVolumeFactor (a b : ℝ) : ℂ :=
  ((Real.pi : ℂ) / (↑(a + b) : ℂ)) ^
    ((Module.finrank ℝ Space3 : ℂ) / 2)

theorem gaussianVolumeFactor_ne_zero
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    gaussianVolumeFactor a b ≠ 0 := by
  unfold gaussianVolumeFactor
  apply Complex.cpow_ne_zero_iff.mpr
  left
  exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    (by exact_mod_cast (ne_of_gt (add_pos ha hb)))

/-- The free Navier Gaussian heat integral has excess at an arbitrary
synthetic point inside the critical strip. Its heat-kernel identity alone
therefore cannot give the RH zero-location bound; a valid payment must use
the arithmetic fact that the sampled point is a zeta zero. -/
theorem synthetic_offline_heat_readout_exceeds_baseline
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ‖gaussianVolumeFactor a b‖ <
      ‖complexAxialHeatIntegral a b
        (spectralCoordinate (⟨3 / 4, 0⟩ : ℂ))‖ := by
  have hc : 0 < a * b / (a + b) := by positivity
  have hs : (1 : ℝ) <
      ‖spectralGaussian (a * b / (a + b)) (⟨3 / 4, 0⟩ : ℂ)‖ := by
    simpa using spectralGaussian_norm_gt_height_gaussian
      (a * b / (a + b)) hc (⟨3 / 4, 0⟩ : ℂ) (by norm_num)
  have hf : 0 < ‖gaussianVolumeFactor a b‖ :=
    norm_pos_iff.mpr (gaussianVolumeFactor_ne_zero a b ha hb)
  rw [complexAxialHeatIntegral_formula a b ha hb]
  change ‖gaussianVolumeFactor a b‖ <
    ‖gaussianVolumeFactor a b *
      spectralGaussian (a * b / (a + b)) (⟨3 / 4, 0⟩ : ℂ)‖
  rw [norm_mul]
  nlinarith

theorem no_stripwide_free_heat_baseline
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ¬ ∀ s : ℂ, 0 < s.re → s.re < 1 →
      ‖complexAxialHeatIntegral a b (spectralCoordinate s)‖ ≤
        ‖gaussianVolumeFactor a b‖ := by
  intro h
  have hs := h (⟨3 / 4, 0⟩ : ℂ) (by norm_num) (by norm_num)
  exact (not_le.mpr (synthetic_offline_heat_readout_exceeds_baseline
    a b ha hb)) hs

/-- Normalized logarithmic excess of the complex-center Navier heat
reading at an actual completed-zeta zero. -/
def navierHeatLogExcess
    (a : ℝ) (ν t : ℝ≥0)
    (ρ : SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero) : ℝ :=
  let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
  Real.log (‖navierComplexWindowReadout a ν t
      (spectralCoordinate ρ.val)‖ / ‖gaussianVolumeFactor a b‖) +
    (a * b / (a + b)) * ρ.val.im ^ 2

theorem navierHeatLogExcess_eq_displacement_sq
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t)
    (ρ : SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero) :
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    navierHeatLogExcess a ν t ρ =
      (a * b / (a + b)) *
        SixBirdsDualityConfinement.RH.FiniteZeroWindows.displacement ρ ^ 2 := by
  dsimp only
  have hb : 0 < 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ) := by positivity
  have hfactor := gaussianVolumeFactor_ne_zero a
    (4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)) ha hb
  have hnorm : ‖gaussianVolumeFactor a
      (4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ))‖ ≠ 0 :=
    (norm_ne_zero_iff).mpr hfactor
  have hquot :
      ‖navierComplexWindowReadout a ν t (spectralCoordinate ρ.val)‖ /
        ‖gaussianVolumeFactor a
          (4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ))‖ =
      ‖spectralGaussian
        (a * (4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)) /
          (a + 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ))) ρ.val‖ := by
    rw [actual_zero_gaussian_eq_navier_heat_readout a ν t ha hν ht ρ]
    change ‖gaussianVolumeFactor a _ * spectralGaussian _ ρ.val‖ /
      ‖gaussianVolumeFactor a _‖ = _
    rw [norm_mul]
    exact mul_div_cancel_left₀ _ hnorm
  dsimp [navierHeatLogExcess]
  rw [hquot]
  exact gaussianLogExcess_eq _ ρ

def navierHeatWindowExcess (a : ℝ) (ν t : ℝ≥0)
    (m : SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero → ℕ)
    (W : Finset SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero) : ℝ :=
  ∑ ρ ∈ W, (m ρ : ℝ) * navierHeatLogExcess a ν t ρ

/-- On genuine `J`-reflected completed-zeta zero windows, a normalized
logarithmic reading of the actual Navier heat multiplier at complex
centers is exactly the RH XI residual energy times the heat width.
This is an observation identity; no nonlinear or arithmetic source
estimate follows. -/
theorem navierHeatWindowExcess_eq_rh_xi
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t)
    (m : SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero → ℕ)
    (hm : ∀ ρ, m (SixBirdsDualityConfinement.RH.ActualInvolution.J_zero ρ) = m ρ)
    (W : Finset SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero)
    (hW : SixBirdsDualityConfinement.RH.ActualInvolution.JReflectedWindow W) :
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    navierHeatWindowExcess a ν t m W =
      (a * b / (a + b)) *
        ‖SixBirdsNeedles.XiCore.hilbertKernelXi
          (SixBirdsDualityConfinement.RH.FiniteZeroWindows.invariantProbe W)
          (SixBirdsDualityConfinement.RH.FiniteZeroWindows.displacementVector m W)‖ ^ 2 := by
  dsimp only
  unfold navierHeatWindowExcess
  calc
    (∑ ρ ∈ W, (m ρ : ℝ) * navierHeatLogExcess a ν t ρ) =
        ∑ ρ ∈ W, (m ρ : ℝ) * gaussianLogExcess
          (a * (4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)) /
            (a + 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ))) ρ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [navierHeatLogExcess_eq_displacement_sq a ν t ha hν ht ρ,
        gaussianLogExcess_eq]
    _ = _ := windowGaussianLogExcess_eq_xi _ m hm W hW

/-- On exhaustive actual zero windows, a zero budget for the complex
Navier heat excess is exactly full RH. This calibrates the strength of
any proposed source law for this observable. -/
theorem canonical_navierHeatWindowExcess_zero_iff_riemannHypothesis
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t) :
    (∀ n : ℕ,
      navierHeatWindowExcess a ν t unitWeights
        (canonicalJensenWindow n) = 0) ↔ RiemannHypothesis := by
  have hb : 0 < 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ) := by positivity
  have hd : 0 < a * (4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)) /
      (a + 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)) := by positivity
  constructor
  · intro hz
    apply riemannHypothesis_of_criticalStripRH
    apply criticalStripRH_of_exhaustive_vanishing_budget
      unitWeights unitWeights_positive canonicalJensenWindow
      canonicalJensenWindow_eventuallyCovered (fun _ => 0)
      tendsto_const_nhds
    intro n
    have hzero := hz n
    rw [navierHeatWindowExcess_eq_rh_xi a ν t ha hν ht
      unitWeights (fun _ => rfl) (canonicalJensenWindow n)
      (canonicalJensenWindow_reflected n),
      canonicalJensenWindow_xi_eq_energy] at hzero
    have he : windowEnergy unitWeights (canonicalJensenWindow n) = 0 := by
      nlinarith
    simp [he]
  · intro hRH n
    have hstrip := criticalStripRH_of_riemannHypothesis hRH
    have he : windowEnergy unitWeights (canonicalJensenWindow n) = 0 := by
      apply (windowEnergy_eq_zero_iff unitWeights unitWeights_positive _).mpr
      intro ρ _
      exact sub_eq_zero.mpr (hstrip ρ.val
        ((completed_zero_iff_zeta_zero_of_re_pos ρ.val
          ρ.property.2.1).mp ρ.property.1)
        ρ.property.2.1 ρ.property.2.2)
    rw [navierHeatWindowExcess_eq_rh_xi a ν t ha hν ht
      unitWeights (fun _ => rfl) (canonicalJensenWindow n)
      (canonicalJensenWindow_reflected n),
      canonicalJensenWindow_xi_eq_energy, he, mul_zero]

/-- The source-corrected diagonal reading of three genuine local
nonlinear Navier paths, divided by the Leray trace factor. -/
def normalizedNonlinearFrameReadout
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ a : ℝ) (z : ℂ) : ℂ :=
  (complexFrameTrace a z (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
    complexFrameTrace a z (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ)) / 2

theorem normalizedNonlinearFrameReadout_eq_heat
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) (z : ℂ) :
    normalizedNonlinearFrameReadout γ hγ ν t₀ hν ht₀ τ a z =
      navierComplexWindowReadout a ν (τ.toNNReal + t₀) z := by
  unfold normalizedNonlinearFrameReadout
  rw [complex_nonlinear_theta_frame_return γ hγ ν t₀ hν ht₀
    τ hτ hmem a ha]
  simp [smul_eq_mul]

/-- Even the source-corrected reading of genuine local nonlinear Navier
paths exceeds the on-line Gaussian baseline at a synthetic off-line
point. The point is not asserted to be a zeta zero. -/
theorem synthetic_offline_nonlinear_frame_exceeds_baseline
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) :
    let t := τ.toNNReal + t₀
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    ‖gaussianVolumeFactor a b‖ <
      ‖normalizedNonlinearFrameReadout γ hγ ν t₀ hν ht₀ τ a
        (spectralCoordinate (⟨3 / 4, 0⟩ : ℂ))‖ := by
  dsimp only
  have ht : 0 < τ.toNNReal + t₀ := by positivity
  have hb : 0 < 4 * Real.pi ^ 2 * (ν : ℝ) *
      ((τ.toNNReal + t₀ : ℝ≥0) : ℝ) := by positivity
  rw [normalizedNonlinearFrameReadout_eq_heat γ hγ ν t₀ hν ht₀
    τ hτ hmem a ha]
  rw [navierComplexWindowReadout_eq_axial_integral]
  exact synthetic_offline_heat_readout_exceeds_baseline a _ ha hb

def nonlinearFrameWindowExcess
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ a : ℝ) (W : Finset NontrivialZero) : ℝ :=
  let t := τ.toNNReal + t₀
  let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
  ∑ ρ ∈ W,
    (Real.log (‖normalizedNonlinearFrameReadout γ hγ ν t₀ hν ht₀
      τ a (spectralCoordinate ρ.val)‖ / ‖gaussianVolumeFactor a b‖) +
      (a * b / (a + b)) * (ρ.val).im ^ 2)

theorem nonlinearFrameWindowExcess_eq_navierHeatWindowExcess
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) (W : Finset NontrivialZero) :
    nonlinearFrameWindowExcess γ hγ ν t₀ hν ht₀ τ a W =
      navierHeatWindowExcess a ν (τ.toNNReal + t₀) unitWeights W := by
  unfold nonlinearFrameWindowExcess navierHeatWindowExcess navierHeatLogExcess
  simp_rw [unitWeights, Nat.cast_one, one_mul,
    normalizedNonlinearFrameReadout_eq_heat γ hγ ν t₀ hν ht₀
      τ hτ hmem a ha]

/-- Even after representing the complex Gaussian by genuine nonlinear
Navier paths plus their actual Duhamel source, zero excess on all
exhaustive completed-zeta windows remains exactly full RH. -/
theorem canonical_nonlinearFrameWindowExcess_zero_iff_riemannHypothesis
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) :
    (∀ n : ℕ,
      nonlinearFrameWindowExcess γ hγ ν t₀ hν ht₀ τ a
        (canonicalJensenWindow n) = 0) ↔ RiemannHypothesis := by
  have ht : 0 < τ.toNNReal + t₀ := by positivity
  simp_rw [nonlinearFrameWindowExcess_eq_navierHeatWindowExcess
    γ hγ ν t₀ hν ht₀ τ hτ hmem a ha]
  exact canonical_navierHeatWindowExcess_zero_iff_riemannHypothesis
    a ν (τ.toNNReal + t₀) ha hν ht

#print axioms complexAxialHeatIntegral_formula
#print axioms spectral_gaussian_eq_complex_navier_integral
#print axioms spectral_gaussian_eq_navier_heat_readout
#print axioms complex_nonlinear_frame_return_at_point
#print axioms actual_zero_gaussian_eq_complex_navier_integral
#print axioms navierComplexWindowReadout_eq_axial_integral
#print axioms solenoidalThetaHeatState_complex_gaussian_trace
#print axioms complex_nonlinear_theta_frame_return
#print axioms complex_nonlinear_frame_return_at_actual_zero
#print axioms actual_zero_gaussian_eq_navier_heat_readout
#print axioms complexAxialWindow_real_center
#print axioms navierComplexWindowReadout_real_center
#print axioms gaussianVolumeFactor_ne_zero
#print axioms synthetic_offline_heat_readout_exceeds_baseline
#print axioms no_stripwide_free_heat_baseline
#print axioms navierHeatLogExcess_eq_displacement_sq
#print axioms navierHeatWindowExcess_eq_rh_xi
#print axioms canonical_navierHeatWindowExcess_zero_iff_riemannHypothesis
#print axioms canonical_nonlinearFrameWindowExcess_zero_iff_riemannHypothesis
#print axioms synthetic_offline_nonlinear_frame_exceeds_baseline
#print axioms complexAxialWindow_norm
#print axioms complexAxialWindow_memLp_two
#print axioms complexAxialWindow_state_integrable
#print axioms complexAxialWindow_transverseFlip
#print axioms complexGaussianStateReadout_transverseBlindState_zero
#print axioms no_complex_axial_field_controls_admissible_xi
#print axioms complexDirectionalStateReadout_thetaAxis
#print axioms complexDirectionalStateReadout_real_one
#print axioms complexDirectionalWindow_norm
#print axioms complexDirectionalWindow_memLp_two
#print axioms complexDirectionalWindow_state_integrable
#print axioms complexDirectionalWindow_heat_complete_square
#print axioms complexDirectionalStateReadout_sub
#print axioms complexDirectionalStateReadout_add
#print axioms maximalMildValue_complex_directional_return
#print axioms complexDirectionalStateReadout_heat_transport
#print axioms maximalMildValue_complex_directional_source_step
#print axioms maximalMildValue_complex_directional_xi_source_step
#print axioms complexDirectionalStateReadout_separates
#print axioms complexDirectionalStateReadout_detects_transverseBlindState
#print axioms heatEnergy_injective
#print axioms full_directional_corrected_return_injective
#print axioms complexGaussianStateReadout_real_center
#print axioms complexGaussianStateReadout_sub
#print axioms maximalMildValue_complex_gaussian_return
#print axioms complexGaussianStateReadout_heat_transverseBlindState_zero
#print axioms complex_nonlinear_perturbed_frame_return
#print axioms exists_complex_nonlinear_perturbed_frame_with_unbounded_initial_xi
#print axioms exists_positive_same_time_complex_corrected_trace_split_pair

end SixBirdsMetaMath.RHNavier.ComplexGaussianNavierRHBridge
