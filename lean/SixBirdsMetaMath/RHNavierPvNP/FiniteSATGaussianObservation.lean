import SixBirdsMetaMath.RHNavier.ComplexGaussianNavierRHBridge
import SixBirdsHiddenness.PvNP.CNFSemantics
import SixBirdsHiddenness.PvNP.StandardSATBridge

/-!
A first native SAT instance of the maintained complex Gaussian heat
observation. The finite sum is over actual Boolean assignments to an
actual CNF formula. The exact identity makes no polynomial-time claim:
the assignment sum has exponentially many possible terms.
-/

noncomputable section
open Finset
open scoped NNReal RealInnerProductSpace InnerProductSpace
namespace SixBirdsMetaMath.RHNavierPvNP.FiniteSATGaussianObservation

open SixBirdsHiddenness.PvNP.CNFSemantics
open SixBirdsNeedles.NSCore
open SixBirdsNeedles.NSCore.ComplexGaussianObservations
open SixBirdsDualityConfinement.RH.ComplexGaussianObservation
open SixBirdsMetaMath.RHNavier.ComplexGaussianNavierRHBridge

/-- The finite observation has one potential term for each of the
`2^n` Boolean assignments. -/
theorem assignment_count (n : Nat) :
    Fintype.card (Assignment n) = 2 ^ n := by
  simp [Assignment]

/-- One complex Gaussian observation operator on a finite weighted
collection of spectral points. SAT assignments and completed-zeta zero
windows will be distinct native instances of this same definition. -/
def finiteHeatObservation {I : Type*} (W : Finset I)
    (weight : I → ℂ) (coordinate : I → ℂ)
    (a : ℝ) (ν t : ℝ≥0) : ℂ :=
  ∑ i ∈ W,
    weight i *
      navierComplexWindowReadout a ν t (spectralCoordinate (coordinate i))

def finiteSpectralObservation {I : Type*} (W : Finset I)
    (weight : I → ℂ) (coordinate : I → ℂ) (c : ℝ) : ℂ :=
  ∑ i ∈ W, weight i * spectralGaussian c (coordinate i)

def finiteFrameObservation {I : Type*} (W : Finset I)
    (weight : I → ℂ) (coordinate : I → ℂ)
    (a : ℝ) (g : Fin 3 → FourierEnergy) : ℂ :=
  ∑ i ∈ W,
    weight i * complexFrameTrace a (spectralCoordinate (coordinate i)) g

theorem finite_heat_eq_spectral {I : Type*} (W : Finset I)
    (weight : I → ℂ) (coordinate : I → ℂ)
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t) :
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    finiteHeatObservation W weight coordinate a ν t =
      (((Real.pi : ℂ) / (↑(a + b) : ℂ)) ^
        ((Module.finrank ℝ Space3 : ℂ) / 2)) *
        finiteSpectralObservation W weight coordinate
          (a * b / (a + b)) := by
  dsimp only
  unfold finiteHeatObservation finiteSpectralObservation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [spectral_gaussian_eq_navier_heat_readout
    a ν t ha hν ht (coordinate i)]
  ring

/-- The shared finite observation on actual local Navier frame states
retains the full nonlinear Duhamel correction for every weighted point. -/
theorem finite_actual_frame_return {I : Type*} (W : Finset I)
    (weight : I → ℂ) (coordinate : I → ℂ)
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) :
    finiteFrameObservation W weight coordinate a
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      finiteFrameObservation W weight coordinate a
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) =
      finiteHeatObservation W weight coordinate a ν
        (τ.toNNReal + t₀) * 2 := by
  unfold finiteFrameObservation finiteHeatObservation
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← mul_add]
  rw [complex_nonlinear_theta_frame_return
    γ hγ ν t₀ hν ht₀ τ hτ hmem a ha
    (spectralCoordinate (coordinate i))]
  simp [smul_eq_mul]
  ring

/-- The same finite operator instantiated on actual nontrivial
completed-zeta zeros. Multiplicity is an explicit weight. -/
def actualZeroHeatObservation
    (m : SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero → ℕ)
    (W : Finset SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero)
    (a : ℝ) (ν t : ℝ≥0) : ℂ :=
  finiteHeatObservation W (fun ρ => (m ρ : ℂ)) (fun ρ => ρ.val) a ν t

theorem actualZeroHeatObservation_eq_spectral
    (m : SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero → ℕ)
    (W : Finset SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero)
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t) :
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    actualZeroHeatObservation m W a ν t =
      (((Real.pi : ℂ) / (↑(a + b) : ℂ)) ^
        ((Module.finrank ℝ Space3 : ℂ) / 2)) *
        finiteSpectralObservation W (fun ρ => (m ρ : ℂ))
          (fun ρ => ρ.val) (a * b / (a + b)) :=
  finite_heat_eq_spectral W (fun ρ => (m ρ : ℂ))
    (fun ρ => ρ.val) a ν t ha hν ht

theorem actualZero_nonlin_frame_return
    (m : SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero → ℕ)
    (W : Finset SixBirdsDualityConfinement.RH.ClassicalZeroLedger.NontrivialZero)
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) :
    finiteFrameObservation W (fun ρ => (m ρ : ℂ))
        (fun ρ => ρ.val) a
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      finiteFrameObservation W (fun ρ => (m ρ : ℂ))
        (fun ρ => ρ.val) a
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) =
      actualZeroHeatObservation m W a ν (τ.toNNReal + t₀) * 2 :=
  finite_actual_frame_return W (fun ρ => (m ρ : ℂ))
    (fun ρ => ρ.val) γ hγ ν t₀ hν ht₀ τ hτ hmem a ha

/-- The free Navier heat window read at spectral coordinates of precisely
the satisfying assignments. `coordinate` is explicit and will require
its own encoding and resource audit in the final construction. -/
def satHeatObservation {n : Nat} (φ : Formula n)
    (coordinate : Assignment n → ℂ)
    (a : ℝ) (ν t : ℝ≥0) : ℂ :=
  ∑ w : Assignment n,
    if evalFormula w φ = true then
      navierComplexWindowReadout a ν t (spectralCoordinate (coordinate w))
    else 0

def satWeight {n : Nat} (φ : Formula n) (w : Assignment n) : ℂ :=
  if evalFormula w φ = true then 1 else 0

theorem satHeatObservation_eq_finite {n : Nat} (φ : Formula n)
    (coordinate : Assignment n → ℂ)
    (a : ℝ) (ν t : ℝ≥0) :
    satHeatObservation φ coordinate a ν t =
      finiteHeatObservation Finset.univ (satWeight φ) coordinate a ν t := by
  unfold satHeatObservation finiteHeatObservation satWeight
  apply Finset.sum_congr rfl
  intro w _hw
  split_ifs <;> simp

/-- The same finite SAT measure read through the RH spectral Gaussian. -/
def satSpectralObservation {n : Nat} (φ : Formula n)
    (coordinate : Assignment n → ℂ) (c : ℝ) : ℂ :=
  ∑ w : Assignment n,
    if evalFormula w φ = true then
      spectralGaussian c (coordinate w)
    else 0

theorem satSpectralObservation_eq_finite {n : Nat} (φ : Formula n)
    (coordinate : Assignment n → ℂ) (c : ℝ) :
    satSpectralObservation φ coordinate c =
      finiteSpectralObservation Finset.univ (satWeight φ) coordinate c := by
  unfold satSpectralObservation finiteSpectralObservation satWeight
  apply Finset.sum_congr rfl
  intro w _hw
  split_ifs <;> simp

/-- A positive Gaussian SAT readout at real spectral coordinates.
The `height` map is data; evaluating this sum directly inspects all
assignments. -/
def satPositiveMass {n : Nat} (φ : Formula n)
    (height : Assignment n → ℝ) (c : ℝ) : ℝ :=
  ∑ w : Assignment n,
    if evalFormula w φ = true then Real.exp (-c * (height w) ^ 2)
    else 0

def criticalCoordinate {n : Nat} (height : Assignment n → ℝ)
    (w : Assignment n) : ℂ :=
  ⟨1 / 2, height w⟩

/-- A concrete spectral coordinate formed from the native binary
assignment code. -/
def binarySATCoordinate {n : Nat} (w : Assignment n) : ℂ :=
  criticalCoordinate (fun v => (assignmentCode v : ℝ)) w

theorem spectralGaussian_criticalCoordinate
    (c r : ℝ) :
    spectralGaussian c (⟨1 / 2, r⟩ : ℂ) =
      (Real.exp (-c * r ^ 2) : ℂ) := by
  have hcoord : spectralCoordinate (⟨1 / 2, r⟩ : ℂ) = (r : ℂ) := by
    apply Complex.ext <;> norm_num [spectralCoordinate]
  rw [spectralGaussian, hcoord, Complex.ofReal_exp]
  push_cast
  ring

/-- The positive SAT mass is literally the RH spectral Gaussian
observation at critical-line coordinates. -/
theorem satSpectralObservation_critical_eq_mass {n : Nat}
    (φ : Formula n) (height : Assignment n → ℝ) (c : ℝ) :
    satSpectralObservation φ (criticalCoordinate height) c =
      (satPositiveMass φ height c : ℂ) := by
  classical
  unfold satSpectralObservation satPositiveMass
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hs : evalFormula w φ = true
  · simpa [hs, criticalCoordinate, Complex.ofReal_exp] using
      spectralGaussian_criticalCoordinate c (height w)
  · simp [hs]

/-- Arbitrary Boolean filters have the same positive-sum property.
This control proves that Gaussian positivity alone is generic and does
not capture the SAT-specific computational bridge. -/
theorem filteredPositiveMass_pos_iff {n : Nat}
    (filter : Assignment n → Bool)
    (height : Assignment n → ℝ) (c : ℝ) :
    0 < (∑ w : Assignment n,
      if filter w = true then Real.exp (-c * (height w) ^ 2)
      else 0) ↔ ∃ w : Assignment n, filter w = true := by
  classical
  constructor
  · intro hpos
    by_contra hnone
    have hall (w : Assignment n) : filter w ≠ true := by
      intro hw
      exact hnone ⟨w, hw⟩
    simp [hall] at hpos
  · rintro ⟨w, hw⟩
    apply Finset.sum_pos'
    · intro x _hx
      by_cases h : filter x = true
      · simp [h, le_of_lt (Real.exp_pos _)]
      · simp [h]
    · refine ⟨w, Finset.mem_univ _, ?_⟩
      simp [hw, Real.exp_pos]

/-- A positive Gaussian sum detects native CNF satisfiability exactly.
The arbitrary-filter theorem above exposes why this alone is not a
SAT-specific complexity argument. -/
theorem satPositiveMass_pos_iff {n : Nat} (φ : Formula n)
    (height : Assignment n → ℝ) (c : ℝ) :
    0 < satPositiveMass φ height c ↔ Satisfiable φ := by
  simpa [satPositiveMass, Satisfiable, Satisfies] using
    filteredPositiveMass_pos_iff (fun w => evalFormula w φ) height c

/-- Gaussian mass removed by imposing one additional concrete CNF
clause. The defect is read on assignments satisfying the old formula
and violating this exact clause. -/
def clauseFailureMass {n : Nat} (φ : Formula n) (clause : Clause n)
    (height : Assignment n → ℝ) (c : ℝ) : ℝ :=
  ∑ w : Assignment n,
    if evalFormula w φ = true ∧ evalClause w clause = false then
      Real.exp (-c * (height w) ^ 2)
    else 0

/-- Exact SAT-specific residual update under adding a clause. The
remaining Gaussian mass is the previous mass less precisely the
mass of assignments eliminated by that clause. -/
theorem satPositiveMass_append_clause {n : Nat} (φ : Formula n)
    (clause : Clause n) (height : Assignment n → ℝ) (c : ℝ) :
    satPositiveMass (φ ++ [clause]) height c =
      satPositiveMass φ height c -
        clauseFailureMass φ clause height c := by
  unfold satPositiveMass clauseFailureMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _hw
  have hEval :
      evalFormula w (φ ++ [clause]) =
        (evalFormula w φ && evalClause w clause) := by
    simp [evalFormula]
  rw [hEval]
  cases hφ : evalFormula w φ <;>
    cases hc : evalClause w clause <;>
    simp_all

/-- Uniform assignment mean and centered energy, used to test whether
a variance-style XI residual can distinguish SAT from UNSAT. -/
def assignmentMean {n : Nat} (f : Assignment n → ℝ) : ℝ :=
  (∑ w : Assignment n, f w) / (2 ^ n : ℝ)

def assignmentCenteredEnergy {n : Nat} (f : Assignment n → ℝ) : ℝ :=
  ∑ w : Assignment n, (f w - assignmentMean f) ^ 2

def satIndicator {n : Nat} (φ : Formula n) (w : Assignment n) : ℝ :=
  if evalFormula w φ = true then 1 else 0

theorem assignmentMean_const {n : Nat} (c : ℝ) :
    assignmentMean (fun _ : Assignment n => c) = c := by
  simp [assignmentMean]

theorem assignmentCenteredEnergy_const {n : Nat} (c : ℝ) :
    assignmentCenteredEnergy (fun _ : Assignment n => c) = 0 := by
  simp [assignmentCenteredEnergy, assignmentMean_const]

/-- A centered-only residual is zero on both extreme native CNFs:
the unsatisfiable empty clause and the satisfiable empty conjunction.
It therefore cannot by itself be a SAT decision readout. -/
theorem centeredEnergy_empty_and_contradiction (n : Nat) :
    assignmentCenteredEnergy
        (satIndicator ([] : Formula n)) = 0 ∧
      assignmentCenteredEnergy
        (satIndicator ([[]] : Formula n)) = 0 := by
  have htrue : satIndicator ([] : Formula n) =
      (fun _ : Assignment n => 1) := by
    funext w
    simp [satIndicator, evalFormula]
  have hfalse : satIndicator ([[]] : Formula n) =
      (fun _ : Assignment n => 0) := by
    funext w
    simp [satIndicator, evalFormula, evalClause]
  rw [htrue, hfalse]
  exact ⟨assignmentCenteredEnergy_const 1,
    assignmentCenteredEnergy_const 0⟩

/-- Exact transport of a native CNF assignment measure through the
same pointwise complex Gaussian identity used by the RH–Navier bridge.
This establishes an operator identity, while computation of the finite
sum and the nonlinear Navier return remain separate obligations. -/
theorem sat_heat_eq_spectral_gaussian {n : Nat}
    (φ : Formula n) (coordinate : Assignment n → ℂ)
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t) :
    let b := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
    satHeatObservation φ coordinate a ν t =
      (((Real.pi : ℂ) / (↑(a + b) : ℂ)) ^
        ((Module.finrank ℝ Space3 : ℂ) / 2)) *
        satSpectralObservation φ coordinate (a * b / (a + b)) := by
  dsimp only
  rw [satHeatObservation_eq_finite,
    satSpectralObservation_eq_finite]
  exact finite_heat_eq_spectral Finset.univ (satWeight φ)
    coordinate a ν t ha hν ht

/-- At critical-line spectral coordinates, the exact free Navier heat
reading of the native SAT measure is nonzero precisely for satisfiable
CNFs. The finite assignment sum is still an exponentially sized
observation; no efficient decision procedure follows. -/
theorem satHeatObservation_ne_zero_iff_satisfiable {n : Nat}
    (φ : Formula n) (height : Assignment n → ℝ)
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t) :
    satHeatObservation φ (criticalCoordinate height) a ν t ≠ 0 ↔
      Satisfiable φ := by
  let b : ℝ := 4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ)
  let c : ℝ := a * b / (a + b)
  let factor : ℂ :=
    ((Real.pi : ℂ) / (↑(a + b) : ℂ)) ^
      ((Module.finrank ℝ Space3 : ℂ) / 2)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hfactor : factor ≠ 0 :=
    gaussianVolumeFactor_ne_zero a b ha hb
  have hread :
      satHeatObservation φ (criticalCoordinate height) a ν t =
        factor * (satPositiveMass φ height c : ℂ) := by
    have h := sat_heat_eq_spectral_gaussian φ
      (criticalCoordinate height) a ν t ha hν ht
    dsimp only at h
    rw [satSpectralObservation_critical_eq_mass] at h
    exact h
  rw [hread]
  constructor
  · intro hne
    have hmassNe : satPositiveMass φ height c ≠ 0 := by
      intro hz
      simp [hz] at hne
    have hmassNonneg : 0 ≤ satPositiveMass φ height c := by
      unfold satPositiveMass
      apply Finset.sum_nonneg
      intro w _hw
      by_cases hs : evalFormula w φ = true
      · simp [hs, le_of_lt (Real.exp_pos _)]
      · simp [hs]
    exact (satPositiveMass_pos_iff φ height c).mp
      (lt_of_le_of_ne hmassNonneg hmassNe.symm)
  · intro hs
    have hmassPos := (satPositiveMass_pos_iff φ height c).mpr hs
    have hmassNe : (satPositiveMass φ height c : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hmassPos)
    exact mul_ne_zero hfactor hmassNe

/-- The actual Gaussian heat observation detects membership of the
corresponding bitstring in the machine-based SAT language. This is an
extensional identity; it does not give a polynomial-time evaluator for
the exponentially sized assignment sum. -/
theorem satHeatObservation_ne_zero_iff_encoded_L_SAT {n : Nat}
    (φ : Formula n) (height : Assignment n → ℝ)
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t) :
    satHeatObservation φ (criticalCoordinate height) a ν t ≠ 0 ↔
      (SixBirdsHiddenness.PvNP.StandardSATBridge.toExternalFormula φ).encode ∈
        SAT.L_SAT := by
  rw [satHeatObservation_ne_zero_iff_satisfiable φ height a ν t ha hν ht]
  exact (SixBirdsHiddenness.PvNP.StandardSATBridge.encoded_mem_L_SAT_iff φ).symm

/-- Actual Navier frame trace summed over the satisfying assignments
of a native CNF. The `g` argument is a physical Fourier-energy frame. -/
def satFrameTrace {n : Nat} (φ : Formula n)
    (coordinate : Assignment n → ℂ) (a : ℝ)
    (g : Fin 3 → FourierEnergy) : ℂ :=
  ∑ w : Assignment n,
    if evalFormula w φ = true then
      complexFrameTrace a (spectralCoordinate (coordinate w)) g
    else 0

/-- The part of the actual frame trace removed by adding a clause:
assignments which satisfy the old CNF and fail the new clause. -/
def clauseFailureFrameTrace {n : Nat} (φ : Formula n)
    (clause : Clause n) (coordinate : Assignment n → ℂ)
    (a : ℝ) (g : Fin 3 → FourierEnergy) : ℂ :=
  ∑ w : Assignment n,
    if evalFormula w φ = true ∧ evalClause w clause = false then
      complexFrameTrace a (spectralCoordinate (coordinate w)) g
    else 0

/-- Clause restriction commutes with the finite frame observation.
The lost term is the trace on precisely the assignments rejected by
the new clause. -/
theorem satFrameTrace_append_clause {n : Nat}
    (φ : Formula n) (clause : Clause n)
    (coordinate : Assignment n → ℂ) (a : ℝ)
    (g : Fin 3 → FourierEnergy) :
    satFrameTrace (φ ++ [clause]) coordinate a g =
      satFrameTrace φ coordinate a g -
        clauseFailureFrameTrace φ clause coordinate a g := by
  unfold satFrameTrace clauseFailureFrameTrace
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _hw
  have hEval : evalFormula w (φ ++ [clause]) =
      (evalFormula w φ && evalClause w clause) := by
    simp [evalFormula]
  rw [hEval]
  cases hφ : evalFormula w φ <;>
    cases hc : evalClause w clause <;>
    simp_all

/-- The SAT clause residual is transported through the maintained
actual nonlinear Navier frame without discarding the Duhamel source.
This is a structural observation identity, not a polynomial SAT solver. -/
theorem actual_navier_clause_residual_return {n : Nat}
    (φ : Formula n) (clause : Clause n)
    (coordinate : Assignment n → ℂ)
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (a : ℝ) :
    satFrameTrace (φ ++ [clause]) coordinate a
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      satFrameTrace (φ ++ [clause]) coordinate a
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) =
      (satFrameTrace φ coordinate a
          (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
        satFrameTrace φ coordinate a
          (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ)) -
        (clauseFailureFrameTrace φ clause coordinate a
          (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
        clauseFailureFrameTrace φ clause coordinate a
          (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ)) := by
  rw [satFrameTrace_append_clause, satFrameTrace_append_clause]
  ring

theorem satFrameTrace_eq_finite {n : Nat} (φ : Formula n)
    (coordinate : Assignment n → ℂ) (a : ℝ)
    (g : Fin 3 → FourierEnergy) :
    satFrameTrace φ coordinate a g =
      finiteFrameObservation Finset.univ (satWeight φ) coordinate a g := by
  unfold satFrameTrace finiteFrameObservation satWeight
  apply Finset.sum_congr rfl
  intro w _hw
  split_ifs <;> simp

/-- The actual nonlinear Navier frame plus its Duhamel source returns
the same finite SAT Gaussian heat observation. The source term remains
visible on the left. -/
theorem sat_actual_nonlinear_frame_return {n : Nat}
    (φ : Formula n) (coordinate : Assignment n → ℂ)
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) :
    satFrameTrace φ coordinate a
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      satFrameTrace φ coordinate a
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) =
      satHeatObservation φ coordinate a ν (τ.toNNReal + t₀) * 2 := by
  simp only [satFrameTrace_eq_finite,
    satHeatObservation_eq_finite]
  exact finite_actual_frame_return Finset.univ (satWeight φ)
    coordinate γ hγ ν t₀ hν ht₀ τ hτ hmem a ha

/-- On the actual local Navier frame, the state plus its retained
Duhamel correction has a nonzero SAT Gaussian observation exactly when
the native CNF has a satisfying assignment. This does not bound the
cost of evaluating that assignment sum. -/
theorem sat_actual_frame_return_ne_zero_iff_satisfiable {n : Nat}
    (φ : Formula n) (height : Assignment n → ℝ)
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) :
    (satFrameTrace φ (criticalCoordinate height) a
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      satFrameTrace φ (criticalCoordinate height) a
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) ≠ 0) ↔
      Satisfiable φ := by
  have ht : 0 < τ.toNNReal + t₀ := by positivity
  rw [sat_actual_nonlinear_frame_return φ
    (criticalCoordinate height) γ hγ ν t₀ hν ht₀ τ hτ hmem a ha]
  constructor
  · intro hne
    have hheat :
        satHeatObservation φ (criticalCoordinate height) a ν
          (τ.toNNReal + t₀) ≠ 0 := by
      intro hz
      simp [hz] at hne
    exact (satHeatObservation_ne_zero_iff_satisfiable
      φ height a ν (τ.toNNReal + t₀) ha hν ht).mp hheat
  · intro hs
    have hheat := (satHeatObservation_ne_zero_iff_satisfiable
      φ height a ν (τ.toNNReal + t₀) ha hν ht).mpr hs
    exact mul_ne_zero hheat (by norm_num)

/-- The preceding actual-state SAT return with its assignment
coordinates fixed to the native binary code. -/
theorem sat_actual_binary_frame_ne_zero_iff_satisfiable {n : Nat}
    (φ : Formula n)
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) :
    (satFrameTrace φ binarySATCoordinate a
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      satFrameTrace φ binarySATCoordinate a
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) ≠ 0) ↔
      Satisfiable φ :=
  sat_actual_frame_return_ne_zero_iff_satisfiable φ
    (fun w => (assignmentCode w : ℝ))
    γ hγ ν t₀ hν ht₀ τ hτ hmem a ha

/-- On the maintained nonlinear Navier frame, the SAT-filtered trace
plus its Duhamel correction detects actual encoded SAT membership. -/
theorem sat_actual_binary_frame_ne_zero_iff_encoded_L_SAT {n : Nat}
    (φ : Formula n)
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) :
    (satFrameTrace φ binarySATCoordinate a
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      satFrameTrace φ binarySATCoordinate a
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) ≠ 0) ↔
      (SixBirdsHiddenness.PvNP.StandardSATBridge.toExternalFormula φ).encode ∈
        SAT.L_SAT := by
  rw [sat_actual_binary_frame_ne_zero_iff_satisfiable
    φ γ hγ ν t₀ hν ht₀ τ hτ hmem a ha]
  exact (SixBirdsHiddenness.PvNP.StandardSATBridge.encoded_mem_L_SAT_iff φ).symm

end SixBirdsMetaMath.RHNavierPvNP.FiniteSATGaussianObservation
