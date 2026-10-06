import SixBirdsMetaMath.RHNavierPvNP.TriadObservationReturn
import SixBirdsHiddenness.PvNP.StandardComplexityReturn
import SixBirdsHiddenness.PvNP.ConcreteTranslationA
import SixBirdsHiddenness.PvNP.ConcreteSATSelfReduction
import SixBirdsHiddenness.PvNP.ConcreteTranslationBRaw
import SixBirdsHiddenness.PvNP.ConcreteCurrentizationRaw

/-!
An all-bitstring Gaussian SAT readout. Each encoded CNF is decoded to
its exact assignment cube and weighted by the same positive spectral
Gaussian used in the finite triad observation. The readout has up to
`2^(maxVar + 1)` terms. Equality of its positivity language with SAT
is exact; an efficient evaluation algorithm is not asserted.
-/

noncomputable section
open scoped NNReal
namespace SixBirdsMetaMath.RHNavierPvNP.ExternalSATGaussianLanguage

open SixBirdsHiddenness.PvNP.CNFSemantics
open SixBirdsHiddenness.PvNP.StandardSATBridge
open SixBirdsHiddenness.PvNP.ConcreteSATSelfReduction
open SixBirdsMetaMath.RHNavierPvNP.FiniteSATGaussianObservation
open SixBirdsMetaMath.RHNavier.ComplexGaussianNavierRHBridge
open SixBirdsNeedles.NSCore
open SixBirdsNeedles.NSCore.ComplexGaussianObservations
open SixBirdsHiddenness.PvNP.ConcreteTranslationA
open SixBirdsHiddenness.PvNP.ConcreteCurrentizationRaw

def externalSATGaussianMassAt (φ : SAT.CNF) (c : ℝ) : ℝ :=
  ∑ w : Assignment (φ.maxVar + 1),
    if SAT.CNF.eval (List.ofFn w) φ = true then
      Real.exp (-c * (assignmentCode w : ℝ) ^ 2)
    else 0

def externalSATGaussianMass (φ : SAT.CNF) : ℝ :=
  externalSATGaussianMassAt φ 1

def externalSATWeight (φ : SAT.CNF)
    (w : Assignment (φ.maxVar + 1)) : ℂ :=
  if SAT.CNF.eval (List.ofFn w) φ = true then 1 else 0

/-- The full external-CNF mass is literally the maintained finite
spectral Gaussian observation, with the concrete verifier as weight
and the fixed binary assignment coordinate. -/
theorem externalSATGaussianMassAt_eq_finiteSpectral
    (φ : SAT.CNF) (c : ℝ) :
    (externalSATGaussianMassAt φ c : ℂ) =
      finiteSpectralObservation Finset.univ
        (externalSATWeight φ) binarySATCoordinate c := by
  unfold externalSATGaussianMassAt finiteSpectralObservation
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  change
    (↑(if SAT.CNF.eval (List.ofFn w) φ = true then
      Real.exp (-c * (assignmentCode w : ℝ) ^ 2)
      else 0) : ℂ) =
    (if SAT.CNF.eval (List.ofFn w) φ = true then (1 : ℂ) else 0) *
      SixBirdsDualityConfinement.RH.ComplexGaussianObservation.spectralGaussian
        c (binarySATCoordinate w)
  split_ifs
  · simpa [binarySATCoordinate, criticalCoordinate,
      Complex.ofReal_exp] using
      (spectralGaussian_criticalCoordinate c
        (assignmentCode w : ℝ)).symm
  · simp

theorem externalSATGaussianMass_eq_finiteSpectral (φ : SAT.CNF) :
    (externalSATGaussianMass φ : ℂ) =
      finiteSpectralObservation Finset.univ
        (externalSATWeight φ) binarySATCoordinate 1 :=
  externalSATGaussianMassAt_eq_finiteSpectral φ 1

/-- Positivity of the full external-CNF Gaussian is exactly actual
SAT satisfiability. The proof uses all assignments in the fixed cube. -/
theorem externalSATGaussianMassAt_pos_iff (φ : SAT.CNF) (c : ℝ) :
    0 < externalSATGaussianMassAt φ c ↔ φ.Satisfiable := by
  have h := filteredPositiveMass_pos_iff
    (fun w : Assignment (φ.maxVar + 1) =>
      SAT.CNF.eval (List.ofFn w) φ)
    (fun w => (assignmentCode w : ℝ)) c
  exact h.trans (external_satisfiable_iff_fixed_fin φ).symm

theorem externalSATGaussianMass_pos_iff (φ : SAT.CNF) :
    0 < externalSATGaussianMass φ ↔ φ.Satisfiable :=
  externalSATGaussianMassAt_pos_iff φ 1

def externalSATHeatObservation (φ : SAT.CNF)
    (a : ℝ) (ν t : ℝ≥0) : ℂ :=
  finiteHeatObservation Finset.univ (externalSATWeight φ)
    binarySATCoordinate a ν t

def externalSATFrameTrace (φ : SAT.CNF) (a : ℝ)
    (g : Fin 3 → FourierEnergy) : ℂ :=
  finiteFrameObservation Finset.univ (externalSATWeight φ)
    binarySATCoordinate a g

/-- For every external CNF, the nonzero free heat observation detects
SAT. Its defining sum still enumerates the entire fixed assignment cube.
-/
theorem externalSATHeat_ne_zero_iff (φ : SAT.CNF)
    (a : ℝ) (ν t : ℝ≥0)
    (ha : 0 < a) (hν : 0 < ν) (ht : 0 < t) :
    externalSATHeatObservation φ a ν t ≠ 0 ↔ φ.Satisfiable := by
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
  have hread : externalSATHeatObservation φ a ν t =
      factor * (externalSATGaussianMassAt φ c : ℂ) := by
    have h := finite_heat_eq_spectral Finset.univ
      (externalSATWeight φ) binarySATCoordinate a ν t ha hν ht
    dsimp only at h
    change externalSATHeatObservation φ a ν t =
      factor * finiteSpectralObservation Finset.univ
        (externalSATWeight φ) binarySATCoordinate c at h
    rw [← externalSATGaussianMassAt_eq_finiteSpectral φ c] at h
    exact h
  rw [hread]
  have hmassNonneg : 0 ≤ externalSATGaussianMassAt φ c := by
    unfold externalSATGaussianMassAt
    apply Finset.sum_nonneg
    intro w _hw
    split_ifs <;> positivity
  constructor
  · intro hne
    have hmassNe : externalSATGaussianMassAt φ c ≠ 0 := by
      intro hz
      simp [hz] at hne
    exact (externalSATGaussianMassAt_pos_iff φ c).mp
      (lt_of_le_of_ne hmassNonneg hmassNe.symm)
  · intro hs
    have hmassPos := (externalSATGaussianMassAt_pos_iff φ c).mpr hs
    have hmassNe : (externalSATGaussianMassAt φ c : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hmassPos)
    exact mul_ne_zero hfactor hmassNe

/-- On the actual local nonlinear Navier frame, the external-CNF
Gaussian trace and its retained Duhamel correction detect SAT. -/
theorem externalSAT_actual_frame_ne_zero_iff (φ : SAT.CNF)
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) :
    (externalSATFrameTrace φ a
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      externalSATFrameTrace φ a
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) ≠ 0) ↔
      φ.Satisfiable := by
  have ht : 0 < τ.toNNReal + t₀ := by positivity
  have hframe := finite_actual_frame_return Finset.univ
    (externalSATWeight φ) binarySATCoordinate
    γ hγ ν t₀ hν ht₀ τ hτ hmem a ha
  change externalSATFrameTrace φ a
      (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
    externalSATFrameTrace φ a
      (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) =
    externalSATHeatObservation φ a ν (τ.toNNReal + t₀) * 2 at hframe
  rw [hframe]
  constructor
  · intro hne
    have hheat : externalSATHeatObservation φ a ν
        (τ.toNNReal + t₀) ≠ 0 := by
      intro hz
      simp [hz] at hne
    exact (externalSATHeat_ne_zero_iff φ a ν
      (τ.toNNReal + t₀) ha hν ht).mp hheat
  · intro hs
    have hheat := (externalSATHeat_ne_zero_iff φ a ν
      (τ.toNNReal + t₀) ha hν ht).mpr hs
    exact mul_ne_zero hheat (by norm_num)

/-- The all-input language read by one fixed actual local Navier
frame and its retained Duhamel correction. The SAT-filtered finite
trace is an exponentially sized mathematical observation. -/
def externalNavierSATLanguage
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ a : ℝ) : Language :=
  {z | ∃ φ : SAT.CNF, z = φ.encode ∧
    externalSATFrameTrace φ a
        (complexFrameValue γ hγ ν t₀ hν ht₀ τ) +
      externalSATFrameTrace φ a
        (complexFrameDuhamel γ hγ ν t₀ hν ht₀ τ) ≠ 0}

theorem externalNavierSATLanguage_eq_L_SAT
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) :
    externalNavierSATLanguage γ hγ ν t₀ hν ht₀ τ a = SAT.L_SAT := by
  ext z
  constructor
  · rintro ⟨φ, hz, hread⟩
    exact ⟨φ, hz,
      (externalSAT_actual_frame_ne_zero_iff
        φ γ hγ ν t₀ hν ht₀ τ hτ hmem a ha).mp hread⟩
  · rintro ⟨φ, hz, hsat⟩
    exact ⟨φ, hz,
      (externalSAT_actual_frame_ne_zero_iff
        φ γ hγ ν t₀ hν ht₀ τ hτ hmem a ha).mpr hsat⟩

/-- The three actual theta-frame initial states have a common
strictly positive local mild time. This prevents the all-input frame
language identity from resting on an empty-time hypothesis. -/
theorem exists_positive_common_theta_time
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ i : Fin 3,
        τ ∈ admissibleMildTimes γ hγ ν hν
          (solenoidalThetaHeatState ν t₀ hν ht₀ i) := by
  have hpositive (i : Fin 3) :
      ∃ T ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i), 0 < T := by
    apply admissibleMildTimes_positive γ hγ ν hν
    exact solenoidalThetaHeatState_admissible γ (by linarith)
      ν t₀ hν ht₀ i
  obtain ⟨T₀, hT₀, hT₀pos⟩ := hpositive 0
  obtain ⟨T₁, hT₁, hT₁pos⟩ := hpositive 1
  obtain ⟨T₂, hT₂, hT₂pos⟩ := hpositive 2
  let τ : ℝ := min T₀ (min T₁ T₂) / 2
  have hτpos : 0 < τ := by
    dsimp [τ]
    positivity
  refine ⟨τ, hτpos, ?_⟩
  intro i
  fin_cases i
  · apply admissibleMildTimes_downward γ hγ ν hν _ hT₀ hτpos.le
    dsimp [τ]
    linarith [min_le_left T₀ (min T₁ T₂)]
  · apply admissibleMildTimes_downward γ hγ ν hν _ hT₁ hτpos.le
    dsimp [τ]
    linarith [min_le_right T₀ (min T₁ T₂),
      min_le_left T₁ T₂]
  · apply admissibleMildTimes_downward γ hγ ν hν _ hT₂ hτpos.le
    dsimp [τ]
    linarith [min_le_right T₀ (min T₁ T₂),
      min_le_right T₁ T₂]

theorem exists_positive_externalNavierSATLanguage_eq_L_SAT
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (a : ℝ) (ha : 0 < a) :
    ∃ τ : ℝ, 0 < τ ∧
      externalNavierSATLanguage γ hγ ν t₀ hν ht₀ τ a = SAT.L_SAT := by
  obtain ⟨τ, hτ, hmem⟩ :=
    exists_positive_common_theta_time γ hγ ν t₀ hν ht₀
  exact ⟨τ, hτ,
    externalNavierSATLanguage_eq_L_SAT
      γ hγ ν t₀ hν ht₀ τ hτ.le hmem a ha⟩

/-- A bitstring is accepted when it encodes a CNF with positive exact
Gaussian assignment mass. This is a mathematical language definition;
it does not provide a polynomial-time implementation. -/
def gaussianSATLanguage : Language :=
  {z | ∃ φ : SAT.CNF,
    z = φ.encode ∧ 0 < externalSATGaussianMass φ}

theorem gaussianSATLanguage_eq_L_SAT :
    gaussianSATLanguage = SAT.L_SAT := by
  ext z
  constructor
  · rintro ⟨φ, hz, hpos⟩
    exact ⟨φ, hz, (externalSATGaussianMass_pos_iff φ).mp hpos⟩
  · rintro ⟨φ, hz, hsat⟩
    exact ⟨φ, hz, (externalSATGaussianMass_pos_iff φ).mpr hsat⟩

/-- If one Boolean decision function reads the exact Gaussian mass
positivity on every external CNF, the checked SAT self-reduction returns
the canonical satisfying bitstring. This is a semantic return: no
machine or polynomial evaluation bound is assumed for `D`. -/
theorem gaussianDecisionFunction_to_canonicalWitness
    (D : SAT.CNF → Bool)
    (hD : ∀ φ : SAT.CNF,
      D φ = true ↔ 0 < externalSATGaussianMass φ)
    (φ : SAT.CNF) :
    (witnessOption D φ = none ↔ ¬ φ.Satisfiable) ∧
    (φ.Satisfiable →
      SAT.CNF.eval (canonicalWitness D φ) φ = true ∧
        ∀ β : SAT.Assignment,
          SAT.CNF.eval β φ = true →
            lexLE (canonicalWitness D φ)
              ((List.range (φ.maxVar + 1)).map
                (SAT.Assignment.get β))) := by
  have hDsat : ∀ ψ : SAT.CNF, D ψ = true ↔ ψ.Satisfiable := by
    intro ψ
    exact (hD ψ).trans (externalSATGaussianMass_pos_iff ψ)
  constructor
  · exact witnessOption_none_iff D hDsat φ
  · intro hsat
    exact ⟨(witnessOption_some_correct D hDsat φ hsat).2,
      fun β hβ => canonicalWitness_lex_first D hDsat φ β hβ⟩

/-- The accepted PvNP source and two concrete SAT translation bridges
exclude a polynomial-time decider for the Gaussian positivity language.
This is conditional and inherits the still-open translation obligations.
-/
theorem gaussianSATLanguage_not_mem_P
    (CurrentizeDec CurrentizeWit : Prop)
    (translationA : SAT.L_SAT ∈ P ↔ CurrentizeDec)
    (translationB : CurrentizeDec ↔ CurrentizeWit)
    (acceptedReadout : ¬ CurrentizeWit) :
    gaussianSATLanguage ∉ P := by
  rw [gaussianSATLanguage_eq_L_SAT]
  exact SixBirdsHiddenness.PvNP.StandardComplexityReturn.sat_not_mem_P
    CurrentizeDec CurrentizeWit translationA translationB acceptedReadout

/-- Under the same accepted PvNP source and explicit translations,
no polynomial-time machine decides the actual-frame Gaussian SAT
language. The theorem uses the exact all-input language equality above;
it does not infer efficiency or a physical SAT solver from the frame.
-/
theorem externalNavierSATLanguage_not_mem_P
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ admissibleMildTimes γ hγ ν hν
        (solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a)
    (CurrentizeDec CurrentizeWit : Prop)
    (translationA : SAT.L_SAT ∈ P ↔ CurrentizeDec)
    (translationB : CurrentizeDec ↔ CurrentizeWit)
    (acceptedReadout : ¬ CurrentizeWit) :
    externalNavierSATLanguage γ hγ ν t₀ hν ht₀ τ a ∉ P := by
  rw [externalNavierSATLanguage_eq_L_SAT
    γ hγ ν t₀ hν ht₀ τ hτ hmem a ha]
  exact SixBirdsHiddenness.PvNP.StandardComplexityReturn.sat_not_mem_P
    CurrentizeDec CurrentizeWit translationA translationB acceptedReadout

/-- At some strictly positive common local mild time, the actual
Navier-frame Gaussian language is outside P under the explicit PvNP
recognition and translation assumptions. The proof selects an actual
local time; it does not grant polynomial access to the frame sum. -/
theorem exists_positive_actual_frame_language_not_mem_P
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (a : ℝ) (ha : 0 < a)
    (CurrentizeDec CurrentizeWit : Prop)
    (translationA : SAT.L_SAT ∈ P ↔ CurrentizeDec)
    (translationB : CurrentizeDec ↔ CurrentizeWit)
    (acceptedReadout : ¬ CurrentizeWit) :
    ∃ τ : ℝ, 0 < τ ∧
      externalNavierSATLanguage γ hγ ν t₀ hν ht₀ τ a ∉ P := by
  obtain ⟨τ, hτ, hmem⟩ :=
    exists_positive_common_theta_time γ hγ ν t₀ hν ht₀
  exact ⟨τ, hτ,
    externalNavierSATLanguage_not_mem_P
      γ hγ ν t₀ hν ht₀ τ hτ.le hmem a ha
      CurrentizeDec CurrentizeWit translationA translationB acceptedReadout⟩

/-- Once Translation A is fixed to the concrete uniform machine event,
the Gaussian language's conditional nonmembership requires only the
decision-to-witness bridge and the accepted recognition readout. -/
theorem gaussianSATLanguage_not_mem_P_of_witness_noncurrentization
    (WitnessCurrentize : Prop)
    (decisionToWitness :
      SixBirdsHiddenness.PvNP.ConcreteTranslationA.currentizeDecSAT ↔
        WitnessCurrentize)
    (acceptedReadout : ¬ WitnessCurrentize) :
    gaussianSATLanguage ∉ P := by
  rw [gaussianSATLanguage_eq_L_SAT]
  exact SixBirdsHiddenness.PvNP.StandardComplexityReturn.sat_not_mem_P
    SixBirdsHiddenness.PvNP.ConcreteTranslationA.currentizeDecSAT
    WitnessCurrentize
    SixBirdsHiddenness.PvNP.ConcreteTranslationA.sat_mem_P_iff_currentizeDecSAT
    decisionToWitness acceptedReadout

/-- A single positive actual Navier mild time gives the same all-input
conditional language return with concrete Translation A already proved.
The Gaussian assignment sum is still exponential. -/
theorem exists_positive_actual_frame_language_not_mem_P_of_witness_noncurrentization
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (a : ℝ) (ha : 0 < a)
    (WitnessCurrentize : Prop)
    (decisionToWitness :
      SixBirdsHiddenness.PvNP.ConcreteTranslationA.currentizeDecSAT ↔
        WitnessCurrentize)
    (acceptedReadout : ¬ WitnessCurrentize) :
    ∃ τ : ℝ, 0 < τ ∧
      externalNavierSATLanguage γ hγ ν t₀ hν ht₀ τ a ∉ P := by
  exact exists_positive_actual_frame_language_not_mem_P
    γ hγ ν t₀ hν ht₀ a ha
    SixBirdsHiddenness.PvNP.ConcreteTranslationA.currentizeDecSAT
    WitnessCurrentize
    SixBirdsHiddenness.PvNP.ConcreteTranslationA.sat_mem_P_iff_currentizeDecSAT
    decisionToWitness acceptedReadout

/-- With both pinned complexity translations now proved, the only
remaining PvNP premise in this all-input Gaussian return is the
negative currentization of the fixed raw canonical SAT witness. By
the proved Translation B equivalence, that premise has exactly the
strength of `SAT.L_SAT ∉ P`. -/
theorem gaussianSATLanguage_not_mem_P_of_raw_witness_noncurrentization
    (acceptedReadout :
      SixBirdsHiddenness.PvNP.ConcreteTranslationBRaw.rawCanonicalSATWitness
        ∉ FP) :
    gaussianSATLanguage ∉ P := by
  exact gaussianSATLanguage_not_mem_P_of_witness_noncurrentization
    (SixBirdsHiddenness.PvNP.ConcreteTranslationBRaw.rawCanonicalSATWitness
      ∈ FP)
    SixBirdsHiddenness.PvNP.ConcreteTranslationBRaw.currentizeDecSAT_iff_rawCanonicalSATWitness_mem_FP
    acceptedReadout

/-- The same single accepted PvNP premise returns through an actual
positive-time Navier frame language. The frame sum retains its
exponential assignment carrier and is not asserted efficient. -/
theorem exists_positive_actual_frame_language_not_mem_P_of_raw_witness_noncurrentization
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (a : ℝ) (ha : 0 < a)
    (acceptedReadout :
      SixBirdsHiddenness.PvNP.ConcreteTranslationBRaw.rawCanonicalSATWitness
        ∉ FP) :
    ∃ τ : ℝ, 0 < τ ∧
      externalNavierSATLanguage γ hγ ν t₀ hν ht₀ τ a ∉ P := by
  exact exists_positive_actual_frame_language_not_mem_P_of_witness_noncurrentization
    γ hγ ν t₀ hν ht₀ a ha
    (SixBirdsHiddenness.PvNP.ConcreteTranslationBRaw.rawCanonicalSATWitness
      ∈ FP)
    SixBirdsHiddenness.PvNP.ConcreteTranslationBRaw.currentizeDecSAT_iff_rawCanonicalSATWitness_mem_FP
    acceptedReadout

/-- The named Six Birds recognition source returns through the exact
all-input Gaussian SAT language once the checked search event is
admitted by the chosen `E_Q_bang` closure. Both source and admission
remain explicit mathematical premises. -/
theorem gaussianSATLanguage_not_mem_P_of_named_raw_source
    (E_Q_bang : TaggedPolynomialEvent → Prop)
    (hAdmission :
      ∀ (e : PolynomialBitEvent)
        (he : ∀ z : List Bool, e.value z = satBit z)
        (C : Nat)
        (hC : ∀ q, e.timeBound q ≤
          C * (q + 1) ^ e.degree),
        E_Q_bang (canonicalSearchEvent e he C hC))
    (Γ : SixBirdsHiddenness.PvNP.RecognitionSource.recognitionSource)
    (hContent : Γ.not_currentize_wit =
      SixBirdsHiddenness.PvNP.RecognitionSource.cslSatHiddenPredicate
        (currentizeWitRaw E_Q_bang))
    (hAccepted : Γ.not_currentize_wit) :
    gaussianSATLanguage ∉ P := by
  rw [gaussianSATLanguage_eq_L_SAT]
  exact sat_not_mem_P_of_named_recognition_source
    E_Q_bang hAdmission Γ hContent hAccepted

/-- The same accepted source and admission return through the
positive-time actual Navier-frame SAT language. The existing frame
membership and Gaussian identities supply this language equality;
the theorem does not pay the Navier strong-closure costs. -/
theorem exists_positive_actual_frame_language_not_mem_P_of_named_raw_source
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (a : ℝ) (ha : 0 < a)
    (E_Q_bang : TaggedPolynomialEvent → Prop)
    (hAdmission :
      ∀ (e : PolynomialBitEvent)
        (he : ∀ z : List Bool, e.value z = satBit z)
        (C : Nat)
        (hC : ∀ q, e.timeBound q ≤
          C * (q + 1) ^ e.degree),
        E_Q_bang (canonicalSearchEvent e he C hC))
    (Γ : SixBirdsHiddenness.PvNP.RecognitionSource.recognitionSource)
    (hContent : Γ.not_currentize_wit =
      SixBirdsHiddenness.PvNP.RecognitionSource.cslSatHiddenPredicate
        (currentizeWitRaw E_Q_bang))
    (hAccepted : Γ.not_currentize_wit) :
    ∃ τ : ℝ, 0 < τ ∧
      externalNavierSATLanguage γ hγ ν t₀ hν ht₀ τ a ∉ P := by
  have hReadout : ¬ currentizeWitRaw E_Q_bang := by
    simpa [hContent,
      SixBirdsHiddenness.PvNP.RecognitionSource.cslSatHiddenPredicate]
      using hAccepted
  exact exists_positive_actual_frame_language_not_mem_P_of_witness_noncurrentization
    γ hγ ν t₀ hν ht₀ a ha
    (currentizeWitRaw E_Q_bang)
    (currentizeDecSAT_iff_currentizeWitRaw
      E_Q_bang hAdmission) hReadout

end SixBirdsMetaMath.RHNavierPvNP.ExternalSATGaussianLanguage
