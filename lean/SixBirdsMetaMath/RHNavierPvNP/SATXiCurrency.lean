import SixBirdsMetaMath.RHNavierPvNP.FiniteSATGaussianObservation
import SixBirdsNeedles.XiCore.HilbertKernelXi

/-!
The native SAT satisfaction indicator as a finite Hilbert state in the
same maintained XI calculus used by the RH and Navier applications.
The dimension is `2^n`, so this identity carries no efficient-readout
claim.
-/

noncomputable section
open scoped NNReal RealInnerProductSpace InnerProductSpace
namespace SixBirdsMetaMath.RHNavierPvNP.SATXiCurrency

open SixBirdsHiddenness.PvNP.CNFSemantics
open SixBirdsMetaMath.RHNavierPvNP.FiniteSATGaussianObservation
open SixBirdsNeedles.XiCore

def satState {n : Nat} (φ : Formula n) :
    EuclideanSpace ℝ (Assignment n) :=
  WithLp.toLp 2 (satIndicator φ)

def constantState (n : Nat) : EuclideanSpace ℝ (Assignment n) :=
  WithLp.toLp 2 (fun _ => (1 : ℝ))

def satMeanProbe (n : Nat) :
    EuclideanSpace ℝ (Assignment n) →L[ℝ] ℝ :=
  innerSL ℝ (constantState n)

/-- The actual unit-clause branch acts on a finite assignment state by
discarding coordinates with the wrong value at variable `i`. -/
def satUnitMask {n : Nat} (i : Fin n) (b : Bool)
    (v : EuclideanSpace ℝ (Assignment n)) :
    EuclideanSpace ℝ (Assignment n) :=
  WithLp.toLp 2 (fun w => if w i = b then v w else 0)

theorem satUnitMask_add {n : Nat} (i : Fin n) (b : Bool)
    (v w : EuclideanSpace ℝ (Assignment n)) :
    satUnitMask i b (v + w) = satUnitMask i b v + satUnitMask i b w := by
  ext α
  by_cases h : α i = b <;> simp [satUnitMask, h]

/-- Conjoining a concrete unit clause is exactly the branch mask on
the actual SAT verifier's Hilbert state. -/
theorem satState_append_unit_eq_mask {n : Nat} (φ : Formula n)
    (i : Fin n) (b : Bool) :
    satState (φ ++ [unitClause i b]) = satUnitMask i b (satState φ) := by
  ext α
  by_cases h : α i = b <;>
    simp [satState, satIndicator, satUnitMask, evalFormula,
      evalClause, evalLiteral, unitClause, h]

/-- The native/hidden XI currency gives an exact commutator law for
every SAT unit branch. It measures how imposing a clause moves state
between the native mean channel and the XI residual channel. -/
theorem satUnitMask_xi_commutator {n : Nat}
    (φ : Formula n) (i : Fin n) (b : Bool) :
    hilbertKernelXi (satMeanProbe n)
        (satUnitMask i b (satState φ)) -
      satUnitMask i b
        (hilbertKernelXi (satMeanProbe n) (satState φ)) =
      satUnitMask i b
        (hilbertNativeCurrency (satMeanProbe n) (satState φ)) -
      hilbertNativeCurrency (satMeanProbe n)
        (satUnitMask i b (satState φ)) := by
  let L := satMeanProbe n
  let v := satState φ
  let B := satUnitMask i b
  have hsplit : hilbertKernelXi L v + hilbertNativeCurrency L v = v := by
    exact L.ker.starProjection_add_starProjection_orthogonal v
  have hsplitB : hilbertKernelXi L (B v) +
      hilbertNativeCurrency L (B v) = B v := by
    exact L.ker.starProjection_add_starProjection_orthogonal (B v)
  have hmask : B (hilbertKernelXi L v) +
      B (hilbertNativeCurrency L v) = B v := by
    rw [← satUnitMask_add, hsplit]
  dsimp only [L, v, B] at hsplit hsplitB hmask ⊢
  have hbalanced := hsplitB.trans hmask.symm
  exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using hbalanced)

/-- The constant-vector probe reads the exact satisfying-assignment
count. In the RH zero-window instance the same form of probe instead
annihilates the signed displacement vector by reflection symmetry. -/
theorem satMeanProbe_eq_mass {n : Nat} (φ : Formula n) :
    satMeanProbe n (satState φ) =
      satPositiveMass φ (fun _ => 0) 0 := by
  classical
  change inner ℝ (constantState n) (satState φ) = _
  rw [constantState, satState, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, satPositiveMass, satIndicator]

theorem satMeanProbe_pos_iff_encoded_L_SAT {n : Nat} (φ : Formula n) :
    0 < satMeanProbe n (satState φ) ↔
      (SixBirdsHiddenness.PvNP.StandardSATBridge.toExternalFormula φ).encode ∈
        SAT.L_SAT := by
  rw [satMeanProbe_eq_mass]
  exact (satPositiveMass_pos_iff φ (fun _ => 0) 0).trans
    (SixBirdsHiddenness.PvNP.StandardSATBridge.encoded_mem_L_SAT_iff φ).symm

/-- A satisfiable SAT state cannot lie entirely in the kernel-XI
residual of this probe: its native witness-count channel is positive.
This differs structurally from the reflected RH displacement state. -/
theorem satState_not_fully_hidden_of_sat {n : Nat} (φ : Formula n)
    (hSat :
      (SixBirdsHiddenness.PvNP.StandardSATBridge.toExternalFormula φ).encode ∈
        SAT.L_SAT) :
    hilbertKernelXi (satMeanProbe n) (satState φ) ≠ satState φ := by
  intro hxi
  have hker : satState φ ∈ (satMeanProbe n).ker := by
    exact (Submodule.starProjection_eq_self_iff).mp hxi
  have hzero : satMeanProbe n (satState φ) = 0 := hker
  exact (ne_of_gt ((satMeanProbe_pos_iff_encoded_L_SAT φ).mpr hSat)) hzero

/-- Total SAT-state energy is the Gaussian assignment mass at zero
spectral parameter, i.e. exactly the number of satisfying assignments.
This equality retains the exponential carrier size. -/
theorem satState_norm_sq_eq_mass {n : Nat} (φ : Formula n) :
    ‖satState φ‖ ^ 2 = satPositiveMass φ (fun _ => 0) 0 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [satState, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  unfold satPositiveMass satIndicator
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases h : evalFormula w φ = true <;> simp [h]

/-- Concrete SAT XI currency: the same maintained Hilbert kernel
projection splits the actual finite SAT energy into native mean and
unobserved residual channels. Neither channel is independently bounded
or polynomial-time computable here. -/
theorem sat_xi_currency {n : Nat} (φ : Formula n) :
    satPositiveMass φ (fun _ => 0) 0 =
      ‖hilbertNativeCurrency (satMeanProbe n) (satState φ)‖ ^ 2 +
        ‖hilbertKernelXi (satMeanProbe n) (satState φ)‖ ^ 2 := by
  rw [← satState_norm_sq_eq_mass]
  exact hilbert_xi_currency (satMeanProbe n) (satState φ)

/-- The two XI channels together detect the actual encoded SAT
language. The mean channel alone and the centered residual alone can
both vanish on important boundary examples. -/
theorem sat_xi_energy_pos_iff_encoded_L_SAT {n : Nat} (φ : Formula n) :
    0 < (‖hilbertNativeCurrency (satMeanProbe n) (satState φ)‖ ^ 2 +
      ‖hilbertKernelXi (satMeanProbe n) (satState φ)‖ ^ 2) ↔
      (SixBirdsHiddenness.PvNP.StandardSATBridge.toExternalFormula φ).encode ∈
        SAT.L_SAT := by
  rw [← sat_xi_currency]
  exact (satPositiveMass_pos_iff φ (fun _ => 0) 0).trans
    (SixBirdsHiddenness.PvNP.StandardSATBridge.encoded_mem_L_SAT_iff φ).symm

/-- The mean probe's hidden subspace is exactly the orthogonal
complement of the constant assignment vector. -/
theorem satMeanProbe_ker (n : Nat) :
    (satMeanProbe n).ker = (ℝ ∙ constantState n)ᗮ := by
  ext v
  simp [satMeanProbe, Submodule.mem_orthogonal_singleton_iff_inner_right]

/-- Every assignment satisfies the empty conjunction, so its SAT
state is the constant assignment vector. -/
theorem satState_empty (n : Nat) :
    satState ([] : Formula n) = constantState n := by
  ext w
  simp [satState, constantState, satIndicator, evalFormula]

/-- The XI residual of the satisfiable empty conjunction vanishes:
its information lies entirely in the native mean channel. Hence XI
residual vanishing alone cannot decide SAT. -/
theorem sat_xi_empty_formula_zero (n : Nat) :
    hilbertKernelXi (satMeanProbe n) (satState ([] : Formula n)) = 0 := by
  rw [satState_empty]
  change (satMeanProbe n).ker.starProjection (constantState n) = 0
  apply (Submodule.starProjection_apply_eq_zero_iff
    (satMeanProbe n).ker).2
  intro u hu
  have hmean : satMeanProbe n u = 0 := hu
  have hinner : ⟪constantState n, u⟫_ℝ = 0 := by
    simpa [satMeanProbe] using hmean
  simpa [real_inner_comm] using hinner

/-- A one-variable SAT unit branch genuinely changes the XI split:
masking the all-ones state creates nonzero hidden residual even though
the original all-ones state has zero XI residual. This rules out
silently commuting SAT self-reduction with the common XI projection. -/
theorem one_variable_unit_mask_does_not_commute_with_xi :
    hilbertKernelXi (satMeanProbe 1)
        (satUnitMask (0 : Fin 1) false (satState ([] : Formula 1))) ≠
      satUnitMask (0 : Fin 1) false
        (hilbertKernelXi (satMeanProbe 1)
          (satState ([] : Formula 1))) := by
  rw [sat_xi_empty_formula_zero]
  have hmaskzero : satUnitMask (0 : Fin 1) false
      (0 : EuclideanSpace ℝ (Assignment 1)) = 0 := by
    ext w
    simp [satUnitMask]
  rw [hmaskzero]
  intro hzero
  have horth : satUnitMask (0 : Fin 1) false
      (constantState 1) ∈ (satMeanProbe 1).kerᗮ := by
    rw [satState_empty 1] at hzero
    exact (Submodule.starProjection_apply_eq_zero_iff
      (satMeanProbe 1).ker).mp hzero
  rw [satMeanProbe_ker] at horth
  have hspan : satUnitMask (0 : Fin 1) false
      (constantState 1) ∈ ℝ ∙ constantState 1 := by
    simpa using horth
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  let wFalse : Assignment 1 := fun _ => false
  let wTrue : Assignment 1 := fun _ => true
  have hf := congrArg
    (fun v : EuclideanSpace ℝ (Assignment 1) => v wFalse) hc
  have ht := congrArg
    (fun v : EuclideanSpace ℝ (Assignment 1) => v wTrue) hc
  simp [satUnitMask, constantState, wFalse, wTrue] at hf ht
  linarith

theorem satState_empty_clause (n : Nat) :
    satState ([[]] : Formula n) = 0 := by
  ext w
  simp [satState, satIndicator, evalFormula, evalClause]

/-- The empty clause is unsatisfiable and gives the zero Hilbert state;
its XI residual also vanishes. Together with the previous theorem,
this is an exact false-target control for using residual vanishing
alone as a SAT criterion. -/
theorem sat_xi_empty_clause_zero (n : Nat) :
    hilbertKernelXi (satMeanProbe n)
      (satState ([[]] : Formula n)) = 0 := by
  rw [satState_empty_clause]
  simp [hilbertKernelXi]

/-- The actual nonlinear Navier frame readout, including its Duhamel
source, is nonzero exactly when the native and XI channels of the
concrete SAT Hilbert state have positive combined energy. This is a
domain-to-domain return through the checked common Gaussian observation;
it carries no efficient-evaluation claim. -/
theorem actual_navier_sat_xi_energy_return {n : Nat}
    (φ : Formula n)
    (γ : ℝ) (hγ : 5 / 2 < γ)
    (ν t₀ : ℝ≥0) (hν : 0 < ν) (ht₀ : 0 < t₀)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hmem : ∀ i : Fin 3,
      τ ∈ SixBirdsNeedles.NSCore.admissibleMildTimes γ hγ ν hν
        (SixBirdsNeedles.NSCore.solenoidalThetaHeatState ν t₀ hν ht₀ i))
    (a : ℝ) (ha : 0 < a) :
    (satFrameTrace φ binarySATCoordinate a
        (SixBirdsNeedles.NSCore.ComplexGaussianObservations.complexFrameValue
          γ hγ ν t₀ hν ht₀ τ) +
      satFrameTrace φ binarySATCoordinate a
        (SixBirdsNeedles.NSCore.ComplexGaussianObservations.complexFrameDuhamel
          γ hγ ν t₀ hν ht₀ τ) ≠ 0) ↔
      0 < (‖hilbertNativeCurrency (satMeanProbe n) (satState φ)‖ ^ 2 +
        ‖hilbertKernelXi (satMeanProbe n) (satState φ)‖ ^ 2) := by
  exact (sat_actual_binary_frame_ne_zero_iff_encoded_L_SAT
    φ γ hγ ν t₀ hν ht₀ τ hτ hmem a ha).trans
    (sat_xi_energy_pos_iff_encoded_L_SAT φ).symm

end SixBirdsMetaMath.RHNavierPvNP.SATXiCurrency
