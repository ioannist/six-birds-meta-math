import Init.Data.Order.Lemmas

/-!
F14 Duality Fixity / Self-Dual Trace Confinement.

The direct theorem uses an involutive ledger, a readout anti-invariant under
a declared additive norm-preserving involution, a positive trace ledger, and
an almost-everywhere separating condition. A
vanishing trace domination ladder forces the anti-invariant ledger to zero and
confines visible mass to the fixed locus. A finite ledger realizes the laws.
-/

namespace SixBirdsMetaMath.FoundationsIV.Symmetry.DualityFixity

/-- Direct F14 data. `U` is an additive norm-preserving involution, encoding
the unitary action needed by the anti-invariance law. `muAE P` means that the complement of `P` has zero
visible measure; `integral` is integration against that same visible measure.
Only the order, trace, integral, and almost-everywhere laws used below are
required. -/
structure DirectDualityLedger (X Response Cone Scalar : Type)
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0]
    [Zero Response] [Add Response] [Neg Response] where
  J : X → X
  J_involutive : ∀ x, J (J x) = x
  psiMinus : X → Response
  U : Response → Response
  U_involutive : ∀ v, U (U v) = v
  U_zero : U 0 = 0
  U_add : ∀ v w, U (v + w) = U v + U w
  U_neg : ∀ v, U (-v) = -(U v)
  psi_antiInvariant : ∀ x, psiMinus (J x) = -(U (psiMinus x))
  normSq : Response → Scalar
  U_normSq : ∀ v, normSq (U v) = normSq v
  normSq_nonneg : ∀ v, 0 ≤ normSq v
  normSq_zero : ∀ v, normSq v = 0 → v = 0
  muAE : (X → Prop) → Prop
  muAE_inter : ∀ {P Q : X → Prop}, muAE P → muAE Q →
    muAE (fun x => P x ∧ Q x)
  muAE_mono : ∀ {P Q : X → Prop}, (∀ x, P x → Q x) → muAE P → muAE Q
  integral : (X → Scalar) → Scalar
  integral_nonneg : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ integral f
  integral_zero_ae : ∀ f, (∀ x, 0 ≤ f x) → integral f = 0 →
    muAE (fun x => f x = 0)
  coneLe : Cone → Cone → Prop
  zeroCone : Cone
  antiInvariantLedger : Cone
  ledger_positive : coneLe zeroCone antiInvariantLedger
  trace : Cone → Scalar
  trace_mono : ∀ {A B : Cone}, coneLe A B → trace A ≤ trace B
  trace_faithful : ∀ {A : Cone}, coneLe zeroCone A → trace A = 0 → A = zeroCone
  trace_identity : trace antiInvariantLedger =
    integral (fun x => normSq (psiMinus x))
  separating : muAE (fun x => psiMinus x = 0 → J x = x)

/-- Direct duality fixity: a positive anti-invariant ledger squeezed beneath
arbitrarily small trace bounds vanishes, and visible mass is confined to the
fixed locus. -/
theorem duality_fixity_direct {X Response Cone Scalar : Type}
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0]
    [Zero Response] [Add Response] [Neg Response]
    (L : DirectDualityLedger X Response Cone Scalar) (B : Nat → Cone)
    (hdom : ∀ n, L.coneLe L.antiInvariantLedger (B n))
    (hvanish : ∀ ε : Scalar, 0 < ε → ∃ n, L.trace (B n) < ε) :
    L.antiInvariantLedger = L.zeroCone ∧ L.muAE (fun x => L.J x = x) := by
  have htrace_nonneg : 0 ≤ L.trace L.antiInvariantLedger := by
    rw [L.trace_identity]
    exact L.integral_nonneg _ (fun x => L.normSq_nonneg (L.psiMinus x))
  have htrace_not_pos : ¬ 0 < L.trace L.antiInvariantLedger := by
    intro hpos
    obtain ⟨n, hn⟩ := hvanish (L.trace L.antiInvariantLedger) hpos
    exact (Std.not_lt_of_ge (L.trace_mono (hdom n))) hn
  have htrace_le_zero : L.trace L.antiInvariantLedger ≤ 0 :=
    Classical.byContradiction (fun hnotle => htrace_not_pos
      ((Std.LawfulOrderLT.lt_iff 0 (L.trace L.antiInvariantLedger)).2
        ⟨htrace_nonneg, hnotle⟩))
  have htrace_zero : L.trace L.antiInvariantLedger = 0 :=
    Std.le_antisymm htrace_le_zero htrace_nonneg
  have hledger_zero : L.antiInvariantLedger = L.zeroCone :=
    L.trace_faithful L.ledger_positive htrace_zero
  have hintegral_zero : L.integral (fun x => L.normSq (L.psiMinus x)) = 0 := by
    rw [← L.trace_identity]
    exact htrace_zero
  have hpsi_zero : L.muAE (fun x => L.psiMinus x = 0) :=
    L.muAE_mono
      (fun x hx => L.normSq_zero (L.psiMinus x) hx)
      (L.integral_zero_ae _ (fun x => L.normSq_nonneg (L.psiMinus x))
        hintegral_zero)
  refine ⟨hledger_zero, ?_⟩
  exact L.muAE_mono (fun x hx => hx.2 hx.1)
    (L.muAE_inter hpsi_zero L.separating)

/-- A three-point ledger: `none` has visible weight one and is fixed; the two
`some` points are exchanged and carry opposite nonzero readouts. -/
def finiteDualityJ : Option Bool → Option Bool
  | none => none
  | some b => some (!b)

def finiteDualityPsi : Option Bool → Int
  | none => 0
  | some false => 1
  | some true => -1

def finiteVisibleWeight : Option Bool → Nat
  | none => 1
  | some _ => 0

/-- The concrete almost-everywhere predicate really means every point of
positive visible weight. -/
theorem finite_muAE_iff_positive_weight (P : Option Bool → Prop) :
    P none ↔ ∀ x, 0 < finiteVisibleWeight x → P x := by
  constructor
  · intro h x hx
    cases x with
    | none => exact h
    | some b => simp [finiteVisibleWeight] at hx
  · intro h
    exact h none (by decide)

/-- A concrete realization of all direct F14 structural laws. The squared
norm is the square of the discrete norm, which is zero exactly at zero. -/
def finiteDirectDualityLedger : DirectDualityLedger (Option Bool) Int Nat Nat where
  J := finiteDualityJ
  J_involutive := by
    intro x
    cases x with
    | none => rfl
    | some b => cases b <;> rfl
  psiMinus := finiteDualityPsi
  U := id
  U_involutive := by intro v; rfl
  U_zero := rfl
  U_add := by intro v w; rfl
  U_neg := by intro v; rfl
  psi_antiInvariant := by
    intro x
    cases x with
    | none => rfl
    | some b => cases b <;> rfl
  normSq := fun v => if v = 0 then 0 else 1
  U_normSq := by intro v; rfl
  normSq_nonneg := by intro v; exact Nat.zero_le _
  normSq_zero := by
    intro v hv
    by_cases h : v = 0
    · exact h
    · simp [h] at hv
  muAE := fun P => P none
  muAE_inter := by
    intro P Q hP hQ
    exact ⟨hP, hQ⟩
  muAE_mono := by
    intro P Q hsub hP
    exact hsub none hP
  integral := fun f => f none
  integral_nonneg := by
    intro f hf
    exact hf none
  integral_zero_ae := by
    intro f _ hf
    exact hf
  coneLe := Nat.le
  zeroCone := 0
  antiInvariantLedger := 0
  ledger_positive := Nat.le_refl 0
  trace := id
  trace_mono := by
    intro A B h
    exact h
  trace_faithful := by
    intro A _ h
    exact h
  trace_identity := rfl
  separating := by
    intro _
    rfl

/-- The concrete ledger admits a domination ladder whose traces are below
every positive bound; hence the direct theorem's hypotheses are inhabited. -/
theorem finite_direct_duality_hypotheses :
    (∀ _n : Nat, finiteDirectDualityLedger.coneLe
      finiteDirectDualityLedger.antiInvariantLedger (0 : Nat)) ∧
    (∀ ε : Nat, 0 < ε → ∃ _n : Nat,
      finiteDirectDualityLedger.trace (0 : Nat) < ε) := by
  constructor
  · intro n
    exact Nat.le_refl 0
  · intro ε hε
    exact ⟨0, hε⟩

/-- The direct theorem applies to the concrete ledger. -/
theorem finite_direct_duality_fixity :
    finiteDirectDualityLedger.antiInvariantLedger =
      finiteDirectDualityLedger.zeroCone ∧
    finiteDirectDualityLedger.muAE
      (fun x => finiteDirectDualityLedger.J x = x) := by
  exact duality_fixity_direct finiteDirectDualityLedger (fun _ => (0 : Nat))
    finite_direct_duality_hypotheses.1 finite_direct_duality_hypotheses.2

/-- A one-dimensional rational matrix, represented by its two finite indices. -/
abbrev RationalMatrix1 := Fin 1 → Fin 1 → Rat

/-- The positive semidefinite cone of one-dimensional rational matrices. -/
def RationalPSDMatrix1 := { A : RationalMatrix1 // 0 ≤ A 0 0 }

/-- A rank-one matrix vvᵀ in one dimension. -/
def rationalRankOne (v : Rat) : RationalMatrix1 := fun _ _ => v * v

/-- Loewner order on one-dimensional positive semidefinite matrices. -/
def rationalLoewner (A B : RationalPSDMatrix1) : Prop := A.1 0 0 ≤ B.1 0 0

/-- Matrix trace in one dimension. -/
def rationalTrace (A : RationalPSDMatrix1) : Rat := A.1 0 0

private theorem rational_square_nonneg (v : Rat) : 0 ≤ v * v := by
  rcases Rat.nonneg_total v with h | h
  · exact Rat.mul_nonneg h h
  · have hh := Rat.mul_nonneg h h
    have hnegneg : -(-(v * v)) = v * v := by
      apply Rat.ext <;> simp
    rw [Rat.neg_mul, Rat.mul_neg, hnegneg] at hh
    exact hh

/-- The only positive weight is at a moving point: at a fixed point in the
zero-ledger case, and at a nonfixed point in the nonzero-ledger case. -/
def rationalVisibleWeight (active : Bool) : Option Bool → Rat
  | none => if active then 0 else 1
  | some false => if active then 1 else 0
  | some true => 0

/-- Every weight in the finite matrix ledger is nonnegative. -/
theorem rational_visible_weight_nonneg (active : Bool) (x : Option Bool) :
    0 ≤ rationalVisibleWeight active x := by
  cases active
  · cases x with
    | none => decide
    | some b => cases b <;> decide
  · cases x with
    | none => decide
    | some b => cases b <;> decide

def rationalAntiInvariantPsi : Option Bool → Rat
  | none => 0
  | some false => 1
  | some true => -1

/-- The finite weighted rank-one sum Σ μ(x) ψ(x)ψ(x)ᵀ. -/
def rationalAntiInvariantMatrix (active : Bool) : RationalMatrix1 :=
  fun i j =>
    rationalVisibleWeight active none * rationalRankOne (rationalAntiInvariantPsi none) i j +
    rationalVisibleWeight active (some false) *
      rationalRankOne (rationalAntiInvariantPsi (some false)) i j +
    rationalVisibleWeight active (some true) *
      rationalRankOne (rationalAntiInvariantPsi (some true)) i j

def rationalAntiInvariantPSD (active : Bool) : RationalPSDMatrix1 :=
  ⟨rationalAntiInvariantMatrix active, by
    cases active <;>
      simp [rationalAntiInvariantMatrix, rationalVisibleWeight,
        rationalAntiInvariantPsi, rationalRankOne, Rat.add_zero, Rat.zero_add] <;>
      decide⟩

def rationalZeroPSD : RationalPSDMatrix1 :=
  ⟨fun _ _ => 0, by decide⟩

/-- The finite integral is the three-point weighted sum. -/
def rationalFiniteIntegral (active : Bool) (f : Option Bool → Rat) : Rat :=
  rationalVisibleWeight active none * f none +
    rationalVisibleWeight active (some false) * f (some false) +
      rationalVisibleWeight active (some true) * f (some true)

/-- The trace of a one-dimensional rank-one matrix is its squared norm. -/
theorem rational_trace_rank_one (v : Rat) :
    rationalRankOne v 0 0 = v * v := by
  simp [rationalRankOne]

/-- Trace distributes over the finite weighted rank-one sum. -/
theorem rational_trace_weighted_rank_one (active : Bool) :
    rationalTrace (rationalAntiInvariantPSD active) =
      rationalFiniteIntegral active
        (fun x => rationalAntiInvariantPsi x * rationalAntiInvariantPsi x) := by
  unfold rationalTrace rationalAntiInvariantPSD rationalAntiInvariantMatrix
    rationalFiniteIntegral
  simp only [rational_trace_rank_one]

/-- One-dimensional PSD matrices satisfy trace monotonicity and trace
faithfulness; the trace of the weighted rank-one sum is the weighted
squared-norm integral. -/
def rationalPSDDualityLedger (active : Bool) :
    DirectDualityLedger (Option Bool) Rat RationalPSDMatrix1 Rat where
  J := finiteDualityJ
  J_involutive := by
    intro x
    cases x with
    | none => rfl
    | some b => cases b <;> rfl
  psiMinus := rationalAntiInvariantPsi
  U := id
  U_involutive := by intro v; rfl
  U_zero := rfl
  U_add := by intro v w; rfl
  U_neg := by intro v; rfl
  psi_antiInvariant := by
    intro x
    cases x with
    | none => rfl
    | some b => cases b <;> decide
  normSq := fun v => v * v
  U_normSq := by intro v; rfl
  normSq_nonneg := rational_square_nonneg
  normSq_zero := by
    intro v hv
    rcases Rat.mul_eq_zero.mp hv with h | h <;> exact h
  muAE := fun P => ∀ x, 0 < rationalVisibleWeight active x → P x
  muAE_inter := by
    intro P Q hP hQ x hx
    exact ⟨hP x hx, hQ x hx⟩
  muAE_mono := by
    intro P Q hsub hP x hx
    exact hsub x (hP x hx)
  integral := rationalFiniteIntegral active
  integral_nonneg := by
    intro f hf
    cases active with
    | false =>
      simpa [rationalFiniteIntegral, rationalVisibleWeight,
        Rat.add_zero, Rat.zero_add] using hf none
    | true =>
      simpa [rationalFiniteIntegral, rationalVisibleWeight,
        Rat.add_zero, Rat.zero_add] using hf (some false)
  integral_zero_ae := by
    intro f _ hf x hx
    cases active with
    | false =>
      cases x with
      | none => simpa [rationalFiniteIntegral, rationalVisibleWeight,
          Rat.add_zero, Rat.zero_add] using hf
      | some b => cases b <;> simp [rationalVisibleWeight] at hx
    | true =>
      cases x with
      | none => simp [rationalVisibleWeight] at hx
      | some b =>
        cases b with
        | false => simpa [rationalFiniteIntegral, rationalVisibleWeight,
            Rat.add_zero, Rat.zero_add] using hf
        | true => simp [rationalVisibleWeight] at hx
  coneLe := rationalLoewner
  zeroCone := rationalZeroPSD
  antiInvariantLedger := rationalAntiInvariantPSD active
  ledger_positive := by
    cases active <;>
      simp [rationalLoewner, rationalZeroPSD, rationalAntiInvariantPSD,
        rationalAntiInvariantMatrix, rationalVisibleWeight,
        rationalAntiInvariantPsi, rationalRankOne, Rat.add_zero, Rat.zero_add] <;>
      decide
  trace := rationalTrace
  trace_mono := by intro A B h; exact h
  trace_faithful := by
    intro A _ h
    apply Subtype.ext
    funext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    exact h
  trace_identity := rational_trace_weighted_rank_one active
  separating := by
    intro x hx hzero
    cases active with
    | false =>
      cases x with
      | none => rfl
      | some b => cases b <;> simp [rationalVisibleWeight] at hx
    | true =>
      cases x with
      | none => simp [rationalVisibleWeight] at hx
      | some b =>
        cases b with
        | false => simp [rationalAntiInvariantPsi] at hzero
        | true => simp [rationalVisibleWeight] at hx

/-- The positive-semidefinite ledger can actually be nonzero. -/
theorem rational_psd_ledger_nonzero :
    (rationalPSDDualityLedger true).antiInvariantLedger ≠
      (rationalPSDDualityLedger true).zeroCone := by
  intro h
  have hentry := congrArg (fun A : RationalPSDMatrix1 => A.1 0 0) h
  simp [rationalPSDDualityLedger, rationalAntiInvariantPSD,
    rationalAntiInvariantMatrix, rationalVisibleWeight,
    rationalAntiInvariantPsi, rationalRankOne, rationalZeroPSD,
    Rat.add_zero, Rat.zero_add] at hentry

/-- The direct theorem applies to the zero-defect member of this same
finite-dimensional PSD family. -/
theorem rational_psd_duality_fixity :
    (rationalPSDDualityLedger false).antiInvariantLedger =
      (rationalPSDDualityLedger false).zeroCone ∧
    (rationalPSDDualityLedger false).muAE
      (fun x => (rationalPSDDualityLedger false).J x = x) := by
  apply duality_fixity_direct (rationalPSDDualityLedger false)
    (fun _ => rationalZeroPSD)
  · intro n
    simp [rationalPSDDualityLedger, rationalLoewner, rationalZeroPSD,
      rationalAntiInvariantPSD, rationalAntiInvariantMatrix,
      rationalVisibleWeight, rationalAntiInvariantPsi, rationalRankOne,
      Rat.add_zero]
    decide
  · intro ε hε
    exact ⟨0, by simpa [rationalPSDDualityLedger, rationalTrace,
      rationalZeroPSD] using hε⟩

/-- A zero ledger has a zero readout almost everywhere and hence full-measure
fixed locus, assuming the ordinary trace normalization at the cone zero. -/
theorem duality_zero_ledger_readout_zero {X Response Cone Scalar : Type}
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0]
    [Zero Response] [Add Response] [Neg Response]
    (L : DirectDualityLedger X Response Cone Scalar)
    (htrace_zero : L.trace L.zeroCone = 0)
    (hledger_zero : L.antiInvariantLedger = L.zeroCone) :
    L.muAE (fun x => L.psiMinus x = 0) ∧ L.muAE (fun x => L.J x = x) := by
  have hintegral_zero : L.integral (fun x => L.normSq (L.psiMinus x)) = 0 := by
    rw [← L.trace_identity, hledger_zero, htrace_zero]
  have hpsi_zero : L.muAE (fun x => L.psiMinus x = 0) :=
    L.muAE_mono (fun x hx => L.normSq_zero (L.psiMinus x) hx)
      (L.integral_zero_ae _ (fun x => L.normSq_nonneg (L.psiMinus x)) hintegral_zero)
  exact ⟨hpsi_zero, L.muAE_mono (fun x hx => hx.2 hx.1)
    (L.muAE_inter hpsi_zero L.separating)⟩

/-- For identity response involution, full measure of the fixed locus forces a
zero ledger. The ordinary squared-norm and a.e.-zero integral laws are local
hypotheses because the existing abstract ledger does not include them. -/
theorem duality_identity_fixed_locus_ledger_zero {X Response Cone Scalar : Type}
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0]
    [Zero Response] [Add Response] [Neg Response]
    (L : DirectDualityLedger X Response Cone Scalar)
    (hU : L.U = id)
    (hno_two_torsion : ∀ v : Response, v = -v → v = 0)
    (hnorm_zero : L.normSq 0 = 0)
    (hintegral_zero : ∀ f : X → Scalar, (∀ x, 0 ≤ f x) →
      L.muAE (fun x => f x = 0) → L.integral f = 0)
    (hfixed : L.muAE (fun x => L.J x = x)) :
    L.antiInvariantLedger = L.zeroCone := by
  have hpsi_zero : L.muAE (fun x => L.psiMinus x = 0) := by
    apply L.muAE_mono (P := fun x => L.J x = x) _ hfixed
    intro x hx
    apply hno_two_torsion
    have hanti := L.psi_antiInvariant x
    rw [hx, hU] at hanti
    exact hanti
  have henergy_zero : L.muAE (fun x => L.normSq (L.psiMinus x) = 0) :=
    L.muAE_mono (fun x hx => by rw [hx]; exact hnorm_zero) hpsi_zero
  apply L.trace_faithful L.ledger_positive
  rw [L.trace_identity]
  exact hintegral_zero _ (fun x => L.normSq_nonneg (L.psiMinus x)) henergy_zero

/-- Identity-involution duality fixity: for separating readouts, a zero ledger
is equivalent to full visible measure of the fixed locus, under the ordinary
normalization and a.e.-zero integral laws. -/
theorem duality_fixity_identity_involution {X Response Cone Scalar : Type}
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0]
    [Zero Response] [Add Response] [Neg Response]
    (L : DirectDualityLedger X Response Cone Scalar)
    (hU : L.U = id)
    (hno_two_torsion : ∀ v : Response, v = -v → v = 0)
    (hnorm_zero : L.normSq 0 = 0)
    (htrace_zero : L.trace L.zeroCone = 0)
    (hintegral_zero : ∀ f : X → Scalar, (∀ x, 0 ≤ f x) →
      L.muAE (fun x => f x = 0) → L.integral f = 0) :
    L.antiInvariantLedger = L.zeroCone ↔ L.muAE (fun x => L.J x = x) := by
  constructor
  · intro hzero
    exact (duality_zero_ledger_readout_zero L htrace_zero hzero).2
  · intro hfixed
    exact duality_identity_fixed_locus_ledger_zero L hU hno_two_torsion
      hnorm_zero hintegral_zero hfixed

/-- Integer responses have no nonzero value equal to its negative. -/
theorem int_eq_neg_self_implies_zero (v : Int) (h : v = -v) : v = 0 := by
  cases v with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ n => exact False.elim (Int.noConfusion h)
  | negSucc n => exact False.elim (Int.noConfusion h)

/-- The concrete finite ledger satisfies the additional local laws and hence
the identity-involution equivalence is instantiated without assumptions. -/
theorem finite_duality_fixity_identity_involution :
    finiteDirectDualityLedger.antiInvariantLedger = finiteDirectDualityLedger.zeroCone ↔
      finiteDirectDualityLedger.muAE (fun x => finiteDirectDualityLedger.J x = x) := by
  apply duality_fixity_identity_involution finiteDirectDualityLedger rfl
    (fun v h => int_eq_neg_self_implies_zero v h) rfl rfl
  intro f _ hae
  exact hae

/-- A countermodel to omitting the a.e.-zero integral law: the existing fields
allow a constant-one integral even when the readout is everywhere zero. -/
def identityLedgerWithoutAEIntegralLaw :
    DirectDualityLedger (Option Bool) Int Nat Nat :=
  { finiteDirectDualityLedger with
    J := id
    J_involutive := fun _ => rfl
    psiMinus := fun _ => 0
    psi_antiInvariant := fun _ => rfl
    integral := fun _ => 1
    integral_nonneg := fun _ _ => Nat.zero_le 1
    integral_zero_ae := by
      intro f _ h
      exact False.elim (Nat.noConfusion h)
    antiInvariantLedger := 1
    ledger_positive := Nat.zero_le 1
    trace_identity := rfl
    separating := fun _ => rfl }

/-- Full-measure fixed locus alone does not force zero in the original
abstract structure, even with identity U and ordinary zero normalizations. -/
theorem identity_fixed_locus_without_ae_integral_law_counterexample :
    identityLedgerWithoutAEIntegralLaw.U = id ∧
    (∀ v : Int, v = -v → v = 0) ∧
    identityLedgerWithoutAEIntegralLaw.normSq 0 = 0 ∧
    identityLedgerWithoutAEIntegralLaw.trace identityLedgerWithoutAEIntegralLaw.zeroCone = 0 ∧
    (∀ x, identityLedgerWithoutAEIntegralLaw.psiMinus x = 0) ∧
    identityLedgerWithoutAEIntegralLaw.muAE
      (fun x => identityLedgerWithoutAEIntegralLaw.J x = x) ∧
    identityLedgerWithoutAEIntegralLaw.antiInvariantLedger ≠
      identityLedgerWithoutAEIntegralLaw.zeroCone := by
  exact ⟨rfl, int_eq_neg_self_implies_zero, rfl, rfl, fun _ => rfl, rfl, by decide⟩

/-- If the response involution has no nonzero minus-one eigenvector, full
visible measure of the fixed locus forces the ledger to zero. -/
theorem duality_no_minus_one_fixed_locus_ledger_zero {X Response Cone Scalar : Type}
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0]
    [Zero Response] [Add Response] [Neg Response]
    (L : DirectDualityLedger X Response Cone Scalar)
    (hU_no_neg : ∀ v : Response, L.U v = -v → v = 0)
    (hnorm_zero : L.normSq 0 = 0)
    (hintegral_zero : ∀ f : X → Scalar, (∀ x, 0 ≤ f x) →
      L.muAE (fun x => f x = 0) → L.integral f = 0)
    (hfixed : L.muAE (fun x => L.J x = x)) :
    L.antiInvariantLedger = L.zeroCone := by
  have hpsi_zero : L.muAE (fun x => L.psiMinus x = 0) := by
    apply L.muAE_mono (P := fun x => L.J x = x) _ hfixed
    intro x hx
    apply hU_no_neg
    have hanti := L.psi_antiInvariant x
    rw [hx] at hanti
    calc
      L.U (L.psiMinus x) = L.U (-(L.U (L.psiMinus x))) := congrArg L.U hanti
      _ = -(L.U (L.U (L.psiMinus x))) := L.U_neg _
      _ = -(L.psiMinus x) := congrArg Neg.neg (L.U_involutive _)
  have henergy_zero : L.muAE (fun x => L.normSq (L.psiMinus x) = 0) :=
    L.muAE_mono (fun x hx => by rw [hx]; exact hnorm_zero) hpsi_zero
  apply L.trace_faithful L.ledger_positive
  rw [L.trace_identity]
  exact hintegral_zero _ (fun x => L.normSq_nonneg (L.psiMinus x)) henergy_zero

/-- For separating readouts and a response involution with no nonzero minus-one
eigenvector, zero ledger is equivalent to a full-measure fixed locus. The local
zero normalizations and a.e.-zero integral law are stated explicitly. -/
theorem duality_fixity_no_minus_one_eigen {X Response Cone Scalar : Type}
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0]
    [Zero Response] [Add Response] [Neg Response]
    (L : DirectDualityLedger X Response Cone Scalar)
    (hU_no_neg : ∀ v : Response, L.U v = -v → v = 0)
    (hnorm_zero : L.normSq 0 = 0)
    (htrace_zero : L.trace L.zeroCone = 0)
    (hintegral_zero : ∀ f : X → Scalar, (∀ x, 0 ≤ f x) →
      L.muAE (fun x => f x = 0) → L.integral f = 0) :
    L.antiInvariantLedger = L.zeroCone ↔ L.muAE (fun x => L.J x = x) := by
  constructor
  · intro hzero
    exact (duality_zero_ledger_readout_zero L htrace_zero hzero).2
  · intro hfixed
    exact duality_no_minus_one_fixed_locus_ledger_zero L hU_no_neg
      hnorm_zero hintegral_zero hfixed

/-- One point of visible weight one, with J = id, U = negation, and readout one.
The integral is evaluation at that point, the squared norm is the ordinary
integer squared norm, and the positive scalar ledger has trace one. -/
def minusOneEigenDualityLedger : DirectDualityLedger Unit Int Nat Nat where
  J := id
  J_involutive := fun _ => rfl
  psiMinus := fun _ => 1
  U := fun v => -v
  U_involutive := Int.neg_neg
  U_zero := rfl
  U_add := fun _ _ => Int.neg_add
  U_neg := fun _ => rfl
  psi_antiInvariant := fun _ => rfl
  normSq := fun v => v.natAbs * v.natAbs
  U_normSq := by intro v; simp only [Int.natAbs_neg]
  normSq_nonneg := fun _ => Nat.zero_le _
  normSq_zero := by
    intro v hv
    have hz : v.natAbs = 0 := (Nat.mul_eq_zero.mp hv).elim id id
    exact Int.natAbs_eq_zero.mp hz
  muAE := fun P => P ()
  muAE_inter := fun hP hQ => ⟨hP, hQ⟩
  muAE_mono := fun hsub hP => hsub () hP
  integral := fun f => f ()
  integral_nonneg := fun _ hf => hf ()
  integral_zero_ae := fun _ _ hf => hf
  coneLe := Nat.le
  zeroCone := 0
  antiInvariantLedger := 1
  ledger_positive := Nat.zero_le 1
  trace := id
  trace_mono := fun h => h
  trace_faithful := fun _ h => h
  trace_identity := rfl
  separating := fun _ => rfl

/-- All local normalization and integration laws hold, but the fixed locus has
full measure while the ledger is nonzero: U has a nonzero minus-one eigenvector. -/
theorem duality_fixity_minus_one_eigen_counterexample :
    minusOneEigenDualityLedger.U = (fun v : Int => -v) ∧
    (∃ v : Int, v ≠ 0 ∧ minusOneEigenDualityLedger.U v = -v) ∧
    minusOneEigenDualityLedger.normSq 0 = 0 ∧
    minusOneEigenDualityLedger.trace minusOneEigenDualityLedger.zeroCone = 0 ∧
    (∀ f : Unit → Nat, (∀ x, 0 ≤ f x) →
      minusOneEigenDualityLedger.muAE (fun x => f x = 0) →
      minusOneEigenDualityLedger.integral f = 0) ∧
    minusOneEigenDualityLedger.muAE (fun x => minusOneEigenDualityLedger.J x = x) ∧
    minusOneEigenDualityLedger.antiInvariantLedger ≠
      minusOneEigenDualityLedger.zeroCone := by
  exact ⟨rfl, ⟨1, by decide, rfl⟩, rfl, rfl, fun _ _ hae => hae, rfl, by decide⟩

/-- The trace squeeze also gives an a.e.-zero readout, without any converse
integration law or normalization at the cone zero. -/
theorem duality_ladder_readout_zero {X Response Cone Scalar : Type}
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0]
    [Zero Response] [Add Response] [Neg Response]
    (L : DirectDualityLedger X Response Cone Scalar) (B : Nat → Cone)
    (hdom : ∀ n, L.coneLe L.antiInvariantLedger (B n))
    (hvanish : ∀ ε : Scalar, 0 < ε → ∃ n, L.trace (B n) < ε) :
    L.muAE (fun x => L.psiMinus x = 0) := by
  have htrace_nonneg : 0 ≤ L.trace L.antiInvariantLedger := by
    rw [L.trace_identity]
    exact L.integral_nonneg _ (fun x => L.normSq_nonneg (L.psiMinus x))
  have htrace_not_pos : ¬ 0 < L.trace L.antiInvariantLedger := by
    intro hpos
    obtain ⟨n, hn⟩ := hvanish (L.trace L.antiInvariantLedger) hpos
    exact (Std.not_lt_of_ge (L.trace_mono (hdom n))) hn
  have htrace_le_zero : L.trace L.antiInvariantLedger ≤ 0 :=
    Classical.byContradiction (fun hnotle => htrace_not_pos
      ((Std.LawfulOrderLT.lt_iff 0 (L.trace L.antiInvariantLedger)).2
        ⟨htrace_nonneg, hnotle⟩))
  have htrace_zero : L.trace L.antiInvariantLedger = 0 :=
    Std.le_antisymm htrace_le_zero htrace_nonneg
  have hintegral_zero : L.integral (fun x => L.normSq (L.psiMinus x)) = 0 :=
    L.trace_identity.symm.trans htrace_zero
  exact L.muAE_mono (fun x hx => L.normSq_zero (L.psiMinus x) hx)
    (L.integral_zero_ae _ (fun x => L.normSq_nonneg (L.psiMinus x)) hintegral_zero)

/-- Ordinary squared-norm normalization and converse a.e.-zero integration
turn an a.e.-zero readout into the constant domination ladder B_n = A_X.
Positivity and trace faithfulness supply self-domination after A_X = 0. -/
theorem duality_readout_zero_constant_ladder {X Response Cone Scalar : Type}
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0]
    [Zero Response] [Add Response] [Neg Response]
    (L : DirectDualityLedger X Response Cone Scalar)
    (hnorm_zero : L.normSq 0 = 0)
    (hintegral_zero : ∀ f : X → Scalar, (∀ x, 0 ≤ f x) →
      L.muAE (fun x => f x = 0) → L.integral f = 0)
    (hpsi_zero : L.muAE (fun x => L.psiMinus x = 0)) :
    let B : Nat → Cone := fun _ => L.antiInvariantLedger
    (∀ n, L.coneLe L.antiInvariantLedger (B n)) ∧
    (∀ ε : Scalar, 0 < ε → ∃ n, L.trace (B n) < ε) := by
  have henergy_zero : L.muAE (fun x => L.normSq (L.psiMinus x) = 0) :=
    L.muAE_mono (fun x hx => by rw [hx]; exact hnorm_zero) hpsi_zero
  have htrace_zero : L.trace L.antiInvariantLedger = 0 :=
    L.trace_identity.trans
      (hintegral_zero _ (fun x => L.normSq_nonneg (L.psiMinus x)) henergy_zero)
  have hledger_zero : L.antiInvariantLedger = L.zeroCone :=
    L.trace_faithful L.ledger_positive htrace_zero
  constructor
  · intro n
    change L.coneLe L.antiInvariantLedger L.antiInvariantLedger
    rw [hledger_zero]
    simpa only [hledger_zero] using L.ledger_positive
  · intro ε hε
    refine ⟨0, ?_⟩
    change L.trace L.antiInvariantLedger < ε
    rw [htrace_zero]
    exact hε

/-- With the two local normalization/integration laws, a trace-vanishing
domination ladder exists exactly when the anti-invariant readout is zero a.e. -/
theorem duality_ladder_exists_iff_readout_vanishes {X Response Cone Scalar : Type}
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0]
    [Zero Response] [Add Response] [Neg Response]
    (L : DirectDualityLedger X Response Cone Scalar)
    (hnorm_zero : L.normSq 0 = 0)
    (hintegral_zero : ∀ f : X → Scalar, (∀ x, 0 ≤ f x) →
      L.muAE (fun x => f x = 0) → L.integral f = 0) :
    (∃ B : Nat → Cone,
      (∀ n, L.coneLe L.antiInvariantLedger (B n)) ∧
      (∀ ε : Scalar, 0 < ε → ∃ n, L.trace (B n) < ε)) ↔
    L.muAE (fun x => L.psiMinus x = 0) := by
  constructor
  · rintro ⟨B, hdom, hvanish⟩
    exact duality_ladder_readout_zero L B hdom hvanish
  · intro hpsi_zero
    exact ⟨fun _ => L.antiInvariantLedger,
      duality_readout_zero_constant_ladder L hnorm_zero hintegral_zero hpsi_zero⟩

/-- The unaugmented ledger fields admit an everywhere-zero readout with no
trace-vanishing domination ladder: the integral can be constantly one. -/
theorem duality_ae_zero_without_ladder_counterexample :
    identityLedgerWithoutAEIntegralLaw.muAE
      (fun x => identityLedgerWithoutAEIntegralLaw.psiMinus x = 0) ∧
    ¬ ∃ B : Nat → Nat,
      (∀ n, identityLedgerWithoutAEIntegralLaw.coneLe
        identityLedgerWithoutAEIntegralLaw.antiInvariantLedger (B n)) ∧
      (∀ ε : Nat, 0 < ε → ∃ n,
        identityLedgerWithoutAEIntegralLaw.trace (B n) < ε) := by
  constructor
  · rfl
  · rintro ⟨B, hdom, hvanish⟩
    have hzero : (1 : Nat) = 0 :=
      (duality_fixity_direct identityLedgerWithoutAEIntegralLaw B hdom hvanish).1
    exact Nat.noConfusion hzero

/-- The data used by the direct trace squeeze, with an arbitrary readout and
map `J`. No anti-invariance, response involution, or involutivity of `J` is
required for this implication. -/
structure DualityFixitySqueezeData (X Response Cone Scalar : Type)
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0] [Zero Response] where
  J : X → X
  psiMinus : X → Response
  normSq : Response → Scalar
  normSq_nonneg : ∀ v, 0 ≤ normSq v
  normSq_zero : ∀ v, normSq v = 0 → v = 0
  muAE : (X → Prop) → Prop
  muAE_inter : ∀ {P Q : X → Prop}, muAE P → muAE Q →
    muAE (fun x => P x ∧ Q x)
  muAE_mono : ∀ {P Q : X → Prop}, (∀ x, P x → Q x) → muAE P → muAE Q
  integral : (X → Scalar) → Scalar
  integral_nonneg : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ integral f
  integral_zero_ae : ∀ f, (∀ x, 0 ≤ f x) → integral f = 0 →
    muAE (fun x => f x = 0)
  coneLe : Cone → Cone → Prop
  zeroCone : Cone
  antiInvariantLedger : Cone
  ledger_positive : coneLe zeroCone antiInvariantLedger
  trace : Cone → Scalar
  trace_mono : ∀ {A B : Cone}, coneLe A B → trace A ≤ trace B
  trace_faithful : ∀ {A : Cone}, coneLe zeroCone A → trace A = 0 → A = zeroCone
  trace_identity : trace antiInvariantLedger =
    integral (fun x => normSq (psiMinus x))
  separating : muAE (fun x => psiMinus x = 0 → J x = x)

/-- The direct squeeze and fixed-locus confinement do not require the
readout's anti-invariance law. -/
theorem duality_fixity_direct_without_anti_invariance
    {X Response Cone Scalar : Type}
    [LE Scalar] [LT Scalar] [Std.IsLinearOrder Scalar]
    [Std.LawfulOrderLT Scalar] [OfNat Scalar 0] [Zero Response]
    (L : DualityFixitySqueezeData X Response Cone Scalar) (B : Nat → Cone)
    (hdom : ∀ n, L.coneLe L.antiInvariantLedger (B n))
    (hvanish : ∀ ε : Scalar, 0 < ε → ∃ n, L.trace (B n) < ε) :
    L.antiInvariantLedger = L.zeroCone ∧ L.muAE (fun x => L.J x = x) := by
  have htrace_nonneg : 0 ≤ L.trace L.antiInvariantLedger := by
    rw [L.trace_identity]
    exact L.integral_nonneg _ (fun x => L.normSq_nonneg (L.psiMinus x))
  have htrace_not_pos : ¬ 0 < L.trace L.antiInvariantLedger := by
    intro hpos
    obtain ⟨n, hn⟩ := hvanish (L.trace L.antiInvariantLedger) hpos
    exact (Std.not_lt_of_ge (L.trace_mono (hdom n))) hn
  have htrace_le_zero : L.trace L.antiInvariantLedger ≤ 0 :=
    Classical.byContradiction (fun hnotle => htrace_not_pos
      ((Std.LawfulOrderLT.lt_iff 0 (L.trace L.antiInvariantLedger)).2
        ⟨htrace_nonneg, hnotle⟩))
  have htrace_zero : L.trace L.antiInvariantLedger = 0 :=
    Std.le_antisymm htrace_le_zero htrace_nonneg
  have hledger_zero : L.antiInvariantLedger = L.zeroCone :=
    L.trace_faithful L.ledger_positive htrace_zero
  have hintegral_zero : L.integral (fun x => L.normSq (L.psiMinus x)) = 0 := by
    rw [← L.trace_identity]
    exact htrace_zero
  have hpsi_zero : L.muAE (fun x => L.psiMinus x = 0) :=
    L.muAE_mono
      (fun x hx => L.normSq_zero (L.psiMinus x) hx)
      (L.integral_zero_ae _ (fun x => L.normSq_nonneg (L.psiMinus x))
        hintegral_zero)
  refine ⟨hledger_zero, ?_⟩
  exact L.muAE_mono (fun x hx => hx.2 hx.1)
    (L.muAE_inter hpsi_zero L.separating)

end SixBirdsMetaMath.FoundationsIV.Symmetry.DualityFixity
