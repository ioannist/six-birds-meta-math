import SixBirdsMetaMath.Main.LegalQuotient

open SixBirdsMetaMath.Main.LegalQuotient

namespace SixBirdsMetaMath.Main.DualityConfinement

/-!
Main paper §7 "Duality-confinement membrane theorem".

This first subsection provides finite-rank rational-matrix models of the
paper's involutive ledger, separating anti-invariant readout, and
anti-invariant carrier membrane records.  General measure theory,
Hilbert-space integration, trace-class operators, and infinite collapse
ladders are deferred in the manifest.
-/

/-- Outer product `u v^T` of two vectors. -/
def outerProduct {m n : Nat} (u : Vec m) (v : Vec n) : Mat m n :=
  fun i j => u i * v j

/-- Finite weighted sum of `Fin n`-indexed matrices. -/
def weightedSumMat {m k : Nat}
    (n : Nat) (weight : Fin n → Rat) (M : Fin n → Mat m k) : Mat m k :=
  fun i j => sumFin n (fun x => weight x * M x i j)

/-- Antisymmetric projection `(I - Jresp) / 2`. -/
def antiInvariantProjection {y : Nat} (Jresp : Mat y y) : Mat y y :=
  matScale (1 / 2 : Rat) (matSub (identityMat y) Jresp)

/-- Anti-invariant readout `ψ_-(x) = P_- ψ(x)`. -/
def antiInvariantReadout {n y : Nat}
    (Jresp : Mat y y) (psi : Fin n → Vec y) : Fin n → Vec y :=
  fun x => matVec (antiInvariantProjection Jresp) (psi x)

/--
Anti-invariant object ledger
`A_X = Σ_x μ(x) · ψ_-(x) ψ_-(x)^T`, the finite-rank analogue of the
paper's integral `∫ ψ_-(x)ψ_-(x)^* dμ(x)`.
-/
def antiInvariantObjectLedger {n y : Nat}
    (mu : Vec n) (Jresp : Mat y y) (psi : Fin n → Vec y) : Mat y y :=
  weightedSumMat n
    (fun x => mu x)
    (fun x =>
      outerProduct (antiInvariantReadout Jresp psi x)
        (antiInvariantReadout Jresp psi x))

/-- Equivariance constraint: `ψ(J x) = Jresp · ψ(x)`. -/
def IsEquivariantReadout {n y : Nat}
    (J : Fin n → Fin n) (Jresp : Mat y y) (psi : Fin n → Vec y) : Prop :=
  ∀ x, psi (J x) = matVec Jresp (psi x)

/-- Object-side involution constraint: `J ∘ J = id`. -/
def IsObjectInvolution {n : Nat} (J : Fin n → Fin n) : Prop :=
  ∀ x, J (J x) = x

/--
Response involution constraint.  Symmetry plus `Jresp · Jresp = I`
models a finite-dimensional linear isometric involution over rationals.
-/
def IsResponseInvolution {y : Nat} (Jresp : Mat y y) : Prop :=
  matMul Jresp Jresp = identityMat y ∧ transpose Jresp = Jresp

/-- Separating anti-invariant readout on the visible support of `mu`. -/
def SeparatesFixedLocus {n y : Nat}
    (J : Fin n → Fin n) (mu : Vec n) (Jresp : Mat y y) (psi : Fin n → Vec y) : Prop :=
  ∀ x, 0 < mu x →
    (antiInvariantReadout Jresp psi x = (fun _ => 0) ↔ J x = x)

/--
Quantitative finite-support separation: one positive lower bound whose
square bounds the anti-invariant readout squared norm on off-fixed
visible points.
-/
def QuantitativelySeparatesFixedLocus {n y : Nat}
    (J : Fin n → Fin n) (mu : Vec n) (Jresp : Mat y y)
    (psi : Fin n → Vec y) (m : Rat) : Prop :=
  0 < m ∧
    ∀ x, 0 < mu x → J x ≠ x →
      m * m ≤ dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x)

/-- Anti-invariant carrier currency `K^- = L^- · C^† · (L^-)^T`. -/
def antiInvariantCarrierCurrency {e ym : Nat}
    (C : Mat e e) (Lminus : Mat ym e) : Mat ym ym :=
  matMul (matMul Lminus (diagonalPseudoInverse C)) (transpose Lminus)

/-- Anti-invariant membrane budget record: `K^- ⪯ Θ^-`. -/
def antiInvariantMembraneBudget {e ym : Nat}
    (C : Mat e e) (Lminus : Mat ym e) (ThetaMinus : Mat ym ym) : Prop :=
  loewnerLE (antiInvariantCarrierCurrency C Lminus) ThetaMinus

/--
Finite-rank trace identity:
`tr A_X = Σ_x μ(x) ||ψ_-(x)||^2`.
-/
theorem traceIdentity {n y : Nat}
    (mu : Vec n) (Jresp : Mat y y) (psi : Fin n → Vec y) :
    traceMat (antiInvariantObjectLedger mu Jresp psi) =
      sumFin n (fun x =>
        mu x * dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x)) := by
  unfold traceMat antiInvariantObjectLedger weightedSumMat outerProduct dot
  rw [sumFin_comm]
  apply congrArg
  funext x
  rw [← sumFin_mul_left]

/-- Total finite weight of off-fixed visible objects. -/
def offFixedWeight {n : Nat} (J : Fin n → Fin n) (mu : Vec n) : Rat :=
  sumFin n (fun x => if J x = x then 0 else mu x)

/--
Separation confinement in the finite-rank model.  The positivity step
from `A_X = 0` to pointwise vanishing on the positive support follows
from the trace identity and the public rational positivity library.
-/
theorem separationConfinement {n y : Nat}
    (J : Fin n → Fin n) (mu : Vec n) (Jresp : Mat y y) (psi : Fin n → Vec y)
    (hSep : SeparatesFixedLocus J mu Jresp psi)
    (hMuNonneg : ∀ x : Fin n, 0 ≤ mu x) :
    antiInvariantObjectLedger mu Jresp psi = zeroMat y y →
      ∀ x, 0 < mu x → J x = x := by
  intro hLedgerZero x hx
  apply (hSep x hx).mp
  let f : Fin n → Rat :=
    fun x => mu x * dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x)
  have hTraceZero :
      traceMat (antiInvariantObjectLedger mu Jresp psi) = 0 := by
    rw [hLedgerZero]
    unfold traceMat zeroMat
    exact sumFin_zero y
  have hSumZero : sumFin n f = 0 := by
    unfold f
    rw [← traceIdentity mu Jresp psi]
    exact hTraceZero
  have hTermNonneg : ∀ x, 0 ≤ f x := by
    intro x
    unfold f
    exact Rat.mul_nonneg (hMuNonneg x) (dot_self_nonneg (antiInvariantReadout Jresp psi x))
  have hEachZero : ∀ x, f x = 0 :=
    (sumFin_eq_zero_of_nonneg f hTermNonneg).mp hSumZero
  have hDotZero :
      dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x) = 0 := by
    have hProductZero := hEachZero x
    unfold f at hProductZero
    have hCases := (Rat.mul_eq_zero).mp hProductZero
    cases hCases with
    | inl hMuZero =>
        exact False.elim ((Rat.ne_of_gt hx) hMuZero)
    | inr hDot =>
        exact hDot
  exact (dot_self_eq_zero (antiInvariantReadout Jresp psi x)).mp hDotZero

/--
Quantitative confinement in the finite-rank model.  The Markov-style
estimate is obtained pointwise from quantitative separation, lifted
through `sumFin`, then identified with `tr A_X` by the trace identity.
-/
theorem quantitativeConfinement {n y : Nat}
    (J : Fin n → Fin n) (mu : Vec n) (Jresp : Mat y y) (psi : Fin n → Vec y) (m : Rat)
    (hQuant : QuantitativelySeparatesFixedLocus J mu Jresp psi m)
    (hMuNonneg : ∀ x : Fin n, 0 ≤ mu x) :
    m * m * offFixedWeight J mu ≤ traceMat (antiInvariantObjectLedger mu Jresp psi) := by
  let sqNorm : Fin n → Rat :=
    fun x => dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x)
  let offWeight : Fin n → Rat := fun x => if J x = x then 0 else mu x
  have hPointwise :
      ∀ x, (m * m) * offWeight x ≤ mu x * sqNorm x := by
    intro x
    unfold offWeight sqNorm
    by_cases hFixed : J x = x
    · rw [if_pos hFixed, Rat.mul_zero]
      have hScaled :
          mu x * 0 ≤ mu x *
            dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x) :=
        rat_mul_mono_nonneg (mu x) 0
          (dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x))
          (hMuNonneg x)
          (dot_self_nonneg (antiInvariantReadout Jresp psi x))
      rw [Rat.mul_zero] at hScaled
      exact hScaled
    · rw [if_neg hFixed]
      by_cases hMuZero : mu x = 0
      · rw [hMuZero, Rat.mul_zero, Rat.zero_mul]
        exact (Rat.le_refl : (0 : Rat) ≤ 0)
      · have hMuPos : 0 < mu x :=
          Rat.lt_of_le_of_ne (hMuNonneg x) (fun hZero => hMuZero hZero.symm)
        have hLower :
            m * m ≤
              dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x) :=
          hQuant.right x hMuPos hFixed
        have hScaled :
            mu x * (m * m) ≤ mu x *
              dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x) :=
          rat_mul_mono_nonneg (mu x) (m * m)
            (dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x))
            (hMuNonneg x) hLower
        calc
          (m * m) * mu x = mu x * (m * m) := by
              rw [Rat.mul_comm]
          _ ≤ mu x *
              dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x) :=
              hScaled
  have hSummed :
      sumFin n (fun x => (m * m) * offWeight x) ≤
        sumFin n (fun x => mu x * sqNorm x) :=
    sumFin_mono
      (fun x => (m * m) * offWeight x)
      (fun x => mu x * sqNorm x)
      hPointwise
  calc
    m * m * offFixedWeight J mu =
        sumFin n (fun x => (m * m) * offWeight x) := by
        unfold offFixedWeight offWeight
        rw [← sumFin_mul_left]
    _ ≤ sumFin n (fun x => mu x * sqNorm x) := hSummed
    _ =
        sumFin n (fun x =>
          mu x * dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x)) := rfl
    _ = traceMat (antiInvariantObjectLedger mu Jresp psi) := by
        rw [traceIdentity]

/-- Dot product is symmetric over rationals. -/
theorem dot_comm {n : Nat} (u v : Vec n) : dot u v = dot v u := by
  unfold dot
  apply congrArg
  funext i
  exact Rat.mul_comm (u i) (v i)

/-- Matrix-vector product by an outer product. -/
theorem matVec_outerProduct {m n : Nat} (u : Vec m) (v : Vec n) (w : Vec n) :
    matVec (outerProduct u v) w = fun i => u i * dot v w := by
  funext i
  unfold matVec outerProduct dot
  rw [
    show sumFin n (fun j => u i * v j * w j) =
        sumFin n (fun j => u i * (v j * w j)) by
      apply congrArg
      funext j
      rw [Rat.mul_assoc]]
  rw [sumFin_mul_left]

/-- Rank-one self outer products are positive semidefinite. -/
theorem posSemidef_outerProduct_self {n : Nat} (v : Vec n) :
    PositiveSemidefinite (outerProduct v v) := by
  intro u
  unfold quad
  rw [matVec_outerProduct]
  have hDotScale :
      dot u (fun i => v i * dot v u) = dot u v * dot v u := by
    unfold dot
    rw [
      show sumFin n (fun i => u i * (v i * sumFin n (fun i => v i * u i))) =
          sumFin n (fun i => (u i * v i) * sumFin n (fun i => v i * u i)) by
        apply congrArg
        funext i
        rw [Rat.mul_assoc]]
    rw [sumFin_mul_right]
  rw [hDotScale]
  rw [dot_comm u v]
  exact rat_mul_self_nonneg (dot v u)

/-- The anti-invariant object ledger is PSD when all finite weights are nonnegative. -/
theorem psd_antiInvariantObjectLedger {n y : Nat}
    (mu : Vec n) (Jresp : Mat y y) (psi : Fin n → Vec y)
    (hMuNonneg : ∀ x, 0 ≤ mu x) :
    PositiveSemidefinite (antiInvariantObjectLedger mu Jresp psi) := by
  induction n with
  | zero =>
      have hLedgerZero :
          antiInvariantObjectLedger mu Jresp psi = zeroMat y y := by
        funext i j
        unfold antiInvariantObjectLedger weightedSumMat zeroMat
        rfl
      rw [hLedgerZero]
      exact posSemidef_zero
  | succ n ih =>
      let muPrev : Vec n := fun x => mu x.castSucc
      let psiPrev : Fin n → Vec y := fun x => psi x.castSucc
      let lastReadout : Vec y := antiInvariantReadout Jresp psi (Fin.last n)
      have hSplit :
          antiInvariantObjectLedger mu Jresp psi =
            matAdd (antiInvariantObjectLedger muPrev Jresp psiPrev)
              (matScale (mu (Fin.last n)) (outerProduct lastReadout lastReadout)) := by
        funext i j
        unfold antiInvariantObjectLedger weightedSumMat matAdd matScale outerProduct
        unfold muPrev psiPrev lastReadout
        rfl
      rw [hSplit]
      have hPrev : PositiveSemidefinite (antiInvariantObjectLedger muPrev Jresp psiPrev) :=
        ih muPrev psiPrev (fun x => hMuNonneg x.castSucc)
      have hLast :
          PositiveSemidefinite (matScale (mu (Fin.last n)) (outerProduct lastReadout lastReadout)) :=
        posSemidef_scale_nonneg (mu (Fin.last n)) (outerProduct lastReadout lastReadout)
          (hMuNonneg (Fin.last n))
          (posSemidef_outerProduct_self lastReadout)
      exact posSemidef_add
        (antiInvariantObjectLedger muPrev Jresp psiPrev)
        (matScale (mu (Fin.last n)) (outerProduct lastReadout lastReadout))
        hPrev
        hLast

/-- Defected domination bridge: `A_X ⪯ K^- + E`, with `E` declared PSD. -/
def DominationBridge {y : Nat} (AX KMinus E : Mat y y) : Prop :=
  PositiveSemidefinite E ∧ loewnerLE AX (matAdd KMinus E)

/-- Matrix contraction predicate: `T^T T ⪯ I`. -/
def IsContraction {m n : Nat} (T : Mat m n) : Prop :=
  loewnerLE (matMul (transpose T) T) (identityMat n)

/-- Exact bridge factorization: `V = T W` for some contraction `T`. -/
def ExactBridgeFactorization {a b c : Nat} (V : Mat a c) (W : Mat b c) : Prop :=
  ∃ T : Mat a b, IsContraction T ∧ V = matMul T W

/--
Douglas domination, reverse direction: if `V = T W` for a contraction
`T`, then `V^T V ⪯ W^T W`.
-/
theorem douglasDominationReverse {a b c : Nat}
    (V : Mat a c) (W : Mat b c)
    (hFact : ExactBridgeFactorization V W) :
    loewnerLE (matMul (transpose V) V) (matMul (transpose W) W) := by
  rcases hFact with ⟨T, hContraction, hVeq⟩
  have hConjugated :
      loewnerLE
        (matMul (matMul (transpose W) (matMul (transpose T) T))
          (transpose (transpose W)))
        (matMul (matMul (transpose W) (identityMat b))
          (transpose (transpose W))) :=
    loewnerLE_conjugate (transpose W) (matMul (transpose T) T) (identityMat b) hContraction
  have hLeft :
      matMul (transpose V) V =
        matMul (matMul (transpose W) (matMul (transpose T) T))
          (transpose (transpose W)) := by
    calc
      matMul (transpose V) V =
          matMul (transpose (matMul T W)) (matMul T W) := by
          rw [hVeq]
      _ = matMul (matMul (transpose W) (transpose T)) (matMul T W) := by
          rw [transpose_matMul]
      _ = matMul (transpose W) (matMul (transpose T) (matMul T W)) := by
          rw [matMul_assoc (transpose W) (transpose T) (matMul T W)]
      _ = matMul (transpose W) (matMul (matMul (transpose T) T) W) := by
          rw [← matMul_assoc (transpose T) T W]
      _ = matMul (matMul (transpose W) (matMul (transpose T) T)) W := by
          rw [← matMul_assoc (transpose W) (matMul (transpose T) T) W]
      _ = matMul (matMul (transpose W) (matMul (transpose T) T))
          (transpose (transpose W)) := by
          rw [transpose_transpose]
  have hRight :
      matMul (matMul (transpose W) (identityMat b)) (transpose (transpose W)) =
        matMul (transpose W) W := by
    calc
      matMul (matMul (transpose W) (identityMat b)) (transpose (transpose W)) =
          matMul (matMul (transpose W) (identityMat b)) W := by
          rw [transpose_transpose]
      _ = matMul (transpose W) W := by
          rw [matMul_identity_right]
  rw [hLeft]
  rw [← hRight]
  exact hConjugated

/--
Duality-confinement master theorem, finite-rank single-bridge form:
a zero-trace dominating bridge confines all positive-weight visible
objects to the fixed locus.
-/
theorem dualityConfinementMaster {n y : Nat}
    (J : Fin n → Fin n) (mu : Vec n) (Jresp : Mat y y) (psi : Fin n → Vec y)
    (B : Mat y y)
    (hSep : SeparatesFixedLocus J mu Jresp psi)
    (hMuNonneg : ∀ x, 0 ≤ mu x)
    (hBridge : loewnerLE (antiInvariantObjectLedger mu Jresp psi) B)
    (hBpsd : PositiveSemidefinite B)
    (hBtraceZero : traceMat B = 0) :
    ∀ x, 0 < mu x → J x = x := by
  intro x hx
  apply (hSep x hx).mp
  let AX := antiInvariantObjectLedger mu Jresp psi
  let f : Fin n → Rat :=
    fun x => mu x * dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x)
  have hAXpsd : PositiveSemidefinite AX := by
    unfold AX
    exact psd_antiInvariantObjectLedger mu Jresp psi hMuNonneg
  have hAXtraceNonneg : 0 ≤ traceMat AX := psd_trace_nonneg AX hAXpsd
  have hBtraceNonnegAsZero : 0 ≤ (0 : Rat) := by
    have hBtraceNonneg : 0 ≤ traceMat B := psd_trace_nonneg B hBpsd
    rw [hBtraceZero] at hBtraceNonneg
    exact hBtraceNonneg
  have hAXtraceLeB : traceMat AX ≤ traceMat B := by
    unfold AX
    exact loewnerLE_traceMat_mono (antiInvariantObjectLedger mu Jresp psi) B hBridge
  have hAXtraceNonpos : traceMat AX ≤ 0 := by
    rw [hBtraceZero] at hAXtraceLeB
    exact hAXtraceLeB
  have hAXtraceZero : traceMat AX = 0 :=
    Rat.le_antisymm hAXtraceNonpos (Rat.le_trans hBtraceNonnegAsZero hAXtraceNonneg)
  have hSumZero : sumFin n f = 0 := by
    unfold f AX at hAXtraceZero
    rw [← traceIdentity mu Jresp psi]
    exact hAXtraceZero
  have hTermNonneg : ∀ x, 0 ≤ f x := by
    intro x
    unfold f
    exact Rat.mul_nonneg (hMuNonneg x) (dot_self_nonneg (antiInvariantReadout Jresp psi x))
  have hEachZero : ∀ x, f x = 0 :=
    (sumFin_eq_zero_of_nonneg f hTermNonneg).mp hSumZero
  have hDotZero :
      dot (antiInvariantReadout Jresp psi x) (antiInvariantReadout Jresp psi x) = 0 := by
    have hProductZero := hEachZero x
    unfold f at hProductZero
    have hCases := (Rat.mul_eq_zero).mp hProductZero
    cases hCases with
    | inl hMuZero =>
        exact False.elim ((Rat.ne_of_gt hx) hMuZero)
    | inr hDot =>
        exact hDot
  exact (dot_self_eq_zero (antiInvariantReadout Jresp psi x)).mp hDotZero

/--
Single-record exhaustive moving ledger relation in the finite-rank
model: `A_X ⪯ ι · A_window · ι^T + T`, with `T` declared PSD.
-/
def ExhaustiveMovingLedger {k y : Nat}
    (AX : Mat y y) (iota : Mat y k) (Awindow : Mat k k) (T : Mat y y) : Prop :=
  PositiveSemidefinite T ∧
    loewnerLE AX (matAdd (matMul (matMul iota Awindow) (transpose iota)) T)

/--
Exhaustive ledger squeeze, finite-rank single-record form.  A window
bound and a zero combined trace produce the same finite-support
confinement conclusion as the domination master theorem.
-/
theorem exhaustiveLedgerSqueeze {n y k : Nat}
    (J : Fin n → Fin n) (mu : Vec n) (Jresp : Mat y y) (psi : Fin n → Vec y)
    (iota : Mat y k) (Awindow : Mat k k) (T : Mat y y) (B : Mat k k)
    (hSep : SeparatesFixedLocus J mu Jresp psi)
    (hMuNonneg : ∀ x, 0 ≤ mu x)
    (hExhaustive :
      ExhaustiveMovingLedger
        (antiInvariantObjectLedger mu Jresp psi) iota Awindow T)
    (hWindowBound : loewnerLE Awindow B)
    (hBpsd : PositiveSemidefinite B)
    (hVanishingTrace :
      traceMat (matMul (matMul iota B) (transpose iota)) + traceMat T = 0) :
    ∀ x, 0 < mu x → J x = x := by
  let transportedWindow := matMul (matMul iota Awindow) (transpose iota)
  let transportedBound := matMul (matMul iota B) (transpose iota)
  let Bcombined := matAdd transportedBound T
  have hTransportedWindowBound :
      loewnerLE transportedWindow transportedBound := by
    unfold transportedWindow transportedBound
    exact loewnerLE_conjugate iota Awindow B hWindowBound
  have hTailRefl : loewnerLE T T := loewnerLE_refl T
  have hMovedBound :
      loewnerLE (matAdd transportedWindow T) Bcombined := by
    unfold Bcombined
    exact loewnerLE_add_mono transportedWindow transportedBound T T
      hTransportedWindowBound
      hTailRefl
  have hBridgeCombined :
      loewnerLE (antiInvariantObjectLedger mu Jresp psi) Bcombined := by
    unfold ExhaustiveMovingLedger at hExhaustive
    exact loewnerLE_trans
      (antiInvariantObjectLedger mu Jresp psi)
      (matAdd transportedWindow T)
      Bcombined
      hExhaustive.right
      hMovedBound
  have hTransportedBoundPsd : PositiveSemidefinite transportedBound := by
    unfold transportedBound
    exact posSemidef_conjugate iota B hBpsd
  have hCombinedPsd : PositiveSemidefinite Bcombined := by
    unfold Bcombined
    exact posSemidef_add transportedBound T hTransportedBoundPsd hExhaustive.left
  have hCombinedTraceZero : traceMat Bcombined = 0 := by
    unfold Bcombined transportedBound
    rw [traceMat_add]
    exact hVanishingTrace
  exact dualityConfinementMaster J mu Jresp psi Bcombined
    hSep
    hMuNonneg
    hBridgeCombined
    hCombinedPsd
    hCombinedTraceZero

/--
General obstruction budget operator
`B(t) = (1+t)(K + E_src) + (1+1/t)E_br`.
-/
def obstructionBudget {y : Nat}
    (t : Rat) (K E_src E_br : Mat y y) : Mat y y :=
  matAdd
    (matScale (1 + t) (matAdd K E_src))
    (matScale (1 + 1 / t) E_br)

/--
Defected duality-confinement record: source and bridge defects are PSD,
`t` is positive, and the object ledger is bounded by the obstruction
budget.
-/
def DefectedDualityRecord {y : Nat}
    (AX K E_src E_br : Mat y y) (t : Rat) : Prop :=
  0 < t ∧
    PositiveSemidefinite E_src ∧
    PositiveSemidefinite E_br ∧
    loewnerLE AX (obstructionBudget t K E_src E_br)

/--
Per-`t` algebraic trace formula for the obstruction budget.  The
square-root infimum and sequence convergence clauses of the paper
proposition are deferred in the manifest.
-/
theorem optimizedTraceBudget {y : Nat}
    (t : Rat) (ht : 0 < t) (K E_src E_br : Mat y y) :
    traceMat (obstructionBudget t K E_src E_br) =
      (1 + t) * (traceMat K + traceMat E_src) +
        (1 + 1 / t) * traceMat E_br := by
  -- `ht` keeps the trace formula on the paper's intended domain `t > 0`.
  have _htNonzero : t ≠ 0 := Rat.ne_of_gt ht
  unfold obstructionBudget
  rw [traceMat_add]
  rw [traceMat_scale]
  rw [traceMat_scale]
  rw [traceMat_add]

end SixBirdsMetaMath.Main.DualityConfinement
