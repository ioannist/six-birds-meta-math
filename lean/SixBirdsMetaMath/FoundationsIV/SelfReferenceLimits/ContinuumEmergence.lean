import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F43 Continuum Emergence.

A continuum layer is modeled as a stable completed limit quotient for a tower,
together with uniform target descent or explicitly statused residual control.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.ContinuumEmergence

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- Coherence of an abstract same-carrier approximation tower. The comparison
map `compare m n` sends stage `m` data to stage `n` data. -/
def TowerCoherent {Index Approx : Type}
    (compare : Index → Index → Approx → Approx) : Prop :=
  (∀ n x, compare n n x = x) ∧
    ∀ k m n x, compare m n (compare k m x) = compare k n x

/-- A completed limit quotient has projections compatible with the tower
comparisons. -/
def ProjectionCoherent {Index Approx Limit : Type}
    (compare : Index → Index → Approx → Approx)
    (projection : Index → Limit → Approx) : Prop :=
  ∀ m n x, compare m n (projection m x) = projection n x

/-- Stable limit quotient: coherence, completion, presentation invariance, and
statused passage of the declared structures. -/
def StableLimitQuotient {Index Approx Limit : Type}
    (compare : Index → Index → Approx → Approx)
    (projection : Index → Limit → Approx)
    (completionDeclared presentationInvariant structuresPassOrStatused : Prop) :
    Prop :=
  TowerCoherent compare ∧
    ProjectionCoherent compare projection ∧
      completionDeclared ∧ presentationInvariant ∧ structuresPassOrStatused

/-- Every declared finite test is covered at some tower index. -/
def PaperCofinal {Index Test : Type} (covers : Index → Test → Prop) : Prop :=
  ∀ test, ∃ index, covers index test

/-- Coherence of the paper's inverse comparison maps `A_j → A_i` for `i ≤ j`. -/
def PaperTowerCoherent {Index Approx : Type}
    (le : Index → Index → Prop) (refl : ∀ i, le i i)
    (trans : ∀ {i j k}, le i j → le j k → le i k)
    (compare : ∀ i j, le i j → Approx → Approx) : Prop :=
  (∀ i x, compare i i (refl i) x = x) ∧
    ∀ i j k (hij : le i j) (hjk : le j k) x,
      compare i k (trans hij hjk) x =
        compare i j hij (compare j k hjk x)

/-- The compatibility equation `φ_ij ∘ p_j = p_i` used in the F43 proof. -/
def PaperProjectionCoherent {Index Approx Limit : Type}
    (le : Index → Index → Prop)
    (compare : ∀ i j, le i j → Approx → Approx)
    (projection : Index → Limit → Approx) : Prop :=
  ∀ i j (hij : le i j) x,
    compare i j hij (projection j x) = projection i x

/-- A target readout on the candidate limit agrees with every stage readout. -/
def PaperStageReadoutCompatible {Index Approx Limit Recon : Type}
    (projection : Index → Limit → Approx)
    (stageReadout : Index → Approx → Recon)
    (target : Limit → Recon) : Prop :=
  ∀ index x, stageReadout index (projection index x) = target x

/-- Stage readouts agree with the inverse comparison maps. -/
def PaperStageReadoutCoherent {Index Approx Recon : Type}
    (le : Index → Index → Prop)
    (compare : ∀ i j, le i j → Approx → Approx)
    (stageReadout : Index → Approx → Recon) : Prop :=
  ∀ i j (hij : le i j) a,
    stageReadout i (compare i j hij a) = stageReadout j a

/-- The candidate target has no split pair along the limit quotient. -/
def PaperLimitTargetFiberConstant {Limit Q Recon : Type}
    (limitQuotient : Limit → Q) (target : Limit → Recon) : Prop :=
  ∀ x y, limitQuotient x = limitQuotient y → target x = target y

/-- Compatibility of a limit readout with every projection, relative to the
declared stage readouts. -/
def PaperLimitReadoutCompatible {Index Approx Limit Q Recon : Type}
    (projection : Index → Limit → Approx) (limitQuotient : Limit → Q)
    (stageReadout : Index → Approx → Recon) (readout : Q → Recon) : Prop :=
  ∀ index x, readout (limitQuotient x) =
    stageReadout index (projection index x)

/-- The four clauses displayed in paper F43. This predicate records the
criterion; it does not construct an inverse limit from those clauses. -/
def PaperStableLimitQuotient
    {Index Test Approx Limit Q Recon Residual : Type}
    (le : Index → Index → Prop) (refl : ∀ i, le i i)
    (trans : ∀ {i j k}, le i j → le j k → le i k)
    (compare : ∀ i j, le i j → Approx → Approx)
    (covers : Index → Test → Prop)
    (residual : Index → Residual)
    (Vanishes : (Index → Residual) → Prop)
    (projection : Index → Limit → Approx)
    (limitQuotient : Limit → Q)
    (stageReadout : Index → Approx → Recon) : Prop :=
  PaperTowerCoherent le refl trans compare ∧
    PaperCofinal covers ∧ Vanishes residual ∧
    ∃ readout : Q → Recon,
      PaperLimitReadoutCompatible projection limitQuotient stageReadout readout

/-- Uniform target descent is represented by a declared residual family and a
declared convergence predicate. -/
def UniformTargetDescent {Index Residual : Type} (residual : Index → Residual)
    (Vanishes : (Index → Residual) → Prop) : Prop :=
  Vanishes residual

/-- Budgeted continuum descent: residuals stay inside a declared tolerance. -/
def BudgetedContinuum {Index Residual Budget : Type} (residual : Index → Residual)
    (budget : Budget) (WithinBudget : Residual → Budget → Prop) : Prop :=
  ∀ n, WithinBudget (residual n) budget

/-- Pointwise continuum status is weaker than uniform target descent. -/
def PointwiseContinuum {Point Target : Type} (approximants : Point → Target)
    (limit : Point → Target) (PointwiseConverges : (Point → Target) → (Point → Target) → Prop) :
    Prop :=
  PointwiseConverges approximants limit

/-- Weak continuum status is descent only through a declared test/probe family. -/
def WeakContinuum {Probe Result : Type} (readout : Probe → Result)
    (TestFamilyAccepts : (Probe → Result) → Prop) : Prop :=
  TestFamilyAccepts readout

/-- Renormalized continuum: raw targets are first transformed by declared
renormalization maps before residual control is asserted. -/
def RenormalizedContinuum {Index Raw Renormalized Residual : Type}
    (raw : Index → Raw) (renormalize : Index → Raw → Renormalized)
    (residual : Index → Residual) (Vanishes : (Index → Residual) → Prop) :
    Prop :=
  (∀ n, ∃ value, renormalize n (raw n) = value) ∧ Vanishes residual

/-- Probabilistic continuum: finite stochastic/fiber laws converge to a stable
continuum law under a declared convergence predicate. -/
def ProbabilisticContinuum {Index Law : Type} (law : Index → Law)
    (limitLaw : Law) (Converges : (Index → Law) → Law → Prop) : Prop :=
  Converges law limitLaw

/-- A continuum layer for a target family is a stable limit quotient plus
uniform target descent. -/
def ContinuumLayer {Index Approx Limit Residual : Type}
    (compare : Index → Index → Approx → Approx)
    (projection : Index → Limit → Approx)
    (completionDeclared presentationInvariant structuresPassOrStatused : Prop)
    (residual : Index → Residual)
    (Vanishes : (Index → Residual) → Prop) : Prop :=
  StableLimitQuotient compare projection completionDeclared presentationInvariant
      structuresPassOrStatused ∧
    UniformTargetDescent residual Vanishes

/-- Thread/limit target descent: a target assigned to approximating threads is
well-defined on the completed quotient. -/
def ContinuumTargetDescends {Thread Limit Target : Type} (limitMap : Thread → Limit)
    (targetLimit : Thread → Target) : Prop :=
  Descends limitMap (fun thread : Thread => thread) targetLimit

/-- Thread split-pair obstruction for a continuum target. -/
def ContinuumTargetObstruction {Thread Limit Target : Type}
    (limitMap : Thread → Limit) (targetLimit : Thread → Target) :
    (Thread × Thread) → Prop :=
  splitPairObstruction limitMap (fun thread : Thread => thread) targetLimit

/-- No thread split-pair obstruction is present. -/
def ContinuumTargetObstructionEmpty {Thread Limit Target : Type}
    (limitMap : Thread → Limit) (targetLimit : Thread → Target) : Prop :=
  ObstructionEmpty (ContinuumTargetObstruction limitMap targetLimit)

/-- Exact continuum dynamics: the continuum update descends through the limit
quotient of threads. -/
def ContinuumDynamicsDescends {Thread Limit : Type} (limitMap : Thread → Limit)
    (threadUpdate : Thread → Thread) : Prop :=
  Descends limitMap threadUpdate limitMap

/-- Dynamic continuum obstruction. -/
def ContinuumDynamicsObstruction {Thread Limit : Type} (limitMap : Thread → Limit)
    (threadUpdate : Thread → Thread) : (Thread × Thread) → Prop :=
  splitPairObstruction limitMap threadUpdate limitMap

/-- No dynamic continuum obstruction is present. -/
def ContinuumDynamicsObstructionEmpty {Thread Limit : Type}
    (limitMap : Thread → Limit) (threadUpdate : Thread → Thread) : Prop :=
  ObstructionEmpty (ContinuumDynamicsObstruction limitMap threadUpdate)

/-- Static continuum only: target descent is present but dynamics does not
descend. -/
def StaticContinuumOnly {Thread Limit Target : Type} (limitMap : Thread → Limit)
    (targetLimit : Thread → Target) (threadUpdate : Thread → Thread) : Prop :=
  ContinuumTargetDescends limitMap targetLimit ∧
    ¬ ContinuumDynamicsDescends limitMap threadUpdate

/-- Source status vocabulary for continuum claims. -/
inductive ContinuumStatus where
  | exactContinuum
  | continuumObjectTargetFailure
  | pointwiseContinuum
  | weakContinuum
  | renormalizedContinuum
  | probabilisticContinuum
  | budgetedContinuum
  | asymptoticContinuum
  | localContinuum
  | globalContinuumObstructed
  | singularContinuumBoundary
  | pathDependentContinuum
  | presentationDependentContinuum
  | protocolContinuumArtifact
  | continuumModuli
  | towerNoncompletion
  | continuumOverread
  | staticContinuumOnly
  | smoothContinuum
deriving DecidableEq

/-- Meaning assignment for the F43 continuum status vocabulary. -/
def ContinuumStatusHolds (exact targetFailure pointwise weak renormalized probabilistic
    budgeted asymptotic localOnly globalObstructed singularBoundary pathDependent
    presentationDependent protocolArtifact moduli noncompletion overread staticOnly
    smooth : Prop) : ContinuumStatus → Prop
  | ContinuumStatus.exactContinuum => exact
  | ContinuumStatus.continuumObjectTargetFailure => targetFailure
  | ContinuumStatus.pointwiseContinuum => pointwise
  | ContinuumStatus.weakContinuum => weak
  | ContinuumStatus.renormalizedContinuum => renormalized
  | ContinuumStatus.probabilisticContinuum => probabilistic
  | ContinuumStatus.budgetedContinuum => budgeted
  | ContinuumStatus.asymptoticContinuum => asymptotic
  | ContinuumStatus.localContinuum => localOnly
  | ContinuumStatus.globalContinuumObstructed => globalObstructed
  | ContinuumStatus.singularContinuumBoundary => singularBoundary
  | ContinuumStatus.pathDependentContinuum => pathDependent
  | ContinuumStatus.presentationDependentContinuum => presentationDependent
  | ContinuumStatus.protocolContinuumArtifact => protocolArtifact
  | ContinuumStatus.continuumModuli => moduli
  | ContinuumStatus.towerNoncompletion => noncompletion
  | ContinuumStatus.continuumOverread => overread
  | ContinuumStatus.staticContinuumOnly => staticOnly
  | ContinuumStatus.smoothContinuum => smooth

/-- Stable limit quotient is exactly the declared coherence/completion gates. -/
theorem stable_limit_quotient_iff_gates {Index Approx Limit : Type}
    (compare : Index → Index → Approx → Approx)
    (projection : Index → Limit → Approx)
    (completionDeclared presentationInvariant structuresPassOrStatused : Prop) :
    StableLimitQuotient compare projection completionDeclared presentationInvariant
        structuresPassOrStatused ↔
      TowerCoherent compare ∧
        ProjectionCoherent compare projection ∧
          completionDeclared ∧ presentationInvariant ∧ structuresPassOrStatused := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Uniform target descent is the declared residual convergence predicate. -/
theorem uniform_target_descent_iff_residual_vanishes {Index Residual : Type}
    (residual : Index → Residual) (Vanishes : (Index → Residual) → Prop) :
    UniformTargetDescent residual Vanishes ↔ Vanishes residual := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- A continuum target descends to the completed quotient iff the thread
split-pair obstruction is empty. -/
theorem continuum_target_descends_iff_no_obstruction {Thread Limit Target : Type}
    (limitMap : Thread → Limit) (targetLimit : Thread → Target)
    (hlimitMap : Function.Surjective limitMap) :
    ContinuumTargetDescends limitMap targetLimit ↔
      ContinuumTargetObstructionEmpty limitMap targetLimit :=
  descent_repair_normal_form limitMap (fun thread : Thread => thread)
    targetLimit hlimitMap

/-- Continuum dynamics descends iff the dynamic split-pair obstruction is
empty. -/
theorem continuum_dynamics_descends_iff_no_obstruction {Thread Limit : Type}
    (limitMap : Thread → Limit) (threadUpdate : Thread → Thread)
    (hlimitMap : Function.Surjective limitMap) :
    ContinuumDynamicsDescends limitMap threadUpdate ↔
      ContinuumDynamicsObstructionEmpty limitMap threadUpdate :=
  descent_repair_normal_form limitMap threadUpdate limitMap hlimitMap

/-- Exact continuum emergence is stable limit quotient plus uniform target
descent. -/
theorem continuum_layer_iff_stable_and_uniform {Index Approx Limit Residual : Type}
    (compare : Index → Index → Approx → Approx)
    (projection : Index → Limit → Approx)
    (completionDeclared presentationInvariant structuresPassOrStatused : Prop)
    (residual : Index → Residual)
    (Vanishes : (Index → Residual) → Prop) :
    ContinuumLayer compare projection completionDeclared presentationInvariant
        structuresPassOrStatused residual Vanishes ↔
      StableLimitQuotient compare projection completionDeclared presentationInvariant
          structuresPassOrStatused ∧
        UniformTargetDescent residual Vanishes := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
Continuum Emergence Normal Form. A tower forms a continuum layer for the
declared target family exactly when it has a stable completed limit quotient
and the target residuals vanish uniformly; thread targets and dynamics are
well-defined on the limit quotient exactly when their split-pair obstructions
are empty.
-/
theorem continuum_emergence {Index Approx Limit Residual Thread Target : Type}
    (compare : Index → Index → Approx → Approx)
    (projection : Index → Limit → Approx)
    (completionDeclared presentationInvariant structuresPassOrStatused : Prop)
    (residual : Index → Residual)
    (Vanishes : (Index → Residual) → Prop)
    (limitMap : Thread → Limit) (targetLimit : Thread → Target)
    (threadUpdate : Thread → Thread)
    (hlimitMap : Function.Surjective limitMap) :
    (StableLimitQuotient compare projection completionDeclared presentationInvariant
        structuresPassOrStatused ↔
      TowerCoherent compare ∧
        ProjectionCoherent compare projection ∧
          completionDeclared ∧ presentationInvariant ∧ structuresPassOrStatused) ∧
      (UniformTargetDescent residual Vanishes ↔ Vanishes residual) ∧
        (ContinuumLayer compare projection completionDeclared presentationInvariant
            structuresPassOrStatused residual Vanishes ↔
          StableLimitQuotient compare projection completionDeclared presentationInvariant
              structuresPassOrStatused ∧
            UniformTargetDescent residual Vanishes) ∧
          (ContinuumTargetDescends limitMap targetLimit ↔
            ContinuumTargetObstructionEmpty limitMap targetLimit) ∧
            (ContinuumDynamicsDescends limitMap threadUpdate ↔
              ContinuumDynamicsObstructionEmpty limitMap threadUpdate) := by
  exact ⟨stable_limit_quotient_iff_gates compare projection completionDeclared
      presentationInvariant structuresPassOrStatused,
    uniform_target_descent_iff_residual_vanishes residual Vanishes,
    continuum_layer_iff_stable_and_uniform compare projection completionDeclared
      presentationInvariant structuresPassOrStatused residual Vanishes,
    continuum_target_descends_iff_no_obstruction limitMap targetLimit hlimitMap,
    continuum_dynamics_descends_iff_no_obstruction limitMap threadUpdate hlimitMap⟩

/-- Paper F43's displayed equivalence for a directed tower and surjective
candidate limit quotient. The four clauses are represented explicitly; the
implication is definitional until a separate completion theorem is supplied. -/
theorem continuum_emergence_paper_criterion
    {Index Test Approx Limit Q Recon Residual : Type}
    (le : Index → Index → Prop) (refl : ∀ i, le i i)
    (trans : ∀ {i j k}, le i j → le j k → le i k)
    (directed : ∀ i j : Index, ∃ k, le i k ∧ le j k)
    (compare : ∀ i j, le i j → Approx → Approx)
    (projection : Index → Limit → Approx)
    (limitQuotient : Limit → Q)
    (hquotient : Function.Surjective limitQuotient)
    (covers : Index → Test → Prop)
    (residual : Index → Residual) (Vanishes : (Index → Residual) → Prop)
    (stageReadout : Index → Approx → Recon) :
    PaperStableLimitQuotient le refl trans compare covers residual Vanishes
        projection limitQuotient stageReadout ↔
      PaperTowerCoherent le refl trans compare ∧
        PaperCofinal covers ∧ Vanishes residual ∧
        ∃ readout : Q → Recon,
          PaperLimitReadoutCompatible projection limitQuotient
            stageReadout readout := by
  let _ := directed
  let _ := hquotient
  rfl

/-- A nontrivial F43 descent bridge. Projection coherence is an explicit
premise; the new content constructs the quotient readout from fiber
constancy and surjectivity, then proves compatibility at every stage. This
does not construct the completed limit carrier itself. -/
theorem continuum_limit_readout_from_coherent_tower
    {Index Test Approx Limit Q Recon Residual : Type}
    (le : Index → Index → Prop) (refl : ∀ i, le i i)
    (trans : ∀ {i j k}, le i j → le j k → le i k)
    (directed : ∀ i j : Index, ∃ k, le i k ∧ le j k)
    (compare : ∀ i j, le i j → Approx → Approx)
    (projection : Index → Limit → Approx)
    (limitQuotient : Limit → Q) (hquotient : Function.Surjective limitQuotient)
    (covers : Index → Test → Prop)
    (residual : Index → Residual) (Vanishes : (Index → Residual) → Prop)
    (stageReadout : Index → Approx → Recon) (target : Limit → Recon)
    (base : Index)
    (htower : PaperTowerCoherent le refl trans compare)
    (hprojection : PaperProjectionCoherent le compare projection)
    (hcofinal : PaperCofinal covers) (hvanishes : Vanishes residual)
    (hreadout : PaperStageReadoutCoherent le compare stageReadout)
    (hbase : ∀ x, stageReadout base (projection base x) = target x)
    (hfibers : PaperLimitTargetFiberConstant limitQuotient target) :
    PaperProjectionCoherent le compare projection ∧
      PaperStableLimitQuotient le refl trans compare covers residual Vanishes
        projection limitQuotient stageReadout := by
  have hstage : PaperStageReadoutCompatible projection stageReadout target := by
    intro index x
    rcases directed base index with ⟨upper, hbaseUpper, hindexUpper⟩
    calc
      stageReadout index (projection index x) =
          stageReadout index (compare index upper hindexUpper
            (projection upper x)) := by rw [hprojection index upper hindexUpper x]
      _ = stageReadout upper (projection upper x) :=
        hreadout index upper hindexUpper (projection upper x)
      _ = stageReadout base (compare base upper hbaseUpper
            (projection upper x)) :=
        (hreadout base upper hbaseUpper (projection upper x)).symm
      _ = stageReadout base (projection base x) := by
        rw [hprojection base upper hbaseUpper x]
      _ = target x := hbase x
  have hdesc : Descends limitQuotient (fun x : Limit => x) target := by
    apply (descent_repair_normal_form limitQuotient
      (fun x : Limit => x) target hquotient).2
    intro pair hsplit
    exact hsplit.2 (hfibers pair.1 pair.2 hsplit.1)
  rcases hdesc with ⟨readout, hreadout⟩
  refine ⟨hprojection, htower, hcofinal, hvanishes, readout, ?_⟩
  intro index x
  have hx := congrFun hreadout x
  calc
    readout (limitQuotient x) = target x := hx
    _ = stageReadout index (projection index x) := (hstage index x).symm

/-- The paper's stable-limit criterion with genuinely index-dependent stages
and residuals. -/
def PaperStableLimitQuotientDependent
    {Index Test Limit Q Recon : Type}
    {Approx Residual : Index → Type}
    (le : Index → Index → Prop) (refl : ∀ i, le i i)
    (trans : ∀ {i j k}, le i j → le j k → le i k)
    (compare : ∀ i j, le i j → Approx j → Approx i)
    (covers : Index → Test → Prop)
    (residual : ∀ i, Residual i)
    (Vanishes : (∀ i, Residual i) → Prop)
    (projection : ∀ i, Limit → Approx i)
    (limitQuotient : Limit → Q)
    (stageReadout : ∀ i, Approx i → Recon) : Prop :=
  ((∀ i x, compare i i (refl i) x = x) ∧
    ∀ i j k (hij : le i j) (hjk : le j k) x,
      compare i k (trans hij hjk) x =
        compare i j hij (compare j k hjk x)) ∧
  PaperCofinal covers ∧ Vanishes residual ∧
  ∃ readout : Q → Recon,
    ∀ i x, readout (limitQuotient x) =
      stageReadout i (projection i x)

/-- F43 for a tower whose carrier and residual type may change at every index. -/
theorem continuum_limit_readout_dependent_tower
    {Index Test Limit Q Recon : Type}
    {Approx Residual : Index → Type}
    (le : Index → Index → Prop) (refl : ∀ i, le i i)
    (trans : ∀ {i j k}, le i j → le j k → le i k)
    (directed : ∀ i j : Index, ∃ k, le i k ∧ le j k)
    (compare : ∀ i j, le i j → Approx j → Approx i)
    (projection : ∀ i, Limit → Approx i)
    (limitQuotient : Limit → Q) (hquotient : Function.Surjective limitQuotient)
    (covers : Index → Test → Prop)
    (residual : ∀ i, Residual i) (Vanishes : (∀ i, Residual i) → Prop)
    (stageReadout : ∀ i, Approx i → Recon) (target : Limit → Recon)
    (base : Index)
    (htower : (∀ i x, compare i i (refl i) x = x) ∧
      ∀ i j k (hij : le i j) (hjk : le j k) x,
        compare i k (trans hij hjk) x =
          compare i j hij (compare j k hjk x))
    (hcofinal : PaperCofinal covers) (hvanishes : Vanishes residual)
    (hprojection : ∀ i j (hij : le i j) x,
      compare i j hij (projection j x) = projection i x)
    (hreadout : ∀ i j (hij : le i j) a,
      stageReadout i (compare i j hij a) = stageReadout j a)
    (hbase : ∀ x, stageReadout base (projection base x) = target x)
    (hfibers : ∀ x y, limitQuotient x = limitQuotient y → target x = target y) :
    PaperStableLimitQuotientDependent le refl trans compare covers residual
      Vanishes projection limitQuotient stageReadout ∧
    ∃ readout : Q → Recon, ∀ x, readout (limitQuotient x) = target x := by
  have hstage : ∀ i x, stageReadout i (projection i x) = target x := by
    intro i x
    rcases directed base i with ⟨k, hbk, hik⟩
    calc
      stageReadout i (projection i x) =
          stageReadout i (compare i k hik (projection k x)) := by
            rw [hprojection i k hik x]
      _ = stageReadout k (projection k x) :=
        hreadout i k hik (projection k x)
      _ = stageReadout base (compare base k hbk (projection k x)) :=
        (hreadout base k hbk (projection k x)).symm
      _ = stageReadout base (projection base x) := by
        rw [hprojection base k hbk x]
      _ = target x := hbase x
  have hdesc : Descends limitQuotient (fun x : Limit => x) target := by
    apply (descent_repair_normal_form limitQuotient
      (fun x : Limit => x) target hquotient).2
    intro pair hsplit
    exact hsplit.2 (hfibers pair.1 pair.2 hsplit.1)
  rcases hdesc with ⟨readout, hreadoutQ⟩
  refine ⟨⟨htower, hcofinal, hvanishes, readout, ?_⟩, readout, ?_⟩
  · intro i x
    exact (congrFun hreadoutQ x).trans (hstage i x).symm
  · intro x
    exact congrFun hreadoutQ x

/-- The stage readouts agree on the limit; compatibility with the limit
quotient is exactly fiber constancy, and its readout is unique. -/
theorem continuum_limit_readout_dependent_tower_full
    {Index Test Limit Q Recon : Type}
    {Approx Residual : Index → Type}
    (le : Index → Index → Prop) (refl : ∀ i, le i i)
    (trans : ∀ {i j k}, le i j → le j k → le i k)
    (directed : ∀ i j : Index, ∃ k, le i k ∧ le j k)
    (compare : ∀ i j, le i j → Approx j → Approx i)
    (projection : ∀ i, Limit → Approx i)
    (limitQuotient : Limit → Q) (hquotient : Function.Surjective limitQuotient)
    (covers : Index → Test → Prop)
    (residual : ∀ i, Residual i) (Vanishes : (∀ i, Residual i) → Prop)
    (stageReadout : ∀ i, Approx i → Recon) (target : Limit → Recon)
    (base : Index)
    (htower : (∀ i x, compare i i (refl i) x = x) ∧
      ∀ i j k (hij : le i j) (hjk : le j k) x,
        compare i k (trans hij hjk) x =
          compare i j hij (compare j k hjk x))
    (hcofinal : PaperCofinal covers) (hvanishes : Vanishes residual)
    (hprojection : ∀ i j (hij : le i j) x,
      compare i j hij (projection j x) = projection i x)
    (hreadout : ∀ i j (hij : le i j) a,
      stageReadout i (compare i j hij a) = stageReadout j a) :
    (∀ i j x, stageReadout i (projection i x) =
      stageReadout j (projection j x)) ∧
    (∀ b : Index,
      PaperStableLimitQuotientDependent le refl trans compare covers residual
          Vanishes projection limitQuotient stageReadout ↔
        ∀ x y, limitQuotient x = limitQuotient y →
          stageReadout b (projection b x) =
            stageReadout b (projection b y)) ∧
    (∀ readout readout' : Q → Recon,
      (∀ i x, readout (limitQuotient x) =
        stageReadout i (projection i x)) →
      (∀ i x, readout' (limitQuotient x) =
        stageReadout i (projection i x)) → readout = readout') ∧
    ((∀ x, stageReadout base (projection base x) = target x) →
      (∀ x y, limitQuotient x = limitQuotient y → target x = target y) →
      PaperStableLimitQuotientDependent le refl trans compare covers residual
          Vanishes projection limitQuotient stageReadout ∧
        ∃ readout : Q → Recon,
          ∀ x, readout (limitQuotient x) = target x) := by
  have hstage : ∀ i j x, stageReadout i (projection i x) =
      stageReadout j (projection j x) := by
    intro i j x
    obtain ⟨k, hik, hjk⟩ := directed i j
    calc
      stageReadout i (projection i x) =
          stageReadout i (compare i k hik (projection k x)) := by
            rw [hprojection i k hik x]
      _ = stageReadout k (projection k x) :=
        hreadout i k hik (projection k x)
      _ = stageReadout j (compare j k hjk (projection k x)) :=
        (hreadout j k hjk (projection k x)).symm
      _ = stageReadout j (projection j x) := by
        rw [hprojection j k hjk x]
  refine ⟨hstage, ?_, ?_, ?_⟩
  · intro b
    constructor
    · rintro ⟨_, _, _, readout, hcompat⟩ x y hxy
      calc
        stageReadout b (projection b x) = readout (limitQuotient x) :=
          (hcompat b x).symm
        _ = readout (limitQuotient y) := congrArg readout hxy
        _ = stageReadout b (projection b y) := hcompat b y
    · intro hfibers
      exact (continuum_limit_readout_dependent_tower le refl trans directed
        compare projection limitQuotient hquotient covers residual Vanishes
        stageReadout (fun x => stageReadout b (projection b x)) b htower
        hcofinal hvanishes hprojection hreadout (fun _ => rfl) hfibers).1
  · intro readout readout' hcompat hcompat'
    funext z
    obtain ⟨x, rfl⟩ := hquotient z
    exact (hcompat base x).trans (hcompat' base x).symm
  · intro hbase hfibers
    exact continuum_limit_readout_dependent_tower le refl trans directed
      compare projection limitQuotient hquotient covers residual Vanishes
      stageReadout target base htower hcofinal hvanishes hprojection
      hreadout hbase hfibers

/-- General F43: the comparison/projection and stage-readout equations alone
make all stages agree. Compatibility with the limit quotient is equivalent to
fiber constancy and is unique; tower coherence, covering cofinality and residual
vanishing enter only the final stability characterization. -/
theorem continuum_limit_readout_dependent_tower_general
    {Index Test Limit Q Recon : Type}
    {Approx Residual : Index → Type}
    (hIndex : Nonempty Index)
    (le : Index → Index → Prop) (refl : ∀ i, le i i)
    (trans : ∀ {i j k}, le i j → le j k → le i k)
    (directed : ∀ i j : Index, ∃ k, le i k ∧ le j k)
    (compare : ∀ i j, le i j → Approx j → Approx i)
    (projection : ∀ i, Limit → Approx i)
    (limitQuotient : Limit → Q) (hquotient : Function.Surjective limitQuotient)
    (covers : Index → Test → Prop)
    (residual : ∀ i, Residual i) (Vanishes : (∀ i, Residual i) → Prop)
    (stageReadout : ∀ i, Approx i → Recon)
    (hprojection : ∀ i j (hij : le i j) x,
      compare i j hij (projection j x) = projection i x)
    (hreadout : ∀ i j (hij : le i j) a,
      stageReadout i (compare i j hij a) = stageReadout j a) :
    (∀ i j, stageReadout i ∘ projection i = stageReadout j ∘ projection j) ∧
    ((∀ b : Index,
      (∃ readout : Q → Recon, ∀ i x,
        readout (limitQuotient x) = stageReadout i (projection i x)) ↔
      ∀ x y, limitQuotient x = limitQuotient y →
        stageReadout b (projection b x) = stageReadout b (projection b y)) ∧
      (∀ readout readout' : Q → Recon,
        (∀ i x, readout (limitQuotient x) = stageReadout i (projection i x)) →
        (∀ i x, readout' (limitQuotient x) = stageReadout i (projection i x)) →
        readout = readout')) ∧
    (∀ b : Index,
      PaperStableLimitQuotientDependent le refl trans compare covers residual
          Vanishes projection limitQuotient stageReadout ↔
      ((∀ i x, compare i i (refl i) x = x) ∧
        ∀ i j k (hij : le i j) (hjk : le j k) x,
          compare i k (trans hij hjk) x =
            compare i j hij (compare j k hjk x)) ∧
      PaperCofinal covers ∧ Vanishes residual ∧
      ∀ x y, limitQuotient x = limitQuotient y →
        stageReadout b (projection b x) = stageReadout b (projection b y)) := by
  have hstage : ∀ i j x, stageReadout i (projection i x) =
      stageReadout j (projection j x) := by
    intro i j x
    obtain ⟨k, hik, hjk⟩ := directed i j
    calc
      stageReadout i (projection i x) =
          stageReadout i (compare i k hik (projection k x)) := by
            rw [hprojection i k hik x]
      _ = stageReadout k (projection k x) := hreadout i k hik (projection k x)
      _ = stageReadout j (compare j k hjk (projection k x)) :=
        (hreadout j k hjk (projection k x)).symm
      _ = stageReadout j (projection j x) := by rw [hprojection j k hjk x]
  have hexists : ∀ b : Index,
      (∃ readout : Q → Recon, ∀ i x,
        readout (limitQuotient x) = stageReadout i (projection i x)) ↔
      ∀ x y, limitQuotient x = limitQuotient y →
        stageReadout b (projection b x) = stageReadout b (projection b y) := by
    intro b
    constructor
    · rintro ⟨readout, hcompat⟩ x y hxy
      calc
        stageReadout b (projection b x) = readout (limitQuotient x) :=
          (hcompat b x).symm
        _ = readout (limitQuotient y) := congrArg readout hxy
        _ = stageReadout b (projection b y) := hcompat b y
    · intro hfibers
      have hdesc : Descends limitQuotient (fun x : Limit => x)
          (fun x => stageReadout b (projection b x)) := by
        apply (descent_repair_normal_form limitQuotient (fun x : Limit => x)
          (fun x => stageReadout b (projection b x)) hquotient).mpr
        intro pair hsplit
        exact hsplit.2 (hfibers pair.1 pair.2 hsplit.1)
      obtain ⟨readout, hcomm⟩ := hdesc
      refine ⟨readout, ?_⟩
      intro i x
      exact (congrFun hcomm x).trans (hstage b i x)
  refine ⟨?_, ⟨hexists, ?_⟩, ?_⟩
  · intro i j
    funext x
    exact hstage i j x
  · intro readout readout' hcompat hcompat'
    funext z
    obtain ⟨x, rfl⟩ := hquotient z
    let b : Index := Classical.choice hIndex
    exact (hcompat b x).trans (hcompat' b x).symm
  · intro b
    constructor
    · rintro ⟨htower, hcofinal, hvanishes, readout, hcompat⟩
      exact ⟨htower, hcofinal, hvanishes, (hexists b).mp ⟨readout, hcompat⟩⟩
    · rintro ⟨htower, hcofinal, hvanishes, hfibers⟩
      obtain ⟨readout, hcompat⟩ := (hexists b).mpr hfibers
      exact ⟨htower, hcofinal, hvanishes, readout, hcompat⟩

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.ContinuumEmergence
