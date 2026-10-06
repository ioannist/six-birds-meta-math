import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
F23 Probability as Stable Unresolved Fiber.

The careful framing from the source is part of the statement: unresolvedness is
not probability by itself, and a numerical distribution is not automatically a
chance law. A layer probability law is a declared measure/ledger on quotient
fibers together with stability under declared continuations.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ProbabilityAsStableUnresolvedFiber

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- A fiber ledger is supported on the quotient fiber named by its index. -/
def FiberLedgerSupported {H Q Ledger : Type} (q : H → Q)
    (ledger : Q → Ledger) (Supports : Ledger → H → Prop) : Prop :=
  ∀ a h, Supports (ledger a) h → q h = a

/-- The quotient-fiber chance of a readout value is computed by applying the
fiber ledger's mass functional to the readout fiber. -/
def FiberReadoutChance {H Q Ledger Z Weight : Type} (ledger : Q → Ledger)
    (mass : Ledger → (H → Prop) → Weight) (readout : H → Z) : Q → Z → Weight :=
  fun a v => mass (ledger a) (fun h => readout h = v)

/-- A readout descends when the current quotient already determines it. -/
def ReadoutDescends {H Q Z : Type} (q : H → Q) (readout : H → Z) : Prop :=
  Descends q (fun h : H => h) readout

/-- The unresolved-readout obstruction: same quotient object, different
readout value. -/
def UnresolvedReadoutObstruction {H Q Z : Type} (q : H → Q)
    (readout : H → Z) : (H × H) → Prop :=
  splitPairObstruction q (fun h : H => h) readout

/-- No unresolved readout obstruction is present. -/
def UnresolvedReadoutObstructionEmpty {H Q Z : Type} (q : H → Q)
    (readout : H → Z) : Prop :=
  ObstructionEmpty (UnresolvedReadoutObstruction q readout)

/-- A genuinely unresolved readout varies inside at least one current quotient
fiber. -/
def UnresolvedReadout {H Q Z : Type} (q : H → Q) (readout : H → Z) : Prop :=
  ∃ pair, UnresolvedReadoutObstruction q readout pair

/-- Abstract transport stability equation:
`pushed a` represents `K_* kappa_a`, while `mixture a` represents
`sum_b Kbar(a,b) kappa'_b`. -/
def StableFiberTransport {Q TargetMeasure : Type}
    (pushed mixture : Q → TargetMeasure) : Prop :=
  ∀ a, pushed a = mixture a

/-- A stable layer chance law consists of source fiber support, target fiber
support, and the transport stability equation. This deliberately excludes bare
ignorance, arbitrary weights, and unbridged frequency records. -/
def StableLayerChance {H Q H' Q' Ledger Ledger' TargetMeasure : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure) :
    Prop :=
  FiberLedgerSupported q ledger Supports ∧
    FiberLedgerSupported q' targetLedger TargetSupports ∧
      StableFiberTransport pushed mixture

/-- Nontrivial fiber chance requires both unresolved readout variation and a
stable fiber probability law. -/
def NontrivialStableFiberChance
    {H Q H' Q' Ledger Ledger' TargetMeasure Z : Type}
    (q : H → Q) (readout : H → Z) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure) :
    Prop :=
  UnresolvedReadout q readout ∧
    StableLayerChance q q' ledger targetLedger Supports TargetSupports pushed mixture

/-- Unresolvedness without a stable ledger is ambiguity only, not chance. -/
def AmbiguityWithoutStableMeasure
    {H Q H' Q' Ledger Ledger' TargetMeasure Z : Type}
    (q : H → Q) (readout : H → Z) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure) :
    Prop :=
  UnresolvedReadout q readout ∧
    ¬ StableLayerChance q q' ledger targetLedger Supports TargetSupports pushed mixture

/-- Predictive sufficiency for a declared future/readout. Probability lawhood
does not by itself assert this. -/
def PredictivelySufficient {H Q Future : Type} (q : H → Q)
    (future : H → Future) : Prop :=
  Descends q (fun h : H => h) future

/-- Closure-deficit status: a finer state can still improve a declared future
prediction beyond the current quotient. -/
def ClosureDeficitStatus {H Q Future : Type} (q : H → Q)
    (future : H → Future) : Prop :=
  ¬ PredictivelySufficient q future

/-- Source status vocabulary preserving the careful framing from F23. -/
inductive ProbabilityFiberStatus where
  | deterministicQuotientReadout
  | stableFiberChance
  | hiddenStateMixture
  | intrinsicKernelChance
  | closureDeficitChance
  | unstableFiberWeights
  | unsupportedPrior
  | frequencyEvidence
  | probabilityOverread
  | scopedProbability
deriving DecidableEq

/-- Meaning assignment for the probability-status vocabulary. -/
def ProbabilityFiberStatusHolds (deterministic stable hidden intrinsic closureDeficit
    unstable unsupported frequency overread scopedStatus : Prop) :
    ProbabilityFiberStatus → Prop
  | ProbabilityFiberStatus.deterministicQuotientReadout => deterministic
  | ProbabilityFiberStatus.stableFiberChance => stable
  | ProbabilityFiberStatus.hiddenStateMixture => hidden
  | ProbabilityFiberStatus.intrinsicKernelChance => intrinsic
  | ProbabilityFiberStatus.closureDeficitChance => closureDeficit
  | ProbabilityFiberStatus.unstableFiberWeights => unstable
  | ProbabilityFiberStatus.unsupportedPrior => unsupported
  | ProbabilityFiberStatus.frequencyEvidence => frequency
  | ProbabilityFiberStatus.probabilityOverread => overread
  | ProbabilityFiberStatus.scopedProbability => scopedStatus

/-- The displayed chance formula is exactly the fiber-ledger mass of the
readout fiber. -/
theorem fiber_readout_chance_formula {H Q Ledger Z Weight : Type}
    (ledger : Q → Ledger) (mass : Ledger → (H → Prop) → Weight)
    (readout : H → Z) :
    FiberReadoutChance ledger mass readout =
      fun a v => mass (ledger a) (fun h => readout h = v) := by
  rfl

/-- A readout descends through the quotient iff no quotient fiber splits that
readout. -/
theorem readout_descends_iff_no_unresolved_obstruction {H Q Z : Type}
    (q : H → Q) (readout : H → Z) (hq : Function.Surjective q) :
    ReadoutDescends q readout ↔ UnresolvedReadoutObstructionEmpty q readout :=
  descent_repair_normal_form q (fun h : H => h) readout hq

/-- Being unresolved is the same as non-emptiness of the unresolved-readout
obstruction. -/
theorem unresolved_readout_iff_not_empty_obstruction {H Q Z : Type}
    (q : H → Q) (readout : H → Z) :
    UnresolvedReadout q readout ↔
      ¬ UnresolvedReadoutObstructionEmpty q readout := by
  constructor
  · intro hunresolved hempty
    rcases hunresolved with ⟨pair, hpair⟩
    exact hempty pair hpair
  · intro hnotEmpty
    classical
    exact Classical.byContradiction (fun hnoWitness =>
      hnotEmpty (fun pair hpair => hnoWitness ⟨pair, hpair⟩))

/-- Stable layer chance is exactly support on source/target fibers plus the
declared transport stability equation. -/
theorem stable_layer_chance_iff_supported_and_stable
    {H Q H' Q' Ledger Ledger' TargetMeasure : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure) :
    StableLayerChance q q' ledger targetLedger Supports TargetSupports pushed mixture ↔
      FiberLedgerSupported q ledger Supports ∧
        FiberLedgerSupported q' targetLedger TargetSupports ∧
          StableFiberTransport pushed mixture := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Nontrivial fiber chance is unresolved readout variation together with a
stable layer chance law. -/
theorem nontrivial_chance_iff_unresolved_and_stable
    {H Q H' Q' Ledger Ledger' TargetMeasure Z : Type}
    (q : H → Q) (readout : H → Z) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure) :
    NontrivialStableFiberChance q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture ↔
      UnresolvedReadout q readout ∧
        StableLayerChance q q' ledger targetLedger Supports TargetSupports
          pushed mixture := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Ambiguity without stability cannot be promoted to stable fiber chance. -/
theorem ambiguity_without_stability_not_chance
    {H Q H' Q' Ledger Ledger' TargetMeasure Z : Type}
    (q : H → Q) (readout : H → Z) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure) :
    AmbiguityWithoutStableMeasure q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture →
      ¬ NontrivialStableFiberChance q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture := by
  intro hamb hchance
  exact hamb.2 hchance.2

/-- A stable probability law can coexist with a closure-deficit status; the
probability law is therefore not being overread as predictive sufficiency. -/
theorem stable_chance_with_closure_deficit_status
    {H Q H' Q' Ledger Ledger' TargetMeasure Future : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure)
    (future : H → Future) :
    StableLayerChance q q' ledger targetLedger Supports TargetSupports pushed mixture →
      ClosureDeficitStatus q future →
        StableLayerChance q q' ledger targetLedger Supports TargetSupports
          pushed mixture ∧ ClosureDeficitStatus q future := by
  intro hstable hdeficit
  exact ⟨hstable, hdeficit⟩

/--
Probability as Stable Unresolved Fiber Normal Form. A readout is deterministic
at the quotient exactly when its unresolved-readout obstruction is empty.
Nontrivial chance requires an unresolved readout plus supported fiber ledgers
that satisfy the declared transport stability equation. Unresolvedness without
that stability remains ambiguity, and a stable probability law is not silently
promoted to predictive sufficiency when closure deficit remains.
-/
theorem probability_as_stable_unresolved_fiber
    {H Q H' Q' Ledger Ledger' TargetMeasure Z Weight Future : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure)
    (readout : H → Z) (mass : Ledger → (H → Prop) → Weight)
    (future : H → Future) (hq : Function.Surjective q) :
    (FiberReadoutChance ledger mass readout =
      fun a v => mass (ledger a) (fun h => readout h = v)) ∧
      (ReadoutDescends q readout ↔ UnresolvedReadoutObstructionEmpty q readout) ∧
        (UnresolvedReadout q readout ↔
          ¬ UnresolvedReadoutObstructionEmpty q readout) ∧
          (StableLayerChance q q' ledger targetLedger Supports TargetSupports
              pushed mixture ↔
            FiberLedgerSupported q ledger Supports ∧
              FiberLedgerSupported q' targetLedger TargetSupports ∧
                StableFiberTransport pushed mixture) ∧
            (NontrivialStableFiberChance q readout q' ledger targetLedger Supports
                TargetSupports pushed mixture ↔
              UnresolvedReadout q readout ∧
                StableLayerChance q q' ledger targetLedger Supports TargetSupports
                  pushed mixture) ∧
              (AmbiguityWithoutStableMeasure q readout q' ledger targetLedger
                  Supports TargetSupports pushed mixture →
                ¬ NontrivialStableFiberChance q readout q' ledger targetLedger
                  Supports TargetSupports pushed mixture) ∧
                (StableLayerChance q q' ledger targetLedger Supports TargetSupports
                    pushed mixture →
                  ClosureDeficitStatus q future →
                    StableLayerChance q q' ledger targetLedger Supports TargetSupports
                      pushed mixture ∧ ClosureDeficitStatus q future) := by
  exact ⟨fiber_readout_chance_formula ledger mass readout,
    readout_descends_iff_no_unresolved_obstruction q readout hq,
    unresolved_readout_iff_not_empty_obstruction q readout,
    stable_layer_chance_iff_supported_and_stable q q' ledger targetLedger Supports
      TargetSupports pushed mixture,
    nontrivial_chance_iff_unresolved_and_stable q readout q' ledger targetLedger
      Supports TargetSupports pushed mixture,
    ambiguity_without_stability_not_chance q readout q' ledger targetLedger Supports
      TargetSupports pushed mixture,
    stable_chance_with_closure_deficit_status q q' ledger targetLedger Supports
      TargetSupports pushed mixture future⟩


/-- The paper's mass formula restricts each readout event to the named q-fiber. -/
def PaperFiberReadoutChance {H Q Ledger Z Weight : Type} (q : H → Q)
    (ledger : Q → Ledger) (mass : Ledger → (H → Prop) → Weight)
    (readout : H → Z) : Q → Z → Weight :=
  fun a v => mass (ledger a) (fun h => q h = a ∧ readout h = v)

/-- Paper probability criterion with the displayed fiber-restricted mass. -/
theorem paper_probability_as_stable_unresolved_fiber
    {H Q H' Q' Ledger Ledger' TargetMeasure Z Weight : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure)
    (readout : H → Z) (mass : Ledger → (H → Prop) → Weight)
    (hq : Function.Surjective q) :
    (PaperFiberReadoutChance q ledger mass readout =
      fun a v => mass (ledger a) (fun h => q h = a ∧ readout h = v)) ∧
    (ReadoutDescends q readout ↔
      ∀ h h', q h = q h' → readout h = readout h') ∧
    (UnresolvedReadout q readout ↔
      ∃ h h', q h = q h' ∧ readout h ≠ readout h') ∧
    (NontrivialStableFiberChance q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture ↔
      UnresolvedReadout q readout ∧
        StableLayerChance q q' ledger targetLedger Supports TargetSupports
          pushed mixture) := by
  constructor
  · rfl
  constructor
  · constructor
    · rintro ⟨lower,hlower⟩ h h' heq
      have hh := congrFun hlower h
      have hh' := congrFun hlower h'
      calc
        readout h = lower (q h) := hh.symm
        _ = lower (q h') := by rw [heq]
        _ = readout h' := hh'
    · intro hconst
      have hempty : UnresolvedReadoutObstructionEmpty q readout := by
        rintro ⟨h,h'⟩ ⟨heq,hne⟩
        exact hne (hconst h h' heq)
      exact (readout_descends_iff_no_unresolved_obstruction q readout hq).mpr hempty
  constructor
  · constructor
    · rintro ⟨⟨h,h'⟩,heq,hne⟩
      exact ⟨h,h',heq,hne⟩
    · rintro ⟨h,h',heq,hne⟩
      exact ⟨(h,h'),heq,hne⟩
  exact nontrivial_chance_iff_unresolved_and_stable q readout q' ledger
    targetLedger Supports TargetSupports pushed mixture

/-- The paper's split form: descent is exactly deterministic fiber readout;
under descent each fiber event is either the whole named fiber or empty;
nontrivial stable fiber chance requires a genuinely unresolved readout. -/
theorem paper_probability_fiber_split
    {H Q H' Q' Ledger Ledger' TargetMeasure Z Weight : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure)
    (readout : H → Z) (mass : Ledger → (H → Prop) → Weight)
    (hq : Function.Surjective q) :
    ((ReadoutDescends q readout ↔
        ∀ h h', q h = q h' → readout h = readout h') ∧
      (ReadoutDescends q readout ∨ UnresolvedReadout q readout) ∧
      ¬ (ReadoutDescends q readout ∧ UnresolvedReadout q readout)) ∧
    (∀ rbar : Q → Z, (∀ h, rbar (q h) = readout h) → ∀ a v,
      ((v = rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun h => q h = a)) ∧
        (v ≠ rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun _ => False))) ∧
      ((v = rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun h => q h = a)) ∧
        (v ≠ rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun _ => False)))) ∧
    (NontrivialStableFiberChance q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture → ¬ ReadoutDescends q readout) := by
  have hcriterion : ReadoutDescends q readout ↔
      ∀ h h', q h = q h' → readout h = readout h' :=
    (paper_probability_as_stable_unresolved_fiber q q' ledger targetLedger
      Supports TargetSupports pushed mixture readout mass hq).2.1
  have hdesc_empty := readout_descends_iff_no_unresolved_obstruction q readout hq
  have hunresolved := unresolved_readout_iff_not_empty_obstruction q readout
  refine ⟨⟨hcriterion, ?_, ?_⟩, ?_, ?_⟩
  · classical
    by_cases hdesc : ReadoutDescends q readout
    · exact Or.inl hdesc
    · exact Or.inr (hunresolved.mpr (fun hempty => hdesc (hdesc_empty.mpr hempty)))
  · intro ⟨hdesc, hsplit⟩
    exact (hunresolved.mp hsplit) (hdesc_empty.mp hdesc)
  · intro rbar hfactor a v
    have hwhole : v = rbar a →
        (fun h => q h = a ∧ readout h = v) = (fun h => q h = a) := by
      intro hv
      funext h
      apply propext
      constructor
      · intro hh
        exact hh.1
      · intro hqa
        refine ⟨hqa, ?_⟩
        calc
          readout h = rbar (q h) := (hfactor h).symm
          _ = rbar a := congrArg rbar hqa
          _ = v := hv.symm
    have hvoid : v ≠ rbar a →
        (fun h => q h = a ∧ readout h = v) = (fun _ => False) := by
      intro hv
      funext h
      apply propext
      constructor
      · intro ⟨hqa, hrv⟩
        apply hv
        calc
          v = readout h := hrv.symm
          _ = rbar (q h) := (hfactor h).symm
          _ = rbar a := congrArg rbar hqa
      · intro hfalse
        exact False.elim hfalse
    refine ⟨⟨hwhole, hvoid⟩, ?_⟩
    constructor
    · intro hv
      exact congrArg (mass (ledger a)) (hwhole hv)
    · intro hv
      exact congrArg (mass (ledger a)) (hvoid hv)
  · intro hchance hdesc
    exact (hunresolved.mp hchance.1) (hdesc_empty.mp hdesc)


/-- The minimal commutative weight monoid for the finite value sum. -/
structure FiniteWeightMonoid (Weight : Type) where
  zero : Weight
  add : Weight → Weight → Weight
  zero_add : ∀ w, add zero w = w
  add_zero : ∀ w, add w zero = w
  add_assoc : ∀ u v w, add (add u v) w = add u (add v w)
  add_comm : ∀ u v, add u v = add v u

/-- Sum over an explicit finite enumeration of readout values. -/
def PaperFiniteChanceSum {H Q Ledger Z Weight : Type}
    (W : FiniteWeightMonoid Weight) (zs : List Z)
    (q : H → Q) (ledger : Q → Ledger)
    (mass : Ledger → (H → Prop) → Weight) (readout : H → Z)
    (a : Q) : Weight :=
  zs.foldr (fun v acc => W.add (PaperFiberReadoutChance q ledger mass readout a v)
    acc) W.zero

/-- Finite additivity distributes a named fiber's weight over its readout
values. The list is a duplicate-free complete enumeration of `Z`. -/
theorem paper_finite_chance_sum_eq_fiber
    {H Q Ledger Z Weight : Type}
    (q : H → Q) (ledger : Q → Ledger)
    (mass : Ledger → (H → Prop) → Weight) (readout : H → Z)
    (W : FiniteWeightMonoid Weight) (zs : List Z)
    (hnodup : zs.Nodup) (hcomplete : ∀ v : Z, v ∈ zs)
    (hempty : ∀ a, mass (ledger a) (fun _ : H => False) = W.zero)
    (hadd : ∀ a (A B : H → Prop),
      (∀ h, ¬ (A h ∧ B h)) →
      mass (ledger a) (fun h => A h ∨ B h) =
        W.add (mass (ledger a) A) (mass (ledger a) B)) :
    ∀ a, PaperFiniteChanceSum W zs q ledger mass readout a =
      mass (ledger a) (fun h => q h = a) := by
  intro a
  have hpartition : ∀ xs : List Z, xs.Nodup →
      PaperFiniteChanceSum W xs q ledger mass readout a =
        mass (ledger a) (fun h => q h = a ∧
          ∃ v, v ∈ xs ∧ readout h = v) := by
    intro xs
    induction xs with
    | nil =>
        intro _
        change W.zero = mass (ledger a) (fun h => q h = a ∧
          ∃ v, v ∈ ([] : List Z) ∧ readout h = v)
        have hevent : (fun h : H => q h = a ∧
            ∃ v, v ∈ ([] : List Z) ∧ readout h = v) =
            (fun _ : H => False) := by
          funext h
          apply propext
          simp
        rw [hevent, hempty a]
    | cons v vs ih =>
        intro hnd
        have hvnot : v ∉ vs := (List.nodup_cons.mp hnd).1
        have hvs : vs.Nodup := (List.nodup_cons.mp hnd).2
        have hdisjoint : ∀ h : H,
            ¬ ((q h = a ∧ readout h = v) ∧
              (q h = a ∧ ∃ u, u ∈ vs ∧ readout h = u)) := by
          intro h ⟨⟨_, hv⟩, ⟨_, u, hu, huval⟩⟩
          apply hvnot
          have huv : u = v := huval.symm.trans hv
          exact huv ▸ hu
        have hunion : (fun h : H =>
            (q h = a ∧ readout h = v) ∨
              (q h = a ∧ ∃ u, u ∈ vs ∧ readout h = u)) =
            (fun h => q h = a ∧
              ∃ u, u ∈ v :: vs ∧ readout h = u) := by
          funext h
          apply propext
          constructor
          · rintro (⟨hqa, hv⟩ | ⟨hqa, u, hu, huval⟩)
            · exact ⟨hqa, v, List.mem_cons.mpr (Or.inl rfl), hv⟩
            · exact ⟨hqa, u, List.mem_cons.mpr (Or.inr hu), huval⟩
          · rintro ⟨hqa, u, hu, huval⟩
            rcases List.mem_cons.mp hu with huv | htail
            · left
              exact ⟨hqa, huval.trans huv⟩
            · right
              exact ⟨hqa, u, htail, huval⟩
        change W.add (PaperFiberReadoutChance q ledger mass readout a v)
          (PaperFiniteChanceSum W vs q ledger mass readout a) = _
        rw [ih hvs]
        change W.add (mass (ledger a) (fun h => q h = a ∧ readout h = v))
          (mass (ledger a) (fun h => q h = a ∧
            ∃ u, u ∈ vs ∧ readout h = u)) = _
        rw [← hadd a _ _ hdisjoint, hunion]
  rw [hpartition zs hnodup]
  congr 1
  funext h
  apply propext
  constructor
  · exact And.left
  · intro hqa
    exact ⟨hqa, readout h, hcomplete (readout h), rfl⟩

/-- Paper F23, including finite additivity of fiber mass over readout values. -/
theorem paper_probability_fiber_split_additive
    {H Q H' Q' Ledger Ledger' TargetMeasure Z Weight : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure)
    (readout : H → Z) (mass : Ledger → (H → Prop) → Weight)
    (hq : Function.Surjective q)
    (W : FiniteWeightMonoid Weight) (zs : List Z)
    (hnodup : zs.Nodup) (hcomplete : ∀ v : Z, v ∈ zs)
    (hempty : ∀ a, mass (ledger a) (fun _ : H => False) = W.zero)
    (hadd : ∀ a (A B : H → Prop),
      (∀ h, ¬ (A h ∧ B h)) →
      mass (ledger a) (fun h => A h ∨ B h) =
        W.add (mass (ledger a) A) (mass (ledger a) B)) :
    ((ReadoutDescends q readout ↔
        ∀ h h', q h = q h' → readout h = readout h') ∧
      (ReadoutDescends q readout ∨ UnresolvedReadout q readout) ∧
      ¬ (ReadoutDescends q readout ∧ UnresolvedReadout q readout)) ∧
    (∀ rbar : Q → Z, (∀ h, rbar (q h) = readout h) → ∀ a v,
      ((v = rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun h => q h = a)) ∧
        (v ≠ rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun _ => False))) ∧
      ((v = rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun h => q h = a)) ∧
        (v ≠ rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun _ => False)))) ∧
    (NontrivialStableFiberChance q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture → ¬ ReadoutDescends q readout) ∧
    (∀ a, PaperFiniteChanceSum W zs q ledger mass readout a =
      mass (ledger a) (fun h => q h = a)) := by
  rcases paper_probability_fiber_split q q' ledger targetLedger Supports
    TargetSupports pushed mixture readout mass hq with ⟨h1, h2, h3⟩
  exact ⟨h1, h2, h3,
    paper_finite_chance_sum_eq_fiber q ledger mass readout W zs hnodup
      hcomplete hempty hadd⟩

/-- Support inside the named fiber lets the ledger ignore the fiber
restriction in the paper's chance formula. -/
theorem paper_fiber_chance_eq_unrestricted_of_support
    {H Q Ledger Z Weight : Type}
    (q : H → Q) (ledger : Q → Ledger) (Supports : Ledger → H → Prop)
    (mass : Ledger → (H → Prop) → Weight) (readout : H → Z)
    (zero : Weight) (add : Weight → Weight → Weight)
    (hsupport : FiberLedgerSupported q ledger Supports)
    (hadd : ∀ a (A B : H → Prop),
      (∀ h, ¬ (A h ∧ B h)) →
      mass (ledger a) (fun h => A h ∨ B h) =
        add (mass (ledger a) A) (mass (ledger a) B))
    (hvanish : ∀ a (E : H → Prop),
      (∀ h, ¬ (E h ∧ Supports (ledger a) h)) →
      mass (ledger a) E = zero) :
    ∀ a v, PaperFiberReadoutChance q ledger mass readout a v =
      mass (ledger a) (fun h => readout h = v) := by
  intro a v
  let inside : H → Prop := fun h => q h = a ∧ readout h = v
  let outside : H → Prop := fun h => readout h = v ∧ q h ≠ a
  have hdisjoint : ∀ h, ¬ (inside h ∧ outside h) := by
    intro h ⟨hi, ho⟩
    exact ho.2 hi.1
  have houtside : ∀ h, ¬ (outside h ∧ Supports (ledger a) h) := by
    intro h ⟨ho, hs⟩
    exact ho.2 (hsupport a h hs)
  have hunion : (fun h => inside h ∨ outside h) =
      (fun h => readout h = v) := by
    funext h
    apply propext
    constructor
    · rintro (hi | ho)
      · exact hi.2
      · exact ho.1
    · intro hr
      by_cases hqa : q h = a
      · exact Or.inl ⟨hqa, hr⟩
      · exact Or.inr ⟨hr, hqa⟩
  have hempty : mass (ledger a) (fun _ : H => False) = zero :=
    hvanish a _ (by intro h; simp)
  have hright : mass (ledger a) inside =
      add (mass (ledger a) inside) zero := by
    have hsplit := hadd a inside (fun _ : H => False)
      (by intro h; simp)
    have hunionEmpty : (fun h => inside h ∨ False) = inside := by
      funext h
      apply propext
      simp
    rw [hunionEmpty, hempty] at hsplit
    exact hsplit
  have hsum := hadd a inside outside hdisjoint
  rw [hunion, hvanish a outside houtside] at hsum
  exact (hsum.trans hright.symm).symm

/-- The unrestricted readout chance needs support and mass laws only at the
named class. -/
theorem paper_fiber_chance_eq_unrestricted_at
    {H Q Ledger Z Weight : Type}
    (q : H → Q) (ledger : Q → Ledger) (Supports : Ledger → H → Prop)
    (mass : Ledger → (H → Prop) → Weight) (readout : H → Z)
    (a : Q) (zero : Weight) (add : Weight → Weight → Weight)
    (hsupport : ∀ h, Supports (ledger a) h → q h = a)
    (hadd : ∀ (A B : H → Prop),
      (∀ h, ¬ (A h ∧ B h)) →
      mass (ledger a) (fun h => A h ∨ B h) =
        add (mass (ledger a) A) (mass (ledger a) B))
    (hvanish : ∀ (E : H → Prop),
      (∀ h, ¬ (E h ∧ Supports (ledger a) h)) →
      mass (ledger a) E = zero) :
    ∀ v, PaperFiberReadoutChance q ledger mass readout a v =
      mass (ledger a) (fun h => readout h = v) := by
  intro v
  let inside : H → Prop := fun h => q h = a ∧ readout h = v
  let outside : H → Prop := fun h => readout h = v ∧ q h ≠ a
  have hdisjoint : ∀ h, ¬ (inside h ∧ outside h) := by
    intro h ⟨hi, ho⟩
    exact ho.2 hi.1
  have houtside : ∀ h, ¬ (outside h ∧ Supports (ledger a) h) := by
    intro h ⟨ho, hs⟩
    exact ho.2 (hsupport h hs)
  have hunion : (fun h => inside h ∨ outside h) =
      (fun h => readout h = v) := by
    funext h
    apply propext
    constructor
    · rintro (hi | ho)
      · exact hi.2
      · exact ho.1
    · intro hr
      by_cases hqa : q h = a
      · exact Or.inl ⟨hqa, hr⟩
      · exact Or.inr ⟨hr, hqa⟩
  have hempty : mass (ledger a) (fun _ : H => False) = zero :=
    hvanish _ (by intro h; simp)
  have hright : mass (ledger a) inside =
      add (mass (ledger a) inside) zero := by
    have hsplit := hadd inside (fun _ : H => False) (by intro h; simp)
    have hunionEmpty : (fun h => inside h ∨ False) = inside := by
      funext h
      apply propext
      simp
    rw [hunionEmpty, hempty] at hsplit
    exact hsplit
  have hsum := hadd inside outside hdisjoint
  rw [hunion, hvanish outside houtside] at hsum
  exact (hsum.trans hright.symm).symm

/-- F23 with the fifth support-based chance clause. -/
theorem paper_probability_fiber_split_supported
    {H Q H' Q' Ledger Ledger' TargetMeasure Z Weight : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure)
    (readout : H → Z) (mass : Ledger → (H → Prop) → Weight)
    (hq : Function.Surjective q)
    (W : FiniteWeightMonoid Weight) (zs : List Z)
    (hnodup : zs.Nodup) (hcomplete : ∀ v : Z, v ∈ zs)
    (hsupport : FiberLedgerSupported q ledger Supports)
    (hadd : ∀ a (A B : H → Prop),
      (∀ h, ¬ (A h ∧ B h)) →
      mass (ledger a) (fun h => A h ∨ B h) =
        W.add (mass (ledger a) A) (mass (ledger a) B))
    (hvanish : ∀ a (E : H → Prop),
      (∀ h, ¬ (E h ∧ Supports (ledger a) h)) →
      mass (ledger a) E = W.zero) :
    (((ReadoutDescends q readout ↔
        ∀ h h', q h = q h' → readout h = readout h') ∧
      (ReadoutDescends q readout ∨ UnresolvedReadout q readout) ∧
      ¬ (ReadoutDescends q readout ∧ UnresolvedReadout q readout)) ∧
    (∀ rbar : Q → Z, (∀ h, rbar (q h) = readout h) → ∀ a v,
      ((v = rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun h => q h = a)) ∧
        (v ≠ rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun _ => False))) ∧
      ((v = rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun h => q h = a)) ∧
        (v ≠ rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun _ => False)))) ∧
    (NontrivialStableFiberChance q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture → ¬ ReadoutDescends q readout) ∧
    (∀ a, PaperFiniteChanceSum W zs q ledger mass readout a =
      mass (ledger a) (fun h => q h = a))) ∧
    (∀ a v, PaperFiberReadoutChance q ledger mass readout a v =
      mass (ledger a) (fun h => readout h = v)) := by
  have hempty : ∀ a, mass (ledger a) (fun _ : H => False) = W.zero := by
    intro a
    exact hvanish a _ (by intro h; simp)
  exact ⟨paper_probability_fiber_split_additive q q' ledger targetLedger
      Supports TargetSupports pushed mixture readout mass hq W zs hnodup
      hcomplete hempty hadd,
    paper_fiber_chance_eq_unrestricted_of_support q ledger Supports mass
      readout W.zero W.add hsupport hadd hvanish⟩

/-- F23 with finite additivity only in clause (iv), and support and mass
conditions only at the named class in clause (v). -/
theorem paper_probability_fiber_split_per_clause
    {H Q H' Q' Ledger Ledger' TargetMeasure Z Weight : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure)
    (readout : H → Z) (mass : Ledger → (H → Prop) → Weight)
    (hq : Function.Surjective q) :
    ((ReadoutDescends q readout ↔
        ∀ h h', q h = q h' → readout h = readout h') ∧
      (ReadoutDescends q readout ∨ UnresolvedReadout q readout) ∧
      ¬ (ReadoutDescends q readout ∧ UnresolvedReadout q readout)) ∧
    (∀ rbar : Q → Z, (∀ h, rbar (q h) = readout h) → ∀ a v,
      ((v = rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun h => q h = a)) ∧
        (v ≠ rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun _ => False))) ∧
      ((v = rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun h => q h = a)) ∧
        (v ≠ rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun _ => False)))) ∧
    (NontrivialStableFiberChance q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture → ¬ ReadoutDescends q readout) ∧
    (∀ (W : FiniteWeightMonoid Weight) (zs : List Z),
      zs.Nodup → (∀ v : Z, v ∈ zs) →
      (∀ a, mass (ledger a) (fun _ : H => False) = W.zero) →
      (∀ a (A B : H → Prop),
        (∀ h, ¬ (A h ∧ B h)) →
        mass (ledger a) (fun h => A h ∨ B h) =
          W.add (mass (ledger a) A) (mass (ledger a) B)) →
      ∀ a, PaperFiniteChanceSum W zs q ledger mass readout a =
        mass (ledger a) (fun h => q h = a)) ∧
    (∀ (a : Q) (zero : Weight) (add : Weight → Weight → Weight),
      (∀ h, Supports (ledger a) h → q h = a) →
      (∀ (A B : H → Prop),
        (∀ h, ¬ (A h ∧ B h)) →
        mass (ledger a) (fun h => A h ∨ B h) =
          add (mass (ledger a) A) (mass (ledger a) B)) →
      (∀ (E : H → Prop),
        (∀ h, ¬ (E h ∧ Supports (ledger a) h)) →
        mass (ledger a) E = zero) →
      ∀ v, PaperFiberReadoutChance q ledger mass readout a v =
        mass (ledger a) (fun h => readout h = v)) := by
  rcases paper_probability_fiber_split q q' ledger targetLedger Supports
    TargetSupports pushed mixture readout mass hq with ⟨h1, h2, h3⟩
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · intro W zs hnodup hcomplete hempty hadd
    exact paper_finite_chance_sum_eq_fiber q ledger mass readout W zs
      hnodup hcomplete hempty hadd
  · intro a zero add hsupport hadd hvanish
    exact paper_fiber_chance_eq_unrestricted_at q ledger Supports mass
      readout a zero add hsupport hadd hvanish

/-- The paper's name for unresolved readout with stable fiber transport. -/
def StableProbability
    {H Q H' Q' Ledger Ledger' TargetMeasure Z : Type}
    (q : H → Q) (readout : H → Z) (q' : H' → Q')
    (ledger : Q → Ledger) (targetLedger : Q' → Ledger')
    (Supports : Ledger → H → Prop) (TargetSupports : Ledger' → H' → Prop)
    (pushed mixture : Q → TargetMeasure) : Prop :=
  NontrivialStableFiberChance q readout q' ledger targetLedger Supports
    TargetSupports pushed mixture

/-- Stable probability is stable transport with a readout that fails to
descend through the source quotient. -/
theorem stable_probability_iff_stable_and_not_descends
    {H Q H' Q' Ledger Ledger' TargetMeasure Z : Type}
    (q : H → Q) (readout : H → Z) (q' : H' → Q')
    (ledger : Q → Ledger) (targetLedger : Q' → Ledger')
    (Supports : Ledger → H → Prop) (TargetSupports : Ledger' → H' → Prop)
    (pushed mixture : Q → TargetMeasure) (hq : Function.Surjective q) :
    StableProbability q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture ↔
      StableLayerChance q q' ledger targetLedger Supports TargetSupports
        pushed mixture ∧ ¬ ReadoutDescends q readout := by
  have hdesc := readout_descends_iff_no_unresolved_obstruction q readout hq
  have hunresolved := unresolved_readout_iff_not_empty_obstruction q readout
  constructor
  · rintro ⟨hu, hs⟩
    exact ⟨hs, fun hd => (hunresolved.mp hu) (hdesc.mp hd)⟩
  · rintro ⟨hs, hnot⟩
    refine ⟨hunresolved.mpr ?_, hs⟩
    intro hempty
    exact hnot (hdesc.mpr hempty)

/-- F23 with stable probability also characterized by stability and failure
of deterministic readout descent. The finite-mass assumptions remain scoped
to clause (iv), and support assumptions to clause (v). -/
theorem paper_probability_fiber_split_per_clause_stable
    {H Q H' Q' Ledger Ledger' TargetMeasure Z Weight : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure)
    (readout : H → Z) (mass : Ledger → (H → Prop) → Weight)
    (hq : Function.Surjective q) :
    (((ReadoutDescends q readout ↔
        ∀ h h', q h = q h' → readout h = readout h') ∧
      (ReadoutDescends q readout ∨ UnresolvedReadout q readout) ∧
      ¬ (ReadoutDescends q readout ∧ UnresolvedReadout q readout)) ∧
    (∀ rbar : Q → Z, (∀ h, rbar (q h) = readout h) → ∀ a v,
      ((v = rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun h => q h = a)) ∧
        (v ≠ rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun _ => False))) ∧
      ((v = rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun h => q h = a)) ∧
        (v ≠ rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun _ => False)))) ∧
    (NontrivialStableFiberChance q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture → ¬ ReadoutDescends q readout) ∧
    (∀ (W : FiniteWeightMonoid Weight) (zs : List Z),
      zs.Nodup → (∀ v : Z, v ∈ zs) →
      (∀ a, mass (ledger a) (fun _ : H => False) = W.zero) →
      (∀ a (A B : H → Prop),
        (∀ h, ¬ (A h ∧ B h)) →
        mass (ledger a) (fun h => A h ∨ B h) =
          W.add (mass (ledger a) A) (mass (ledger a) B)) →
      ∀ a, PaperFiniteChanceSum W zs q ledger mass readout a =
        mass (ledger a) (fun h => q h = a)) ∧
    (∀ (a : Q) (zero : Weight) (add : Weight → Weight → Weight),
      (∀ h, Supports (ledger a) h → q h = a) →
      (∀ (A B : H → Prop),
        (∀ h, ¬ (A h ∧ B h)) →
        mass (ledger a) (fun h => A h ∨ B h) =
          add (mass (ledger a) A) (mass (ledger a) B)) →
      (∀ (E : H → Prop),
        (∀ h, ¬ (E h ∧ Supports (ledger a) h)) →
        mass (ledger a) E = zero) →
      ∀ v, PaperFiberReadoutChance q ledger mass readout a v =
        mass (ledger a) (fun h => readout h = v))) ∧
    (StableProbability q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture ↔
      StableLayerChance q q' ledger targetLedger Supports TargetSupports
        pushed mixture ∧ ¬ ReadoutDescends q readout) := by
  exact ⟨paper_probability_fiber_split_per_clause q q' ledger targetLedger
    Supports TargetSupports pushed mixture readout mass hq,
    stable_probability_iff_stable_and_not_descends q readout q' ledger
      targetLedger Supports TargetSupports pushed mixture hq⟩

/-- For a finite ledger with strictly positive weight exactly on each named
fiber, point mass is equivalent to deterministic descent; two positive
readout values characterize unresolvedness. -/
theorem finite_positive_fiber_chance_criterion
    {H Q Ledger Z : Type} [Fintype H]
    (q : H → Q) (ledger : Q → Ledger) (readout : H → Z)
    (mass : Ledger → (H → Prop) → ℝ) (w : Q → H → ℝ)
    (hq : Function.Surjective q)
    (hnonneg : ∀ a h, 0 ≤ w a h)
    (hnormal : ∀ a, (∑ h : H, w a h) = 1)
    (hsupport : ∀ a h, 0 < w a h ↔ q h = a)
    (hrep : ∀ a (E : H → Prop) [DecidablePred E],
      mass (ledger a) E = ∑ h : H, if E h then w a h else 0) :
    (ReadoutDescends q readout ↔
      ∀ a, ∃ v, PaperFiberReadoutChance q ledger mass readout a v = 1) ∧
    (UnresolvedReadout q readout ↔
      ∃ a v v', v ≠ v' ∧
        0 < PaperFiberReadoutChance q ledger mass readout a v ∧
        0 < PaperFiberReadoutChance q ledger mass readout a v') := by
  classical
  have hchance (a : Q) (v : Z) :
      PaperFiberReadoutChance q ledger mass readout a v =
        ∑ h : H, if q h = a ∧ readout h = v then w a h else 0 :=
    hrep a (fun h => q h = a ∧ readout h = v)
  have hpos (a : Q) (v : Z) :
      0 < PaperFiberReadoutChance q ledger mass readout a v ↔
        ∃ h : H, q h = a ∧ readout h = v := by
    rw [hchance]
    have hn : ∀ h ∈ (Finset.univ : Finset H),
        0 ≤ (if q h = a ∧ readout h = v then w a h else 0) := by
      intro h _
      split_ifs <;> simp [hnonneg]
    rw [Finset.sum_pos_iff_of_nonneg hn]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hh⟩
      by_cases he : q h = a ∧ readout h = v
      · exact ⟨h, he⟩
      · simp [he] at hh
    · rintro ⟨h, hqa, hrv⟩
      exact ⟨h, by simpa [hqa, hrv] using (hsupport a h).2 hqa⟩
  have hpoint (a : Q) (v : Z)
      (hv : PaperFiberReadoutChance q ledger mass readout a v = 1) :
      ∀ h, q h = a → readout h = v := by
    have hle : ∀ h ∈ (Finset.univ : Finset H),
        (if q h = a ∧ readout h = v then w a h else 0) ≤ w a h := by
      intro h _
      split_ifs <;> simp [hnonneg]
    have hsum : (∑ h : H, if q h = a ∧ readout h = v then w a h else 0) =
        ∑ h : H, w a h := by
      rw [← hchance, hv, hnormal]
    have hterms := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
    intro h hqa
    by_contra hne
    have hzero : w a h = 0 := by
      have ht := hterms h (Finset.mem_univ h)
      simpa [hqa, hne] using ht.symm
    exact (ne_of_gt ((hsupport a h).2 hqa)) hzero
  have hdesc : ReadoutDescends q readout ↔
      ∀ h h', q h = q h' → readout h = readout h' :=
    (paper_probability_as_stable_unresolved_fiber q q ledger ledger
      (fun _ _ => True) (fun _ _ => True) (fun _ => ()) (fun _ => ())
      readout mass hq).2.1
  constructor
  · constructor
    · intro hd a
      obtain ⟨h, hqa⟩ := hq a
      refine ⟨readout h, ?_⟩
      rw [hchance]
      calc
        (∑ x : H, if q x = a ∧ readout x = readout h then w a x else 0) =
            ∑ x : H, w a x := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hxa : q x = a
          · have hr : readout x = readout h := hdesc.mp hd x h (hxa.trans hqa.symm)
            simp [hxa, hr]
          · have hw : w a x = 0 := le_antisymm (le_of_not_gt
              (fun hp => hxa ((hsupport a x).1 hp))) (hnonneg a x)
            simp [hxa, hw]
        _ = 1 := hnormal a
    · intro hp
      apply hdesc.mpr
      intro h h' hqq
      obtain ⟨v, hv⟩ := hp (q h)
      exact (hpoint (q h) v hv h rfl).trans
        (hpoint (q h) v hv h' hqq.symm).symm
  · constructor
    · rintro ⟨⟨h, h'⟩, hobs⟩
      refine ⟨q h, readout h, readout h', hobs.2, ?_, ?_⟩
      · exact (hpos (q h) (readout h)).2 ⟨h, rfl, rfl⟩
      · exact (hpos (q h) (readout h')).2 ⟨h', hobs.1.symm, rfl⟩
    · rintro ⟨a, v, v', hv, hp, hp'⟩
      obtain ⟨h, hqa, hrv⟩ := (hpos a v).1 hp
      obtain ⟨h', hqa', hrv'⟩ := (hpos a v').1 hp'
      exact ⟨(h, h'), hqa.trans hqa'.symm, by
        intro he
        exact hv (hrv.symm.trans (he.trans hrv'))⟩

theorem paper_probability_fiber_split_per_clause_point_mass
    {H Q H' Q' Ledger Ledger' TargetMeasure Z : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure)
    (readout : H → Z) (mass : Ledger → (H → Prop) → ℝ)
    (hq : Function.Surjective q) :
(    (((ReadoutDescends q readout ↔
        ∀ h h', q h = q h' → readout h = readout h') ∧
      (ReadoutDescends q readout ∨ UnresolvedReadout q readout) ∧
      ¬ (ReadoutDescends q readout ∧ UnresolvedReadout q readout)) ∧
    (∀ rbar : Q → Z, (∀ h, rbar (q h) = readout h) → ∀ a v,
      ((v = rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun h => q h = a)) ∧
        (v ≠ rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun _ => False))) ∧
      ((v = rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun h => q h = a)) ∧
        (v ≠ rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun _ => False)))) ∧
    (NontrivialStableFiberChance q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture → ¬ ReadoutDescends q readout) ∧
    (∀ (W : FiniteWeightMonoid ℝ) (zs : List Z),
      zs.Nodup → (∀ v : Z, v ∈ zs) →
      (∀ a, mass (ledger a) (fun _ : H => False) = W.zero) →
      (∀ a (A B : H → Prop),
        (∀ h, ¬ (A h ∧ B h)) →
        mass (ledger a) (fun h => A h ∨ B h) =
          W.add (mass (ledger a) A) (mass (ledger a) B)) →
      ∀ a, PaperFiniteChanceSum W zs q ledger mass readout a =
        mass (ledger a) (fun h => q h = a)) ∧
    (∀ (a : Q) (zero : ℝ) (add : ℝ → ℝ → ℝ),
      (∀ h, Supports (ledger a) h → q h = a) →
      (∀ (A B : H → Prop),
        (∀ h, ¬ (A h ∧ B h)) →
        mass (ledger a) (fun h => A h ∨ B h) =
          add (mass (ledger a) A) (mass (ledger a) B)) →
      (∀ (E : H → Prop),
        (∀ h, ¬ (E h ∧ Supports (ledger a) h)) →
        mass (ledger a) E = zero) →
      ∀ v, PaperFiberReadoutChance q ledger mass readout a v =
        mass (ledger a) (fun h => readout h = v))) ∧
    (StableProbability q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture ↔
      StableLayerChance q q' ledger targetLedger Supports TargetSupports
        pushed mixture ∧ ¬ ReadoutDescends q readout)) ∧
    (∀ [Fintype H] (w : Q → H → ℝ),
      (∀ a h, 0 ≤ w a h) →
      (∀ a, (∑ h : H, w a h) = 1) →
      (∀ a h, 0 < w a h ↔ q h = a) →
      (∀ a (E : H → Prop) [DecidablePred E],
        mass (ledger a) E = ∑ h : H, if E h then w a h else 0) →
      (ReadoutDescends q readout ↔
        ∀ a, ∃ v, PaperFiberReadoutChance q ledger mass readout a v = 1) ∧
      (UnresolvedReadout q readout ↔
        ∃ a v v', v ≠ v' ∧
          0 < PaperFiberReadoutChance q ledger mass readout a v ∧
          0 < PaperFiberReadoutChance q ledger mass readout a v')) := by
  refine ⟨paper_probability_fiber_split_per_clause_stable q q' ledger
    targetLedger Supports TargetSupports pushed mixture readout mass hq, ?_⟩
  intro _ w hnonneg hnormal hsupport hrep
  exact finite_positive_fiber_chance_criterion q ledger readout mass w hq
    hnonneg hnormal hsupport hrep

/-- The total declared weight on one quotient fiber. Off-fiber weights are
ignored, and no decidable equality on the quotient carrier is required. -/
noncomputable def PaperFiberWeightSum {H Q : Type} [Fintype H]
    (q : H → Q) (w : Q → H → ℝ) (a : Q) : ℝ := by
  classical
  exact ∑ h : H, if q h = a then w a h else 0

/-- The original global weight hypotheses imply the weaker fiber-restricted
ones, with the same weights and mass functional. -/
theorem finite_full_support_implies_fiber_restricted
    {H Q Ledger : Type} [Fintype H]
    (q : H → Q) (ledger : Q → Ledger)
    (mass : Ledger → (H → Prop) → ℝ) (w : Q → H → ℝ)
    (hnonneg : ∀ a h, 0 ≤ w a h)
    (hnormal : ∀ a, (∑ h : H, w a h) = 1)
    (hsupport : ∀ a h, 0 < w a h ↔ q h = a)
    (hrep : ∀ a (E : H → Prop) [DecidablePred E],
      mass (ledger a) E = ∑ h : H, if E h then w a h else 0) :
    (∀ a h, q h = a → 0 < w a h) ∧
    (∀ a, PaperFiberWeightSum q w a = 1) ∧
    (∀ a (E : H → Prop) [DecidablePred E],
      (∀ h, E h → q h = a) →
      mass (ledger a) E = ∑ h : H, if E h then w a h else 0) := by
  classical
  refine ⟨fun a h hh => (hsupport a h).2 hh, ?_, fun a E _ _ => hrep a E⟩
  intro a
  rw [PaperFiberWeightSum, ← hnormal a]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : q h = a
  · simp [hh]
  · have hw : w a h = 0 := le_antisymm
      (le_of_not_gt (fun hp => hh ((hsupport a h).1 hp))) (hnonneg a h)
    simp [hh, hw]

/-- For finite normalized strictly positive fiber weights, point-mass chance
is exactly descent, even when the ledger map is non-injective. Representation
of mass is required only for events contained in the named fiber. -/
theorem finite_positive_fiber_chance_criterion_on_fiber
    {H Q Ledger Z : Type} [Fintype H]
    (q : H → Q) (ledger : Q → Ledger) (readout : H → Z)
    (mass : Ledger → (H → Prop) → ℝ) (w : Q → H → ℝ)
    (hq : Function.Surjective q)
    (hpositive : ∀ a h, q h = a → 0 < w a h)
    (hnormal : ∀ a, PaperFiberWeightSum q w a = 1)
    (hrep : ∀ a (E : H → Prop) [DecidablePred E],
      (∀ h, E h → q h = a) →
      mass (ledger a) E = ∑ h : H, if E h then w a h else 0) :
    (ReadoutDescends q readout ↔
      ∀ a, ∃ v, PaperFiberReadoutChance q ledger mass readout a v = 1) ∧
    (UnresolvedReadout q readout ↔
      ∃ a v v', v ≠ v' ∧
        0 < PaperFiberReadoutChance q ledger mass readout a v ∧
        0 < PaperFiberReadoutChance q ledger mass readout a v') := by
  classical
  let cutWeight : Q → H → ℝ := fun a h => if q h = a then w a h else 0
  let cutMass : Q → (H → Prop) → ℝ :=
    fun a E => ∑ h : H, if E h then cutWeight a h else 0
  have hnonneg : ∀ a h, 0 ≤ cutWeight a h := by
    intro a h
    by_cases hh : q h = a
    · simpa [cutWeight, hh] using (hpositive a h hh).le
    · simp [cutWeight, hh]
  have hnormalCut : ∀ a, (∑ h : H, cutWeight a h) = 1 := by
    intro a
    exact hnormal a
  have hsupport : ∀ a h, 0 < cutWeight a h ↔ q h = a := by
    intro a h
    by_cases hh : q h = a
    · simp [cutWeight, hh, hpositive a h hh]
    · simp [cutWeight, hh]
  have hrepCut : ∀ a (E : H → Prop) [DecidablePred E],
      cutMass a E = ∑ h : H, if E h then cutWeight a h else 0 := by
    intro a E _
    unfold cutMass
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : E h <;> simp [hh]
  have hchance : ∀ a v,
      PaperFiberReadoutChance q ledger mass readout a v =
        PaperFiberReadoutChance q id cutMass readout a v := by
    intro a v
    rw [PaperFiberReadoutChance,
      hrep a (fun h => q h = a ∧ readout h = v) (fun _ hh => hh.1)]
    unfold PaperFiberReadoutChance cutMass
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : q h = a ∧ readout h = v
    · simp [hh, cutWeight]
    · simp [hh]
  have hcriterion := finite_positive_fiber_chance_criterion q id readout
    cutMass cutWeight hq hnonneg hnormalCut hsupport hrepCut
  simpa only [← hchance] using hcriterion

/-- A constant Unit ledger satisfies the fiber-restricted hypotheses on two
singleton fibers. The shared mass counts events; it need not be normalized on
the whole carrier, demonstrating that the new clause allows shared ledgers. -/
theorem finite_fiber_restricted_noninjective_ledger_example :
    ∃ (ledger : Bool → Unit) (mass : Unit → (Bool → Prop) → ℝ)
        (w : Bool → Bool → ℝ),
      ¬ Function.Injective ledger ∧
      (∀ a h, (id : Bool → Bool) h = a → 0 < w a h) ∧
      (∀ a, PaperFiberWeightSum id w a = 1) ∧
      (∀ a (E : Bool → Prop) [DecidablePred E],
        (∀ h, E h → h = a) →
        mass (ledger a) E = ∑ h : Bool, if E h then w a h else 0) := by
  classical
  let mass : Unit → (Bool → Prop) → ℝ :=
    fun _ E => ∑ h : Bool, if E h then 1 else 0
  refine ⟨fun _ => (), mass, fun _ _ => 1, ?_, ?_, ?_, ?_⟩
  · intro hinj
    have hbad : false = true := hinj (show (() : Unit) = () from rfl)
    cases hbad
  · intro a h _
    norm_num
  · intro a
    cases a <;> simp [PaperFiberWeightSum]
  · intro a E _ _
    unfold mass
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : E h <;> simp [hh]

/-- F23's original per-clause stability bundle, specialized to real mass,
with the finite point-mass clause scoped to fiber-restricted weight hypotheses.
No finite-carrier or weight hypothesis is imposed on the earlier clauses. -/
theorem paper_probability_fiber_split_per_clause_stable_strengthened
    {H Q H' Q' Ledger Ledger' TargetMeasure Z : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure)
    (readout : H → Z) (mass : Ledger → (H → Prop) → ℝ)
    (hq : Function.Surjective q) :
    ((((ReadoutDescends q readout ↔
        ∀ h h', q h = q h' → readout h = readout h') ∧
      (ReadoutDescends q readout ∨ UnresolvedReadout q readout) ∧
      ¬ (ReadoutDescends q readout ∧ UnresolvedReadout q readout)) ∧
    (∀ rbar : Q → Z, (∀ h, rbar (q h) = readout h) → ∀ a v,
      ((v = rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun h => q h = a)) ∧
        (v ≠ rbar a →
          (fun h => q h = a ∧ readout h = v) = (fun _ => False))) ∧
      ((v = rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun h => q h = a)) ∧
        (v ≠ rbar a →
          PaperFiberReadoutChance q ledger mass readout a v =
            mass (ledger a) (fun _ => False)))) ∧
    (NontrivialStableFiberChance q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture → ¬ ReadoutDescends q readout) ∧
    (∀ (W : FiniteWeightMonoid ℝ) (zs : List Z),
      zs.Nodup → (∀ v : Z, v ∈ zs) →
      (∀ a, mass (ledger a) (fun _ : H => False) = W.zero) →
      (∀ a (A B : H → Prop),
        (∀ h, ¬ (A h ∧ B h)) →
        mass (ledger a) (fun h => A h ∨ B h) =
          W.add (mass (ledger a) A) (mass (ledger a) B)) →
      ∀ a, PaperFiniteChanceSum W zs q ledger mass readout a =
        mass (ledger a) (fun h => q h = a)) ∧
    (∀ (a : Q) (zero : ℝ) (add : ℝ → ℝ → ℝ),
      (∀ h, Supports (ledger a) h → q h = a) →
      (∀ (A B : H → Prop),
        (∀ h, ¬ (A h ∧ B h)) →
        mass (ledger a) (fun h => A h ∨ B h) =
          add (mass (ledger a) A) (mass (ledger a) B)) →
      (∀ (E : H → Prop),
        (∀ h, ¬ (E h ∧ Supports (ledger a) h)) →
        mass (ledger a) E = zero) →
      ∀ v, PaperFiberReadoutChance q ledger mass readout a v =
        mass (ledger a) (fun h => readout h = v))) ∧
    (StableProbability q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture ↔
      StableLayerChance q q' ledger targetLedger Supports TargetSupports
        pushed mixture ∧ ¬ ReadoutDescends q readout)) ∧
    (∀ [Fintype H] (w : Q → H → ℝ),
      (∀ a h, q h = a → 0 < w a h) →
      (∀ a, PaperFiberWeightSum q w a = 1) →
      (∀ a (E : H → Prop) [DecidablePred E],
        (∀ h, E h → q h = a) →
        mass (ledger a) E = ∑ h : H, if E h then w a h else 0) →
      (ReadoutDescends q readout ↔
        ∀ a, ∃ v, PaperFiberReadoutChance q ledger mass readout a v = 1) ∧
      (UnresolvedReadout q readout ↔
        ∃ a v v', v ≠ v' ∧
          0 < PaperFiberReadoutChance q ledger mass readout a v ∧
          0 < PaperFiberReadoutChance q ledger mass readout a v')) := by
  refine ⟨paper_probability_fiber_split_per_clause_stable q q' ledger
    targetLedger Supports TargetSupports pushed mixture readout mass hq, ?_⟩
  intro _ w hpositive hnormal hrep
  exact finite_positive_fiber_chance_criterion_on_fiber q ledger readout mass w
    hq hpositive hnormal hrep

/-- Stable supplies source support at every class. At each class where mass
is disjoint-additive and vanishes off that support, the paper's fiber chance is
the unrestricted readout-event mass; no monoid or finiteness is required. -/
theorem stable_probability_concentrated_every_class
    {H Q H' Q' Ledger Ledger' TargetMeasure Z Weight : Type}
    (q : H → Q) (q' : H' → Q') (ledger : Q → Ledger)
    (targetLedger : Q' → Ledger') (Supports : Ledger → H → Prop)
    (TargetSupports : Ledger' → H' → Prop) (pushed mixture : Q → TargetMeasure)
    (mass : Ledger → (H → Prop) → Weight) (readout : H → Z)
    (hstable : StableLayerChance q q' ledger targetLedger Supports
      TargetSupports pushed mixture) :
    FiberLedgerSupported q ledger Supports ∧
    (∀ (a : Q) (zero : Weight) (add : Weight → Weight → Weight),
      (∀ (A B : H → Prop),
        (∀ h, ¬ (A h ∧ B h)) →
        mass (ledger a) (fun h => A h ∨ B h) =
          add (mass (ledger a) A) (mass (ledger a) B)) →
      (∀ (E : H → Prop),
        (∀ h, ¬ (E h ∧ Supports (ledger a) h)) → mass (ledger a) E = zero) →
      ∀ v, PaperFiberReadoutChance q ledger mass readout a v =
        mass (ledger a) (fun h => readout h = v)) := by
  refine ⟨hstable.1, ?_⟩
  intro a zero add hadd hvanish
  exact paper_fiber_chance_eq_unrestricted_at q ledger Supports mass readout
    a zero add (hstable.1 a) hadd hvanish

/-- Under clause (vi)'s normalized positive fiber weights, stable probability
is exactly stability together with a class whose chance charges two values. -/
theorem stable_probability_iff_stable_and_charges_two
    {H Q H' Q' Ledger Ledger' TargetMeasure Z : Type} [Fintype H]
    (q : H → Q) (readout : H → Z) (q' : H' → Q')
    (ledger : Q → Ledger) (targetLedger : Q' → Ledger')
    (Supports : Ledger → H → Prop) (TargetSupports : Ledger' → H' → Prop)
    (pushed mixture : Q → TargetMeasure)
    (mass : Ledger → (H → Prop) → ℝ) (w : Q → H → ℝ)
    (hq : Function.Surjective q)
    (hpositive : ∀ a h, q h = a → 0 < w a h)
    (hnormal : ∀ a, PaperFiberWeightSum q w a = 1)
    (hrep : ∀ a (E : H → Prop) [DecidablePred E],
      (∀ h, E h → q h = a) →
      mass (ledger a) E = ∑ h : H, if E h then w a h else 0) :
    StableProbability q readout q' ledger targetLedger Supports
        TargetSupports pushed mixture ↔
      StableLayerChance q q' ledger targetLedger Supports TargetSupports
        pushed mixture ∧
      ∃ a v v', v ≠ v' ∧
        0 < PaperFiberReadoutChance q ledger mass readout a v ∧
        0 < PaperFiberReadoutChance q ledger mass readout a v' := by
  have hcharges := (finite_positive_fiber_chance_criterion_on_fiber
    q ledger readout mass w hq hpositive hnormal hrep).2
  constructor
  · rintro ⟨hunresolved, hstable⟩
    exact ⟨hstable, hcharges.mp hunresolved⟩
  · rintro ⟨hstable, hcharged⟩
    exact ⟨hcharges.mpr hcharged, hstable⟩

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ProbabilityAsStableUnresolvedFiber
