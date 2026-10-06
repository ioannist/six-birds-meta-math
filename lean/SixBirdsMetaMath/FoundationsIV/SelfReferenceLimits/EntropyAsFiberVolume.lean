import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
F39 Entropy as Fiber Volume.

Entropy is modeled as the ledgered size/spread of distinctions left unresolved
inside quotient fibers. A nontrivial fiber is only multiplicity until a ledger,
support, and target scope are declared.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.EntropyAsFiberVolume

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- The unresolved fiber over a quotient value. -/
def Fiber {H Q : Type} (q : H → Q) (a : Q) : H → Prop :=
  fun h => q h = a

/-- A fiber ledger assigns an entropy/volume/status value to each unresolved
fiber. This abstracts counting, volume, probability, density, or audit currency. -/
def FiberLedger (H Entropy : Type) : Type :=
  (H → Prop) → Entropy

/-- The local entropy of a quotient fiber under a declared ledger. -/
def FiberEntropy {H Q Entropy : Type} (ledger : FiberLedger H Entropy)
    (q : H → Q) (a : Q) : Entropy :=
  ledger (Fiber q a)

/-- Global entropy is whatever declared aggregator the package uses on local
fiber entropy values. -/
def GlobalQuotientEntropy {Q Entropy Global : Type}
    (weight : Q → Entropy) (fiberEntropy : Q → Entropy)
    (aggregate : (Q → Entropy) → (Q → Entropy) → Global) : Global :=
  aggregate weight fiberEntropy

/-- A quotient fiber has unresolved raw multiplicity when two distinct raw
states lie in the same quotient class. -/
def NontrivialFiber {H Q : Type} (q : H → Q) : Prop :=
  ∃ h h' : H, q h = q h' ∧ h ≠ h'

/-- Unmeasured multiplicity is not entropy until the package declares a ledger. -/
def UnmeasuredFiberMultiplicity {H Q : Type} (q : H → Q)
    (ledgerDeclared : Prop) : Prop :=
  NontrivialFiber q ∧ ¬ ledgerDeclared

/-- A raw-state recovery map exists when the identity readout descends through
the quotient. -/
def RawRecoverable {H Q : Type} (q : H → Q) : Prop :=
  Descends q (fun h : H => h) (fun h : H => h)

/-- Zero raw entropy is the absence of same-fiber raw split pairs. -/
def RawEntropyZero {H Q : Type} (q : H → Q) : Prop :=
  ObstructionEmpty (splitPairObstruction q (fun h : H => h) (fun h : H => h))

/-- Positive raw fiber entropy is represented structurally by an unresolved raw
split pair inside a quotient fiber. -/
def PositiveFiberEntropy {H Q : Type} (q : H → Q) : Prop :=
  ∃ pair, splitPairObstruction q (fun h : H => h) (fun h : H => h) pair

/-- A target readout is resolved by a quotient exactly when it descends through
that quotient. -/
def TargetReadoutDescends {H Q T : Type} (q : H → Q) (target : H → T) : Prop :=
  Descends q (fun h : H => h) target

/-- Zero target entropy is the absence of target variation inside quotient
fibers. -/
def TargetEntropyZero {H Q T : Type} (q : H → Q) (target : H → T) : Prop :=
  ObstructionEmpty (splitPairObstruction q (fun h : H => h) target)

/-- Positive target entropy is represented structurally by target variation
inside a quotient fiber. -/
def TargetUnresolved {H Q T : Type} (q : H → Q) (target : H → T) : Prop :=
  ∃ pair, splitPairObstruction q (fun h : H => h) target pair

/-- Raw entropy may be present even while the declared target is fully resolved. -/
def TargetResolvedDespiteRawEntropy {H Q T : Type} (q : H → Q)
    (target : H → T) : Prop :=
  PositiveFiberEntropy q ∧ TargetEntropyZero q target

/-- A coarser quotient factors through a finer quotient. -/
def QuotientCoarsening {H QFine QCoarse : Type} (qFine : H → QFine)
    (qCoarse : H → QCoarse) : Prop :=
  ∃ collapse : QFine → QCoarse, collapse ∘ qFine = qCoarse

/-- Abstract chain-rule identity for quotient entropy under coarsening. The
extra term records entropy of the fine-fiber label unresolved by the coarse
quotient. -/
def CoarseningEntropyIdentity {H QFine QCoarse Entropy : Type}
    (qFine : H → QFine) (qCoarse : H → QCoarse)
    (entropy : {Q : Type} → (H → Q) → Entropy)
    (mixing : (H → QFine) → (H → QCoarse) → Entropy)
    (combine : Entropy → Entropy → Entropy) : Prop :=
  entropy qCoarse = combine (entropy qFine) (mixing qFine qCoarse)

/-- Entropy monotonicity under coarsening for a declared entropy order. -/
def CoarseningEntropyMonotone {H QFine QCoarse Entropy : Type}
    (qFine : H → QFine) (qCoarse : H → QCoarse)
    (entropy : {Q : Type} → (H → Q) → Entropy) (Le : Entropy → Entropy → Prop) :
    Prop :=
  Le (entropy qFine) (entropy qCoarse)

/-- Strict access extension contracts unresolved fiber entropy when the refined
quotient has an entropy value below the old quotient in the declared order. -/
def StrictExtensionEntropyContraction {H QOld QNew Entropy : Type}
    (qOld : H → QOld) (qNew : H → QNew)
    (entropy : {Q : Type} → (H → Q) → Entropy) (Le : Entropy → Entropy → Prop) :
    Prop :=
  QuotientCoarsening qNew qOld ∧ Le (entropy qNew) (entropy qOld)

/-- An entropy claim is well-formed only after quotient, ledger, support, and
target scope have been declared. -/
def EntropyClaimWellFormed (quotientDeclared ledgerDeclared supportDeclared
    targetScopeDeclared : Prop) : Prop :=
  quotientDeclared ∧ ledgerDeclared ∧ supportDeclared ∧ targetScopeDeclared

/-- Entropy overread: an entropy claim is made while some required declaration
is missing. -/
def EntropyOverread (quotientDeclared ledgerDeclared supportDeclared
    targetScopeDeclared : Prop) : Prop :=
  ¬ EntropyClaimWellFormed quotientDeclared ledgerDeclared supportDeclared
    targetScopeDeclared

/-- Stable entropy law: the declared entropy readout is transported by a
declared continuation. -/
def StableEntropyLaw {Hs Ht Entropy : Type} (continuation : Hs → Ht)
    (sourceEntropy : Hs → Entropy) (targetEntropy : Ht → Entropy)
    (SameEntropy : Entropy → Entropy → Prop) : Prop :=
  ∀ h, SameEntropy (sourceEntropy h) (targetEntropy (continuation h))

/-- Entropy arrow: entropy is a record-status readout and is monotone under the
declared continuation. -/
def EntropyArrow {Hs Ht Entropy : Type} (continuation : Hs → Ht)
    (sourceEntropy : Hs → Entropy) (targetEntropy : Ht → Entropy)
    (Le : Entropy → Entropy → Prop) : Prop :=
  ∀ h, Le (sourceEntropy h) (targetEntropy (continuation h))

/-- Source status vocabulary for entropy claims. -/
inductive EntropyStatus where
  | resolvedFiber
  | positiveFiberEntropy
  | targetResolved
  | targetUnresolved
  | coarseningEntropyIncrease
  | entropyNeutralCoarsening
  | mixingEntropy
  | stableEntropyLaw
  | entropyArrow
  | horizonFiberEntropy
  | unmeasuredFiberMultiplicity
  | presentationDependentEntropy
  | binningArtifact
  | budgetedEntropy
  | entropyOverread
deriving DecidableEq

/-- Meaning assignment for the F39 entropy status vocabulary. -/
def EntropyStatusHolds (resolved positive targetResolved targetUnresolved
    coarseningIncrease neutralCoarsening mixing stable arrow horizon unmeasured
    presentationDependent binning budgeted overread : Prop) : EntropyStatus → Prop
  | EntropyStatus.resolvedFiber => resolved
  | EntropyStatus.positiveFiberEntropy => positive
  | EntropyStatus.targetResolved => targetResolved
  | EntropyStatus.targetUnresolved => targetUnresolved
  | EntropyStatus.coarseningEntropyIncrease => coarseningIncrease
  | EntropyStatus.entropyNeutralCoarsening => neutralCoarsening
  | EntropyStatus.mixingEntropy => mixing
  | EntropyStatus.stableEntropyLaw => stable
  | EntropyStatus.entropyArrow => arrow
  | EntropyStatus.horizonFiberEntropy => horizon
  | EntropyStatus.unmeasuredFiberMultiplicity => unmeasured
  | EntropyStatus.presentationDependentEntropy => presentationDependent
  | EntropyStatus.binningArtifact => binning
  | EntropyStatus.budgetedEntropy => budgeted
  | EntropyStatus.entropyOverread => overread

/-- Fiber membership is quotient equality. -/
theorem fiber_membership_iff {H Q : Type} (q : H → Q) (a : Q) (h : H) :
    Fiber q a h ↔ q h = a := by
  rfl

/-- Raw entropy vanishes exactly when the raw state is recoverable from the
quotient, on the declared support carrier. -/
theorem raw_entropy_zero_iff_recoverable {H Q : Type} (q : H → Q)
    (hq : Function.Surjective q) :
    RawEntropyZero q ↔ RawRecoverable q := by
  exact (descent_repair_normal_form q (fun h : H => h) (fun h : H => h) hq).symm

/-- Target entropy vanishes exactly when the target readout descends through
the quotient. -/
theorem target_entropy_zero_iff_descends {H Q T : Type} (q : H → Q)
    (target : H → T) (hq : Function.Surjective q) :
    TargetEntropyZero q target ↔ TargetReadoutDescends q target := by
  exact (descent_repair_normal_form q (fun h : H => h) target hq).symm

/-- Positive target entropy is exactly failure of target descent, under a
declared quotient carrier. -/
theorem target_unresolved_iff_not_descends {H Q T : Type} (q : H → Q)
    (target : H → T) (hq : Function.Surjective q) :
    TargetUnresolved q target ↔ ¬ TargetReadoutDescends q target := by
  constructor
  · intro hunresolved hdesc
    rcases hunresolved with ⟨pair, hpair⟩
    have hempty :
        ObstructionEmpty (splitPairObstruction q (fun h : H => h) target) :=
      (descent_repair_normal_form q (fun h : H => h) target hq).mp hdesc
    exact hempty pair hpair
  · intro hnot
    classical
    exact Classical.byContradiction (fun hnone => by
      have hempty :
          ObstructionEmpty (splitPairObstruction q (fun h : H => h) target) := by
        intro pair hpair
        exact hnone ⟨pair, hpair⟩
      exact hnot ((descent_repair_normal_form q (fun h : H => h) target hq).mpr hempty))

/-- A coarse quotient fiber is the union of fine quotient fibers lying over the
coarse value. -/
theorem coarse_fiber_decomposes {H QFine QCoarse : Type} (qFine : H → QFine)
    (qCoarse : H → QCoarse) (collapse : QFine → QCoarse)
    (hfactor : collapse ∘ qFine = qCoarse) (b : QCoarse) (h : H) :
    Fiber qCoarse b h ↔ ∃ a : QFine, collapse a = b ∧ Fiber qFine a h := by
  constructor
  · intro hb
    refine ⟨qFine h, ?_, rfl⟩
    calc
      collapse (qFine h) = qCoarse h := congrFun hfactor h
      _ = b := hb
  · intro hexists
    rcases hexists with ⟨a, ha, hfine⟩
    calc
      qCoarse h = collapse (qFine h) := (congrFun hfactor h).symm
      _ = collapse a := by rw [hfine]
      _ = b := ha

/-- The chain-rule identity plus nonnegative mixing term gives monotonicity of
entropy under quotient coarsening. -/
theorem coarsening_identity_to_monotone {H QFine QCoarse Entropy : Type}
    (qFine : H → QFine) (qCoarse : H → QCoarse)
    (entropy : {Q : Type} → (H → Q) → Entropy)
    (mixing : (H → QFine) → (H → QCoarse) → Entropy)
    (combine : Entropy → Entropy → Entropy) (Le : Entropy → Entropy → Prop)
    (hidentity :
      CoarseningEntropyIdentity qFine qCoarse entropy mixing combine)
    (hcombineLe : ∀ a b, Le a (combine a b)) :
    CoarseningEntropyMonotone qFine qCoarse entropy Le := by
  unfold CoarseningEntropyMonotone
  rw [hidentity]
  exact hcombineLe (entropy qFine) (mixing qFine qCoarse)

/-- Well-formed entropy claims are exactly the four required declarations. -/
theorem entropy_claim_well_formed_iff (quotientDeclared ledgerDeclared
    supportDeclared targetScopeDeclared : Prop) :
    EntropyClaimWellFormed quotientDeclared ledgerDeclared supportDeclared
        targetScopeDeclared ↔
      quotientDeclared ∧ ledgerDeclared ∧ supportDeclared ∧ targetScopeDeclared := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
Entropy as Fiber Volume Normal Form. Entropy is a ledgered fiber quantity; zero
raw or target entropy is exactly recoverability/descent through the quotient;
coarse fibers decompose into fine fibers; and the declared chain-rule identity
implies monotonicity under coarsening.
-/
theorem entropy_as_fiber_volume {H Q T QFine QCoarse Entropy : Type}
    (q : H → Q) (target : H → T) (qFine : H → QFine)
    (qCoarse : H → QCoarse) (collapse : QFine → QCoarse)
    (entropy : {Q' : Type} → (H → Q') → Entropy)
    (mixing : (H → QFine) → (H → QCoarse) → Entropy)
    (combine : Entropy → Entropy → Entropy) (Le : Entropy → Entropy → Prop)
    (hq : Function.Surjective q)
    (hfactor : collapse ∘ qFine = qCoarse)
    (hidentity :
      CoarseningEntropyIdentity qFine qCoarse entropy mixing combine)
    (hcombineLe : ∀ a b, Le a (combine a b)) :
    (RawEntropyZero q ↔ RawRecoverable q) ∧
      (TargetEntropyZero q target ↔ TargetReadoutDescends q target) ∧
        (TargetUnresolved q target ↔ ¬ TargetReadoutDescends q target) ∧
          (∀ b h, Fiber qCoarse b h ↔
            ∃ a : QFine, collapse a = b ∧ Fiber qFine a h) ∧
            CoarseningEntropyMonotone qFine qCoarse entropy Le := by
  exact ⟨raw_entropy_zero_iff_recoverable q hq,
    target_entropy_zero_iff_descends q target hq,
    target_unresolved_iff_not_descends q target hq,
    fun b h => coarse_fiber_decomposes qFine qCoarse collapse hfactor b h,
    coarsening_identity_to_monotone qFine qCoarse entropy mixing combine Le
      hidentity hcombineLe⟩


/-- The declared zero law relates the actual entropy value to singleton fibers. -/
theorem paper_entropy_as_fiber_volume {H Q T QFine QCoarse Entropy : Type}
    (q : H → Q) (target : H → T) (qFine : H → QFine)
    (qCoarse : H → QCoarse) (collapse : QFine → QCoarse)
    (entropy : {Q' : Type} → (H → Q') → Entropy) (zero : Entropy)
    (mixing : (H → QFine) → (H → QCoarse) → Entropy)
    (combine : Entropy → Entropy → Entropy) (Le : Entropy → Entropy → Prop)
    (hq : Function.Surjective q)
    (hzero : ∀ {Q' : Type} (q' : H → Q'),
      entropy q' = zero ↔ ∀ x y, q' x = q' y → x = y)
    (hfactor : collapse ∘ qFine = qCoarse)
    (hidentity : CoarseningEntropyIdentity qFine qCoarse entropy mixing combine)
    (hcombineLe : ∀ a b, Le a (combine a b)) :
    (entropy q = zero ↔ RawEntropyZero q) ∧
      (TargetEntropyZero q target ↔ TargetReadoutDescends q target) ∧
      (TargetUnresolved q target ↔ ¬ TargetReadoutDescends q target) ∧
      (∀ b h, Fiber qCoarse b h ↔
        ∃ a : QFine, collapse a = b ∧ Fiber qFine a h) ∧
      CoarseningEntropyMonotone qFine qCoarse entropy Le := by
  have hz : entropy q = zero ↔ RawEntropyZero q := by
    rw [hzero]
    constructor
    · intro hinj pair hpair
      exact hpair.2 (hinj pair.1 pair.2 hpair.1)
    · intro hempty x y heq
      exact Classical.byContradiction (fun hne => hempty (x,y) ⟨heq, hne⟩)
  exact ⟨hz, target_entropy_zero_iff_descends q target hq,
    target_unresolved_iff_not_descends q target hq,
    fun b h => coarse_fiber_decomposes qFine qCoarse collapse hfactor b h,
    coarsening_identity_to_monotone qFine qCoarse entropy mixing combine Le
      hidentity hcombineLe⟩


/-- A zero mixing cost for adjoining the target is exactly target descent,
provided zero cost characterizes equality of the two fiber relations. -/
theorem target_adjoining_mixing_zero_iff_descends
    {H Q T Entropy : Type} (q : H → Q) (t : H → T)
    (m : (H → Q × T) → (H → Q) → Entropy) (zero : Entropy)
    (hq : Function.Surjective q)
    (hzero : ∀ qF qC, m qF qC = zero ↔
      ∀ x y, qF x = qF y ↔ qC x = qC y) :
    m (fun h => (q h, t h)) q = zero ↔ TargetReadoutDescends q t := by
  constructor
  · intro hm
    have hfiber := (hzero (fun h => (q h, t h)) q).1 hm
    have hempty : TargetEntropyZero q t := by
      intro ⟨x,y⟩ ⟨hxy,hne⟩
      have heq : (q x, t x) = (q y, t y) := (hfiber x y).2 hxy
      exact hne (congrArg Prod.snd heq)
    exact (target_entropy_zero_iff_descends q t hq).1 hempty
  · intro hdesc
    rcases hdesc with ⟨tbar, hcomm⟩
    apply (hzero (fun h => (q h, t h)) q).2
    intro x y
    constructor
    · intro heq
      exact congrArg Prod.fst heq
    · intro hxy
      apply Prod.ext hxy
      calc
        t x = tbar (q x) := (congrFun hcomm x).symm
        _ = tbar (q y) := congrArg tbar hxy
        _ = t y := congrFun hcomm y

/-- F39 with one polymorphic mixing operation for both the general
coarsening identity and the target-adjoining zero criterion. -/
theorem paper_entropy_as_fiber_volume_with_mixing_descent
    {H Q T QFine QCoarse Entropy : Type}
    (q : H → Q) (target : H → T) (qFine : H → QFine)
    (qCoarse : H → QCoarse) (collapse : QFine → QCoarse)
    (entropy : {Q' : Type} → (H → Q') → Entropy) (zero : Entropy)
    (mixing : {QF QC : Type} → (H → QF) → (H → QC) → Entropy)
    (combine : Entropy → Entropy → Entropy) (Le : Entropy → Entropy → Prop)
    (hq : Function.Surjective q)
    (hzero : ∀ {Q' : Type} (q' : H → Q'),
      entropy q' = zero ↔ ∀ x y, q' x = q' y → x = y)
    (hfactor : collapse ∘ qFine = qCoarse)
    (hidentity : CoarseningEntropyIdentity qFine qCoarse entropy
      (fun f c => mixing f c) combine)
    (hcombineLe : ∀ a b, Le a (combine a b))
    (hzeroMix : ∀ (qF : H → Q × T) (qC : H → Q),
      mixing qF qC = zero ↔ ∀ x y, qF x = qF y ↔ qC x = qC y) :
    ((entropy q = zero ↔ RawEntropyZero q) ∧
      (TargetEntropyZero q target ↔ TargetReadoutDescends q target) ∧
      (TargetUnresolved q target ↔ ¬ TargetReadoutDescends q target) ∧
      (∀ b h, Fiber qCoarse b h ↔
        ∃ a : QFine, collapse a = b ∧ Fiber qFine a h) ∧
      CoarseningEntropyMonotone qFine qCoarse entropy Le) ∧
    (mixing (fun h => (q h, target h)) q = zero ↔
      TargetReadoutDescends q target) := by
  exact ⟨paper_entropy_as_fiber_volume q target qFine qCoarse collapse
      entropy zero (fun f c => mixing f c) combine Le hq hzero hfactor
      hidentity hcombineLe,
    target_adjoining_mixing_zero_iff_descends q target
      (fun f c => mixing f c) zero hq hzeroMix⟩

/-- Only the target-adjoining pair needs a zero-mixing fiber criterion. -/
theorem target_adjoining_single_pair_zero_iff_descends
    {H Q T Entropy : Type} (q : H → Q) (t : H → T)
    (m : (H → Q × T) → (H → Q) → Entropy) (zero : Entropy)
    (hq : Function.Surjective q)
    (hzeroPair : m (fun h => (q h, t h)) q = zero ↔
      ∀ x y, (q x, t x) = (q y, t y) ↔ q x = q y) :
    m (fun h => (q h, t h)) q = zero ↔ TargetReadoutDescends q t := by
  constructor
  · intro hm
    have hfiber := hzeroPair.mp hm
    have hempty : TargetEntropyZero q t := by
      intro ⟨x,y⟩ ⟨hxy,hne⟩
      exact hne (congrArg Prod.snd ((hfiber x y).2 hxy))
    exact (target_entropy_zero_iff_descends q t hq).1 hempty
  · rintro ⟨tbar, hcomm⟩
    apply hzeroPair.mpr
    intro x y
    constructor
    · exact fun heq => congrArg Prod.fst heq
    · intro hxy
      apply Prod.ext hxy
      calc
        t x = tbar (q x) := (congrFun hcomm x).symm
        _ = tbar (q y) := congrArg tbar hxy
        _ = t y := congrFun hcomm y

/-- F39 with the zero-mixing hypothesis restricted to the displayed pair. -/
theorem paper_entropy_as_fiber_volume_single_pair
    {H Q T QFine QCoarse Entropy : Type}
    (q : H → Q) (target : H → T) (qFine : H → QFine)
    (qCoarse : H → QCoarse) (collapse : QFine → QCoarse)
    (entropy : {Q' : Type} → (H → Q') → Entropy) (zero : Entropy)
    (mixing : {QF QC : Type} → (H → QF) → (H → QC) → Entropy)
    (combine : Entropy → Entropy → Entropy) (Le : Entropy → Entropy → Prop)
    (hq : Function.Surjective q)
    (hzero : ∀ {Q' : Type} (q' : H → Q'),
      entropy q' = zero ↔ ∀ x y, q' x = q' y → x = y)
    (hfactor : collapse ∘ qFine = qCoarse)
    (hidentity : CoarseningEntropyIdentity qFine qCoarse entropy
      (fun f c => mixing f c) combine)
    (hcombineLe : ∀ a b, Le a (combine a b))
    (hzeroPair : mixing (fun h => (q h, target h)) q = zero ↔
      ∀ x y, (q x, target x) = (q y, target y) ↔ q x = q y) :
    ((entropy q = zero ↔ RawEntropyZero q) ∧
      (TargetEntropyZero q target ↔ TargetReadoutDescends q target) ∧
      (TargetUnresolved q target ↔ ¬ TargetReadoutDescends q target) ∧
      (∀ b h, Fiber qCoarse b h ↔
        ∃ a : QFine, collapse a = b ∧ Fiber qFine a h) ∧
      CoarseningEntropyMonotone qFine qCoarse entropy Le) ∧
    (mixing (fun h => (q h, target h)) q = zero ↔
      TargetReadoutDescends q target) := by
  exact ⟨paper_entropy_as_fiber_volume q target qFine qCoarse collapse
      entropy zero (fun f c => mixing f c) combine Le hq hzero hfactor
      hidentity hcombineLe,
    target_adjoining_single_pair_zero_iff_descends q target
      (fun f c => mixing f c) zero hq hzeroPair⟩

/-- F39 with the pairwise zero-mixing law confined to the final moreover
clause. -/
theorem paper_entropy_as_fiber_volume_conditional_mixing
    {H Q T QFine QCoarse Entropy : Type}
    (q : H → Q) (target : H → T) (qFine : H → QFine)
    (qCoarse : H → QCoarse) (collapse : QFine → QCoarse)
    (entropy : {Q' : Type} → (H → Q') → Entropy) (zero : Entropy)
    (mixing : {QF QC : Type} → (H → QF) → (H → QC) → Entropy)
    (combine : Entropy → Entropy → Entropy) (Le : Entropy → Entropy → Prop)
    (hq : Function.Surjective q)
    (hzero : ∀ {Q' : Type} (q' : H → Q'),
      entropy q' = zero ↔ ∀ x y, q' x = q' y → x = y)
    (hfactor : collapse ∘ qFine = qCoarse)
    (hidentity : CoarseningEntropyIdentity qFine qCoarse entropy
      (fun f c => mixing f c) combine)
    (hcombineLe : ∀ a b, Le a (combine a b)) :
    (entropy q = zero ↔ RawEntropyZero q) ∧
    (TargetEntropyZero q target ↔ TargetReadoutDescends q target) ∧
    (TargetUnresolved q target ↔ ¬ TargetReadoutDescends q target) ∧
    (∀ b h, Fiber qCoarse b h ↔
      ∃ a : QFine, collapse a = b ∧ Fiber qFine a h) ∧
    CoarseningEntropyMonotone qFine qCoarse entropy Le ∧
    ((mixing (fun h => (q h, target h)) q = zero ↔
      ∀ x y, (q x, target x) = (q y, target y) ↔ q x = q y) →
      (mixing (fun h => (q h, target h)) q = zero ↔
        TargetReadoutDescends q target) ∧
      (mixing (fun h => (q h, target h)) q = zero ↔
        TargetEntropyZero q target)) := by
  rcases paper_entropy_as_fiber_volume q target qFine qCoarse collapse
    entropy zero (fun f c => mixing f c) combine Le hq hzero hfactor
    hidentity hcombineLe with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro hzeroPair
  have hm := target_adjoining_single_pair_zero_iff_descends q target
    (fun f c => mixing f c) zero hq hzeroPair
  exact ⟨hm, hm.trans h2.symm⟩

/-- The finite fiber containing a history. -/
noncomputable def shannonFiber {H Q : Type} [Fintype H]
    (q : H → Q) (h : H) : Finset H := by
  classical
  exact Finset.univ.filter (fun x => q x = q h)

/-- Average logarithmic fiber size for a finite, nonempty history carrier. -/
noncomputable def shannonFiberEntropy {H Q : Type} [Fintype H]
    (q : H → Q) : ℝ :=
  (∑ h : H, Real.log ((shannonFiber q h).card : ℝ)) /
    (Fintype.card H : ℝ)

/-- Mixing cost of forgetting a finer quotient label. -/
noncomputable def shannonFiberMixing {H QFine QCoarse : Type} [Fintype H]
    (qFine : H → QFine) (qCoarse : H → QCoarse) : ℝ :=
  shannonFiberEntropy qCoarse - shannonFiberEntropy qFine

/-- A refinement enlarges each fiber, so its finite Shannon mixing cost is
nonnegative and vanishes exactly when no fiber distinction is lost. -/
theorem shannon_fiber_mixing_nonneg_and_zero_iff
    {H QFine QCoarse : Type} [Fintype H] [Nonempty H]
    (qFine : H → QFine) (qCoarse : H → QCoarse)
    (hfactor : QuotientCoarsening qFine qCoarse) :
    0 ≤ shannonFiberMixing qFine qCoarse ∧
    (shannonFiberMixing qFine qCoarse = 0 ↔
      ∀ x y, qFine x = qFine y ↔ qCoarse x = qCoarse y) := by
  classical
  obtain ⟨collapse, hcollapse⟩ := hfactor
  have hcoarse : ∀ x y, qFine x = qFine y → qCoarse x = qCoarse y := by
    intro x y hxy
    have hx := congrFun hcollapse x
    have hy := congrFun hcollapse y
    exact hy.symm.trans ((congrArg collapse hxy).symm.trans hx) |>.symm
  have hmem (q : H → QFine) (h x : H) :
      x ∈ shannonFiber q h ↔ q x = q h := by
    simp [shannonFiber]
  have hsubset (h : H) : shannonFiber qFine h ⊆ shannonFiber qCoarse h := by
    intro x hx
    have hqx : qFine x = qFine h := by simpa [shannonFiber] using hx
    simp [shannonFiber, hcoarse x h hqx]
  have hpos (q : H → QFine) (h : H) :
      0 < ((shannonFiber q h).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨h, by simp [shannonFiber]⟩)
  have hposCoarse (h : H) :
      0 < ((shannonFiber qCoarse h).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨h, by simp [shannonFiber]⟩)
  have hlogle (h : H) :
      Real.log ((shannonFiber qFine h).card : ℝ) ≤
        Real.log ((shannonFiber qCoarse h).card : ℝ) :=
    Real.log_le_log (hpos qFine h)
      (by exact_mod_cast Finset.card_le_card (hsubset h))
  have hsumle :
      (∑ h : H, Real.log ((shannonFiber qFine h).card : ℝ)) ≤
        ∑ h : H, Real.log ((shannonFiber qCoarse h).card : ℝ) := by
    exact Finset.sum_le_sum (fun h _ => hlogle h)
  have hdenom : (0 : ℝ) < (Fintype.card H : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hEntropyLe : shannonFiberEntropy qFine ≤
      shannonFiberEntropy qCoarse := by
    unfold shannonFiberEntropy
    exact div_le_div_of_nonneg_right hsumle hdenom.le
  constructor
  · exact sub_nonneg.mpr hEntropyLe
  · constructor
    · intro hzero x y
      have hEeq : shannonFiberEntropy qFine =
          shannonFiberEntropy qCoarse := by
        exact (sub_eq_zero.mp hzero).symm
      have hsumEq :
          (∑ h : H, Real.log ((shannonFiber qFine h).card : ℝ)) =
            ∑ h : H, Real.log ((shannonFiber qCoarse h).card : ℝ) := by
        exact (div_left_inj' hdenom.ne').mp hEeq
      have hlogEq (h : H) :
          Real.log ((shannonFiber qFine h).card : ℝ) =
            Real.log ((shannonFiber qCoarse h).card : ℝ) :=
        (Finset.sum_eq_sum_iff_of_le
          (fun h _ => hlogle h)).mp hsumEq h (Finset.mem_univ h)
      have hcardEq (h : H) :
          (shannonFiber qFine h).card = (shannonFiber qCoarse h).card := by
        exact_mod_cast Real.log_injOn_pos (hpos qFine h)
          (hposCoarse h) (hlogEq h)
      have hfiberEq (h : H) : shannonFiber qFine h = shannonFiber qCoarse h :=
        Finset.eq_of_subset_of_card_le (hsubset h) (hcardEq h).ge
      constructor
      · exact hcoarse x y
      · intro hxy
        have hy : y ∈ shannonFiber qCoarse x := by
          simpa [shannonFiber] using hxy.symm
        have hy' : y ∈ shannonFiber qFine x := (hfiberEq x).symm ▸ hy
        have hfine : qFine y = qFine x := by
          simpa [shannonFiber] using hy'
        exact hfine.symm
    · intro hfibers
      apply sub_eq_zero.mpr
      have hterm (h : H) : shannonFiber qFine h =
          shannonFiber qCoarse h := by
        ext x
        simp only [shannonFiber, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact hfibers x h
      unfold shannonFiberEntropy
      congr 1
      apply Finset.sum_congr rfl
      intro h _
      rw [hterm h]

/-- The finite Shannon entropy obeys the coarsening chain equation with
addition as combination and the mixing difference as the extra term. -/
theorem shannon_fiber_chain_identity
    {H QFine QCoarse : Type} [Fintype H]
    (qFine : H → QFine) (qCoarse : H → QCoarse) :
    shannonFiberEntropy qCoarse =
      shannonFiberEntropy qFine + shannonFiberMixing qFine qCoarse := by
  unfold shannonFiberMixing
  ring

/-- For the target-adjoined refinement, Shannon mixing vanishes exactly when
the target has no unresolved variation inside the original fibers. -/
theorem shannon_target_entropy_zero_iff_mixing_zero
    {H Q T : Type} [Fintype H] [Nonempty H]
    (q : H → Q) (target : H → T) :
    TargetEntropyZero q target ↔
      shannonFiberMixing (fun h => (q h, target h)) q = 0 := by
  have hfactor : QuotientCoarsening (fun h => (q h, target h)) q := by
    exact ⟨Prod.fst, rfl⟩
  have hm := (shannon_fiber_mixing_nonneg_and_zero_iff
    (fun h => (q h, target h)) q hfactor).2
  constructor
  · intro ht
    apply hm.mpr
    intro x y
    constructor
    · intro hxy
      exact congrArg Prod.fst hxy
    · intro hxy
      exact Prod.ext hxy (Classical.byContradiction (fun hne =>
        ht (x, y) ⟨hxy, hne⟩))
  · intro hmzero pair hobs
    have hfibers := hm.mp hmzero pair.1 pair.2
    exact hobs.2 ((Prod.mk.inj (hfibers.mpr hobs.1)).2)

/-- The realizable finite Shannon package: additive chain identity, monotonicity
for the declared refinement, exact zero criterion, and target resolution. -/
theorem paper_shannon_fiber_entropy_instance
    {H QFine QCoarse : Type} [Fintype H] [Nonempty H]
    (qFine : H → QFine) (qCoarse : H → QCoarse)
    (hfactor : QuotientCoarsening qFine qCoarse) :
    CoarseningEntropyIdentity qFine qCoarse
      (fun q => shannonFiberEntropy q)
      (fun f c => shannonFiberMixing f c) (· + ·) ∧
    CoarseningEntropyMonotone qFine qCoarse
      (fun q => shannonFiberEntropy q) (· ≤ ·) ∧
    (shannonFiberMixing qFine qCoarse = 0 ↔
      ∀ x y, qFine x = qFine y ↔ qCoarse x = qCoarse y) ∧
    (∀ {Q T : Type} (q : H → Q) (target : H → T),
      TargetEntropyZero q target ↔
        shannonFiberMixing (fun h => (q h, target h)) q = 0) := by
  have hm := shannon_fiber_mixing_nonneg_and_zero_iff qFine qCoarse hfactor
  refine ⟨shannon_fiber_chain_identity qFine qCoarse, ?_, hm.2, ?_⟩
  · exact sub_nonneg.mp hm.1
  · intro Q T q target
    exact shannon_target_entropy_zero_iff_mixing_zero q target

/-- The global monotonicity premise of the abstract F39 bundle cannot hold
for real addition: a negative mixing argument reverses the inequality. -/
theorem real_add_not_globally_increasing :
    ¬ (∀ a b : ℝ, a ≤ a + b) := by
  intro h
  have hbad := h 0 (-1)
  norm_num at hbad

/-- F39 with combine monotonicity required only at the actual fine entropy and
mixing value, allowing real addition with nonnegative coarsening mixing. -/
theorem paper_entropy_as_fiber_volume_conditional_mixing_at_pair
    {H Q T QFine QCoarse Entropy : Type}
    (q : H → Q) (target : H → T) (qFine : H → QFine)
    (qCoarse : H → QCoarse) (collapse : QFine → QCoarse)
    (entropy : {Q' : Type} → (H → Q') → Entropy) (zero : Entropy)
    (mixing : {QF QC : Type} → (H → QF) → (H → QC) → Entropy)
    (combine : Entropy → Entropy → Entropy) (Le : Entropy → Entropy → Prop)
    (hq : Function.Surjective q)
    (hzero : ∀ {Q' : Type} (q' : H → Q'),
      entropy q' = zero ↔ ∀ x y, q' x = q' y → x = y)
    (hfactor : collapse ∘ qFine = qCoarse)
    (hidentity : CoarseningEntropyIdentity qFine qCoarse entropy
      (fun f c => mixing f c) combine)
    (hcombineLe : Le (entropy qFine)
      (combine (entropy qFine) (mixing qFine qCoarse))) :
    (entropy q = zero ↔ RawEntropyZero q) ∧
    (TargetEntropyZero q target ↔ TargetReadoutDescends q target) ∧
    (TargetUnresolved q target ↔ ¬ TargetReadoutDescends q target) ∧
    (∀ b h, Fiber qCoarse b h ↔
      ∃ a : QFine, collapse a = b ∧ Fiber qFine a h) ∧
    CoarseningEntropyMonotone qFine qCoarse entropy Le ∧
    ((mixing (fun h => (q h, target h)) q = zero ↔
      ∀ x y, (q x, target x) = (q y, target y) ↔ q x = q y) →
      (mixing (fun h => (q h, target h)) q = zero ↔
        TargetReadoutDescends q target) ∧
      (mixing (fun h => (q h, target h)) q = zero ↔
        TargetEntropyZero q target)) := by
  have hz : entropy q = zero ↔ RawEntropyZero q := by
    rw [hzero]
    constructor
    · intro hinj pair hpair
      exact hpair.2 (hinj pair.1 pair.2 hpair.1)
    · intro hempty x y heq
      exact Classical.byContradiction (fun hne => hempty (x, y) ⟨heq, hne⟩)
  have hmono : CoarseningEntropyMonotone qFine qCoarse entropy Le := by
    unfold CoarseningEntropyMonotone
    rw [hidentity]
    exact hcombineLe
  refine ⟨hz, target_entropy_zero_iff_descends q target hq,
    target_unresolved_iff_not_descends q target hq,
    fun b h => coarse_fiber_decomposes qFine qCoarse collapse hfactor b h,
    hmono, ?_⟩
  intro hzeroPair
  have hm := target_adjoining_single_pair_zero_iff_descends q target
    (fun f c => mixing f c) zero hq hzeroPair
  exact ⟨hm, hm.trans (target_entropy_zero_iff_descends q target hq).symm⟩

/-- Finite Shannon fiber entropy vanishes exactly when every fiber is a
singleton. This supplies the abstract entropy zero law for every readout. -/
theorem shannon_fiber_entropy_zero_iff
    {H Q : Type} [Fintype H] [Nonempty H] (q : H → Q) :
    shannonFiberEntropy q = 0 ↔ ∀ x y, q x = q y → x = y := by
  classical
  have hidFiber : ∀ h : H, shannonFiber (id : H → H) h = {h} := by
    intro h
    ext x
    simp [shannonFiber]
  have hid : shannonFiberEntropy (id : H → H) = 0 := by
    simp [shannonFiberEntropy, hidFiber]
  have hm := shannon_fiber_mixing_nonneg_and_zero_iff (id : H → H) q ⟨q, rfl⟩
  constructor
  · intro he x y hxy
    have hmix : shannonFiberMixing (id : H → H) q = 0 := by
      simp [shannonFiberMixing, he, hid]
    exact ((hm.2).1 hmix x y).2 hxy
  · intro hinj
    have hfibers : ∀ x y, (id : H → H) x = id y ↔ q x = q y := by
      intro x y
      exact ⟨congrArg q, hinj x y⟩
    have hmix := (hm.2).2 hfibers
    simpa [shannonFiberMixing, hid] using hmix

/-- The finite real Shannon package supplies every F39 clause with only the
actual combine inequality. Its joint-target zero criterion is proved, so the
final mixing/descent clause is unconditional for this instance. -/
theorem paper_shannon_entropy_as_fiber_volume
    {H Q T QFine QCoarse : Type} [Fintype H] [Nonempty H]
    (q : H → Q) (target : H → T) (qFine : H → QFine)
    (qCoarse : H → QCoarse) (collapse : QFine → QCoarse)
    (hq : Function.Surjective q) (hfactor : collapse ∘ qFine = qCoarse) :
    (shannonFiberEntropy q = 0 ↔ RawEntropyZero q) ∧
    (TargetEntropyZero q target ↔ TargetReadoutDescends q target) ∧
    (TargetUnresolved q target ↔ ¬ TargetReadoutDescends q target) ∧
    (∀ b h, Fiber qCoarse b h ↔
      ∃ a : QFine, collapse a = b ∧ Fiber qFine a h) ∧
    CoarseningEntropyMonotone qFine qCoarse (fun q => shannonFiberEntropy q) (· ≤ ·) ∧
    (shannonFiberMixing (fun h => (q h, target h)) q = 0 ↔
      TargetReadoutDescends q target) ∧
    (shannonFiberMixing (fun h => (q h, target h)) q = 0 ↔
      TargetEntropyZero q target) ∧
    CoarseningEntropyIdentity qFine qCoarse (fun q => shannonFiberEntropy q)
      (fun f c => shannonFiberMixing f c) (· + ·) ∧
    0 ≤ shannonFiberMixing qFine qCoarse ∧
    (shannonFiberMixing qFine qCoarse = 0 ↔
      ∀ x y, qFine x = qFine y ↔ qCoarse x = qCoarse y) := by
  have hpackage := paper_shannon_fiber_entropy_instance qFine qCoarse
    ⟨collapse, hfactor⟩
  have hused : shannonFiberEntropy qFine ≤
      shannonFiberEntropy qFine + shannonFiberMixing qFine qCoarse := by
    calc
      shannonFiberEntropy qFine ≤ shannonFiberEntropy qCoarse := hpackage.2.1
      _ = shannonFiberEntropy qFine + shannonFiberMixing qFine qCoarse := hpackage.1
  obtain ⟨h1, h2, h3, h4, h5, hmore⟩ :=
    paper_entropy_as_fiber_volume_conditional_mixing_at_pair q target qFine
      qCoarse collapse (fun q => shannonFiberEntropy q) 0
      (fun f c => shannonFiberMixing f c) (· + ·) (· ≤ ·) hq
      (fun q' => shannon_fiber_entropy_zero_iff q') hfactor hpackage.1 hused
  have hjoint := shannon_fiber_mixing_nonneg_and_zero_iff
    (fun h => (q h, target h)) q ⟨Prod.fst, rfl⟩
  obtain ⟨hdesc, htarget⟩ := hmore hjoint.2
  exact ⟨h1, h2, h3, h4, h5, hdesc, htarget, hpackage.1,
    (shannon_fiber_mixing_nonneg_and_zero_iff qFine qCoarse
      ⟨collapse, hfactor⟩).1, hpackage.2.2.1⟩

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.EntropyAsFiberVolume
