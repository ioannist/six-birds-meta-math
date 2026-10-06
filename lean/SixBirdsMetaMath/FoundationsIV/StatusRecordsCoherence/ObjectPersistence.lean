import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F19 Object Persistence.

Object identity persists through change exactly when the continuation descends
through the source and target object quotients.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ObjectPersistence

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- Later object identity pulled back along the continuation. -/
def transportedLaterIdentity {Hi Hj Qj : Type} (γ : Hi → Hj) (qj : Hj → Qj) :
    Hi → Qj :=
  fun h => qj (γ h)

/-- Object identity persists along a declared continuation. -/
def Persists {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : Prop :=
  Descends qi γ qj

/-- The persistence split-pair obstruction. -/
def PersistenceObstruction {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : (Hi × Hi) → Prop :=
  splitPairObstruction qi γ qj

/-- No persistence obstruction is present. -/
def PersistenceObstructionEmpty {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (γ : Hi → Hj) (qj : Hj → Qj) : Prop :=
  ObstructionEmpty (PersistenceObstruction qi γ qj)

/-- Split obstruction: one old object can become multiple later objects. -/
def SplitObstruction {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : (Hi × Hi) → Prop :=
  PersistenceObstruction qi γ qj

/-- No split obstruction is present. -/
def SplitObstructionEmpty {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : Prop :=
  ObstructionEmpty (SplitObstruction qi γ qj)

/-- Merge obstruction: distinct old objects become the same transported later
object. -/
def MergeObstruction {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : (Hi × Hi) → Prop :=
  fun pair =>
    transportedLaterIdentity γ qj pair.1 =
      transportedLaterIdentity γ qj pair.2 ∧ qi pair.1 ≠ qi pair.2

/-- No merge obstruction is present. -/
def MergeObstructionEmpty {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : Prop :=
  ObstructionEmpty (MergeObstruction qi γ qj)

/-- Exact endurance: no splitting and no merging. -/
def ExactEndurance {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : Prop :=
  SplitObstructionEmpty qi γ qj ∧ MergeObstructionEmpty qi γ qj

/-- Forward persistence with possible merging. -/
def PersistentWithMerge {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : Prop :=
  SplitObstructionEmpty qi γ qj ∧ ¬ MergeObstructionEmpty qi γ qj

/-- Identity branching: old identity does not determine later identity. -/
def IdentityBranching {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : Prop :=
  ¬ SplitObstructionEmpty qi γ qj ∧ MergeObstructionEmpty qi γ qj

/-- Identity rewrite: both splitting and merging occur. -/
def IdentityRewrite {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : Prop :=
  ¬ SplitObstructionEmpty qi γ qj ∧ ¬ MergeObstructionEmpty qi γ qj

/-- Dissolution obstruction: the transported later identity leaves the declared
viable object region. -/
def DissolutionObstruction {Hi Hj Qj : Type} (γ : Hi → Hj) (qj : Hj → Qj)
    (viable : Qj → Prop) : Hi → Prop :=
  fun h => ¬ viable (qj (γ h))

/-- No dissolution obstruction is present. -/
def DissolutionObstructionEmpty {Hi Hj Qj : Type} (γ : Hi → Hj) (qj : Hj → Qj)
    (viable : Qj → Prop) : Prop :=
  ObstructionEmpty (DissolutionObstruction γ qj viable)

/-- Persistence stays inside the declared target object kind. -/
def ViablePersistence {Hi Hj Qj : Type} (γ : Hi → Hj) (qj : Hj → Qj)
    (viable : Qj → Prop) : Prop :=
  ∀ h : Hi, viable (qj (γ h))

/-- Product quotient for relation-valued persistence. -/
def relationPersistenceQuotient {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (qj : Hj → Qj) : Hi × Hj → Qi × Qj :=
  fun pair => (qi pair.1, qj pair.2)

/-- Relation-valued persistence descends through both object quotients. -/
def RelationValuedPersistence {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (qj : Hj → Qj) (C : Hi × Hj → Prop) : Prop :=
  Descends (relationPersistenceQuotient qi qj) (fun pair : Hi × Hj => pair) C

/-- Relation-valued persistence obstruction. -/
def RelationPersistenceObstruction {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (qj : Hj → Qj) (C : Hi × Hj → Prop) : ((Hi × Hj) × (Hi × Hj)) → Prop :=
  splitPairObstruction (relationPersistenceQuotient qi qj)
    (fun pair : Hi × Hj => pair) C

/-- No relation-valued persistence obstruction is present. -/
def RelationPersistenceObstructionEmpty {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (qj : Hj → Qj) (C : Hi × Hj → Prop) : Prop :=
  ObstructionEmpty (RelationPersistenceObstruction qi qj C)

/-- Identity transport is coherent over a two-step route comparison. -/
def IdentityHolonomyCoherent {Qi Qj Qk : Type} (γbar : Qi → Qj)
    (ηbar : Qj → Qk) (compBar : Qi → Qk) : Prop :=
  ∀ a : Qi, compBar a = ηbar (γbar a)

/-- Identity holonomy defect. -/
def IdentityHolonomyDefect {Qi Qj Qk : Type} (γbar : Qi → Qj)
    (ηbar : Qj → Qk) (compBar : Qi → Qk) : Qi → Prop :=
  fun a => compBar a ≠ ηbar (γbar a)

/-- No identity holonomy defect is present. -/
def IdentityHolonomyDefectEmpty {Qi Qj Qk : Type} (γbar : Qi → Qj)
    (ηbar : Qj → Qk) (compBar : Qi → Qk) : Prop :=
  ObstructionEmpty (IdentityHolonomyDefect γbar ηbar compBar)

/-- Canonical repair carrying both old identity and transported later identity. -/
def persistenceExtension {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : Hi → Qi × Qj :=
  fun h => (qi h, qj (γ h))

/-- The persistence extension retains old identity. -/
def RetainsOldIdentity {Hi Qi E : Type} (qi : Hi → Qi) (extension : Hi → E) :
    Prop :=
  Descends extension (fun h : Hi => h) qi

/-- The persistence extension carries transported later identity. -/
def CarriesLaterIdentity {Hi Hj Qj E : Type} (extension : Hi → E)
    (γ : Hi → Hj) (qj : Hj → Qj) : Prop :=
  Descends extension (fun h : Hi => h) (transportedLaterIdentity γ qj)

/-- Four split/merge comparison statuses. -/
inductive PersistenceComparisonStatus where
  | exactEndurance
  | persistentWithMerge
  | identityBranching
  | identityRewrite
deriving DecidableEq

/-- Meaning of each split/merge comparison status. -/
def PersistenceComparisonStatusHolds {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (γ : Hi → Hj) (qj : Hj → Qj) : PersistenceComparisonStatus → Prop
  | PersistenceComparisonStatus.exactEndurance => ExactEndurance qi γ qj
  | PersistenceComparisonStatus.persistentWithMerge => PersistentWithMerge qi γ qj
  | PersistenceComparisonStatus.identityBranching => IdentityBranching qi γ qj
  | PersistenceComparisonStatus.identityRewrite => IdentityRewrite qi γ qj

/-- Exactly one split/merge comparison status applies. -/
def ExactlyOnePersistenceComparisonStatus {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (γ : Hi → Hj) (qj : Hj → Qj) : Prop :=
  ∃ status : PersistenceComparisonStatus,
    PersistenceComparisonStatusHolds qi γ qj status ∧
      ∀ other : PersistenceComparisonStatus,
        PersistenceComparisonStatusHolds qi γ qj other → other = status

/-- Broader F19 status vocabulary. -/
inductive ObjectPersistenceStatus where
  | exactEndurance
  | persistentWithMerge
  | identityBranching
  | persistenceFailureWithoutBranchRecord
  | identityRewrite
  | incomparableObjectPackage
  | objectDissolution
  | relationValuedPersistence
  | identityHolonomy
  | scopedPersistence
  | localPersistenceGlobalObstruction
  | persistenceOverread
deriving DecidableEq

/-- Meaning assignment for the broader F19 status vocabulary. -/
def ObjectPersistenceStatusHolds (exact merge branching noBranch rewrite
    incomparable dissolution relationValued holonomy scopedStatus localGlobal overread :
    Prop) : ObjectPersistenceStatus → Prop
  | ObjectPersistenceStatus.exactEndurance => exact
  | ObjectPersistenceStatus.persistentWithMerge => merge
  | ObjectPersistenceStatus.identityBranching => branching
  | ObjectPersistenceStatus.persistenceFailureWithoutBranchRecord => noBranch
  | ObjectPersistenceStatus.identityRewrite => rewrite
  | ObjectPersistenceStatus.incomparableObjectPackage => incomparable
  | ObjectPersistenceStatus.objectDissolution => dissolution
  | ObjectPersistenceStatus.relationValuedPersistence => relationValued
  | ObjectPersistenceStatus.identityHolonomy => holonomy
  | ObjectPersistenceStatus.scopedPersistence => scopedStatus
  | ObjectPersistenceStatus.localPersistenceGlobalObstruction => localGlobal
  | ObjectPersistenceStatus.persistenceOverread => overread

/-- Object persistence is exactly absence of the split-pair persistence
obstruction. -/
theorem persists_iff_no_obstruction {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (γ : Hi → Hj) (qj : Hj → Qj) (hqi : Function.Surjective qi) :
    Persists qi γ qj ↔ PersistenceObstructionEmpty qi γ qj :=
  descent_repair_normal_form qi γ qj hqi

/-- Split obstruction emptiness is the same persistence criterion. -/
theorem split_empty_iff_persists {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (γ : Hi → Hj) (qj : Hj → Qj) (hqi : Function.Surjective qi) :
    SplitObstructionEmpty qi γ qj ↔ Persists qi γ qj := by
  exact (persists_iff_no_obstruction qi γ qj hqi).symm

/-- Viability is exactly absence of dissolution obstruction. -/
theorem viable_persistence_iff_no_dissolution {Hi Hj Qj : Type} (γ : Hi → Hj)
    (qj : Hj → Qj) (viable : Qj → Prop) :
    ViablePersistence γ qj viable ↔ DissolutionObstructionEmpty γ qj viable := by
  constructor
  · intro hviable h hdiss
    exact hdiss (hviable h)
  · intro hempty h
    exact Classical.byContradiction (fun hnot => hempty h hnot)

/-- Product quotient surjectivity follows from the two component quotient maps. -/
theorem relation_persistence_quotient_surjective {Hi Qi Hj Qj : Type}
    (qi : Hi → Qi) (qj : Hj → Qj)
    (hqi : Function.Surjective qi) (hqj : Function.Surjective qj) :
    Function.Surjective (relationPersistenceQuotient qi qj) := by
  intro target
  rcases target with ⟨a, b⟩
  rcases hqi a with ⟨h, hh⟩
  rcases hqj b with ⟨k, hk⟩
  exact ⟨(h, k), Prod.ext hh hk⟩

/-- Relation-valued persistence is exactly absence of its relation split-pair
obstruction. -/
theorem relation_persistence_iff_no_obstruction {Hi Qi Hj Qj : Type}
    (qi : Hi → Qi) (qj : Hj → Qj) (C : Hi × Hj → Prop)
    (hqi : Function.Surjective qi) (hqj : Function.Surjective qj) :
    RelationValuedPersistence qi qj C ↔
      RelationPersistenceObstructionEmpty qi qj C :=
  descent_repair_normal_form (relationPersistenceQuotient qi qj)
    (fun pair : Hi × Hj => pair) C
    (relation_persistence_quotient_surjective qi qj hqi hqj)

/-- Identity holonomy coherence is exactly absence of holonomy defects. -/
theorem identity_holonomy_iff_no_defect {Qi Qj Qk : Type} (γbar : Qi → Qj)
    (ηbar : Qj → Qk) (compBar : Qi → Qk) :
    IdentityHolonomyCoherent γbar ηbar compBar ↔
      IdentityHolonomyDefectEmpty γbar ηbar compBar := by
  constructor
  · intro hcoh a hdefect
    exact hdefect (hcoh a)
  · intro hempty a
    exact Classical.byContradiction (fun hneq => hempty a hneq)

/-- The persistence extension retains old identity. -/
theorem persistence_extension_retains_old {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (γ : Hi → Hj) (qj : Hj → Qj) :
    RetainsOldIdentity qi (persistenceExtension qi γ qj) := by
  refine ⟨Prod.fst, ?_⟩
  funext h
  rfl

/-- The persistence extension carries transported later identity. -/
theorem persistence_extension_carries_later {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (γ : Hi → Hj) (qj : Hj → Qj) :
    CarriesLaterIdentity (persistenceExtension qi γ qj) γ qj := by
  refine ⟨Prod.snd, ?_⟩
  funext h
  rfl

/-- The split/merge comparison has exactly one status. -/
theorem persistence_comparison_status_partition {Hi Qi Hj Qj : Type}
    (qi : Hi → Qi) (γ : Hi → Hj) (qj : Hj → Qj) :
    ExactlyOnePersistenceComparisonStatus qi γ qj := by
  classical
  by_cases hsplit : SplitObstructionEmpty qi γ qj
  · by_cases hmerge : MergeObstructionEmpty qi γ qj
    · refine ⟨PersistenceComparisonStatus.exactEndurance, ⟨hsplit, hmerge⟩, ?_⟩
      intro other hother
      cases other with
      | exactEndurance => rfl
      | persistentWithMerge => exact False.elim (hother.2 hmerge)
      | identityBranching => exact False.elim (hother.1 hsplit)
      | identityRewrite => exact False.elim (hother.1 hsplit)
    · refine ⟨PersistenceComparisonStatus.persistentWithMerge, ⟨hsplit, hmerge⟩, ?_⟩
      intro other hother
      cases other with
      | exactEndurance => exact False.elim (hmerge hother.2)
      | persistentWithMerge => rfl
      | identityBranching => exact False.elim (hother.1 hsplit)
      | identityRewrite => exact False.elim (hother.1 hsplit)
  · by_cases hmerge : MergeObstructionEmpty qi γ qj
    · refine ⟨PersistenceComparisonStatus.identityBranching, ⟨hsplit, hmerge⟩, ?_⟩
      intro other hother
      cases other with
      | exactEndurance => exact False.elim (hsplit hother.1)
      | persistentWithMerge => exact False.elim (hsplit hother.1)
      | identityBranching => rfl
      | identityRewrite => exact False.elim (hother.2 hmerge)
    · refine ⟨PersistenceComparisonStatus.identityRewrite, ⟨hsplit, hmerge⟩, ?_⟩
      intro other hother
      cases other with
      | exactEndurance => exact False.elim (hsplit hother.1)
      | persistentWithMerge => exact False.elim (hsplit hother.1)
      | identityBranching => exact False.elim (hmerge hother.2)
      | identityRewrite => rfl

/--
Object Persistence Normal Form. A continuation transports object identity
exactly when it descends through the source and target object quotients. The
split/merge comparison classifies endurance, merging, branching, and rewrite;
relation-valued persistence, dissolution, holonomy, and strict-extension repair
are separate typed gates.
-/
theorem object_persistence {Hi Qi Hj Qj Qk : Type}
    (qi : Hi → Qi) (γ : Hi → Hj) (qj : Hj → Qj)
    (hqi : Function.Surjective qi) (hqj : Function.Surjective qj)
    (viable : Qj → Prop) (C : Hi × Hj → Prop)
    (γbar : Qi → Qj) (ηbar : Qj → Qk) (compBar : Qi → Qk) :
    (Persists qi γ qj ↔ PersistenceObstructionEmpty qi γ qj) ∧
      (SplitObstructionEmpty qi γ qj ↔ Persists qi γ qj) ∧
        ExactlyOnePersistenceComparisonStatus qi γ qj ∧
          (ViablePersistence γ qj viable ↔
            DissolutionObstructionEmpty γ qj viable) ∧
            (RelationValuedPersistence qi qj C ↔
              RelationPersistenceObstructionEmpty qi qj C) ∧
              (IdentityHolonomyCoherent γbar ηbar compBar ↔
                IdentityHolonomyDefectEmpty γbar ηbar compBar) ∧
                RetainsOldIdentity qi (persistenceExtension qi γ qj) ∧
                  CarriesLaterIdentity (persistenceExtension qi γ qj) γ qj := by
  exact ⟨persists_iff_no_obstruction qi γ qj hqi,
    split_empty_iff_persists qi γ qj hqi,
    persistence_comparison_status_partition qi γ qj,
    viable_persistence_iff_no_dissolution γ qj viable,
    relation_persistence_iff_no_obstruction qi qj C hqi hqj,
    identity_holonomy_iff_no_defect γbar ηbar compBar,
    persistence_extension_retains_old qi γ qj,
    persistence_extension_carries_later qi γ qj⟩

/-- Descended single-step and composite transports agree on the quotient:
surjectivity of the initial quotient makes every class testable upstairs. -/
theorem identity_holonomy_coherent_of_descended_composition
    {Hi Qi Hj Qj Hk Qk : Type}
    (qi : Hi → Qi) (qj : Hj → Qj) (qk : Hk → Qk)
    (γ : Hi → Hj) (η : Hj → Hk)
    (γbar : Qi → Qj) (ηbar : Qj → Qk) (compBar : Qi → Qk)
    (hqi : Function.Surjective qi)
    (hγ : γbar ∘ qi = qj ∘ γ)
    (hη : ηbar ∘ qj = qk ∘ η)
    (hcomp : compBar ∘ qi = qk ∘ η ∘ γ) :
    IdentityHolonomyCoherent γbar ηbar compBar := by
  intro a
  obtain ⟨h, rfl⟩ := hqi a
  calc
    compBar (qi h) = qk (η (γ h)) := congrFun hcomp h
    _ = ηbar (qj (γ h)) := (congrFun hη (γ h)).symm
    _ = ηbar (γbar (qi h)) := congrArg ηbar (congrFun hγ h).symm

/-- F19 with composition coherence when the arbitrary holonomy data are
actual descents. The new carrier, transport, and descent equations are confined
to the added clause; all original hypotheses and clauses are retained. -/
theorem object_persistence_strengthened {Hi Qi Hj Qj Qk : Type}
    (qi : Hi → Qi) (γ : Hi → Hj) (qj : Hj → Qj)
    (hqi : Function.Surjective qi) (hqj : Function.Surjective qj)
    (viable : Qj → Prop) (C : Hi × Hj → Prop)
    (γbar : Qi → Qj) (ηbar : Qj → Qk) (compBar : Qi → Qk) :
    ((Persists qi γ qj ↔ PersistenceObstructionEmpty qi γ qj) ∧
      (SplitObstructionEmpty qi γ qj ↔ Persists qi γ qj) ∧
        ExactlyOnePersistenceComparisonStatus qi γ qj ∧
          (ViablePersistence γ qj viable ↔
            DissolutionObstructionEmpty γ qj viable) ∧
            (RelationValuedPersistence qi qj C ↔
              RelationPersistenceObstructionEmpty qi qj C) ∧
              (IdentityHolonomyCoherent γbar ηbar compBar ↔
                IdentityHolonomyDefectEmpty γbar ηbar compBar) ∧
                RetainsOldIdentity qi (persistenceExtension qi γ qj) ∧
                  CarriesLaterIdentity (persistenceExtension qi γ qj) γ qj) ∧
    (∀ (Hk : Type) (qk : Hk → Qk) (η : Hj → Hk),
      γbar ∘ qi = qj ∘ γ → ηbar ∘ qj = qk ∘ η →
      compBar ∘ qi = qk ∘ η ∘ γ →
        IdentityHolonomyCoherent γbar ηbar compBar) := by
  refine ⟨object_persistence qi γ qj hqi hqj viable C γbar ηbar compBar, ?_⟩
  intro Hk qk η hγ hη hcomp
  exact identity_holonomy_coherent_of_descended_composition qi qj qk γ η
    γbar ηbar compBar hqi hγ hη hcomp

/-- Relation predicates factor through arbitrary quotient maps by existential
image; in particular only the requested source-surjectivity premise is retained. -/
theorem relation_persistence_iff_no_obstruction_of_source_surjective
    {Hi Qi Hj Qj : Type}
    (qi : Hi → Qi) (qj : Hj → Qj) (C : Hi × Hj → Prop)
    (_hqi : Function.Surjective qi) :
    RelationValuedPersistence qi qj C ↔
      RelationPersistenceObstructionEmpty qi qj C := by
  constructor
  · rintro ⟨Cbar, hcomm⟩ pair ⟨heq, hne⟩
    exact hne ((congrFun hcomm pair.1).symm.trans
      ((congrArg Cbar heq).trans (congrFun hcomm pair.2)))
  · intro hempty
    have hconstant : ∀ p p', relationPersistenceQuotient qi qj p =
        relationPersistenceQuotient qi qj p' → (C p ↔ C p') := by
      intro p p' heq
      exact iff_of_eq (Classical.byContradiction (fun hne =>
        hempty (p, p') ⟨heq, hne⟩))
    refine ⟨fun z => ∃ p, relationPersistenceQuotient qi qj p = z ∧ C p, ?_⟩
    funext p
    apply propext
    constructor
    · rintro ⟨p', heq, hp'⟩
      exact (hconstant p' p heq).mp hp'
    · intro hp
      exact ⟨p, rfl, hp⟩

/-- The strengthened persistence bundle needs only source quotient surjectivity. -/
theorem object_persistence_strengthened_of_source_surjective {Hi Qi Hj Qj Qk : Type}
    (qi : Hi → Qi) (γ : Hi → Hj) (qj : Hj → Qj)
    (hqi : Function.Surjective qi)
    (viable : Qj → Prop) (C : Hi × Hj → Prop)
    (γbar : Qi → Qj) (ηbar : Qj → Qk) (compBar : Qi → Qk) :
    ((Persists qi γ qj ↔ PersistenceObstructionEmpty qi γ qj) ∧
      (SplitObstructionEmpty qi γ qj ↔ Persists qi γ qj) ∧
        ExactlyOnePersistenceComparisonStatus qi γ qj ∧
          (ViablePersistence γ qj viable ↔
            DissolutionObstructionEmpty γ qj viable) ∧
            (RelationValuedPersistence qi qj C ↔
              RelationPersistenceObstructionEmpty qi qj C) ∧
              (IdentityHolonomyCoherent γbar ηbar compBar ↔
                IdentityHolonomyDefectEmpty γbar ηbar compBar) ∧
                RetainsOldIdentity qi (persistenceExtension qi γ qj) ∧
                  CarriesLaterIdentity (persistenceExtension qi γ qj) γ qj) ∧
    (∀ (Hk : Type) (qk : Hk → Qk) (η : Hj → Hk),
      γbar ∘ qi = qj ∘ γ → ηbar ∘ qj = qk ∘ η →
      compBar ∘ qi = qk ∘ η ∘ γ →
        IdentityHolonomyCoherent γbar ηbar compBar) := by
  refine ⟨⟨persists_iff_no_obstruction qi γ qj hqi,
    split_empty_iff_persists qi γ qj hqi,
    persistence_comparison_status_partition qi γ qj,
    viable_persistence_iff_no_dissolution γ qj viable,
    relation_persistence_iff_no_obstruction_of_source_surjective qi qj C hqi,
    identity_holonomy_iff_no_defect γbar ηbar compBar,
    persistence_extension_retains_old qi γ qj,
    persistence_extension_carries_later qi γ qj⟩, ?_⟩
  intro Hk qk η hγ hη hcomp
  exact identity_holonomy_coherent_of_descended_composition qi qj qk γ η
    γbar ηbar compBar hqi hγ hη hcomp

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ObjectPersistence
