import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F36 Singular Limit Completion.

A singular limit is modeled as failure of a limiting target to descend through
the declared completed quotient of limiting processes. A completion resolves a
target exactly when same completed object implies same limiting target value.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.SingularLimitCompletion

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- The completed object assigned to a limiting process. -/
def CompletedLimitMap (Process Qhat : Type) := Process → Qhat

/-- A target-limit readout assigned to a limiting process. -/
def TargetLimitReadout (Process That : Type) := Process → That

/-- The target-limit readout is completed when it descends through the
completed quotient limit map. -/
def TargetLimitCompleted {Process Qhat That : Type} (limit : Process → Qhat)
    (targetLimit : Process → That) : Prop :=
  Descends limit (fun process : Process => process) targetLimit

/-- Singular target obstruction: same completed object, different target-limit
value. -/
def SingularTargetObstruction {Process Qhat That : Type} (limit : Process → Qhat)
    (targetLimit : Process → That) : (Process × Process) → Prop :=
  splitPairObstruction limit (fun process : Process => process) targetLimit

/-- No singular target obstruction is present. -/
def SingularTargetObstructionEmpty {Process Qhat That : Type}
    (limit : Process → Qhat) (targetLimit : Process → That) : Prop :=
  ObstructionEmpty (SingularTargetObstruction limit targetLimit)

/-- Target-family completion, represented by a joint target-limit signature. -/
def TargetFamilyLimitCompleted {Process Qhat Signature : Type}
    (limit : Process → Qhat) (signatureLimit : Process → Signature) : Prop :=
  TargetLimitCompleted limit signatureLimit

/-- Target-family singular obstruction. -/
def TargetFamilySingularObstruction {Process Qhat Signature : Type}
    (limit : Process → Qhat) (signatureLimit : Process → Signature) :
    (Process × Process) → Prop :=
  SingularTargetObstruction limit signatureLimit

/-- No target-family singular obstruction is present. -/
def TargetFamilySingularObstructionEmpty {Process Qhat Signature : Type}
    (limit : Process → Qhat) (signatureLimit : Process → Signature) : Prop :=
  SingularTargetObstructionEmpty limit signatureLimit

/-- A completed object is already realized by the current quotient if it lies in
the image of the completion map. -/
def CurrentRealizedLimit {Q Qhat Process : Type} (completion : Q → Qhat)
    (limit : Process → Qhat) (process : Process) : Prop :=
  ∃ current : Q, completion current = limit process

/-- A boundary-completed object is outside the current quotient image. -/
def BoundaryCompletedLimit {Q Qhat Process : Type} (completion : Q → Qhat)
    (limit : Process → Qhat) (process : Process) : Prop :=
  ¬ CurrentRealizedLimit completion limit process

/-- A singularity is removable for a process and target scope when the limit is
not current-realized but the target family descends through the completion. -/
def RemovableByCompletion {Q Qhat Process Signature : Type}
    (completion : Q → Qhat) (limit : Process → Qhat)
    (signatureLimit : Process → Signature) (process : Process) : Prop :=
  BoundaryCompletedLimit completion limit process ∧
    TargetFamilyLimitCompleted limit signatureLimit

/-- Path-dependent or holonomy singularity: the singular obstruction has a
witness. -/
def PathDependentLimit {Process Qhat That : Type} (limit : Process → Qhat)
    (targetLimit : Process → That) : Prop :=
  ∃ pair, SingularTargetObstruction limit targetLimit pair

/-- A declared process class has completed objects when the supplied predicate
certifies every process. This keeps convergence substrate explicit. -/
def CompletedObjectExists {Process Qhat : Type} (limit : Process → Qhat)
    (ExistsAt : (Process → Qhat) → Process → Prop) : Prop :=
  ∀ process, ExistsAt limit process

/-- A raw target may fail while a declared renormalized target-limit readout
descends through the completed quotient. -/
def RenormalizedLimitCompleted {Process Qhat RenTarget : Type}
    (limit : Process → Qhat) (renormalizedTargetLimit : Process → RenTarget) :
    Prop :=
  TargetLimitCompleted limit renormalizedTargetLimit

/-- A weak/coarsened limit is completion of a coarsened target-limit readout. -/
def WeakLimitCompleted {Process Qhat RawTarget CoarseTarget : Type}
    (limit : Process → Qhat) (rawTargetLimit : Process → RawTarget)
    (coarsenTarget : RawTarget → CoarseTarget) : Prop :=
  TargetLimitCompleted limit (coarsenTarget ∘ rawTargetLimit)

/-- A probabilistic limit completion is a stable law that descends through the
completed quotient. -/
def ProbabilisticLimitCompleted {Process Qhat Law : Type} (limit : Process → Qhat)
    (limitLaw : Process → Law) (Stable : (Process → Law) → Prop) : Prop :=
  Stable limitLaw ∧ TargetLimitCompleted limit limitLaw

/-- Canonical path-memory repair: remember the completed object and the target
limit value. -/
def singularPathRepairQuotient {Process Qhat That : Type} (limit : Process → Qhat)
    (targetLimit : Process → That) : Process → Qhat × That :=
  sourceRepairQuotient limit (fun process : Process => process) targetLimit

/-- Source status vocabulary for singular-limit claims. -/
inductive SingularLimitStatus where
  | currentLimit
  | removableByCompletion
  | boundaryObject
  | pathDependentLimit
  | completionAbsent
  | limitNonexistence
  | targetBlowup
  | needleBlocked
  | renormalizedLimit
  | weakLimit
  | probabilisticLimit
  | hiddenLimitState
  | localLimitCompletion
  | globalLimitObstructed
  | presentationDependentLimit
  | protocolLimitArtifact
  | singularityOverread
deriving DecidableEq

/-- Meaning assignment for the F36 status vocabulary. -/
def SingularLimitStatusHolds (current removable boundary pathDependent absent
    nonexistence blowup needleBlocked renormalized weak probabilistic hidden localOnly
    globalObstructed presentationDependent protocol overread : Prop) :
    SingularLimitStatus → Prop
  | SingularLimitStatus.currentLimit => current
  | SingularLimitStatus.removableByCompletion => removable
  | SingularLimitStatus.boundaryObject => boundary
  | SingularLimitStatus.pathDependentLimit => pathDependent
  | SingularLimitStatus.completionAbsent => absent
  | SingularLimitStatus.limitNonexistence => nonexistence
  | SingularLimitStatus.targetBlowup => blowup
  | SingularLimitStatus.needleBlocked => needleBlocked
  | SingularLimitStatus.renormalizedLimit => renormalized
  | SingularLimitStatus.weakLimit => weak
  | SingularLimitStatus.probabilisticLimit => probabilistic
  | SingularLimitStatus.hiddenLimitState => hidden
  | SingularLimitStatus.localLimitCompletion => localOnly
  | SingularLimitStatus.globalLimitObstructed => globalObstructed
  | SingularLimitStatus.presentationDependentLimit => presentationDependent
  | SingularLimitStatus.protocolLimitArtifact => protocol
  | SingularLimitStatus.singularityOverread => overread

/-- Target Limit Completion Normal Form. -/
theorem target_limit_completed_iff_no_obstruction {Process Qhat That : Type}
    (limit : Process → Qhat) (targetLimit : Process → That)
    (hlimit : Function.Surjective limit) :
    TargetLimitCompleted limit targetLimit ↔
      SingularTargetObstructionEmpty limit targetLimit :=
  descent_repair_normal_form limit (fun process : Process => process) targetLimit
    hlimit

/-- Factorization form of target limit completion. -/
theorem target_limit_completed_iff_factorization {Process Qhat That : Type}
    (limit : Process → Qhat) (targetLimit : Process → That) :
    TargetLimitCompleted limit targetLimit ↔
      ∃ targetHat : Qhat → That, targetHat ∘ limit = targetLimit := by
  constructor
  · intro hcomplete
    rcases hcomplete with ⟨targetHat, htargetHat⟩
    exact ⟨targetHat, by simpa [Function.comp] using htargetHat⟩
  · intro hfactor
    rcases hfactor with ⟨targetHat, htargetHat⟩
    exact ⟨targetHat, by simpa [Function.comp] using htargetHat⟩

/-- Target-family limit completion is the same normal form for the joint
signature. -/
theorem target_family_completed_iff_no_obstruction
    {Process Qhat Signature : Type} (limit : Process → Qhat)
    (signatureLimit : Process → Signature) (hlimit : Function.Surjective limit) :
    TargetFamilyLimitCompleted limit signatureLimit ↔
      TargetFamilySingularObstructionEmpty limit signatureLimit :=
  target_limit_completed_iff_no_obstruction limit signatureLimit hlimit

/-- Path dependence is exactly non-completion of the target limit, under the
declared completed quotient carrier. -/
theorem path_dependent_iff_not_completed {Process Qhat That : Type}
    (limit : Process → Qhat) (targetLimit : Process → That)
    (hlimit : Function.Surjective limit) :
    PathDependentLimit limit targetLimit ↔
      ¬ TargetLimitCompleted limit targetLimit := by
  constructor
  · intro hpath hcomplete
    rcases hpath with ⟨pair, hpair⟩
    have hempty :=
      (target_limit_completed_iff_no_obstruction limit targetLimit hlimit).1 hcomplete
    exact hempty pair hpair
  · intro hnotComplete
    classical
    exact Classical.byContradiction (fun hnoPath =>
      hnotComplete
        ((target_limit_completed_iff_no_obstruction limit targetLimit hlimit).2
          (fun pair hpair => hnoPath ⟨pair, hpair⟩)))

/-- Removable completion is boundary-completed object plus completed target
family descent. -/
theorem removable_by_completion_iff_boundary_and_family
    {Q Qhat Process Signature : Type} (completion : Q → Qhat)
    (limit : Process → Qhat) (signatureLimit : Process → Signature)
    (process : Process) :
    RemovableByCompletion completion limit signatureLimit process ↔
      BoundaryCompletedLimit completion limit process ∧
        TargetFamilyLimitCompleted limit signatureLimit := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- The canonical path-memory repair refines the completed object map. -/
theorem singular_path_repair_refines {Process Qhat That : Type}
    (limit : Process → Qhat) (targetLimit : Process → That) :
    SourceRefinement (singularPathRepairQuotient limit targetLimit) limit :=
  source_repair_refines limit (fun process : Process => process) targetLimit

/-- After canonical path-memory repair, the target limit descends. -/
theorem singular_path_repair_completes {Process Qhat That : Type}
    (limit : Process → Qhat) (targetLimit : Process → That) :
    TargetLimitCompleted (singularPathRepairQuotient limit targetLimit) targetLimit :=
  source_repair_descends limit (fun process : Process => process) targetLimit

/-- Renormalized limit completion is ordinary target-limit completion for the
declared renormalized readout. -/
theorem renormalized_limit_completed_iff_completed {Process Qhat RenTarget : Type}
    (limit : Process → Qhat) (renormalizedTargetLimit : Process → RenTarget) :
    RenormalizedLimitCompleted limit renormalizedTargetLimit ↔
      TargetLimitCompleted limit renormalizedTargetLimit := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
Singular Limit Completion Normal Form. A limiting target is completed exactly
when it descends through the completed quotient limit map, equivalently when no
two processes with the same completed object have different target limits.
Path-dependent singularities are precisely the nonempty obstruction case, and
the canonical repair records the missing path/target residue.
-/
theorem singular_limit_completion {Q Qhat Process That Signature RenTarget : Type}
    (completion : Q → Qhat) (limit : Process → Qhat)
    (targetLimit : Process → That) (signatureLimit : Process → Signature)
    (renormalizedTargetLimit : Process → RenTarget) (process : Process)
    (hlimit : Function.Surjective limit) :
    (TargetLimitCompleted limit targetLimit ↔
      SingularTargetObstructionEmpty limit targetLimit) ∧
      (TargetLimitCompleted limit targetLimit ↔
        ∃ targetHat : Qhat → That, targetHat ∘ limit = targetLimit) ∧
        (TargetFamilyLimitCompleted limit signatureLimit ↔
          TargetFamilySingularObstructionEmpty limit signatureLimit) ∧
          (PathDependentLimit limit targetLimit ↔
            ¬ TargetLimitCompleted limit targetLimit) ∧
            (RemovableByCompletion completion limit signatureLimit process ↔
              BoundaryCompletedLimit completion limit process ∧
                TargetFamilyLimitCompleted limit signatureLimit) ∧
              SourceRefinement (singularPathRepairQuotient limit targetLimit) limit ∧
                TargetLimitCompleted (singularPathRepairQuotient limit targetLimit)
                  targetLimit ∧
                  (RenormalizedLimitCompleted limit renormalizedTargetLimit ↔
                    SingularTargetObstructionEmpty limit renormalizedTargetLimit) := by
  exact ⟨target_limit_completed_iff_no_obstruction limit targetLimit hlimit,
    target_limit_completed_iff_factorization limit targetLimit,
    target_family_completed_iff_no_obstruction limit signatureLimit hlimit,
    path_dependent_iff_not_completed limit targetLimit hlimit,
    removable_by_completion_iff_boundary_and_family completion limit signatureLimit
      process,
    singular_path_repair_refines limit targetLimit,
    singular_path_repair_completes limit targetLimit,
    (renormalized_limit_completed_iff_completed limit renormalizedTargetLimit).trans
      (target_limit_completed_iff_no_obstruction limit renormalizedTargetLimit hlimit)⟩

/-- Removability requires a new completed object and no target-family split. -/
theorem removable_iff_not_current_and_no_obstruction
    {Q Qhat Process Signature : Type} (completion : Q → Qhat)
    (limit : Process → Qhat) (signatureLimit : Process → Signature)
    (process : Process) (hlimit : Function.Surjective limit) :
    RemovableByCompletion completion limit signatureLimit process ↔
      ¬ CurrentRealizedLimit completion limit process ∧
        TargetFamilySingularObstructionEmpty limit signatureLimit := by
  exact (removable_by_completion_iff_boundary_and_family completion limit
    signatureLimit process).trans
      (and_congr Iff.rfl
        (target_family_completed_iff_no_obstruction limit signatureLimit hlimit))

/-- F36 with the explicit current-absence and obstruction criterion. -/
theorem singular_limit_completion_paper
    {Q Qhat Process That Signature RenTarget : Type}
    (completion : Q → Qhat) (limit : Process → Qhat)
    (targetLimit : Process → That) (signatureLimit : Process → Signature)
    (renormalizedTargetLimit : Process → RenTarget) (process : Process)
    (hlimit : Function.Surjective limit) :
    ((TargetLimitCompleted limit targetLimit ↔
      SingularTargetObstructionEmpty limit targetLimit) ∧
      (TargetLimitCompleted limit targetLimit ↔
        ∃ targetHat : Qhat → That, targetHat ∘ limit = targetLimit) ∧
        (TargetFamilyLimitCompleted limit signatureLimit ↔
          TargetFamilySingularObstructionEmpty limit signatureLimit) ∧
          (PathDependentLimit limit targetLimit ↔
            ¬ TargetLimitCompleted limit targetLimit) ∧
            (RemovableByCompletion completion limit signatureLimit process ↔
              BoundaryCompletedLimit completion limit process ∧
                TargetFamilyLimitCompleted limit signatureLimit) ∧
              SourceRefinement (singularPathRepairQuotient limit targetLimit) limit ∧
                TargetLimitCompleted (singularPathRepairQuotient limit targetLimit)
                  targetLimit ∧
                  (RenormalizedLimitCompleted limit renormalizedTargetLimit ↔
                    SingularTargetObstructionEmpty limit renormalizedTargetLimit)) ∧
      (RemovableByCompletion completion limit signatureLimit process ↔
        ¬ CurrentRealizedLimit completion limit process ∧
          TargetFamilySingularObstructionEmpty limit signatureLimit) := by
  exact ⟨singular_limit_completion completion limit targetLimit signatureLimit
      renormalizedTargetLimit process hlimit,
    removable_iff_not_current_and_no_obstruction completion limit signatureLimit
      process hlimit⟩

/-- Postprocessing a completed target preserves its factorization through the
limit quotient; no surjectivity or injectivity is needed in this direction. -/
theorem target_limit_completed_of_postprocessing
    {Process Qhat That RenTarget : Type}
    (limit : Process → Qhat) (targetLimit : Process → That)
    (renormalizedTargetLimit : Process → RenTarget) (R : That → RenTarget)
    (hren : renormalizedTargetLimit = R ∘ targetLimit) :
    TargetLimitCompleted limit targetLimit →
      TargetLimitCompleted limit renormalizedTargetLimit := by
  rintro ⟨targetHat, hcomm⟩
  refine ⟨R ∘ targetHat, ?_⟩
  funext p
  have hp := congrFun hcomm p
  simpa only [hren, Function.comp_apply] using congrArg R hp

/-- Injective postprocessing reflects completion through a surjective limit
quotient: equality after postprocessing already implies equality before it. -/
theorem target_limit_completed_of_injective_postprocessing
    {Process Qhat That RenTarget : Type}
    (limit : Process → Qhat) (targetLimit : Process → That)
    (renormalizedTargetLimit : Process → RenTarget) (R : That → RenTarget)
    (hlimit : Function.Surjective limit)
    (hren : renormalizedTargetLimit = R ∘ targetLimit)
    (hR : Function.Injective R) :
    TargetLimitCompleted limit renormalizedTargetLimit →
      TargetLimitCompleted limit targetLimit := by
  intro hcomplete
  apply (target_limit_completed_iff_no_obstruction limit targetLimit hlimit).2
  intro pair hpair
  obtain ⟨p, p'⟩ := pair
  obtain ⟨targetHat, hcomm⟩ := hcomplete
  have hp := congrFun hcomm p
  have hp' := congrFun hcomm p'
  apply hpair.2
  apply hR
  have heq : renormalizedTargetLimit p = renormalizedTargetLimit p' :=
    hp.symm.trans ((congrArg targetHat hpair.1).trans hp')
  simpa only [hren, Function.comp_apply] using heq

/-- The postprocessing clause of F36, with reflection conditional only on
injectivity of the postprocessor. -/
theorem target_limit_completion_postprocessing
    {Process Qhat That RenTarget : Type}
    (limit : Process → Qhat) (targetLimit : Process → That)
    (renormalizedTargetLimit : Process → RenTarget) (R : That → RenTarget)
    (hlimit : Function.Surjective limit)
    (hren : renormalizedTargetLimit = R ∘ targetLimit) :
    (TargetLimitCompleted limit targetLimit →
      TargetLimitCompleted limit renormalizedTargetLimit) ∧
    (Function.Injective R →
      TargetLimitCompleted limit renormalizedTargetLimit →
        TargetLimitCompleted limit targetLimit) := by
  exact ⟨target_limit_completed_of_postprocessing limit targetLimit
    renormalizedTargetLimit R hren,
    fun hR => target_limit_completed_of_injective_postprocessing limit targetLimit
      renormalizedTargetLimit R hlimit hren hR⟩

/-- F36 with postprocessing preservation and injective reflection, guarded
only in the additional clause by the renormalization equation. -/
theorem singular_limit_completion_paper_strengthened
    {Q Qhat Process That Signature RenTarget : Type}
    (completion : Q → Qhat) (limit : Process → Qhat)
    (targetLimit : Process → That) (signatureLimit : Process → Signature)
    (renormalizedTargetLimit : Process → RenTarget) (process : Process)
    (hlimit : Function.Surjective limit) :
    (((TargetLimitCompleted limit targetLimit ↔
      SingularTargetObstructionEmpty limit targetLimit) ∧
      (TargetLimitCompleted limit targetLimit ↔
        ∃ targetHat : Qhat → That, targetHat ∘ limit = targetLimit) ∧
        (TargetFamilyLimitCompleted limit signatureLimit ↔
          TargetFamilySingularObstructionEmpty limit signatureLimit) ∧
          (PathDependentLimit limit targetLimit ↔
            ¬ TargetLimitCompleted limit targetLimit) ∧
            (RemovableByCompletion completion limit signatureLimit process ↔
              BoundaryCompletedLimit completion limit process ∧
                TargetFamilyLimitCompleted limit signatureLimit) ∧
              SourceRefinement (singularPathRepairQuotient limit targetLimit) limit ∧
                TargetLimitCompleted (singularPathRepairQuotient limit targetLimit)
                  targetLimit ∧
                  (RenormalizedLimitCompleted limit renormalizedTargetLimit ↔
                    SingularTargetObstructionEmpty limit renormalizedTargetLimit)) ∧
      (RemovableByCompletion completion limit signatureLimit process ↔
        ¬ CurrentRealizedLimit completion limit process ∧
          TargetFamilySingularObstructionEmpty limit signatureLimit)) ∧
    (∀ R : That → RenTarget, renormalizedTargetLimit = R ∘ targetLimit →
      (TargetLimitCompleted limit targetLimit →
        TargetLimitCompleted limit renormalizedTargetLimit) ∧
      (Function.Injective R →
        TargetLimitCompleted limit renormalizedTargetLimit →
          TargetLimitCompleted limit targetLimit)) := by
  refine ⟨singular_limit_completion_paper completion limit targetLimit
    signatureLimit renormalizedTargetLimit process hlimit, ?_⟩
  intro R hren
  exact target_limit_completion_postprocessing limit targetLimit
    renormalizedTargetLimit R hlimit hren

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.SingularLimitCompletion
