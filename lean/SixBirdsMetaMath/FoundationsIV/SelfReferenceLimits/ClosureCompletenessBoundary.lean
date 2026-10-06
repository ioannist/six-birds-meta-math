import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
import SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ReflexiveNonclosure

/-!
F52 Closure Completeness Boundary.

Completeness is scoped residual coverage under meta-audit. A package is
complete only relative to a declared scope when every native residual has an
adequate status, nonclaims are registered, and the coverage claim is accepted
from a level-shifted audit rather than self-certified at the same layer.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.ClosureCompletenessBoundary

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
open SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ReflexiveNonclosure

/-- Accepted residual-status labels for the scope-relative completeness law. -/
inductive ResidualCoverageStatus where
  | zero
  | killedByClosure
  | discharged
  | budgeted
  | bridged
  | currentized
  | hidden
  | probabilistic
  | moduli
  | selected
  | outsideDeclaredScope
  | nonclaim
  | blocked
  | openResidual
deriving DecidableEq

/-- A native residual is unstatused when the scoped status map does not cover
it. -/
def UnstatusedResidual {Residual : Type} (hasStatus : Residual → Prop) :
    Residual → Prop :=
  fun residual => ¬ hasStatus residual

/-- No native residual is unstatused. -/
def UnstatusedResidualEmpty {Residual : Type} (hasStatus : Residual → Prop) :
    Prop :=
  ObstructionEmpty (UnstatusedResidual hasStatus)

/-- A native residual has an inadequate status when its assigned status fails
the declared adequacy gate. -/
def InadequateStatusResidual {Residual : Type} (statusAdequate : Residual → Prop) :
    Residual → Prop :=
  fun residual => ¬ statusAdequate residual

/-- No native residual has an inadequate status. -/
def InadequateStatusResidualEmpty {Residual : Type}
    (statusAdequate : Residual → Prop) : Prop :=
  ObstructionEmpty (InadequateStatusResidual statusAdequate)

/-- Residual coverage means every native residual has a status and the status
passes its adequacy gate. -/
def ResidualCoverage {Residual : Type} (hasStatus statusAdequate : Residual → Prop) :
    Prop :=
  ∀ residual, hasStatus residual ∧ statusAdequate residual

/-- A scope boundary direction is outside the declared completeness scope. -/
def CompletenessBoundary {Direction : Type} (inScope : Direction → Prop) :
    Direction → Prop :=
  fun direction => ¬ inScope direction

/-- A completeness boundary is named when every outside-scope direction is
explicitly registered. -/
def BoundaryNamed {Direction : Type} (inScope namedOutside : Direction → Prop) :
    Prop :=
  ∀ direction, CompletenessBoundary inScope direction → namedOutside direction

/-- A claim beyond the boundary is an overread when it is not named as outside
scope. -/
def BoundaryOverread {Direction : Type} (inScope claimed namedOutside : Direction → Prop) :
    Prop :=
  ∃ direction, CompletenessBoundary inScope direction ∧
    claimed direction ∧ ¬ namedOutside direction

/-- Meta-audit verdicts for the scoped coverage claim. -/
inductive MetaAuditVerdict where
  | accepted
  | rejected
  | pending
  | outsideScope
  | undefinedCircular
deriving DecidableEq

/-- A level-shifted meta-audit accepts the scoped coverage claim. -/
def MetaCovered (verdict : MetaAuditVerdict) : Prop :=
  verdict = MetaAuditVerdict.accepted

/-- Scoped closure completeness: formed package, declared scope and residual
extractor, adequate residual coverage, closed nonclaim register, and accepted
meta-audit. -/
def AuditedScopedClosureComplete {Residual : Type} (formed scopeDeclared
    residualExtractorDeclared nonclaimRegisterClosed : Prop)
    (hasStatus statusAdequate : Residual → Prop)
    (metaVerdict : MetaAuditVerdict) : Prop :=
  formed ∧ scopeDeclared ∧ residualExtractorDeclared ∧
    ResidualCoverage hasStatus statusAdequate ∧
      nonclaimRegisterClosed ∧ MetaCovered metaVerdict

/-- Internal coverage without a meta-audit is useful bookkeeping but not
theorem-grade closure completeness. -/
def InternallyCoveredPendingMetaAudit {Residual : Type} (formed scopeDeclared
    residualExtractorDeclared nonclaimRegisterClosed : Prop)
    (hasStatus statusAdequate : Residual → Prop)
    (metaVerdict : MetaAuditVerdict) : Prop :=
  formed ∧ scopeDeclared ∧ residualExtractorDeclared ∧
    ResidualCoverage hasStatus statusAdequate ∧
      nonclaimRegisterClosed ∧ ¬ MetaCovered metaVerdict

/-- Exact completeness forbids nonzero budgeted residuals unless the exact
scope explicitly allows the status. -/
def ExactCompleteness {Residual : Type} (hasStatus statusAdequate exactAllowed :
    Residual → Prop) : Prop :=
  ∀ residual, hasStatus residual ∧ statusAdequate residual ∧ exactAllowed residual

/-- Budgeted completeness keeps the budget status attached and does not claim
exact residual-free closure. -/
def BudgetedCompleteness {Residual : Type} (withinBudget otherwiseStatused :
    Residual → Prop) : Prop :=
  ∀ residual, withinBudget residual ∨ otherwiseStatused residual

/-- Source status vocabulary for F52 closure-completeness claims. -/
inductive ClosureCompletenessStatus where
  | scopedComplete
  | internallyCoveredPendingMetaAudit
  | unstatusedResidual
  | inadequatelyStatusedResidual
  | scopeAbsent
  | residualExtractorAbsent
  | nonclaimRegisterIncomplete
  | openResidual
  | budgetedComplete
  | probabilisticallyComplete
  | localComplete
  | globalCompletenessObstructed
  | asymptoticallyComplete
  | presentationRelativeComplete
  | protocolRelativeComplete
  | undefinedCircular
  | outsideScope
  | finalityOverclaim
  | completenessOverread
deriving DecidableEq

/-- Meaning assignment for the F52 status vocabulary. -/
def ClosureCompletenessStatusHolds (scopedComplete pendingMeta unstatused inadequate
    scopeAbsent extractorAbsent nonclaimIncomplete openResidual budgeted probabilistic
    localComplete globalObstructed asymptotic presentationRelative protocolRelative
    circular outside finalityOverclaim overread : Prop) :
    ClosureCompletenessStatus → Prop
  | ClosureCompletenessStatus.scopedComplete => scopedComplete
  | ClosureCompletenessStatus.internallyCoveredPendingMetaAudit => pendingMeta
  | ClosureCompletenessStatus.unstatusedResidual => unstatused
  | ClosureCompletenessStatus.inadequatelyStatusedResidual => inadequate
  | ClosureCompletenessStatus.scopeAbsent => scopeAbsent
  | ClosureCompletenessStatus.residualExtractorAbsent => extractorAbsent
  | ClosureCompletenessStatus.nonclaimRegisterIncomplete => nonclaimIncomplete
  | ClosureCompletenessStatus.openResidual => openResidual
  | ClosureCompletenessStatus.budgetedComplete => budgeted
  | ClosureCompletenessStatus.probabilisticallyComplete => probabilistic
  | ClosureCompletenessStatus.localComplete => localComplete
  | ClosureCompletenessStatus.globalCompletenessObstructed => globalObstructed
  | ClosureCompletenessStatus.asymptoticallyComplete => asymptotic
  | ClosureCompletenessStatus.presentationRelativeComplete => presentationRelative
  | ClosureCompletenessStatus.protocolRelativeComplete => protocolRelative
  | ClosureCompletenessStatus.undefinedCircular => circular
  | ClosureCompletenessStatus.outsideScope => outside
  | ClosureCompletenessStatus.finalityOverclaim => finalityOverclaim
  | ClosureCompletenessStatus.completenessOverread => overread

/-- Residual coverage is exactly absence of unstatused residuals and inadequate
status gates. -/
theorem residual_coverage_iff_empty_obstructions {Residual : Type}
    (hasStatus statusAdequate : Residual → Prop) :
    ResidualCoverage hasStatus statusAdequate ↔
      UnstatusedResidualEmpty hasStatus ∧
        InadequateStatusResidualEmpty statusAdequate := by
  constructor
  · intro hcoverage
    constructor
    · intro residual hunstatused
      exact hunstatused (hcoverage residual).1
    · intro residual hinadequate
      exact hinadequate (hcoverage residual).2
  · intro hempty residual
    constructor
    · exact Classical.byContradiction (fun hmissing =>
        False.elim (hempty.1 residual hmissing))
    · exact Classical.byContradiction (fun hbad =>
        False.elim (hempty.2 residual hbad))

/-- Meta coverage is just acceptance by the level-shifted audit verdict. -/
theorem meta_covered_iff_accepted (verdict : MetaAuditVerdict) :
    MetaCovered verdict ↔ verdict = MetaAuditVerdict.accepted := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- The completeness boundary is named exactly when every outside-scope
direction has an explicit outside-scope record. -/
theorem boundary_named_iff {Direction : Type} (inScope namedOutside : Direction → Prop) :
    BoundaryNamed inScope namedOutside ↔
      ∀ direction, ¬ inScope direction → namedOutside direction := by
  constructor
  · intro h direction hout
    exact h direction hout
  · intro h direction hout
    exact h direction hout

/-- Boundary overread is a claimed outside-scope direction without a boundary
record. -/
theorem boundary_overread_iff {Direction : Type}
    (inScope claimed namedOutside : Direction → Prop) :
    BoundaryOverread inScope claimed namedOutside ↔
      ∃ direction, ¬ inScope direction ∧ claimed direction ∧
        ¬ namedOutside direction := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Scoped completeness is formed closure plus adequate residual coverage and
accepted meta-audit, with scope, extractor, and nonclaim register declared. -/
theorem scoped_closure_complete_iff {Residual : Type}
    (formed scopeDeclared residualExtractorDeclared nonclaimRegisterClosed : Prop)
    (hasStatus statusAdequate : Residual → Prop)
    (metaVerdict : MetaAuditVerdict) :
    AuditedScopedClosureComplete formed scopeDeclared residualExtractorDeclared
        nonclaimRegisterClosed hasStatus statusAdequate metaVerdict ↔
      formed ∧ scopeDeclared ∧ residualExtractorDeclared ∧
        UnstatusedResidualEmpty hasStatus ∧
          InadequateStatusResidualEmpty statusAdequate ∧
            nonclaimRegisterClosed ∧ MetaCovered metaVerdict := by
  constructor
  · intro hcomplete
    rcases hcomplete with
      ⟨hformed, hscope, hextractor, hcoverage, hnonclaim, hmeta⟩
    have hempty := (residual_coverage_iff_empty_obstructions hasStatus statusAdequate).1
      hcoverage
    exact ⟨hformed, hscope, hextractor, hempty.1, hempty.2, hnonclaim, hmeta⟩
  · intro h
    rcases h with
      ⟨hformed, hscope, hextractor, hunstat, hbad, hnonclaim, hmeta⟩
    exact ⟨hformed, hscope, hextractor,
      (residual_coverage_iff_empty_obstructions hasStatus statusAdequate).2
        ⟨hunstat, hbad⟩,
      hnonclaim, hmeta⟩

/-- Internally covered but not meta-audited is exactly the same residual
coverage package with meta coverage missing. -/
theorem internally_covered_pending_meta_audit_iff {Residual : Type}
    (formed scopeDeclared residualExtractorDeclared nonclaimRegisterClosed : Prop)
    (hasStatus statusAdequate : Residual → Prop)
    (metaVerdict : MetaAuditVerdict) :
    InternallyCoveredPendingMetaAudit formed scopeDeclared residualExtractorDeclared
        nonclaimRegisterClosed hasStatus statusAdequate metaVerdict ↔
      formed ∧ scopeDeclared ∧ residualExtractorDeclared ∧
        UnstatusedResidualEmpty hasStatus ∧
          InadequateStatusResidualEmpty statusAdequate ∧
            nonclaimRegisterClosed ∧ ¬ MetaCovered metaVerdict := by
  constructor
  · intro hpending
    rcases hpending with
      ⟨hformed, hscope, hextractor, hcoverage, hnonclaim, hnotMeta⟩
    have hempty := (residual_coverage_iff_empty_obstructions hasStatus statusAdequate).1
      hcoverage
    exact ⟨hformed, hscope, hextractor, hempty.1, hempty.2, hnonclaim, hnotMeta⟩
  · intro h
    rcases h with
      ⟨hformed, hscope, hextractor, hunstat, hbad, hnonclaim, hnotMeta⟩
    exact ⟨hformed, hscope, hextractor,
      (residual_coverage_iff_empty_obstructions hasStatus statusAdequate).2
        ⟨hunstat, hbad⟩,
      hnonclaim, hnotMeta⟩

/--
Closure Completeness Boundary Normal Form. Scoped completeness is equivalent
to formed closure, declared scope, declared residual extractor, no unstatused
residuals, no inadequate statuses, closed nonclaim register, and accepted
meta-audit. Boundary directions are harmless exactly when named as outside
scope. Same-layer finality is blocked by the Reflexive Nonclosure policy.
-/
theorem closure_completeness_boundary
    {Residual Direction CompletenessClaim MetaClaim : Type}
    (formed scopeDeclared residualExtractorDeclared nonclaimRegisterClosed : Prop)
    (hasStatus statusAdequate : Residual → Prop)
    (metaVerdict : MetaAuditVerdict)
    (inScope claimed namedOutside : Direction → Prop)
    (policy : SameLayerAuditPolicy CompletenessClaim)
    (metaAudit : MetaLayerAudit CompletenessClaim MetaClaim) :
    (ResidualCoverage hasStatus statusAdequate ↔
      UnstatusedResidualEmpty hasStatus ∧
        InadequateStatusResidualEmpty statusAdequate) ∧
      (MetaCovered metaVerdict ↔ metaVerdict = MetaAuditVerdict.accepted) ∧
        (AuditedScopedClosureComplete formed scopeDeclared residualExtractorDeclared
            nonclaimRegisterClosed hasStatus statusAdequate metaVerdict ↔
          formed ∧ scopeDeclared ∧ residualExtractorDeclared ∧
            UnstatusedResidualEmpty hasStatus ∧
              InadequateStatusResidualEmpty statusAdequate ∧
                nonclaimRegisterClosed ∧ MetaCovered metaVerdict) ∧
          (InternallyCoveredPendingMetaAudit formed scopeDeclared
              residualExtractorDeclared nonclaimRegisterClosed hasStatus
              statusAdequate metaVerdict ↔
            formed ∧ scopeDeclared ∧ residualExtractorDeclared ∧
              UnstatusedResidualEmpty hasStatus ∧
                InadequateStatusResidualEmpty statusAdequate ∧
                  nonclaimRegisterClosed ∧ ¬ MetaCovered metaVerdict) ∧
            (BoundaryNamed inScope namedOutside ↔
              ∀ direction, ¬ inScope direction → namedOutside direction) ∧
              (BoundaryOverread inScope claimed namedOutside ↔
                ∃ direction, ¬ inScope direction ∧ claimed direction ∧
                  ¬ namedOutside direction) ∧
                (∀ claim : CompletenessClaim, SelfCertificationBlocked policy claim) := by
  refine ⟨residual_coverage_iff_empty_obstructions hasStatus statusAdequate, ?_⟩
  refine ⟨meta_covered_iff_accepted metaVerdict, ?_⟩
  refine ⟨scoped_closure_complete_iff formed scopeDeclared residualExtractorDeclared
    nonclaimRegisterClosed hasStatus statusAdequate metaVerdict, ?_⟩
  refine ⟨internally_covered_pending_meta_audit_iff formed scopeDeclared
    residualExtractorDeclared nonclaimRegisterClosed hasStatus statusAdequate metaVerdict, ?_⟩
  refine ⟨boundary_named_iff inScope namedOutside, ?_⟩
  refine ⟨boundary_overread_iff inScope claimed namedOutside, ?_⟩
  exact (reflexive_nonclosure policy metaAudit).1

/-- Coverage of every direction for which completeness is claimed. -/
def ClaimedDirectionCovered {D : Type} (inScope claimed namedOutside : D → Prop) :
    Prop :=
  ∀ d, claimed d → inScope d ∨ namedOutside d

/-- The paper's scoped internal completeness boundary. -/
def ScopedClosureComplete {R D : Type} (formed scopeDeclared : Prop)
    (hasStatus adequate : R → Prop)
    (inScope claimed namedOutside : D → Prop) : Prop :=
  formed ∧ scopeDeclared ∧ ResidualCoverage hasStatus adequate ∧
    ClaimedDirectionCovered inScope claimed namedOutside

/-- The paper's meta-completeness adds acceptance by the meta-audit. -/
def MetaComplete {R D : Type} (formed scopeDeclared : Prop)
    (hasStatus adequate : R → Prop)
    (inScope claimed namedOutside : D → Prop)
    (verdict : MetaAuditVerdict) : Prop :=
  ScopedClosureComplete formed scopeDeclared hasStatus adequate
    inScope claimed namedOutside ∧ MetaCovered verdict

/-- Paper scoped and meta completeness, including claimed-direction coverage. -/
theorem paper_closure_completeness_boundary {R D : Type}
    (formed scopeDeclared : Prop) (hasStatus adequate : R → Prop)
    (inScope claimed namedOutside : D → Prop)
    (verdict : MetaAuditVerdict) :
    (ResidualCoverage hasStatus adequate ↔
      ∀ r, hasStatus r ∧ adequate r) ∧
    (MetaCovered verdict ↔ verdict = MetaAuditVerdict.accepted) ∧
    (ScopedClosureComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside ↔
      formed ∧ scopeDeclared ∧ ResidualCoverage hasStatus adequate ∧
        (∀ d, claimed d → inScope d ∨ namedOutside d)) ∧
    (MetaComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside verdict ↔
      ScopedClosureComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside ∧ MetaCovered verdict) ∧
    (ScopedClosureComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside ↔
      formed ∧ scopeDeclared ∧ UnstatusedResidualEmpty hasStatus ∧
        InadequateStatusResidualEmpty adequate ∧
        ¬ BoundaryOverread inScope claimed namedOutside) := by
  refine ⟨Iff.rfl, meta_covered_iff_accepted verdict, Iff.rfl, Iff.rfl, ?_⟩
  constructor
  · rintro ⟨hf,hs,hcov,hdir⟩
    have hempty := (residual_coverage_iff_empty_obstructions hasStatus adequate).mp hcov
    refine ⟨hf,hs,hempty.1,hempty.2,?_⟩
    rintro ⟨d,hd, hc,hn⟩
    rcases hdir d hc with hi | ho
    · exact hd hi
    · exact hn ho
  · rintro ⟨hf,hs,hu,hi,hno⟩
    refine ⟨hf,hs,(residual_coverage_iff_empty_obstructions hasStatus adequate).mpr
      ⟨hu,hi⟩,?_⟩
    intro d hc
    by_cases hd : inScope d
    · exact Or.inl hd
    · right
      exact Classical.byContradiction (fun hn => hno ⟨d,hd,hc,hn⟩)

/-- Meta coverage for an arbitrary declared verdict carrier and its accepted
verdict. The five-constructor `MetaCovered` is this definition specialized
to `MetaAuditVerdict.accepted`. -/
def PaperMetaCovered {V : Type} (accepted v : V) : Prop :=
  v = accepted

/-- Scoped completeness with an arbitrary meta-audit verdict carrier. -/
def PaperMetaComplete {R D V : Type} (formed scopeDeclared : Prop)
    (hasStatus adequate : R → Prop)
    (inScope claimed namedOutside : D → Prop)
    (accepted v : V) : Prop :=
  ScopedClosureComplete formed scopeDeclared hasStatus adequate
    inScope claimed namedOutside ∧ PaperMetaCovered accepted v

/-- The existing five-constructor meta predicate is an instance of the
arbitrary-verdict predicate. -/
theorem meta_covered_five_verdict_instance (v : MetaAuditVerdict) :
    MetaCovered v ↔ PaperMetaCovered MetaAuditVerdict.accepted v := by
  rfl

/-- The old five-constructor meta-completeness predicate is the corresponding
specialization of the generalized one. -/
theorem meta_complete_five_verdict_instance {R D : Type}
    (formed scopeDeclared : Prop) (hasStatus adequate : R → Prop)
    (inScope claimed namedOutside : D → Prop) (v : MetaAuditVerdict) :
    MetaComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside v ↔
      PaperMetaComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside MetaAuditVerdict.accepted v := by
  rfl

/-- F52 for any declared verdict type containing a chosen accepted verdict.
The final clause gives the exact failure condition for meta-completeness. -/
theorem paper_closure_completeness_boundary_general
    {R D V : Type}
    (formed scopeDeclared : Prop) (hasStatus adequate : R → Prop)
    (inScope claimed namedOutside : D → Prop)
    (accepted v : V) :
    (ResidualCoverage hasStatus adequate ↔
      ∀ r, hasStatus r ∧ adequate r) ∧
    (PaperMetaCovered accepted v ↔ v = accepted) ∧
    (ScopedClosureComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside ↔
      formed ∧ scopeDeclared ∧ ResidualCoverage hasStatus adequate ∧
        (∀ d, claimed d → inScope d ∨ namedOutside d)) ∧
    (PaperMetaComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside accepted v ↔
      ScopedClosureComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside ∧ PaperMetaCovered accepted v) ∧
    (ScopedClosureComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside ↔
      formed ∧ scopeDeclared ∧ UnstatusedResidualEmpty hasStatus ∧
        InadequateStatusResidualEmpty adequate ∧
        ¬ BoundaryOverread inScope claimed namedOutside) ∧
    (¬ PaperMetaComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside accepted v ↔
      ¬ formed ∨ ¬ scopeDeclared ∨
        ¬ UnstatusedResidualEmpty hasStatus ∨
        ¬ InadequateStatusResidualEmpty adequate ∨
        BoundaryOverread inScope claimed namedOutside ∨ v ≠ accepted) := by
  have hscoped :
      ScopedClosureComplete formed scopeDeclared hasStatus adequate
          inScope claimed namedOutside ↔
        formed ∧ scopeDeclared ∧ UnstatusedResidualEmpty hasStatus ∧
          InadequateStatusResidualEmpty adequate ∧
            ¬ BoundaryOverread inScope claimed namedOutside := by
    constructor
    · rintro ⟨hf, hs, hcov, hdir⟩
      have hempty :=
        (residual_coverage_iff_empty_obstructions hasStatus adequate).mp hcov
      refine ⟨hf, hs, hempty.1, hempty.2, ?_⟩
      rintro ⟨d, hd, hc, hn⟩
      rcases hdir d hc with hi | ho
      · exact hd hi
      · exact hn ho
    · rintro ⟨hf, hs, hu, hi, hno⟩
      refine ⟨hf, hs,
        (residual_coverage_iff_empty_obstructions hasStatus adequate).mpr
          ⟨hu, hi⟩, ?_⟩
      intro d hc
      by_cases hd : inScope d
      · exact Or.inl hd
      · exact Or.inr (Classical.byContradiction
          (fun hn => hno ⟨d, hd, hc, hn⟩))
  refine ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, hscoped, ?_⟩
  classical
  change ¬ (ScopedClosureComplete formed scopeDeclared hasStatus adequate
      inScope claimed namedOutside ∧ v = accepted) ↔
    ¬ formed ∨ ¬ scopeDeclared ∨
      ¬ UnstatusedResidualEmpty hasStatus ∨
      ¬ InadequateStatusResidualEmpty adequate ∨
      BoundaryOverread inScope claimed namedOutside ∨ v ≠ accepted
  rw [hscoped]
  by_cases hf : formed <;>
    by_cases hs : scopeDeclared <;>
    by_cases hu : UnstatusedResidualEmpty hasStatus <;>
    by_cases hi : InadequateStatusResidualEmpty adequate <;>
    by_cases hb : BoundaryOverread inScope claimed namedOutside <;>
    by_cases hv : v = accepted <;>
    simp [hf, hs, hu, hi, hb, hv]

/-- Each of the four scoped-completeness conjuncts can fail alone on
one-element residual and direction types. -/
theorem scoped_closure_complete_four_conjuncts_independent :
    (∃ (formed scopeDeclared : Prop)
      (hasStatus adequate inScope claimed namedOutside : Unit → Prop),
      ¬ formed ∧ scopeDeclared ∧ ResidualCoverage hasStatus adequate ∧
        ClaimedDirectionCovered inScope claimed namedOutside) ∧
    (∃ (formed scopeDeclared : Prop)
      (hasStatus adequate inScope claimed namedOutside : Unit → Prop),
      formed ∧ ¬ scopeDeclared ∧ ResidualCoverage hasStatus adequate ∧
        ClaimedDirectionCovered inScope claimed namedOutside) ∧
    (∃ (formed scopeDeclared : Prop)
      (hasStatus adequate inScope claimed namedOutside : Unit → Prop),
      formed ∧ scopeDeclared ∧ ¬ ResidualCoverage hasStatus adequate ∧
        ClaimedDirectionCovered inScope claimed namedOutside) ∧
    (∃ (formed scopeDeclared : Prop)
      (hasStatus adequate inScope claimed namedOutside : Unit → Prop),
      formed ∧ scopeDeclared ∧ ResidualCoverage hasStatus adequate ∧
        ¬ ClaimedDirectionCovered inScope claimed namedOutside) := by
  refine ⟨⟨False, True, (fun _ => True), (fun _ => True),
      (fun _ => True), (fun _ => True), (fun _ => False), ?_⟩,
    ⟨True, False, (fun _ => True), (fun _ => True),
      (fun _ => True), (fun _ => True), (fun _ => False), ?_⟩,
    ⟨True, True, (fun _ => False), (fun _ => True),
      (fun _ => True), (fun _ => True), (fun _ => False), ?_⟩,
    ⟨True, True, (fun _ => True), (fun _ => True),
      (fun _ => False), (fun _ => True), (fun _ => False), ?_⟩⟩
  all_goals simp [ResidualCoverage, ClaimedDirectionCovered]

theorem paper_closure_completeness_boundary_general_sharp
    {R D V : Type}
    (formed scopeDeclared : Prop) (hasStatus adequate : R → Prop)
    (inScope claimed namedOutside : D → Prop)
    (accepted v : V) :
(    (ResidualCoverage hasStatus adequate ↔
      ∀ r, hasStatus r ∧ adequate r) ∧
    (PaperMetaCovered accepted v ↔ v = accepted) ∧
    (ScopedClosureComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside ↔
      formed ∧ scopeDeclared ∧ ResidualCoverage hasStatus adequate ∧
        (∀ d, claimed d → inScope d ∨ namedOutside d)) ∧
    (PaperMetaComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside accepted v ↔
      ScopedClosureComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside ∧ PaperMetaCovered accepted v) ∧
    (ScopedClosureComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside ↔
      formed ∧ scopeDeclared ∧ UnstatusedResidualEmpty hasStatus ∧
        InadequateStatusResidualEmpty adequate ∧
        ¬ BoundaryOverread inScope claimed namedOutside) ∧
    (¬ PaperMetaComplete formed scopeDeclared hasStatus adequate
        inScope claimed namedOutside accepted v ↔
      ¬ formed ∨ ¬ scopeDeclared ∨
        ¬ UnstatusedResidualEmpty hasStatus ∨
        ¬ InadequateStatusResidualEmpty adequate ∨
        BoundaryOverread inScope claimed namedOutside ∨ v ≠ accepted)) ∧
    (    (∃ (formed scopeDeclared : Prop)
      (hasStatus adequate inScope claimed namedOutside : Unit → Prop),
      ¬ formed ∧ scopeDeclared ∧ ResidualCoverage hasStatus adequate ∧
        ClaimedDirectionCovered inScope claimed namedOutside) ∧
    (∃ (formed scopeDeclared : Prop)
      (hasStatus adequate inScope claimed namedOutside : Unit → Prop),
      formed ∧ ¬ scopeDeclared ∧ ResidualCoverage hasStatus adequate ∧
        ClaimedDirectionCovered inScope claimed namedOutside) ∧
    (∃ (formed scopeDeclared : Prop)
      (hasStatus adequate inScope claimed namedOutside : Unit → Prop),
      formed ∧ scopeDeclared ∧ ¬ ResidualCoverage hasStatus adequate ∧
        ClaimedDirectionCovered inScope claimed namedOutside) ∧
    (∃ (formed scopeDeclared : Prop)
      (hasStatus adequate inScope claimed namedOutside : Unit → Prop),
      formed ∧ scopeDeclared ∧ ResidualCoverage hasStatus adequate ∧
        ¬ ClaimedDirectionCovered inScope claimed namedOutside)) := by
  exact ⟨paper_closure_completeness_boundary_general formed scopeDeclared hasStatus adequate
    inScope claimed namedOutside accepted v,
    scoped_closure_complete_four_conjuncts_independent⟩

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.ClosureCompletenessBoundary
