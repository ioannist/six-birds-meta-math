import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.LocallyConstant.Basic

/-!
F44 Criticality / Phase Boundary.

A phase is modeled as a locally stable formed quotient/status signature over a
control carrier. A boundary is non-local-constancy of that signature or a
formation/status change, and criticality is the boundary status where the
declared margin vanishes or response/scale descent becomes non-uniform.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Criticality

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- Two controls are in the same phase when their formed package signatures
agree. -/
def SamePhase {Control Phase : Type} (phase : Control → Phase)
    (left right : Control) : Prop :=
  phase left = phase right

/-- A phase transition along a declared control variation is a change in the
phase quotient value. -/
def PhaseTransition {Control Phase : Type} (phase : Control → Phase)
    (left right : Control) : Prop :=
  phase left ≠ phase right

/-- A path has a phase transition when its endpoint phase signatures differ. -/
def PhaseTransitionAlong {Path Control Phase : Type} (path : Path → Control)
    (start finish : Path) (phase : Control → Phase) : Prop :=
  PhaseTransition phase (path start) (path finish)

/-- The phase signature descends through the declared control quotient. -/
def PhaseQuotientDescends {Control C Phase : Type}
    (controlQuotient : Control → C) (phase : Control → Phase) : Prop :=
  Descends controlQuotient (fun control : Control => control) phase

/-- Control-overread obstruction for a phase signature. -/
def PhaseQuotientObstruction {Control C Phase : Type}
    (controlQuotient : Control → C) (phase : Control → Phase) :
    (Control × Control) → Prop :=
  splitPairObstruction controlQuotient (fun control : Control => control) phase

/-- No control-overread obstruction is present for the phase signature. -/
def PhaseQuotientObstructionEmpty {Control C Phase : Type}
    (controlQuotient : Control → C) (phase : Control → Phase) : Prop :=
  ObstructionEmpty (PhaseQuotientObstruction controlQuotient phase)

/-- A declared neighborhood relation is locally constant for the phase quotient
at a control when all formed controls in every declared neighborhood have the
same phase as the center. -/
def PhaseLocallyConstantAt {Control Phase Neighborhood : Type}
    (formed : Control → Prop) (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (control : Control) : Prop :=
  ∀ neighborhoodId other,
    neighborhood control neighborhoodId other → formed other →
      phase other = phase control

/-- A boundary-status change includes unformed boundary points, residual-status
changes, or other declared closure-status changes at the control. -/
def FormationOrStatusChange {Control : Type} (statusChanges : Control → Prop)
    (control : Control) : Prop :=
  statusChanges control

/-- Phase boundary: the phase quotient is not locally constant, or formation /
status changes at the control. -/
def PhaseBoundary {Control Phase Neighborhood : Type} (formed : Control → Prop)
    (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (statusChanges : Control → Prop) (control : Control) : Prop :=
  ¬ PhaseLocallyConstantAt formed phase neighborhood control ∨
    FormationOrStatusChange statusChanges control

/-- Local constancy in at least one neighborhood, as stated in the paper F44.
Unlike `PhaseLocallyConstantAt`, this has an existential neighborhood and does
not filter neighboring controls by formedness. -/
def PaperPhaseLocallyConstantAt {Control Phase Neighborhood : Type}
    (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (control : Control) : Prop :=
  ∃ neighborhoodId, ∀ other,
    neighborhood control neighborhoodId other → phase other = phase control

/-- F44's boundary requires a formed center and failure of every locally
constant neighborhood. -/
def PaperPhaseBoundary {Control Phase Neighborhood : Type}
    (formed : Control → Prop) (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (control : Control) : Prop :=
  formed control ∧ ¬ PaperPhaseLocallyConstantAt phase neighborhood control

/-- F44's criticality uses exactly the paper boundary, instability disjunction,
and residual status. -/
def PaperCriticalAt {Control Phase Neighborhood : Type}
    (formed : Control → Prop) (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (marginVanishes nonUniformResponse residualsStatused : Control → Prop)
    (control : Control) : Prop :=
  PaperPhaseBoundary formed phase neighborhood control ∧
    (marginVanishes control ∨ nonUniformResponse control) ∧
      residualsStatused control

/-- A phase region is a declared connected region of formed controls carrying a
single phase value. Maximality is supplied by the local control package. -/
def PhaseRegion {Control Phase Region : Type} (formed : Control → Prop)
    (phase : Control → Phase) (contains : Region → Control → Prop)
    (connected maximal : Region → Prop) (region : Region) : Prop :=
  connected region ∧ maximal region ∧
    ∃ phaseValue : Phase,
      ∀ control, contains region control → formed control ∧ phase control = phaseValue

/-- An order parameter is a readout that separates phase classes on the
declared support. -/
def OrderParameter {Control Phase Value : Type} (formed : Control → Prop)
    (phase : Control → Phase) (readout : Control → Value) : Prop :=
  ∀ left right,
    formed left → formed right → phase left ≠ phase right →
      readout left ≠ readout right

/-- A selected observable can be continuous across a structural phase change. -/
def ContinuousPhaseTransition {Control Phase Value : Type} (phase : Control → Phase)
    (readout : Control → Value) (ContinuousAcross : Value → Value → Prop)
    (left right : Control) : Prop :=
  PhaseTransition phase left right ∧
    ContinuousAcross (readout left) (readout right)

/-- A jump transition is a phase transition with a declared readout jump. -/
def JumpTransition {Control Phase Value : Type} (phase : Control → Phase)
    (readout : Control → Value) (Jump : Value → Value → Prop)
    (left right : Control) : Prop :=
  PhaseTransition phase left right ∧ Jump (readout left) (readout right)

/-- A crossover is readout change without phase-signature change. -/
def Crossover {Control Phase Value : Type} (phase : Control → Phase)
    (readout : Control → Value) (Changes : Value → Value → Prop)
    (left right : Control) : Prop :=
  SamePhase phase left right ∧ Changes (readout left) (readout right)

/-- Criticality gate: vanishing stability margin or non-uniform response/scale
descent at a boundary. -/
def CriticalInstability {Control : Type} (marginVanishes : Control → Prop)
    (nonUniformScaleOrResponse : Control → Prop) (control : Control) : Prop :=
  marginVanishes control ∨ nonUniformScaleOrResponse control

/-- Critical point/region relative to the declared residual and response
structure. -/
def CriticalAt {Control Phase Neighborhood : Type} (formed : Control → Prop)
    (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (statusChanges marginVanishes nonUniformScaleOrResponse residualsStatused :
      Control → Prop)
    (control : Control) : Prop :=
  PhaseBoundary formed phase neighborhood statusChanges control ∧
    CriticalInstability marginVanishes nonUniformScaleOrResponse control ∧
      residualsStatused control

/-- Phase coexistence/moduli at a boundary: more than one lawful phase
completion is available. -/
def PhaseCoexistence {Control Moduli : Type} (phaseModuli : Control → Moduli → Prop)
    (Nontrivial : (Moduli → Prop) → Prop) (control : Control) : Prop :=
  Nontrivial (phaseModuli control)

/-- Hysteresis or phase holonomy: selected phase depends on route memory through
control space. -/
def PhaseHolonomy {Route Control Phase : Type} (selectedPhase : Route → Control → Phase)
    (control : Control) : Prop :=
  ∃ r₁ r₂ : Route, selectedPhase r₁ control ≠ selectedPhase r₂ control

/-- Source status vocabulary for phase and criticality claims. -/
inductive CriticalityStatus where
  | samePhase
  | quotientPhaseTransition
  | statusPhaseTransition
  | transportPhaseTransition
  | symmetryPhaseTransition
  | phaseCoexistence
  | phaseModuli
  | continuousTransition
  | jumpTransition
  | critical
  | crossover
  | finiteStageRounded
  | metastablePhase
  | phaseHolonomy
  | hysteresis
  | localPhase
  | globalPhaseObstructed
  | hiddenPhase
  | presentationPhaseArtifact
  | protocolPhaseArtifact
  | unformedBoundary
  | phaseOverread
deriving DecidableEq

/-- Meaning assignment for the F44 criticality status vocabulary. -/
def CriticalityStatusHolds (same quotient status transport symmetry coexistence
    moduli continuous jump criticalStatus crossover rounded metastable holonomy
    hysteresis localOnly globalObstructed hidden presentationArtifact protocolArtifact
    unformed overread : Prop) : CriticalityStatus → Prop
  | CriticalityStatus.samePhase => same
  | CriticalityStatus.quotientPhaseTransition => quotient
  | CriticalityStatus.statusPhaseTransition => status
  | CriticalityStatus.transportPhaseTransition => transport
  | CriticalityStatus.symmetryPhaseTransition => symmetry
  | CriticalityStatus.phaseCoexistence => coexistence
  | CriticalityStatus.phaseModuli => moduli
  | CriticalityStatus.continuousTransition => continuous
  | CriticalityStatus.jumpTransition => jump
  | CriticalityStatus.critical => criticalStatus
  | CriticalityStatus.crossover => crossover
  | CriticalityStatus.finiteStageRounded => rounded
  | CriticalityStatus.metastablePhase => metastable
  | CriticalityStatus.phaseHolonomy => holonomy
  | CriticalityStatus.hysteresis => hysteresis
  | CriticalityStatus.localPhase => localOnly
  | CriticalityStatus.globalPhaseObstructed => globalObstructed
  | CriticalityStatus.hiddenPhase => hidden
  | CriticalityStatus.presentationPhaseArtifact => presentationArtifact
  | CriticalityStatus.protocolPhaseArtifact => protocolArtifact
  | CriticalityStatus.unformedBoundary => unformed
  | CriticalityStatus.phaseOverread => overread

/-- Same phase is equality of the phase quotient value. -/
theorem same_phase_iff_phase_equal {Control Phase : Type} (phase : Control → Phase)
    (left right : Control) :
    SamePhase phase left right ↔ phase left = phase right := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Phase transition is non-constancy of the phase quotient across a declared
variation. -/
theorem phase_transition_iff_phase_changes {Control Phase : Type}
    (phase : Control → Phase) (left right : Control) :
    PhaseTransition phase left right ↔ phase left ≠ phase right := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- A phase signature descends through the control quotient exactly when no
control-overread split pair is present. -/
theorem phase_quotient_descends_iff_no_obstruction {Control C Phase : Type}
    (controlQuotient : Control → C) (phase : Control → Phase)
    (hcontrol : Function.Surjective controlQuotient) :
    PhaseQuotientDescends controlQuotient phase ↔
      PhaseQuotientObstructionEmpty controlQuotient phase :=
  descent_repair_normal_form controlQuotient (fun control : Control => control)
    phase hcontrol

/-- Boundary is exactly non-local-constancy or declared formation/status
change. -/
theorem phase_boundary_iff_not_locally_constant_or_status_change
    {Control Phase Neighborhood : Type} (formed : Control → Prop)
    (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (statusChanges : Control → Prop) (control : Control) :
    PhaseBoundary formed phase neighborhood statusChanges control ↔
      ¬ PhaseLocallyConstantAt formed phase neighborhood control ∨
        FormationOrStatusChange statusChanges control := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Criticality is the boundary status together with vanishing margin or
non-uniform scale/response descent, with residuals explicitly statused. -/
theorem critical_at_iff_boundary_and_instability {Control Phase Neighborhood : Type}
    (formed : Control → Prop) (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (statusChanges marginVanishes nonUniformScaleOrResponse residualsStatused :
      Control → Prop)
    (control : Control) :
    CriticalAt formed phase neighborhood statusChanges marginVanishes
        nonUniformScaleOrResponse residualsStatused control ↔
      PhaseBoundary formed phase neighborhood statusChanges control ∧
        (marginVanishes control ∨ nonUniformScaleOrResponse control) ∧
          residualsStatused control := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Crossover is readout change while the formed phase signature remains fixed. -/
theorem crossover_iff_same_phase_and_readout_change {Control Phase Value : Type}
    (phase : Control → Phase) (readout : Control → Value)
    (Changes : Value → Value → Prop) (left right : Control) :
    Crossover phase readout Changes left right ↔
      SamePhase phase left right ∧ Changes (readout left) (readout right) := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
Criticality / Phase Boundary Normal Form. Phase transition is change in the
formed phase quotient; the phase signature must descend through the declared
control quotient to be control-native; a boundary is non-local-constancy or a
formation/status change; and criticality is the special boundary status with
vanishing margin or non-uniform response/scale descent plus statused residuals.
-/
theorem criticality_phase_boundary {Control C Phase Neighborhood Value : Type}
    (controlQuotient : Control → C) (phase : Control → Phase)
    (formed : Control → Prop)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (statusChanges marginVanishes nonUniformScaleOrResponse residualsStatused :
      Control → Prop)
    (readout : Control → Value) (Changes : Value → Value → Prop)
    (left right control : Control)
    (hcontrol : Function.Surjective controlQuotient) :
    (PhaseQuotientDescends controlQuotient phase ↔
      PhaseQuotientObstructionEmpty controlQuotient phase) ∧
      (PhaseTransition phase left right ↔ phase left ≠ phase right) ∧
        (PhaseBoundary formed phase neighborhood statusChanges control ↔
          ¬ PhaseLocallyConstantAt formed phase neighborhood control ∨
            FormationOrStatusChange statusChanges control) ∧
          (CriticalAt formed phase neighborhood statusChanges marginVanishes
              nonUniformScaleOrResponse residualsStatused control ↔
            PhaseBoundary formed phase neighborhood statusChanges control ∧
              (marginVanishes control ∨ nonUniformScaleOrResponse control) ∧
                residualsStatused control) ∧
            (Crossover phase readout Changes left right ↔
              SamePhase phase left right ∧ Changes (readout left) (readout right)) := by
  exact ⟨phase_quotient_descends_iff_no_obstruction controlQuotient phase hcontrol,
    phase_transition_iff_phase_changes phase left right,
    phase_boundary_iff_not_locally_constant_or_status_change formed phase
      neighborhood statusChanges control,
    critical_at_iff_boundary_and_instability formed phase neighborhood statusChanges
      marginVanishes nonUniformScaleOrResponse residualsStatused control,
    crossover_iff_same_phase_and_readout_change phase readout Changes left right⟩

/-- The four formulas of the paper F44 statement. `statusChanges` is absent:
the displayed boundary requires formedness and has no status-change disjunct. -/
theorem criticality_phase_boundary_paper {Control C Phase Neighborhood Value : Type}
    (controlQuotient : Control → C) (phase : Control → Phase)
    (formed : Control → Prop)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (statusChanges marginVanishes nonUniformResponse residualsStatused : Control → Prop)
    (readout : Control → Value) (left right control : Control)
    (hcontrol : Function.Surjective controlQuotient) :
    (Descends controlQuotient (fun x : Control => x) readout ↔
      ObstructionEmpty
        (splitPairObstruction controlQuotient (fun x : Control => x) readout)) ∧
      (PhaseTransition phase left right ↔ phase left ≠ phase right) ∧
        (PaperPhaseBoundary formed phase neighborhood control ↔
          formed control ∧
            ¬ ∃ neighborhoodId, ∀ other,
              neighborhood control neighborhoodId other →
                phase other = phase control) ∧
          (PaperCriticalAt formed phase neighborhood marginVanishes
              nonUniformResponse residualsStatused control ↔
            PaperPhaseBoundary formed phase neighborhood control ∧
              (marginVanishes control ∨ nonUniformResponse control) ∧
                residualsStatused control) := by
  let _ := statusChanges
  exact ⟨descent_repair_normal_form controlQuotient (fun x : Control => x)
      readout hcontrol,
    phase_transition_iff_phase_changes phase left right,
    Iff.rfl, Iff.rfl⟩

/-- Paper F44: descent through the control quotient is the split-pair
criterion, and fiber-invariant phase data with a quotient-respecting
neighborhood make boundary and criticality fiber-invariant as well. -/
theorem criticality_phase_boundary_descent
    {Control C Phase Neighborhood Value : Type}
    (controlQuotient : Control → C) (phase : Control → Phase)
    (formed : Control → Prop)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (marginVanishes nonUniformResponse residualsStatused : Control → Prop)
    (readout : Control → Value)
    (hcontrol : Function.Surjective controlQuotient) :
    (Descends controlQuotient (fun x : Control => x) readout ↔
      ObstructionEmpty
        (splitPairObstruction controlQuotient (fun x : Control => x) readout)) ∧
    (((∀ x x', controlQuotient x = controlQuotient x' →
        phase x = phase x') ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (formed x ↔ formed x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (marginVanishes x ↔ marginVanishes x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (nonUniformResponse x ↔ nonUniformResponse x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (residualsStatused x ↔ residualsStatused x')) ∧
      (∀ x x' W y, controlQuotient x = controlQuotient x' →
        (neighborhood x W y ↔ neighborhood x' W y))) →
      ∀ x x', controlQuotient x = controlQuotient x' →
        (PaperPhaseBoundary formed phase neighborhood x ↔
          PaperPhaseBoundary formed phase neighborhood x') ∧
        (PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x ↔
          PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x')) := by
  refine ⟨descent_repair_normal_form controlQuotient
    (fun x : Control => x) readout hcontrol, ?_⟩
  intro hdata x x' heq
  rcases hdata with ⟨hphase, hformed, hmargin, hresponse, hresidual, hneighborhood⟩
  have hlocal : PaperPhaseLocallyConstantAt phase neighborhood x ↔
      PaperPhaseLocallyConstantAt phase neighborhood x' := by
    constructor
    · intro ⟨W, hW⟩
      refine ⟨W, ?_⟩
      intro y hy
      calc
        phase y = phase x := hW y ((hneighborhood x x' W y heq).2 hy)
        _ = phase x' := hphase x x' heq
    · intro ⟨W, hW⟩
      refine ⟨W, ?_⟩
      intro y hy
      calc
        phase y = phase x' := hW y ((hneighborhood x x' W y heq).1 hy)
        _ = phase x := (hphase x x' heq).symm
  have hboundary : PaperPhaseBoundary formed phase neighborhood x ↔
      PaperPhaseBoundary formed phase neighborhood x' := by
    constructor
    · intro hb
      exact ⟨(hformed x x' heq).1 hb.1,
        fun hl' => hb.2 (hlocal.2 hl')⟩
    · intro hb
      exact ⟨(hformed x x' heq).2 hb.1,
        fun hl => hb.2 (hlocal.1 hl)⟩
  refine ⟨hboundary, ?_⟩
  constructor
  · intro hc
    refine ⟨hboundary.1 hc.1, ?_, (hresidual x x' heq).1 hc.2.2⟩
    cases hc.2.1 with
    | inl hm => exact Or.inl ((hmargin x x' heq).1 hm)
    | inr hr => exact Or.inr ((hresponse x x' heq).1 hr)
  · intro hc
    refine ⟨hboundary.2 hc.1, ?_, (hresidual x x' heq).2 hc.2.2⟩
    cases hc.2.1 with
    | inl hm => exact Or.inl ((hmargin x x' heq).2 hm)
    | inr hr => exact Or.inr ((hresponse x x' heq).2 hr)

/-- A fiber-invariant predicate descends through a surjective control map. -/
private theorem predicate_descends_of_fiber_invariant
    {Control C : Type} (c : Control → C) (hc : Function.Surjective c)
    (P : Control → Prop)
    (hP : ∀ x x', c x = c x' → (P x ↔ P x')) :
    Descends c (fun x : Control => x) P := by
  classical
  let Pbar : C → Prop := fun z => P (Classical.choose (hc z))
  refine ⟨Pbar, ?_⟩
  funext x
  apply propext
  exact hP (Classical.choose (hc (c x))) x
    (Classical.choose_spec (hc (c x)))

/-- F44: stable phase data make boundary and criticality both invariant and
descended through the control quotient. -/
theorem criticality_phase_boundary_descent_paper
    {Control C Phase Neighborhood Value : Type}
    (controlQuotient : Control → C) (phase : Control → Phase)
    (formed : Control → Prop)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (marginVanishes nonUniformResponse residualsStatused : Control → Prop)
    (readout : Control → Value)
    (hcontrol : Function.Surjective controlQuotient) :
    (Descends controlQuotient (fun x : Control => x) readout ↔
      ObstructionEmpty
        (splitPairObstruction controlQuotient (fun x : Control => x) readout)) ∧
    (((∀ x x', controlQuotient x = controlQuotient x' → phase x = phase x') ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (formed x ↔ formed x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (marginVanishes x ↔ marginVanishes x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (nonUniformResponse x ↔ nonUniformResponse x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (residualsStatused x ↔ residualsStatused x')) ∧
      (∀ x x' W y, controlQuotient x = controlQuotient x' →
        (neighborhood x W y ↔ neighborhood x' W y))) →
      (∀ x x', controlQuotient x = controlQuotient x' →
        (PaperPhaseBoundary formed phase neighborhood x ↔
          PaperPhaseBoundary formed phase neighborhood x') ∧
        (PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x ↔
          PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x')) ∧
      Descends controlQuotient (fun x : Control => x)
        (PaperPhaseBoundary formed phase neighborhood) ∧
      Descends controlQuotient (fun x : Control => x)
        (PaperCriticalAt formed phase neighborhood marginVanishes
          nonUniformResponse residualsStatused)) := by
  rcases criticality_phase_boundary_descent controlQuotient phase formed
      neighborhood marginVanishes nonUniformResponse residualsStatused readout
      hcontrol with ⟨hreadout, hboundary⟩
  refine ⟨hreadout, ?_⟩
  intro hdata
  have h := hboundary hdata
  refine ⟨h, ?_, ?_⟩
  · exact predicate_descends_of_fiber_invariant controlQuotient hcontrol
      (PaperPhaseBoundary formed phase neighborhood)
      (fun x x' heq => (h x x' heq).1)
  · exact predicate_descends_of_fiber_invariant controlQuotient hcontrol
      (PaperCriticalAt formed phase neighborhood marginVanishes
        nonUniformResponse residualsStatused)
      (fun x x' heq => (h x x' heq).2)

/-- A finite list of formed controls whose consecutive entries are neighbors
for every neighborhood parameter. The endpoint indices are part of the type. -/
inductive FiniteFormedNeighborhoodPath
    {Control Neighborhood : Type}
    (formed : Control → Prop)
    (neighborhood : Control → Neighborhood → Control → Prop) :
    Control → Control → List Control → Prop where
  | stop (x : Control) (hx : formed x) :
      FiniteFormedNeighborhoodPath formed neighborhood x x [x]
  | step (x y z : Control) (tail : List Control)
      (hx : formed x) (hnear : ∀ W, neighborhood x W y)
      (hrest : FiniteFormedNeighborhoodPath formed neighborhood y z (y :: tail)) :
      FiniteFormedNeighborhoodPath formed neighborhood x z (x :: y :: tail)

/-- A phase change along a finite formed path forces a boundary at the start
of one of its consecutive edges. -/
theorem finite_phase_transition_has_boundary
    {Control Phase Neighborhood : Type}
    (formed : Control → Prop) (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (left right : Control) (path : List Control)
    (hpath : FiniteFormedNeighborhoodPath formed neighborhood left right path)
    (htransition : PhaseTransition phase left right) :
    ∃ (before after : List Control) (x y : Control),
      path = before ++ x :: y :: after ∧
        phase x ≠ phase y ∧
          PaperPhaseBoundary formed phase neighborhood x := by
  induction hpath with
  | stop x hx =>
      exact False.elim (htransition rfl)
  | step x y z tail hx hnear hrest ih =>
      by_cases hxy : phase x = phase y
      · have hyz : PhaseTransition phase y z := by
          intro hyz
          exact htransition (hxy.trans hyz)
        obtain ⟨before, after, u, v, hshape, hchange, hboundary⟩ := ih hyz
        refine ⟨x :: before, after, u, v, ?_, hchange, hboundary⟩
        simp [hshape]
      · refine ⟨[], tail, x, y, rfl, hxy, hx, ?_⟩
        rintro ⟨W, hconstant⟩
        exact hxy (hconstant y (hnear W)).symm

theorem criticality_phase_boundary_descent_paper_finite_path
    {Control C Phase Neighborhood Value : Type}
    (controlQuotient : Control → C) (phase : Control → Phase)
    (formed : Control → Prop)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (marginVanishes nonUniformResponse residualsStatused : Control → Prop)
    (readout : Control → Value)
    (hcontrol : Function.Surjective controlQuotient) :
(    (Descends controlQuotient (fun x : Control => x) readout ↔
      ObstructionEmpty
        (splitPairObstruction controlQuotient (fun x : Control => x) readout)) ∧
    (((∀ x x', controlQuotient x = controlQuotient x' → phase x = phase x') ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (formed x ↔ formed x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (marginVanishes x ↔ marginVanishes x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (nonUniformResponse x ↔ nonUniformResponse x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (residualsStatused x ↔ residualsStatused x')) ∧
      (∀ x x' W y, controlQuotient x = controlQuotient x' →
        (neighborhood x W y ↔ neighborhood x' W y))) →
      (∀ x x', controlQuotient x = controlQuotient x' →
        (PaperPhaseBoundary formed phase neighborhood x ↔
          PaperPhaseBoundary formed phase neighborhood x') ∧
        (PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x ↔
          PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x')) ∧
      Descends controlQuotient (fun x : Control => x)
        (PaperPhaseBoundary formed phase neighborhood) ∧
      Descends controlQuotient (fun x : Control => x)
        (PaperCriticalAt formed phase neighborhood marginVanishes
          nonUniformResponse residualsStatused))) ∧
    (∀ (left right : Control) (path : List Control),
      FiniteFormedNeighborhoodPath formed neighborhood left right path →
      PhaseTransition phase left right →
        ∃ (before after : List Control) (x y : Control),
          path = before ++ x :: y :: after ∧
            phase x ≠ phase y ∧
              PaperPhaseBoundary formed phase neighborhood x) := by
  refine ⟨criticality_phase_boundary_descent_paper controlQuotient phase formed
    neighborhood marginVanishes nonUniformResponse residualsStatused readout
    hcontrol, ?_⟩
  intro left right path hpath htransition
  exact finite_phase_transition_has_boundary formed phase neighborhood
    left right path hpath htransition

/-- The proposed relation on all subsets. Non-open subsets make this relation
empty and therefore cannot be allowed as local-constancy witnesses. -/
def topNeighborhood {Control : Type} [TopologicalSpace Control]
    (x : Control) (W : Set Control) (y : Control) : Prop :=
  IsOpen W ∧ (x ∈ W → y ∈ W)

/-- A non-open neighborhood index vacuously certifies local constancy, so the
relation indexed by all subsets cannot support the proposed path theorem. -/
theorem top_neighborhood_nonopen_precludes_boundary
    {Control Phase : Type} [TopologicalSpace Control]
    (formed : Control → Prop) (phase : Control → Phase)
    (W : Set Control) (hW : ¬ IsOpen W) (x : Control) :
    ¬ PaperPhaseBoundary formed phase topNeighborhood x := by
  intro hboundary
  apply hboundary.2
  refine ⟨W, ?_⟩
  intro y hnear
  exact False.elim (hW hnear.1)

/-- A concrete counterexample to the path claim when all subsets are admitted
as neighborhood indices: the identity path in the real interval changes phase
but has no boundary under `topNeighborhood`. -/
theorem top_neighborhood_path_counterexample :
    ∃ γ : unitInterval → ℝ, Continuous γ ∧
      (∀ s, (fun _ : ℝ => True) (γ s)) ∧
      γ 0 ≠ γ 1 ∧
      ¬ ∃ s, PaperPhaseBoundary (fun _ : ℝ => True)
        (fun x : ℝ => x) topNeighborhood (γ s) := by
  refine ⟨Subtype.val, continuous_subtype_val, fun _ => trivial,
    zero_ne_one, ?_⟩
  rintro ⟨s, hboundary⟩
  exact top_neighborhood_nonopen_precludes_boundary (fun _ : ℝ => True)
    (fun x : ℝ => x) {0} (not_isOpen_singleton 0) (s : ℝ) hboundary

/-- The intended topological relation, indexed only by open sets. An open set
missing the center imposes no restriction on the other point. -/
def openTopNeighborhood {Control : Type} [TopologicalSpace Control]
    (x : Control) (W : TopologicalSpace.Opens Control) (y : Control) : Prop :=
  topNeighborhood x (W : Set Control) y

/-- A continuous formed path with different endpoint phases meets a phase
boundary. Neighborhood indices are open sets, excluding vacuous non-open
local-constancy witnesses. No topology on the phase type is needed. -/
theorem topological_phase_transition_has_boundary
    {Control Phase : Type} [TopologicalSpace Control]
    (formed : Control → Prop) (phase : Control → Phase)
    (γ : unitInterval → Control) (hγ : Continuous γ)
    (hformed : ∀ s, formed (γ s)) (htransition : phase (γ 0) ≠ phase (γ 1)) :
    ∃ s, PaperPhaseBoundary formed phase openTopNeighborhood (γ s) := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hlocal : IsLocallyConstant (phase ∘ γ) := by
    apply (IsLocallyConstant.iff_exists_open _).2
    intro s
    have hconstant : PaperPhaseLocallyConstantAt phase openTopNeighborhood (γ s) := by
      apply Classical.byContradiction
      intro hnot
      exact hnone ⟨s, hformed s, hnot⟩
    obtain ⟨W, hW⟩ := hconstant
    by_cases hxW : γ s ∈ W
    · refine ⟨γ ⁻¹' (W : Set Control), hγ.isOpen_preimage _ W.isOpen, hxW, ?_⟩
      intro s' hs'
      exact hW (γ s') ⟨W.isOpen, fun _ => hs'⟩
    · refine ⟨Set.univ, isOpen_univ, Set.mem_univ s, ?_⟩
      intro s' _
      exact hW (γ s') ⟨W.isOpen, fun hmem => False.elim (hxW hmem)⟩
  exact htransition (hlocal.apply_eq_of_preconnectedSpace 0 1)

/-- F44's descent and arbitrary-neighborhood finite-path clauses, together
with the continuous-path clause for open-set-indexed neighborhoods. -/
theorem criticality_phase_boundary_descent_paper_topological_path
    {Control C Phase Neighborhood Value : Type} [TopologicalSpace Control]
    (controlQuotient : Control → C) (phase : Control → Phase)
    (formed : Control → Prop)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (marginVanishes nonUniformResponse residualsStatused : Control → Prop)
    (readout : Control → Value)
    (hcontrol : Function.Surjective controlQuotient) :
    (((Descends controlQuotient (fun x : Control => x) readout ↔
      ObstructionEmpty
        (splitPairObstruction controlQuotient (fun x : Control => x) readout)) ∧
    (((∀ x x', controlQuotient x = controlQuotient x' → phase x = phase x') ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (formed x ↔ formed x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (marginVanishes x ↔ marginVanishes x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (nonUniformResponse x ↔ nonUniformResponse x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (residualsStatused x ↔ residualsStatused x')) ∧
      (∀ x x' W y, controlQuotient x = controlQuotient x' →
        (neighborhood x W y ↔ neighborhood x' W y))) →
      (∀ x x', controlQuotient x = controlQuotient x' →
        (PaperPhaseBoundary formed phase neighborhood x ↔
          PaperPhaseBoundary formed phase neighborhood x') ∧
        (PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x ↔
          PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x')) ∧
      Descends controlQuotient (fun x : Control => x)
        (PaperPhaseBoundary formed phase neighborhood) ∧
      Descends controlQuotient (fun x : Control => x)
        (PaperCriticalAt formed phase neighborhood marginVanishes
          nonUniformResponse residualsStatused))) ∧
    (∀ (left right : Control) (path : List Control),
      FiniteFormedNeighborhoodPath formed neighborhood left right path →
      PhaseTransition phase left right →
        ∃ (before after : List Control) (x y : Control),
          path = before ++ x :: y :: after ∧
            phase x ≠ phase y ∧
              PaperPhaseBoundary formed phase neighborhood x)) ∧
    (∀ γ : unitInterval → Control, Continuous γ →
      (∀ s, formed (γ s)) → phase (γ 0) ≠ phase (γ 1) →
        ∃ s, PaperPhaseBoundary formed phase openTopNeighborhood (γ s)) := by
  refine ⟨criticality_phase_boundary_descent_paper_finite_path
    controlQuotient phase formed neighborhood marginVanishes nonUniformResponse
    residualsStatused readout hcontrol, ?_⟩
  intro γ hγ hformed htransition
  exact topological_phase_transition_has_boundary formed phase γ hγ hformed htransition

/-- A formed finite path where each neighborhood at the current vertex
contains some control with the phase of the next vertex. -/
inductive FiniteFormedPhaseNeighborhoodPath
    {Control Phase Neighborhood : Type}
    (formed : Control → Prop) (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop) :
    Control → Control → List Control → Prop where
  | stop (x : Control) (hx : formed x) :
      FiniteFormedPhaseNeighborhoodPath formed phase neighborhood x x [x]
  | step (x y z : Control) (tail : List Control)
      (hx : formed x)
      (hnear : ∀ W, ∃ witness, neighborhood x W witness ∧ phase witness = phase y)
      (hrest : FiniteFormedPhaseNeighborhoodPath formed phase neighborhood
        y z (y :: tail)) :
      FiniteFormedPhaseNeighborhoodPath formed phase neighborhood x z (x :: y :: tail)

/-- The former hypothesis is a special case: take the next vertex itself as
the witness in every neighborhood. -/
theorem finite_formed_neighborhood_path_implies_phase_path
    {Control Phase Neighborhood : Type}
    (formed : Control → Prop) (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (left right : Control) (path : List Control)
    (hpath : FiniteFormedNeighborhoodPath formed neighborhood left right path) :
    FiniteFormedPhaseNeighborhoodPath formed phase neighborhood left right path := by
  induction hpath with
  | stop x hx => exact .stop x hx
  | step x y z tail hx hnear _ ih =>
      exact .step x y z tail hx (fun W => ⟨y, hnear W, rfl⟩) ih

/-- Phase witnesses in every neighborhood suffice for a boundary at one
phase-changing consecutive edge of a finite formed path. -/
theorem finite_phase_witness_transition_has_boundary
    {Control Phase Neighborhood : Type}
    (formed : Control → Prop) (phase : Control → Phase)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (left right : Control) (path : List Control)
    (hpath : FiniteFormedPhaseNeighborhoodPath formed phase neighborhood
      left right path)
    (htransition : PhaseTransition phase left right) :
    ∃ (before after : List Control) (x y : Control),
      path = before ++ x :: y :: after ∧
        phase x ≠ phase y ∧ PaperPhaseBoundary formed phase neighborhood x := by
  induction hpath with
  | stop x hx => exact False.elim (htransition rfl)
  | step x y z tail hx hnear _ ih =>
      by_cases hxy : phase x = phase y
      · have hyz : PhaseTransition phase y z := by
          intro hyz
          exact htransition (hxy.trans hyz)
        obtain ⟨before, after, u, v, hshape, hchange, hboundary⟩ := ih hyz
        refine ⟨x :: before, after, u, v, ?_, hchange, hboundary⟩
        simp [hshape]
      · refine ⟨[], tail, x, y, rfl, hxy, hx, ?_⟩
        rintro ⟨W, hconstant⟩
        obtain ⟨witness, hnearWitness, hphase⟩ := hnear W
        exact hxy ((hconstant witness hnearWitness).symm.trans hphase)

/-- The existing F44 descent, finite-path and topological-path clauses,
extended by the weaker finite path of neighborhood phase witnesses. -/
theorem criticality_phase_boundary_descent_paper_topological_path_strengthened
    {Control C Phase Neighborhood Value : Type} [TopologicalSpace Control]
    (controlQuotient : Control → C) (phase : Control → Phase)
    (formed : Control → Prop)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (marginVanishes nonUniformResponse residualsStatused : Control → Prop)
    (readout : Control → Value)
    (hcontrol : Function.Surjective controlQuotient) :
    ((((Descends controlQuotient (fun x : Control => x) readout ↔
      ObstructionEmpty
        (splitPairObstruction controlQuotient (fun x : Control => x) readout)) ∧
    (((∀ x x', controlQuotient x = controlQuotient x' → phase x = phase x') ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (formed x ↔ formed x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (marginVanishes x ↔ marginVanishes x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (nonUniformResponse x ↔ nonUniformResponse x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (residualsStatused x ↔ residualsStatused x')) ∧
      (∀ x x' W y, controlQuotient x = controlQuotient x' →
        (neighborhood x W y ↔ neighborhood x' W y))) →
      (∀ x x', controlQuotient x = controlQuotient x' →
        (PaperPhaseBoundary formed phase neighborhood x ↔
          PaperPhaseBoundary formed phase neighborhood x') ∧
        (PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x ↔
          PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x')) ∧
      Descends controlQuotient (fun x : Control => x)
        (PaperPhaseBoundary formed phase neighborhood) ∧
      Descends controlQuotient (fun x : Control => x)
        (PaperCriticalAt formed phase neighborhood marginVanishes
          nonUniformResponse residualsStatused))) ∧
    (∀ (left right : Control) (path : List Control),
      FiniteFormedNeighborhoodPath formed neighborhood left right path →
      PhaseTransition phase left right →
        ∃ (before after : List Control) (x y : Control),
          path = before ++ x :: y :: after ∧
            phase x ≠ phase y ∧
              PaperPhaseBoundary formed phase neighborhood x)) ∧
    (∀ γ : unitInterval → Control, Continuous γ →
      (∀ s, formed (γ s)) → phase (γ 0) ≠ phase (γ 1) →
        ∃ s, PaperPhaseBoundary formed phase openTopNeighborhood (γ s))) ∧
    (∀ (left right : Control) (path : List Control),
      FiniteFormedNeighborhoodPath formed neighborhood left right path →
        FiniteFormedPhaseNeighborhoodPath formed phase neighborhood left right path) ∧
    (∀ (left right : Control) (path : List Control),
      FiniteFormedPhaseNeighborhoodPath formed phase neighborhood left right path →
      PhaseTransition phase left right →
        ∃ (before after : List Control) (x y : Control),
          path = before ++ x :: y :: after ∧
            phase x ≠ phase y ∧ PaperPhaseBoundary formed phase neighborhood x) := by
  exact ⟨criticality_phase_boundary_descent_paper_topological_path
    controlQuotient phase formed neighborhood marginVanishes nonUniformResponse
    residualsStatused readout hcontrol,
    fun left right path hpath => finite_formed_neighborhood_path_implies_phase_path
      formed phase neighborhood left right path hpath,
    fun left right path hpath htransition => finite_phase_witness_transition_has_boundary
      formed phase neighborhood left right path hpath htransition⟩

/-- With open-set indices, a boundary is a formed center with globally
nonconstant phase and a phase change in every open neighborhood of the center.
No separation axiom is needed. -/
theorem paper_phase_boundary_open_iff
    {Control Phase : Type} [TopologicalSpace Control]
    (formed : Control → Prop) (phase : Control → Phase) (x : Control) :
    PaperPhaseBoundary formed phase openTopNeighborhood x ↔
      formed x ∧ (∃ y z, phase y ≠ phase z) ∧
        (∀ W : Set Control, IsOpen W → x ∈ W →
          ∃ y ∈ W, phase y ≠ phase x) := by
  classical
  constructor
  · intro hboundary
    have hchange : ∃ y, phase y ≠ phase x := by
      by_contra hnone
      apply hboundary.2
      refine ⟨⟨∅, isOpen_empty⟩, ?_⟩
      intro y _
      exact Classical.byContradiction (fun hne => hnone ⟨y, hne⟩)
    obtain ⟨y, hy⟩ := hchange
    refine ⟨hboundary.1, ⟨y, x, hy⟩, ?_⟩
    intro W hW hxW
    by_contra hnone
    apply hboundary.2
    refine ⟨⟨W, hW⟩, ?_⟩
    intro z hnear
    exact Classical.byContradiction (fun hne => hnone ⟨z, hnear.2 hxW, hne⟩)
  · rintro ⟨hformed, hglobal, hlocal⟩
    refine ⟨hformed, ?_⟩
    rintro ⟨W, hconstant⟩
    by_cases hxW : x ∈ W
    · obtain ⟨y, hyW, hy⟩ := hlocal W W.isOpen hxW
      exact hy (hconstant y ⟨W.isOpen, fun _ => hyW⟩)
    · obtain ⟨y, z, hyz⟩ := hglobal
      have hnear : ∀ w, openTopNeighborhood x W w :=
        fun _ => ⟨W.isOpen, fun hx => False.elim (hxW hx)⟩
      exact hyz ((hconstant y (hnear y)).trans (hconstant z (hnear z)).symm)

/-- The finite-path phase-witness hypothesis is exactly membership in the
closure of the next vertex's phase class, in every topological space. -/
theorem open_phase_step_iff_mem_closure
    {Control Phase : Type} [TopologicalSpace Control]
    (phase : Control → Phase) (x next : Control) :
    (∀ W : TopologicalSpace.Opens Control,
      ∃ y, openTopNeighborhood x W y ∧ phase y = phase next) ↔
      x ∈ closure {y : Control | phase y = phase next} := by
  constructor
  · intro hstep
    apply mem_closure_iff.mpr
    intro W hW hxW
    obtain ⟨y, hnear, hphase⟩ := hstep ⟨W, hW⟩
    exact ⟨y, hnear.2 hxW, hphase⟩
  · intro hclosure W
    by_cases hxW : x ∈ W
    · obtain ⟨y, hyW, hphase⟩ := mem_closure_iff.mp hclosure W W.isOpen hxW
      exact ⟨y, ⟨W.isOpen, fun _ => hyW⟩, hphase⟩
    · exact ⟨next, ⟨W.isOpen, fun hx => False.elim (hxW hx)⟩, rfl⟩

/-- A finite list of formed controls with each vertex in the closure of the
phase class of the next vertex; endpoints and list shape are explicit. -/
inductive FiniteFormedPhaseClosurePath
    {Control Phase : Type} [TopologicalSpace Control]
    (formed : Control → Prop) (phase : Control → Phase) :
    Control → Control → List Control → Prop where
  | stop (x : Control) (hx : formed x) :
      FiniteFormedPhaseClosurePath formed phase x x [x]
  | step (x y z : Control) (tail : List Control)
      (hx : formed x) (hclosure : x ∈ closure {w : Control | phase w = phase y})
      (hrest : FiniteFormedPhaseClosurePath formed phase y z (y :: tail)) :
      FiniteFormedPhaseClosurePath formed phase x z (x :: y :: tail)

/-- Closure-class paths satisfy the topological phase-witness path condition. -/
theorem finite_phase_closure_path_implies_phase_path
    {Control Phase : Type} [TopologicalSpace Control]
    (formed : Control → Prop) (phase : Control → Phase)
    (left right : Control) (path : List Control)
    (hpath : FiniteFormedPhaseClosurePath formed phase left right path) :
    FiniteFormedPhaseNeighborhoodPath formed phase openTopNeighborhood
      left right path := by
  induction hpath with
  | stop x hx => exact .stop x hx
  | step x y z tail hx hclosure _ ih =>
      exact .step x y z tail hx ((open_phase_step_iff_mem_closure phase x y).mpr
        hclosure) ih

/-- A finite formed path through closures of successive phase classes crosses
a boundary at a phase-changing consecutive edge. -/
theorem finite_phase_closure_transition_has_boundary
    {Control Phase : Type} [TopologicalSpace Control]
    (formed : Control → Prop) (phase : Control → Phase)
    (left right : Control) (path : List Control)
    (hpath : FiniteFormedPhaseClosurePath formed phase left right path)
    (htransition : PhaseTransition phase left right) :
    ∃ (before after : List Control) (x y : Control),
      path = before ++ x :: y :: after ∧
        phase x ≠ phase y ∧ PaperPhaseBoundary formed phase openTopNeighborhood x := by
  exact finite_phase_witness_transition_has_boundary formed phase openTopNeighborhood
    left right path (finite_phase_closure_path_implies_phase_path
      formed phase left right path hpath) htransition

/-- The full F44 coverage theorem retains every existing descent and path
clause and adds the topological boundary and closure-class characterizations. -/
theorem criticality_phase_boundary_descent_paper_full
    {Control C Phase Neighborhood Value : Type} [TopologicalSpace Control]
    (controlQuotient : Control → C) (phase : Control → Phase)
    (formed : Control → Prop)
    (neighborhood : Control → Neighborhood → Control → Prop)
    (marginVanishes nonUniformResponse residualsStatused : Control → Prop)
    (readout : Control → Value)
    (hcontrol : Function.Surjective controlQuotient) :
    (((((Descends controlQuotient (fun x : Control => x) readout ↔
      ObstructionEmpty
        (splitPairObstruction controlQuotient (fun x : Control => x) readout)) ∧
    (((∀ x x', controlQuotient x = controlQuotient x' → phase x = phase x') ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (formed x ↔ formed x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (marginVanishes x ↔ marginVanishes x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (nonUniformResponse x ↔ nonUniformResponse x')) ∧
      (∀ x x', controlQuotient x = controlQuotient x' →
        (residualsStatused x ↔ residualsStatused x')) ∧
      (∀ x x' W y, controlQuotient x = controlQuotient x' →
        (neighborhood x W y ↔ neighborhood x' W y))) →
      (∀ x x', controlQuotient x = controlQuotient x' →
        (PaperPhaseBoundary formed phase neighborhood x ↔
          PaperPhaseBoundary formed phase neighborhood x') ∧
        (PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x ↔
          PaperCriticalAt formed phase neighborhood marginVanishes
            nonUniformResponse residualsStatused x')) ∧
      Descends controlQuotient (fun x : Control => x)
        (PaperPhaseBoundary formed phase neighborhood) ∧
      Descends controlQuotient (fun x : Control => x)
        (PaperCriticalAt formed phase neighborhood marginVanishes
          nonUniformResponse residualsStatused))) ∧
    (∀ (left right : Control) (path : List Control),
      FiniteFormedNeighborhoodPath formed neighborhood left right path →
      PhaseTransition phase left right →
        ∃ (before after : List Control) (x y : Control),
          path = before ++ x :: y :: after ∧
            phase x ≠ phase y ∧
              PaperPhaseBoundary formed phase neighborhood x)) ∧
    (∀ γ : unitInterval → Control, Continuous γ →
      (∀ s, formed (γ s)) → phase (γ 0) ≠ phase (γ 1) →
        ∃ s, PaperPhaseBoundary formed phase openTopNeighborhood (γ s))) ∧
    (∀ (left right : Control) (path : List Control),
      FiniteFormedNeighborhoodPath formed neighborhood left right path →
        FiniteFormedPhaseNeighborhoodPath formed phase neighborhood left right path) ∧
    (∀ (left right : Control) (path : List Control),
      FiniteFormedPhaseNeighborhoodPath formed phase neighborhood left right path →
      PhaseTransition phase left right →
        ∃ (before after : List Control) (x y : Control),
          path = before ++ x :: y :: after ∧
            phase x ≠ phase y ∧ PaperPhaseBoundary formed phase neighborhood x)) ∧
    (∀ x : Control,
      PaperPhaseBoundary formed phase openTopNeighborhood x ↔
        formed x ∧ (∃ y z, phase y ≠ phase z) ∧
          (∀ W : Set Control, IsOpen W → x ∈ W →
            ∃ y ∈ W, phase y ≠ phase x)) ∧
    (∀ x next : Control,
      (∀ W : TopologicalSpace.Opens Control,
        ∃ y, openTopNeighborhood x W y ∧ phase y = phase next) ↔
        x ∈ closure {y : Control | phase y = phase next}) ∧
    (∀ (left right : Control) (path : List Control),
      FiniteFormedPhaseClosurePath formed phase left right path →
      PhaseTransition phase left right →
        ∃ (before after : List Control) (x y : Control),
          path = before ++ x :: y :: after ∧
            phase x ≠ phase y ∧ PaperPhaseBoundary formed phase openTopNeighborhood x) := by
  exact ⟨criticality_phase_boundary_descent_paper_topological_path_strengthened
    controlQuotient phase formed neighborhood marginVanishes nonUniformResponse
    residualsStatused readout hcontrol,
    paper_phase_boundary_open_iff formed phase,
    open_phase_step_iff_mem_closure phase,
    fun left right path hpath htransition => finite_phase_closure_transition_has_boundary
      formed phase left right path hpath htransition⟩

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Criticality
