import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F50 Vacuum / Background Selection.

Background is modeled as a readout on lawful closure moduli. The normal form is
the law/state split for ambient structure: either the readout is invariant over
all declared moduli, or the base permits background moduli and any definite
background is selected state data. A vacuum is the same discipline applied to a
declared extremal/stability/null criterion on the background moduli.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.VacuumBackgroundSelection

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- A raw closure-level background readout is well defined on moduli when it
descends through the declared closure-moduli quotient. -/
def BackgroundReadoutDescends {Closure Moduli Background : Type}
    (moduliQuotient : Closure → Moduli) (background : Closure → Background) :
    Prop :=
  Descends moduliQuotient (fun closure : Closure => closure) background

/-- Obstruction to a raw background readout descending to closure moduli. -/
def BackgroundReadoutObstruction {Closure Moduli Background : Type}
    (moduliQuotient : Closure → Moduli) (background : Closure → Background) :
    (Closure × Closure) → Prop :=
  splitPairObstruction moduliQuotient (fun closure : Closure => closure) background

/-- No descent obstruction for the raw background readout. -/
def BackgroundReadoutObstructionEmpty {Closure Moduli Background : Type}
    (moduliQuotient : Closure → Moduli) (background : Closure → Background) :
    Prop :=
  ObstructionEmpty (BackgroundReadoutObstruction moduliQuotient background)

/-- Background variation obstruction on the already-declared moduli quotient:
two lawful moduli carry different background values. -/
def BackgroundVariationObstruction {Moduli Background : Type}
    (background : Moduli → Background) : (Moduli × Moduli) → Prop :=
  fun pair => background pair.1 ≠ background pair.2

/-- No background variation remains over the lawful closure moduli. -/
def BackgroundVariationObstructionEmpty {Moduli Background : Type}
    (background : Moduli → Background) : Prop :=
  ObstructionEmpty (BackgroundVariationObstruction background)

/-- The background is necessary relative to the base when every lawful closure
modulus has the same background value. -/
def NecessaryBackground {Moduli Background : Type}
    (background : Moduli → Background) : Prop :=
  ∀ m m', background m = background m'

/-- The base admits background moduli when lawful closure moduli can carry
distinct background values. -/
def BackgroundModuli {Moduli Background : Type}
    (background : Moduli → Background) : Prop :=
  ∃ m m', background m ≠ background m'

/-- The selected background value of a selected modulus. -/
def selectedBackground {Moduli Background : Type} (background : Moduli → Background)
    (selectedModulus : Moduli) : Background :=
  background selectedModulus

/-- A selected background claim supplies selector status for a selected
modulus. The value itself is `selectedBackground background selectedModulus`. -/
def SelectedBackground (selectorStatus : Prop) : Prop :=
  selectorStatus

/-- A background-dependent target varies across at least one pair of background
moduli that also changes the target. -/
def BackgroundDependentTarget {Moduli Background Target : Type}
    (background : Moduli → Background) (target : Moduli → Target) : Prop :=
  ∃ m m', background m ≠ background m' ∧ target m ≠ target m'

/-- Full background independence for a declared target family: the target is
constant over the background-moduli space. -/
def BackgroundIndependentForTarget {Moduli Target : Type}
    (target : Moduli → Target) : Prop :=
  ∀ m m', target m = target m'

/-- Obstruction to target-level background independence. -/
def BackgroundIndependenceObstruction {Moduli Target : Type}
    (target : Moduli → Target) : (Moduli × Moduli) → Prop :=
  fun pair => target pair.1 ≠ target pair.2

/-- No target-level background-independence obstruction is present. -/
def BackgroundIndependenceObstructionEmpty {Moduli Target : Type}
    (target : Moduli → Target) : Prop :=
  ObstructionEmpty (BackgroundIndependenceObstruction target)

/-- The declared vacuum subset cut out by a stability/extremal/null criterion. -/
def VacuumSet {Moduli : Type} (vacuumCriterion : Moduli → Prop) : Moduli → Prop :=
  fun m => vacuumCriterion m

/-- No lawful modulus satisfies the declared vacuum criterion. -/
def VacuumAbsent {Moduli : Type} (vacuumCriterion : Moduli → Prop) : Prop :=
  ∀ m, ¬ vacuumCriterion m

/-- A unique vacuum is a criterion-satisfying modulus that all other vacuum
candidates equal. -/
def UniqueVacuum {Moduli : Type} (vacuumCriterion : Moduli → Prop) : Prop :=
  ∃ v, vacuumCriterion v ∧ ∀ v', vacuumCriterion v' → v' = v

/-- Vacuum moduli/degeneracy: at least two distinct lawful moduli satisfy the
vacuum criterion. -/
def VacuumModuli {Moduli : Type} (vacuumCriterion : Moduli → Prop) : Prop :=
  ∃ v v', vacuumCriterion v ∧ vacuumCriterion v' ∧ v ≠ v'

/-- A selected vacuum is selector status plus membership in the declared vacuum
subset. -/
def SelectedVacuum {Moduli : Type} (vacuumCriterion : Moduli → Prop)
    (selectorStatus : Prop) (selectedModulus : Moduli) : Prop :=
  selectorStatus ∧ VacuumSet vacuumCriterion selectedModulus

/-- A selected background from genuine background moduli is a strict selected
modulus extension unless an additional equivalence identifies the alternatives. -/
def StrictSelectedBackgroundExtension {Moduli Background : Type}
    (background : Moduli → Background) (selectorStatus : Prop) : Prop :=
  BackgroundModuli background ∧ selectorStatus

/-- Source status vocabulary for F50 background and vacuum claims. -/
inductive BackgroundStatus where
  | closureObstructed
  | uniqueClosure
  | necessaryBackground
  | backgroundModuli
  | selectedBackground
  | recordedBackground
  | hiddenBackground
  | probabilisticBackground
  | boundarySelectedBackground
  | initialBackground
  | emergentBackground
  | dynamicBackground
  | backgroundTransition
  | vacuumAbsent
  | uniqueVacuum
  | vacuumModuli
  | degenerateVacua
  | metastableVacuum
  | localVacuum
  | backgroundIndependentForTarget
  | backgroundDependent
  | backgroundOverread
  | vacuumSelectionMissing
  | vacuumEntropy
  | vacuumFineTuning
  | backgroundTransport
  | backgroundTransportFailure
  | backgroundPhaseTransition
  | backgroundCommonSource
  | hiddenBackgroundSource
  | emergentCompositeBackground
  | scaleEmergentBackground
  | pathDependentBackground
  | singularBackgroundSelection
  | backgroundComplementarity
  | backgroundSymmetryBreaking
  | backgroundAnomaly
  | backgroundRoleMismatch
  | presentationBackgroundArtifact
deriving DecidableEq

/-- Meaning assignment for the F50 status vocabulary. -/
def BackgroundStatusHolds (closureObstructed uniqueClosure necessary moduli selected
    recorded hidden probabilistic boundarySelected initial emergent dynamic transition
    vacuumAbsent uniqueVacuum vacuumModuli degenerate metastable localVacuum
    independentForTarget dependent overread selectionMissing entropy fineTuning transport
    transportFailure phaseTransition commonSource hiddenSource compositeEmergent
    scaleEmergent pathDependent singular complementarity symmetryBreaking anomaly
    roleMismatch presentationArtifact : Prop) : BackgroundStatus → Prop
  | BackgroundStatus.closureObstructed => closureObstructed
  | BackgroundStatus.uniqueClosure => uniqueClosure
  | BackgroundStatus.necessaryBackground => necessary
  | BackgroundStatus.backgroundModuli => moduli
  | BackgroundStatus.selectedBackground => selected
  | BackgroundStatus.recordedBackground => recorded
  | BackgroundStatus.hiddenBackground => hidden
  | BackgroundStatus.probabilisticBackground => probabilistic
  | BackgroundStatus.boundarySelectedBackground => boundarySelected
  | BackgroundStatus.initialBackground => initial
  | BackgroundStatus.emergentBackground => emergent
  | BackgroundStatus.dynamicBackground => dynamic
  | BackgroundStatus.backgroundTransition => transition
  | BackgroundStatus.vacuumAbsent => vacuumAbsent
  | BackgroundStatus.uniqueVacuum => uniqueVacuum
  | BackgroundStatus.vacuumModuli => vacuumModuli
  | BackgroundStatus.degenerateVacua => degenerate
  | BackgroundStatus.metastableVacuum => metastable
  | BackgroundStatus.localVacuum => localVacuum
  | BackgroundStatus.backgroundIndependentForTarget => independentForTarget
  | BackgroundStatus.backgroundDependent => dependent
  | BackgroundStatus.backgroundOverread => overread
  | BackgroundStatus.vacuumSelectionMissing => selectionMissing
  | BackgroundStatus.vacuumEntropy => entropy
  | BackgroundStatus.vacuumFineTuning => fineTuning
  | BackgroundStatus.backgroundTransport => transport
  | BackgroundStatus.backgroundTransportFailure => transportFailure
  | BackgroundStatus.backgroundPhaseTransition => phaseTransition
  | BackgroundStatus.backgroundCommonSource => commonSource
  | BackgroundStatus.hiddenBackgroundSource => hiddenSource
  | BackgroundStatus.emergentCompositeBackground => compositeEmergent
  | BackgroundStatus.scaleEmergentBackground => scaleEmergent
  | BackgroundStatus.pathDependentBackground => pathDependent
  | BackgroundStatus.singularBackgroundSelection => singular
  | BackgroundStatus.backgroundComplementarity => complementarity
  | BackgroundStatus.backgroundSymmetryBreaking => symmetryBreaking
  | BackgroundStatus.backgroundAnomaly => anomaly
  | BackgroundStatus.backgroundRoleMismatch => roleMismatch
  | BackgroundStatus.presentationBackgroundArtifact => presentationArtifact

/-- A raw background readout descends to moduli exactly when the split-pair
descent obstruction is empty. -/
theorem background_readout_descends_iff_no_obstruction
    {Closure Moduli Background : Type} (moduliQuotient : Closure → Moduli)
    (background : Closure → Background)
    (hmoduli : Function.Surjective moduliQuotient) :
    BackgroundReadoutDescends moduliQuotient background ↔
      BackgroundReadoutObstructionEmpty moduliQuotient background :=
  descent_repair_normal_form moduliQuotient (fun closure : Closure => closure)
    background hmoduli

/-- F50's fiber-constancy criterion for the raw background to factor through
the surjective closure-moduli quotient. -/
theorem background_readout_descends_iff_fiber_constant
    {Closure Moduli Background : Type} (moduliQuotient : Closure → Moduli)
    (background : Closure → Background)
    (hmoduli : Function.Surjective moduliQuotient) :
    BackgroundReadoutDescends moduliQuotient background ↔
      ∀ x y, moduliQuotient x = moduliQuotient y →
        background x = background y := by
  constructor
  · rintro ⟨b, hb⟩ x y hxy
    calc
      background x = b (moduliQuotient x) := (congrFun hb x).symm
      _ = b (moduliQuotient y) := congrArg b hxy
      _ = background y := congrFun hb y
  · intro hconstant
    apply (background_readout_descends_iff_no_obstruction moduliQuotient
      background hmoduli).mpr
    rintro ⟨x, y⟩ ⟨hxy, hne⟩
    exact hne (hconstant x y hxy)

/-- Necessary background iff the background-variation obstruction is empty. -/
theorem necessary_background_iff_no_variation {Moduli Background : Type}
    (background : Moduli → Background) :
    NecessaryBackground background ↔
      BackgroundVariationObstructionEmpty background := by
  constructor
  · intro hnecessary pair hpair
    exact hpair (hnecessary pair.1 pair.2)
  · intro hempty m m'
    exact Classical.byContradiction (fun hneq =>
      False.elim (hempty (m, m') hneq))

/-- Background moduli are exactly nonempty background-variation obstruction. -/
theorem background_moduli_iff_obstruction_witness {Moduli Background : Type}
    (background : Moduli → Background) :
    BackgroundModuli background ↔
      ∃ pair, BackgroundVariationObstruction background pair := by
  constructor
  · intro h
    rcases h with ⟨m, m', hneq⟩
    exact ⟨(m, m'), hneq⟩
  · intro h
    rcases h with ⟨pair, hpair⟩
    exact ⟨pair.1, pair.2, hpair⟩

/-- Every background readout on declared moduli is either necessary or varies
over background moduli. -/
theorem necessary_background_or_moduli {Moduli Background : Type}
    (background : Moduli → Background) :
    NecessaryBackground background ∨ BackgroundModuli background := by
  classical
  by_cases hnecessary : NecessaryBackground background
  · exact Or.inl hnecessary
  · have hsome : ∃ m, ¬ ∀ m', background m = background m' :=
      Classical.not_forall.mp hnecessary
    rcases hsome with ⟨m, hm⟩
    have hsome' : ∃ m', background m ≠ background m' :=
      Classical.not_forall.mp hm
    rcases hsome' with ⟨m', hneq⟩
    exact Or.inr ⟨m, m', hneq⟩

/-- The necessary-background and background-moduli cases are disjoint. -/
theorem necessary_background_not_moduli {Moduli Background : Type}
    (background : Moduli → Background) :
    ¬ (NecessaryBackground background ∧ BackgroundModuli background) := by
  intro h
  rcases h with ⟨hnecessary, hmoduli⟩
  rcases hmoduli with ⟨m, m', hneq⟩
  exact hneq (hnecessary m m')

/-- Selected-background evaluation is just evaluation of the background readout
at the selected modulus. -/
theorem selected_background_value {Moduli Background : Type}
    (background : Moduli → Background) (selectedModulus : Moduli) :
    selectedBackground background selectedModulus = background selectedModulus := by
  rfl

/-- The declared vacuum subset is exactly the declared criterion. -/
theorem vacuum_set_iff_criterion {Moduli : Type}
    (vacuumCriterion : Moduli → Prop) (m : Moduli) :
    VacuumSet vacuumCriterion m ↔ vacuumCriterion m := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Unique vacuum is the ordinary exists-unique form for the declared vacuum
criterion. -/
theorem unique_vacuum_iff_exists_unique {Moduli : Type}
    (vacuumCriterion : Moduli → Prop) :
    UniqueVacuum vacuumCriterion ↔
      ∃ v, vacuumCriterion v ∧ ∀ v', vacuumCriterion v' → v' = v := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Vacuum moduli contradict uniqueness. -/
theorem unique_vacuum_not_moduli {Moduli : Type}
    (vacuumCriterion : Moduli → Prop) :
    ¬ (UniqueVacuum vacuumCriterion ∧ VacuumModuli vacuumCriterion) := by
  intro h
  rcases h with ⟨hunique, hmoduli⟩
  rcases hunique with ⟨v, hv, huniq⟩
  rcases hmoduli with ⟨v₁, v₂, hv₁, hv₂, hneq⟩
  have h₁ : v₁ = v := huniq v₁ hv₁
  have h₂ : v₂ = v := huniq v₂ hv₂
  exact hneq (h₁.trans h₂.symm)

/-- A vacuum criterion is absent, unique, or degenerate. This is the Lean form
of the source's empty/singleton/multiple vacuum classification. -/
theorem vacuum_absent_or_unique_or_moduli {Moduli : Type}
    (vacuumCriterion : Moduli → Prop) :
    VacuumAbsent vacuumCriterion ∨
      UniqueVacuum vacuumCriterion ∨ VacuumModuli vacuumCriterion := by
  classical
  by_cases habsent : VacuumAbsent vacuumCriterion
  · exact Or.inl habsent
  · have hexists : ∃ v, vacuumCriterion v :=
      Classical.byContradiction (fun hnone =>
        habsent (fun v hv => hnone ⟨v, hv⟩))
    rcases hexists with ⟨v, hv⟩
    by_cases hunique : UniqueVacuum vacuumCriterion
    · exact Or.inr (Or.inl hunique)
    · have hnot_all : ¬ ∀ v', vacuumCriterion v' → v' = v := by
        intro huniq
        exact hunique ⟨v, hv, huniq⟩
      have hwitness : ∃ v', ¬ (vacuumCriterion v' → v' = v) :=
        Classical.not_forall.mp hnot_all
      rcases hwitness with ⟨v', hv'not⟩
      have hv'and : vacuumCriterion v' ∧ ¬ v' = v :=
        Classical.not_imp.mp hv'not
      exact Or.inr (Or.inr ⟨v, v', hv, hv'and.1, fun hsame => hv'and.2 hsame.symm⟩)

/-- Background independence for a target family is exactly absence of target
variation over the background-moduli space. -/
theorem background_independent_iff_no_obstruction {Moduli Target : Type}
    (target : Moduli → Target) :
    BackgroundIndependentForTarget target ↔
      BackgroundIndependenceObstructionEmpty target := by
  constructor
  · intro hind pair hpair
    exact hpair (hind pair.1 pair.2)
  · intro hempty m m'
    exact Classical.byContradiction (fun hneq =>
      False.elim (hempty (m, m') hneq))

/-- Background-dependent targets have a concrete pair of background and target
variation. -/
theorem background_dependent_target_iff {Moduli Background Target : Type}
    (background : Moduli → Background) (target : Moduli → Target) :
    BackgroundDependentTarget background target ↔
      ∃ m m', background m ≠ background m' ∧ target m ≠ target m' := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
Vacuum / Background Selection Normal Form. A well-defined background readout
first descends to closure moduli; on those moduli it is either necessary
invariant or background-modulus-dependent. A selected background is evaluation
at selected modulus data. A vacuum is the subset cut out by a declared
criterion, classified as absent, unique, or moduli/degenerate, and background
independence for targets means target invariance over the declared moduli.
-/
theorem vacuum_background_selection {Closure Moduli Background Target : Type}
    (moduliQuotient : Closure → Moduli) (rawBackground : Closure → Background)
    (background : Moduli → Background) (target : Moduli → Target)
    (vacuumCriterion : Moduli → Prop) (selectedModulus : Moduli)
    (hmoduli : Function.Surjective moduliQuotient) :
    (BackgroundReadoutDescends moduliQuotient rawBackground ↔
      BackgroundReadoutObstructionEmpty moduliQuotient rawBackground) ∧
      (NecessaryBackground background ↔
        BackgroundVariationObstructionEmpty background) ∧
        (BackgroundModuli background ↔
          ∃ pair, BackgroundVariationObstruction background pair) ∧
          (NecessaryBackground background ∨ BackgroundModuli background) ∧
            ¬ (NecessaryBackground background ∧ BackgroundModuli background) ∧
            selectedBackground background selectedModulus = background selectedModulus ∧
              (VacuumSet vacuumCriterion selectedModulus ↔
                vacuumCriterion selectedModulus) ∧
                (VacuumAbsent vacuumCriterion ∨
                  UniqueVacuum vacuumCriterion ∨ VacuumModuli vacuumCriterion) ∧
                  ¬ (UniqueVacuum vacuumCriterion ∧ VacuumModuli vacuumCriterion) ∧
                    (BackgroundIndependentForTarget target ↔
                      BackgroundIndependenceObstructionEmpty target) := by
  refine ⟨background_readout_descends_iff_no_obstruction moduliQuotient
    rawBackground hmoduli, ?_⟩
  refine ⟨necessary_background_iff_no_variation background, ?_⟩
  refine ⟨background_moduli_iff_obstruction_witness background, ?_⟩
  refine ⟨necessary_background_or_moduli background, ?_⟩
  refine ⟨necessary_background_not_moduli background, ?_⟩
  refine ⟨selected_background_value background selectedModulus, ?_⟩
  refine ⟨vacuum_set_iff_criterion vacuumCriterion selectedModulus, ?_⟩
  refine ⟨vacuum_absent_or_unique_or_moduli vacuumCriterion, ?_⟩
  refine ⟨unique_vacuum_not_moduli vacuumCriterion, ?_⟩
  exact background_independent_iff_no_obstruction target

/-- The paper-facing vacuum predicate: the selected modulus is the unique
member of the declared vacuum set, and its target is formed. -/
def PaperVacuum {Moduli Target : Type} (vacuumCriterion : Moduli → Prop)
    (formedTarget : Target → Prop) (target : Moduli → Target)
    (selectedModulus : Moduli) : Prop :=
  VacuumSet vacuumCriterion selectedModulus ∧
    (∀ m, VacuumSet vacuumCriterion m → m = selectedModulus) ∧
    formedTarget (target selectedModulus)

/-- A paper-facing vacuum is exactly a singleton vacuum set with a formed
target at its sole modulus. -/
theorem paper_vacuum_iff_singleton_formed {Moduli Target : Type}
    (vacuumCriterion : Moduli → Prop) (formedTarget : Target → Prop)
    (target : Moduli → Target) (selectedModulus : Moduli) :
    PaperVacuum vacuumCriterion formedTarget target selectedModulus ↔
      VacuumSet vacuumCriterion = (fun m => m = selectedModulus) ∧
        formedTarget (target selectedModulus) := by
  constructor
  · intro ⟨hv, hunique, hformed⟩
    constructor
    · funext m
      apply propext
      constructor
      · exact hunique m
      · intro hm
        cases hm
        exact hv
    · exact hformed
  · intro ⟨hset, hformed⟩
    have hv : VacuumSet vacuumCriterion selectedModulus := by
      rw [hset]
    refine ⟨hv, ?_, hformed⟩
    intro m hm
    simpa only [hset] using hm

/-- The paper's F50 normal form, including the singleton and formed-target
characterization of a selected vacuum. -/
theorem paper_vacuum_background_selection
    {Closure Moduli Background Target : Type}
    (moduliQuotient : Closure → Moduli) (rawBackground : Closure → Background)
    (background : Moduli → Background) (target : Moduli → Target)
    (vacuumCriterion : Moduli → Prop) (formedTarget : Target → Prop)
    (selectedModulus : Moduli) (hmoduli : Function.Surjective moduliQuotient) :
    ((BackgroundReadoutDescends moduliQuotient rawBackground ↔
      BackgroundReadoutObstructionEmpty moduliQuotient rawBackground) ∧
      (NecessaryBackground background ↔
        BackgroundVariationObstructionEmpty background) ∧
        (BackgroundModuli background ↔
          ∃ pair, BackgroundVariationObstruction background pair) ∧
        (NecessaryBackground background ∨ BackgroundModuli background) ∧
          ¬ (NecessaryBackground background ∧ BackgroundModuli background) ∧
          selectedBackground background selectedModulus = background selectedModulus ∧
            (VacuumSet vacuumCriterion selectedModulus ↔
              vacuumCriterion selectedModulus) ∧
              (VacuumAbsent vacuumCriterion ∨
                UniqueVacuum vacuumCriterion ∨ VacuumModuli vacuumCriterion) ∧
                ¬ (UniqueVacuum vacuumCriterion ∧ VacuumModuli vacuumCriterion) ∧
                  (BackgroundIndependentForTarget target ↔
                    BackgroundIndependenceObstructionEmpty target)) ∧
    (PaperVacuum vacuumCriterion formedTarget target selectedModulus ↔
      VacuumSet vacuumCriterion = (fun m => m = selectedModulus) ∧
        formedTarget (target selectedModulus)) := by
  exact ⟨vacuum_background_selection moduliQuotient rawBackground background
    target vacuumCriterion selectedModulus hmoduli,
    paper_vacuum_iff_singleton_formed vacuumCriterion formedTarget target
      selectedModulus⟩

/-- Under the declared descent equation, necessary background is exactly
constancy of the raw background on the closure space. -/
theorem necessary_background_iff_raw_constant
    {Closure Moduli Background : Type}
    (mu : Closure → Moduli) (b₀ : Closure → Background)
    (b : Moduli → Background) (hmu : Function.Surjective mu)
    (hdesc : b ∘ mu = b₀) :
    NecessaryBackground b ↔ ∀ x x', b₀ x = b₀ x' := by
  constructor
  · intro h x x'
    have hx := congrFun hdesc x
    have hx' := congrFun hdesc x'
    exact hx.symm.trans ((h (mu x) (mu x')).trans hx')
  · intro h m m'
    obtain ⟨x, rfl⟩ := hmu m
    obtain ⟨x', rfl⟩ := hmu m'
    have hx := congrFun hdesc x
    have hx' := congrFun hdesc x'
    exact hx.trans ((h x x').trans hx'.symm)

/-- F50 including constancy of the raw background under its descent equation. -/
theorem paper_vacuum_background_selection_with_raw_constancy
    {Closure Moduli Background Target : Type}
    (moduliQuotient : Closure → Moduli) (rawBackground : Closure → Background)
    (background : Moduli → Background) (target : Moduli → Target)
    (vacuumCriterion : Moduli → Prop) (formedTarget : Target → Prop)
    (selectedModulus : Moduli) (hmoduli : Function.Surjective moduliQuotient)
    (hdesc : background ∘ moduliQuotient = rawBackground) :
    (((BackgroundReadoutDescends moduliQuotient rawBackground ↔
      BackgroundReadoutObstructionEmpty moduliQuotient rawBackground) ∧
      (NecessaryBackground background ↔
        BackgroundVariationObstructionEmpty background) ∧
        (BackgroundModuli background ↔
          ∃ pair, BackgroundVariationObstruction background pair) ∧
        (NecessaryBackground background ∨ BackgroundModuli background) ∧
          ¬ (NecessaryBackground background ∧ BackgroundModuli background) ∧
          selectedBackground background selectedModulus = background selectedModulus ∧
            (VacuumSet vacuumCriterion selectedModulus ↔
              vacuumCriterion selectedModulus) ∧
              (VacuumAbsent vacuumCriterion ∨
                UniqueVacuum vacuumCriterion ∨ VacuumModuli vacuumCriterion) ∧
                ¬ (UniqueVacuum vacuumCriterion ∧ VacuumModuli vacuumCriterion) ∧
                  (BackgroundIndependentForTarget target ↔
                    BackgroundIndependenceObstructionEmpty target)) ∧
    (PaperVacuum vacuumCriterion formedTarget target selectedModulus ↔
      VacuumSet vacuumCriterion = (fun m => m = selectedModulus) ∧
        formedTarget (target selectedModulus))) ∧
    (NecessaryBackground background ↔
      ∀ x x', rawBackground x = rawBackground x') := by
  exact ⟨paper_vacuum_background_selection moduliQuotient rawBackground background
      target vacuumCriterion formedTarget selectedModulus hmoduli,
    necessary_background_iff_raw_constant moduliQuotient rawBackground background
      hmoduli hdesc⟩

/-- F50 for an arbitrary declared moduli background; its raw-constancy law
uses the descent equation only in the final conditional clause. -/
theorem paper_vacuum_background_selection_conditional_raw_constancy
    {Closure Moduli Background Target : Type}
    (moduliQuotient : Closure → Moduli) (rawBackground : Closure → Background)
    (background : Moduli → Background) (target : Moduli → Target)
    (vacuumCriterion : Moduli → Prop) (formedTarget : Target → Prop)
    (selectedModulus : Moduli) (hmoduli : Function.Surjective moduliQuotient) :
    ((∀ x y, moduliQuotient x = moduliQuotient y →
        rawBackground x = rawBackground y) ↔
      ∃ beta : Moduli → Background,
        beta ∘ moduliQuotient = rawBackground) ∧
    (NecessaryBackground background ↔
      ∀ m m', background m = background m') ∧
    (BackgroundModuli background ↔
      ∃ m m', background m ≠ background m') ∧
    (PaperVacuum vacuumCriterion formedTarget target selectedModulus ↔
      VacuumSet vacuumCriterion = (fun m => m = selectedModulus) ∧
        formedTarget (target selectedModulus)) ∧
    (NecessaryBackground background ∨ BackgroundModuli background) ∧
    ¬ (NecessaryBackground background ∧ BackgroundModuli background) ∧
    (background ∘ moduliQuotient = rawBackground →
      (NecessaryBackground background ↔
        ∀ x y, rawBackground x = rawBackground y)) := by
  refine ⟨?_, (by constructor <;> intro h <;> exact h),
    (by constructor <;> intro h <;> exact h),
    paper_vacuum_iff_singleton_formed vacuumCriterion formedTarget target
      selectedModulus,
    necessary_background_or_moduli background,
    necessary_background_not_moduli background,
    fun hdesc => necessary_background_iff_raw_constant moduliQuotient
      rawBackground background hmoduli hdesc⟩
  exact (background_readout_descends_iff_fiber_constant moduliQuotient
    rawBackground hmoduli).symm

/-- Empty, singleton, and multiple vacuum sets form an exhaustive, disjoint
classification; no finiteness hypothesis is needed. -/
def ExactlyOneVacuumCardinality {Moduli : Type}
    (vacuumCriterion : Moduli → Prop) : Prop :=
  (VacuumAbsent vacuumCriterion ∨ UniqueVacuum vacuumCriterion ∨
    VacuumModuli vacuumCriterion) ∧
  ¬ (VacuumAbsent vacuumCriterion ∧ UniqueVacuum vacuumCriterion) ∧
  ¬ (VacuumAbsent vacuumCriterion ∧ VacuumModuli vacuumCriterion) ∧
  ¬ (UniqueVacuum vacuumCriterion ∧ VacuumModuli vacuumCriterion)

theorem vacuum_cardinality_exactly_one {Moduli : Type}
    (vacuumCriterion : Moduli → Prop) :
    ExactlyOneVacuumCardinality vacuumCriterion := by
  refine ⟨vacuum_absent_or_unique_or_moduli vacuumCriterion, ?_, ?_,
    unique_vacuum_not_moduli vacuumCriterion⟩
  · rintro ⟨ha, ⟨m, hm, _⟩⟩
    exact ha m hm
  · rintro ⟨ha, ⟨m, _, hm, _, _⟩⟩
    exact ha m hm

/-- F50 with the vacuum-set trichotomy, existence characterization, and
uniqueness of a formed singleton vacuum. -/
theorem paper_vacuum_background_selection_cardinality
    {Closure Moduli Background Target : Type}
    (moduliQuotient : Closure → Moduli) (rawBackground : Closure → Background)
    (background : Moduli → Background) (target : Moduli → Target)
    (vacuumCriterion : Moduli → Prop) (formedTarget : Target → Prop)
    (selectedModulus : Moduli) (hmoduli : Function.Surjective moduliQuotient) :
    (((∀ x y, moduliQuotient x = moduliQuotient y →
        rawBackground x = rawBackground y) ↔
      ∃ beta : Moduli → Background,
        beta ∘ moduliQuotient = rawBackground) ∧
    (NecessaryBackground background ↔
      ∀ m m', background m = background m') ∧
    (BackgroundModuli background ↔
      ∃ m m', background m ≠ background m') ∧
    (PaperVacuum vacuumCriterion formedTarget target selectedModulus ↔
      VacuumSet vacuumCriterion = (fun m => m = selectedModulus) ∧
        formedTarget (target selectedModulus)) ∧
    (NecessaryBackground background ∨ BackgroundModuli background) ∧
    ¬ (NecessaryBackground background ∧ BackgroundModuli background) ∧
    (background ∘ moduliQuotient = rawBackground →
      (NecessaryBackground background ↔
        ∀ x y, rawBackground x = rawBackground y))) ∧
    ExactlyOneVacuumCardinality vacuumCriterion ∧
    ((∃ m, PaperVacuum vacuumCriterion formedTarget target m) ↔
      ∃ m, VacuumSet vacuumCriterion = (fun m' => m' = m) ∧
        formedTarget (target m)) ∧
    (∀ m m', PaperVacuum vacuumCriterion formedTarget target m →
      PaperVacuum vacuumCriterion formedTarget target m' → m = m') := by
  refine ⟨paper_vacuum_background_selection_conditional_raw_constancy
    moduliQuotient rawBackground background target vacuumCriterion formedTarget
    selectedModulus hmoduli, vacuum_cardinality_exactly_one vacuumCriterion,
    ?_, ?_⟩
  · constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, (paper_vacuum_iff_singleton_formed
        vacuumCriterion formedTarget target m).mp hm⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, (paper_vacuum_iff_singleton_formed
        vacuumCriterion formedTarget target m).mpr hm⟩
  · intro m m' hm hm'
    exact (hm.2.1 m' hm'.1).symm

/-- A descended background agrees with the vacuum background on its raw fiber.
If background moduli vary, some non-vacuum modulus has a different background.
These conclusions do not require surjectivity of the raw moduli map. -/
theorem vacuum_background_link {Closure Moduli Background Target : Type}
    (mu : Closure → Moduli) (rawBackground : Closure → Background)
    (background : Moduli → Background) (target : Moduli → Target)
    (vacuumCriterion : Moduli → Prop) (formedTarget : Target → Prop)
    (selectedModulus : Moduli)
    (hdesc : background ∘ mu = rawBackground)
    (hvacuum : PaperVacuum vacuumCriterion formedTarget target selectedModulus) :
    (∀ x, mu x = selectedModulus → rawBackground x = background selectedModulus) ∧
    (BackgroundModuli background →
      ∃ m, ¬ VacuumSet vacuumCriterion m ∧
        background m ≠ background selectedModulus) := by
  constructor
  · intro x hx
    exact (congrFun hdesc x).symm.trans (congrArg background hx)
  · intro hmoduli
    classical
    have hdifferent : ∃ m, background m ≠ background selectedModulus := by
      rcases hmoduli with ⟨m, m', hne⟩
      by_cases hm : background m = background selectedModulus
      · refine ⟨m', ?_⟩
        intro hm'
        exact hne (hm.trans hm'.symm)
      · exact ⟨m, hm⟩
    rcases hdifferent with ⟨m, hm⟩
    exact ⟨m, fun hv => hm (congrArg background (hvacuum.2.1 m hv)), hm⟩

/-- Background variation outside a singleton vacuum needs no descent equation;
agreement on its raw fiber uses the descent equation only in the second clause. -/
theorem vacuum_background_link_split {Closure Moduli Background Target : Type}
    (mu : Closure → Moduli) (rawBackground : Closure → Background)
    (background : Moduli → Background) (target : Moduli → Target)
    (vacuumCriterion : Moduli → Prop) (formedTarget : Target → Prop)
    (selectedModulus : Moduli) :
    (PaperVacuum vacuumCriterion formedTarget target selectedModulus →
      BackgroundModuli background →
        ∃ m, ¬ VacuumSet vacuumCriterion m ∧
          background m ≠ background selectedModulus) ∧
    (background ∘ mu = rawBackground →
      PaperVacuum vacuumCriterion formedTarget target selectedModulus →
        ∀ x, mu x = selectedModulus →
          rawBackground x = background selectedModulus) := by
  constructor
  · intro hvacuum hmoduli
    classical
    have hdifferent : ∃ m, background m ≠ background selectedModulus := by
      rcases hmoduli with ⟨m, m', hne⟩
      by_cases hm : background m = background selectedModulus
      · refine ⟨m', ?_⟩
        intro hm'
        exact hne (hm.trans hm'.symm)
      · exact ⟨m, hm⟩
    rcases hdifferent with ⟨m, hm⟩
    exact ⟨m, fun hv => hm (congrArg background (hvacuum.2.1 m hv)), hm⟩
  · intro hdesc _hvacuum x hx
    exact (congrFun hdesc x).symm.trans (congrArg background hx)

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.VacuumBackgroundSelection
