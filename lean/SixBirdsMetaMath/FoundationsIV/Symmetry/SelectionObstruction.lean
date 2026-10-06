import SixBirdsMetaMath.FoundationsIV.Access.NoFreeDistinction
import Mathlib.Logic.IsEmpty.Defs

/-!
F15a Selection Obstruction / Repair Normal Form.

The theorem-grade branch only: exact symmetry cannot select a non-fixed branch
without extra breaking data. The future branch-selection formation law is not
encoded here.
-/

namespace SixBirdsMetaMath.FoundationsIV.Symmetry.SelectionObstruction

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
open SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure
open SixBirdsMetaMath.FoundationsIV.Access.NoFreeDistinction

/-- A point is fixed by every symmetry action. -/
def FixedByAll {G X : Type} (act : G → X → X) (x : X) : Prop :=
  ∀ g : G, act g x = x

/-- The symmetry action on the orbit quotient is trivial. -/
def TrivialOrbitAction {G O : Type} (actO : G → O → O) : Prop :=
  ∀ g : G, ∀ o : O, actO g o = o

/-- A selector is equivariant between the quotient action and branch action. -/
def EquivariantSelector {G O X : Type} (actO : G → O → O)
    (actX : G → X → X) (selector : O → X) : Prop :=
  ∀ g : G, ∀ o : O, selector (actO g o) = actX g (selector o)

/-- A selectedness predicate splits a symmetry orbit. -/
def SelectionSplitPair {X O : Type} (orbit : X → O)
    (selected : X → Bool) : (X × X) → Prop :=
  DistinctionSplitPair orbit selected

/-- Selectedness descends through the symmetry orbit quotient. -/
def SelectednessDescends {X O : Type} (orbit : X → O)
    (selected : X → Bool) : Prop :=
  DefinableFromAccess orbit selected

/-- No selectedness split-pair obstruction is present. -/
def SelectionObstructionEmpty {X O : Type} (orbit : X → O)
    (selected : X → Bool) : Prop :=
  DistinctionObstructionEmpty orbit selected

/-- Selectedness really distinguishes two branches in the same orbit. -/
def HasSelectionSplit {X O : Type} (orbit : X → O)
    (selected : X → Bool) : Prop :=
  HasDistinctionSplit orbit selected

/-- A branch selector with a genuine same-orbit/different-selectedness witness. -/
def SelectsNontrivialOrbit {X O : Type} (orbit : X → O)
    (selected : X → Bool) : Prop :=
  ∃ x y : X, orbit x = orbit y ∧ selected x ≠ selected y

/-- Canonical symmetry-breaking extension. -/
def breakerExtension {X O B : Type} (orbit : X → O) (breaker : X → B) :
    X → O × B :=
  financedRefinement orbit breaker

/-- The breaker record splits a symmetry orbit. -/
def HasBreakerSplit {X O B : Type} (orbit : X → O) (breaker : X → B) :
    Prop :=
  HasDistinctionSplit orbit breaker

/-- Branch-stability obstruction for a package and declared transition. -/
def BranchStabilitySplitPair {X P : Type} (package : X → P) (transition : X → X) :
    (X × X) → Prop :=
  fun pair =>
    package pair.1 = package pair.2 ∧
      package (transition pair.1) ≠ package (transition pair.2)

/-- The branch package is stable under a transition when the transition descends
through the package. -/
def BranchStable {X P : Type} (package : X → P) (transition : X → X) :
    Prop :=
  FactorsThroughQ package (fun x => package (transition x))

/-- No branch-stability split-pair obstruction is present. -/
def BranchStabilityObstructionEmpty {X P : Type} (package : X → P)
    (transition : X → X) : Prop :=
  ObstructionEmpty (BranchStabilitySplitPair package transition)

/-- F15a status vocabulary, excluding the future formation theorem. -/
inductive SelectionObstructionStatus where
  | fixedBranch
  | symmetricOrbitQuotient
  | recordedSymmetryBreaking
  | conditionedSelection
  | symmetricDistribution
  | selectionTie
  | unstableBranchRecord
  | bareChoiceOrGaugeSection
  | selectionOverread
  | symmetryNotFormed
deriving DecidableEq

/-- Meaning of each theorem-grade branch-selection status. -/
def SelectionObstructionStatusHolds (fixed symmetric recorded conditioned
    distribution tie unstable bareChoice overread notFormed : Prop) :
    SelectionObstructionStatus → Prop
  | SelectionObstructionStatus.fixedBranch => fixed
  | SelectionObstructionStatus.symmetricOrbitQuotient => symmetric
  | SelectionObstructionStatus.recordedSymmetryBreaking => recorded
  | SelectionObstructionStatus.conditionedSelection => conditioned
  | SelectionObstructionStatus.symmetricDistribution => distribution
  | SelectionObstructionStatus.selectionTie => tie
  | SelectionObstructionStatus.unstableBranchRecord => unstable
  | SelectionObstructionStatus.bareChoiceOrGaugeSection => bareChoice
  | SelectionObstructionStatus.selectionOverread => overread
  | SelectionObstructionStatus.symmetryNotFormed => notFormed

/-- An equivariant selector over a trivial orbit action selects only fixed
branches. -/
theorem invariant_selector_fixed {G O X : Type} (actO : G → O → O)
    (actX : G → X → X) (selector : O → X) :
    EquivariantSelector actO actX selector →
      TrivialOrbitAction actO →
        ∀ o : O, FixedByAll actX (selector o) := by
  intro hequiv htrivial o g
  calc
    actX g (selector o) = selector (actO g o) := (hequiv g o).symm
    _ = selector o := by rw [htrivial g o]

/-- A non-fixed branch contradicts invariant selection from symmetric data. -/
theorem no_invariant_selector_on_nonfixed {G O X : Type} (actO : G → O → O)
    (actX : G → X → X) (selector : O → X) (o : O) :
    EquivariantSelector actO actX selector →
      TrivialOrbitAction actO →
        (∃ g : G, actX g (selector o) ≠ selector o) → False := by
  intro hequiv htrivial hnonfixed
  rcases hnonfixed with ⟨g, hnotFixed⟩
  exact hnotFixed (invariant_selector_fixed actO actX selector hequiv htrivial o g)

/-- Selectedness descends through the orbit quotient exactly when the selection
split-pair obstruction is empty. -/
theorem selectedness_descends_iff_no_split {X O : Type} (orbit : X → O)
    (selected : X → Bool) (horbit : Function.Surjective orbit) :
    SelectednessDescends orbit selected ↔
      SelectionObstructionEmpty orbit selected :=
  distinction_definable_iff_no_split orbit selected horbit

/-- A selectedness split is equivalent to non-empty obstruction. -/
theorem has_selection_split_iff_not_empty {X O : Type} (orbit : X → O)
    (selected : X → Bool) :
    HasSelectionSplit orbit selected ↔
      ¬ SelectionObstructionEmpty orbit selected :=
  has_distinction_split_iff_not_empty orbit selected

/-- A true same-orbit/different-selectedness witness is exactly a selection
split. -/
theorem selects_nontrivial_orbit_iff_split {X O : Type} (orbit : X → O)
    (selected : X → Bool) :
    SelectsNontrivialOrbit orbit selected ↔ HasSelectionSplit orbit selected := by
  rfl

/-- The breaker extension retains the symmetric orbit quotient. -/
theorem breaker_extension_retains_orbit {X O B : Type} (orbit : X → O)
    (breaker : X → B) :
    RetainsAccess orbit (breakerExtension orbit breaker) :=
  financed_refinement_retains_access orbit breaker

/-- The breaker extension carries the breaker record. -/
theorem breaker_extension_carries_breaker {X O B : Type} (orbit : X → O)
    (breaker : X → B) :
    CarriesDistinction (breakerExtension orbit breaker) breaker :=
  financed_refinement_carries_distinction orbit breaker

/-- A breaker that splits an orbit yields a strict retentive extension. -/
theorem breaker_extension_strict_of_split {X O B : Type} (orbit : X → O)
    (breaker : X → B) :
    HasBreakerSplit orbit breaker →
      StrictAccessExtension orbit (breakerExtension orbit breaker) :=
  financed_refinement_strict_of_split orbit breaker

/-- Any package retaining the orbit quotient and carrying the breaker factors
through the canonical breaker extension. -/
theorem breaker_extension_minimal {X O B P : Type} (orbit : X → O)
    (breaker : X → B) (package : X → P)
    (hretains : RetainsAccess orbit package)
    (hcarries : CarriesDistinction package breaker) :
    FactorsThroughQ package (breakerExtension orbit breaker) :=
  financed_refinement_minimal orbit breaker package hretains hcarries

/-- Branch stability is equivalent to absence of the branch-stability
split-pair obstruction. -/
theorem branch_stable_iff_no_obstruction {X P : Type} (package : X → P)
    (transition : X → X) (hpackage : Function.Surjective package) :
    BranchStable package transition ↔
      BranchStabilityObstructionEmpty package transition := by
  constructor
  · intro hstable pair hsplit
    rcases pair with ⟨x, y⟩
    rcases hstable with ⟨transitionBar, hcomm⟩
    have hx : transitionBar (package x) = package (transition x) :=
      congrFun hcomm x
    have hy : transitionBar (package y) = package (transition y) :=
      congrFun hcomm y
    exact hsplit.2 (by
      calc
        package (transition x) = transitionBar (package x) := hx.symm
        _ = transitionBar (package y) := by rw [hsplit.1]
        _ = package (transition y) := hy)
  · intro hempty
    have hclosed : PackageClosed package (fun x => package (transition x)) :=
      (sufficiency_closure package (fun x => package (transition x)) hpackage).2.1.2
        hempty
    exact (sufficiency_closure package (fun x => package (transition x)) hpackage).1.1
      hclosed

/--
Selection Obstruction / Repair Normal Form. Invariant selectors over a trivial
orbit action select only fixed branches; selectedness descends to the symmetry
quotient iff its split-pair obstruction is empty; nontrivial selectedness cannot
be claimed at the unchanged quotient; and the canonical breaker extension
`(p, breaker)` retains the orbit quotient, carries the breaker, is strict when
the breaker splits an orbit, and is minimal among packages doing both.
-/
theorem selection_obstruction {G X O B : Type} (actO : G → O → O)
    (actX : G → X → X) (orbit : X → O) (selected : X → Bool)
    (breaker : X → B) (horbit : Function.Surjective orbit)
    (selector : O → X) :
    (EquivariantSelector actO actX selector →
      TrivialOrbitAction actO →
        ∀ o : O, FixedByAll actX (selector o)) ∧
      (∀ o : O,
        EquivariantSelector actO actX selector →
          TrivialOrbitAction actO →
            (∃ g : G, actX g (selector o) ≠ selector o) → False) ∧
        (SelectednessDescends orbit selected ↔
          SelectionObstructionEmpty orbit selected) ∧
          (HasSelectionSplit orbit selected ↔
            ¬ SelectionObstructionEmpty orbit selected) ∧
            (SelectsNontrivialOrbit orbit selected ↔
              HasSelectionSplit orbit selected) ∧
              RetainsAccess orbit (breakerExtension orbit breaker) ∧
                CarriesDistinction (breakerExtension orbit breaker) breaker ∧
                  (HasBreakerSplit orbit breaker →
                    StrictAccessExtension orbit (breakerExtension orbit breaker)) ∧
                    (∀ {P : Type} (package : X → P),
                      RetainsAccess orbit package →
                        CarriesDistinction package breaker →
                          FactorsThroughQ package (breakerExtension orbit breaker)) ∧
                      (∀ {P : Type} (package : X → P) (transition : X → X),
                        Function.Surjective package →
                          (BranchStable package transition ↔
                            BranchStabilityObstructionEmpty package transition)) := by
  refine ⟨invariant_selector_fixed actO actX selector, ?_⟩
  constructor
  · intro o hequiv htrivial hnonfixed
    exact no_invariant_selector_on_nonfixed actO actX selector o hequiv htrivial
      hnonfixed
  · exact ⟨selectedness_descends_iff_no_split orbit selected horbit,
      has_selection_split_iff_not_empty orbit selected,
      selects_nontrivial_orbit_iff_split orbit selected,
      breaker_extension_retains_orbit orbit breaker,
      breaker_extension_carries_breaker orbit breaker,
      breaker_extension_strict_of_split orbit breaker,
      (fun package hretains hcarries =>
        breaker_extension_minimal orbit breaker package hretains hcarries),
      (fun package transition hpackage =>
        branch_stable_iff_no_obstruction package transition hpackage)⟩

/-- An induced action on genuine orbit classes is trivial, so equivariant
sections land in the common fixed locus. -/
theorem orbit_induced_action_selector_fixed
    {G X O : Type} (actX : G → X → X) (actO : G → O → O)
    (π : X → O) (hπ : Function.Surjective π)
    (horbit : ∀ x x', π x = π x' ↔ ∃ g, actX g x = x')
    (hinduced : ∀ g x, actO g (π x) = π (actX g x)) :
    TrivialOrbitAction actO ∧
    (∀ σ : O → X, EquivariantSelector actO actX σ →
      ∀ o, FixedByAll actX (σ o)) ∧
    ((¬ ∃ x : X, FixedByAll actX x) →
      (∃ _o : O, True) →
        ¬ ∃ σ : O → X,
          (∀ o, π (σ o) = o) ∧ EquivariantSelector actO actX σ) := by
  have htrivial : TrivialOrbitAction actO := by
    intro g o
    obtain ⟨x, rfl⟩ := hπ o
    calc
      actO g (π x) = π (actX g x) := hinduced g x
      _ = π x := ((horbit x (actX g x)).2 ⟨g, rfl⟩).symm
  refine ⟨htrivial, ?_, ?_⟩
  · intro σ hequiv
    exact invariant_selector_fixed actO actX σ hequiv htrivial
  · intro hnofixed ⟨o, _⟩ ⟨σ, _, hequiv⟩
    exact hnofixed ⟨σ o,
      invariant_selector_fixed actO actX σ hequiv htrivial o⟩

/-- F15a's selectedness obstruction together with the orbit-map consequences
for the induced quotient action. -/
theorem selection_obstruction_orbit_paper
    {G X O : Type} (actO : G → O → O) (actX : G → X → X)
    (π : X → O) (selected : X → Bool) (selector : O → X)
    (hπ : Function.Surjective π)
    (horbit : ∀ x x', π x = π x' ↔ ∃ g, actX g x = x')
    (hinduced : ∀ g x, actO g (π x) = π (actX g x)) :
    (EquivariantSelector actO actX selector →
      TrivialOrbitAction actO →
        ∀ o, FixedByAll actX (selector o)) ∧
    (SelectednessDescends π selected ↔ SelectionObstructionEmpty π selected) ∧
    (HasSelectionSplit π selected ↔ ¬ SelectionObstructionEmpty π selected) ∧
    TrivialOrbitAction actO ∧
    (∀ σ : O → X, EquivariantSelector actO actX σ →
      ∀ o, FixedByAll actX (σ o)) ∧
    ((¬ ∃ x : X, FixedByAll actX x) →
      (∃ _o : O, True) →
        ¬ ∃ σ : O → X,
          (∀ o, π (σ o) = o) ∧ EquivariantSelector actO actX σ) := by
  have horbitResult := orbit_induced_action_selector_fixed actX actO π
    hπ horbit hinduced
  exact ⟨invariant_selector_fixed actO actX selector,
    selectedness_descends_iff_no_split π selected hπ,
    has_selection_split_iff_not_empty π selected,
    horbitResult.1, horbitResult.2.1, horbitResult.2.2⟩

/-- Full F15a bundle: the existing selection and repair normal form plus
triviality and fixed-point consequences of an induced orbit action. -/
theorem selection_obstruction_orbit_full_paper
    {G X O B : Type} (actO : G → O → O) (actX : G → X → X)
    (π : X → O) (selected : X → Bool) (breaker : X → B)
    (hπ : Function.Surjective π) (selector : O → X)
    (horbit : ∀ x x', π x = π x' ↔ ∃ g, actX g x = x')
    (hinduced : ∀ g x, actO g (π x) = π (actX g x)) :
    ((EquivariantSelector actO actX selector →
      TrivialOrbitAction actO →
        ∀ o : O, FixedByAll actX (selector o)) ∧
      (∀ o : O,
        EquivariantSelector actO actX selector →
          TrivialOrbitAction actO →
            (∃ g : G, actX g (selector o) ≠ selector o) → False) ∧
        (SelectednessDescends π selected ↔
          SelectionObstructionEmpty π selected) ∧
          (HasSelectionSplit π selected ↔
            ¬ SelectionObstructionEmpty π selected) ∧
            (SelectsNontrivialOrbit π selected ↔
              HasSelectionSplit π selected) ∧
              RetainsAccess π (breakerExtension π breaker) ∧
                CarriesDistinction (breakerExtension π breaker) breaker ∧
                  (HasBreakerSplit π breaker →
                    StrictAccessExtension π (breakerExtension π breaker)) ∧
                    (∀ {P : Type} (package : X → P),
                      RetainsAccess π package →
                        CarriesDistinction package breaker →
                          FactorsThroughQ package (breakerExtension π breaker)) ∧
                      (∀ {P : Type} (package : X → P) (transition : X → X),
                        Function.Surjective package →
                          (BranchStable package transition ↔
                            BranchStabilityObstructionEmpty package transition))) ∧
    TrivialOrbitAction actO ∧
    (∀ σ : O → X, EquivariantSelector actO actX σ →
      ∀ o, FixedByAll actX (σ o)) ∧
    ((¬ ∃ x : X, FixedByAll actX x) →
      (∃ _o : O, True) →
        ¬ ∃ σ : O → X,
          (∀ o, π (σ o) = o) ∧ EquivariantSelector actO actX σ) := by
  have horbitResult := orbit_induced_action_selector_fixed actX actO π
    hπ horbit hinduced
  exact ⟨selection_obstruction actO actX π selected breaker hπ selector,
    horbitResult.1, horbitResult.2.1, horbitResult.2.2⟩

/-- F15a with the orbit quotient and induced-action equations used only for
the final orbit conclusions. -/
theorem selection_obstruction_orbit_conditional_paper
    {G X O B : Type} (actO : G → O → O) (actX : G → X → X)
    (π : X → O) (selected : X → Bool) (breaker : X → B)
    (hπ : Function.Surjective π) (selector : O → X) :
    ((EquivariantSelector actO actX selector →
      TrivialOrbitAction actO →
        ∀ o : O, FixedByAll actX (selector o)) ∧
      (∀ o : O,
        EquivariantSelector actO actX selector →
          TrivialOrbitAction actO →
            (∃ g : G, actX g (selector o) ≠ selector o) → False) ∧
        (SelectednessDescends π selected ↔
          SelectionObstructionEmpty π selected) ∧
          (HasSelectionSplit π selected ↔
            ¬ SelectionObstructionEmpty π selected) ∧
            (SelectsNontrivialOrbit π selected ↔
              HasSelectionSplit π selected) ∧
              RetainsAccess π (breakerExtension π breaker) ∧
                CarriesDistinction (breakerExtension π breaker) breaker ∧
                  (HasBreakerSplit π breaker →
                    StrictAccessExtension π (breakerExtension π breaker)) ∧
                    (∀ {P : Type} (package : X → P),
                      RetainsAccess π package →
                        CarriesDistinction package breaker →
                          FactorsThroughQ package (breakerExtension π breaker)) ∧
                      (∀ {P : Type} (package : X → P) (transition : X → X),
                        Function.Surjective package →
                          (BranchStable package transition ↔
                            BranchStabilityObstructionEmpty package transition))) ∧
    ((∀ x x', π x = π x' ↔ ∃ g, actX g x = x') →
      (∀ g x, actO g (π x) = π (actX g x)) →
        TrivialOrbitAction actO ∧
        (∀ σ : O → X, EquivariantSelector actO actX σ →
          ∀ o, FixedByAll actX (σ o)) ∧
        ((¬ ∃ x : X, FixedByAll actX x) →
          (∃ _o : O, True) →
            ¬ ∃ σ : O → X,
              (∀ o, π (σ o) = o) ∧ EquivariantSelector actO actX σ)) := by
  exact ⟨selection_obstruction actO actX π selected breaker hπ selector,
    fun horbit hinduced =>
      orbit_induced_action_selector_fixed actX actO π hπ horbit hinduced⟩

/-- For a surjective orbit quotient with its induced action, absence of fixed
points obstructs every equivariant map. An equivariant section exists exactly
for a trivial branch action, when every section is also a left inverse. -/
theorem selection_obstruction_orbit_strengthened
    {G X O : Type} (actO : G → O → O) (actX : G → X → X)
    (π : X → O) (hπ : Function.Surjective π)
    (horbit : ∀ x x', π x = π x' ↔ ∃ g, actX g x = x')
    (hinduced : ∀ g x, actO g (π x) = π (actX g x)) :
    ((¬ ∃ x : X, FixedByAll actX x) →
      (∃ _o : O, True) →
        ¬ ∃ σ : O → X, EquivariantSelector actO actX σ) ∧
    ((∃ σ : O → X,
      (∀ o, π (σ o) = o) ∧ EquivariantSelector actO actX σ) ↔
        ∀ g x, actX g x = x) ∧
    ((∀ g x, actX g x = x) →
      ∀ σ : O → X, (∀ o, π (σ o) = o) → σ ∘ π = id) := by
  have hOrbit := orbit_induced_action_selector_fixed actX actO π hπ horbit hinduced
  refine ⟨?_, ?_, ?_⟩
  · intro hnofixed ⟨o, _⟩ ⟨σ, hequiv⟩
    exact hnofixed ⟨σ o, hOrbit.2.1 σ hequiv o⟩
  · constructor
    · rintro ⟨σ, hsection, hequiv⟩ g x
      obtain ⟨k, hk⟩ := (horbit (σ (π x)) x).mp (hsection (π x))
      have hσx : σ (π x) = x := (hOrbit.2.1 σ hequiv (π x) k).symm.trans hk
      calc
        actX g x = actX g (σ (π x)) := congrArg (actX g) hσx.symm
        _ = σ (π x) := hOrbit.2.1 σ hequiv (π x) g
        _ = x := hσx
    · intro htrivial
      classical
      let σ : O → X := fun o => Classical.choose (hπ o)
      have hsection : ∀ o, π (σ o) = o := fun o => Classical.choose_spec (hπ o)
      refine ⟨σ, hsection, ?_⟩
      intro g o
      calc
        σ (actO g o) = σ o := congrArg σ (hOrbit.1 g o)
        _ = actX g (σ o) := (htrivial g (σ o)).symm
  · intro htrivial σ hsection
    funext x
    obtain ⟨g, hg⟩ := (horbit (σ (π x)) x).mp (hsection (π x))
    exact (htrivial g (σ (π x))).symm.trans hg

/-- Equivariant maps from a genuine orbit quotient are exactly maps into the
common fixed locus. Such a map exists iff that locus or the empty domain
supplies it; no section condition is required. -/
theorem selection_obstruction_equivariant_maps_characterization
    {G X O : Type} (actO : G → O → O) (actX : G → X → X)
    (π : X → O) (hπ : Function.Surjective π)
    (horbit : ∀ x x', π x = π x' ↔ ∃ g, actX g x = x')
    (hinduced : ∀ g x, actO g (π x) = π (actX g x)) :
    (∀ σ : O → X, EquivariantSelector actO actX σ ↔
      ∀ o, FixedByAll actX (σ o)) ∧
    ((∃ σ : O → X, EquivariantSelector actO actX σ) ↔
      ((∃ x : X, FixedByAll actX x) ∨ IsEmpty O)) := by
  classical
  have hOrbit := orbit_induced_action_selector_fixed actX actO π hπ horbit hinduced
  have hchar : ∀ σ : O → X, EquivariantSelector actO actX σ ↔
      ∀ o, FixedByAll actX (σ o) := by
    intro σ
    constructor
    · exact hOrbit.2.1 σ
    · intro hfixed g o
      exact (congrArg σ (hOrbit.1 g o)).trans (hfixed o g).symm
  refine ⟨hchar, ?_⟩
  constructor
  · rintro ⟨σ, hequiv⟩
    by_cases hO : Nonempty O
    · exact Or.inl ⟨σ (Classical.choice hO), (hchar σ).mp hequiv _⟩
    · exact Or.inr ⟨fun o => hO ⟨o⟩⟩
  · rintro (⟨x, hfixed⟩ | hempty)
    · exact ⟨fun _ => x, (hchar _).mpr (fun _ => hfixed)⟩
    · let σ : O → X := fun o => False.elim (hempty.false o)
      exact ⟨σ, fun _ o => False.elim (hempty.false o)⟩

end SixBirdsMetaMath.FoundationsIV.Symmetry.SelectionObstruction
