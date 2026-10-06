import Mathlib.Logic.IsEmpty.Defs
import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F26 Moduli / Contingency.

Contingency is lawful residual freedom: a readout is necessary when it is
invariant across the lawful moduli family, and contingent when it varies across
inequivalent lawful closures. Presentation/gauge multiplicity is quotiented out
by the declared closure equivalence.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ModuliContingency

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- There exists at least one lawful closure. -/
def HasLawfulClosure {Closure : Type} (Lawful : Closure → Prop) : Prop :=
  ∃ c, Lawful c

/-- No lawful closure exists; this is obstruction, not contingency. -/
def ClosureObstructed {Closure : Type} (Lawful : Closure → Prop) : Prop :=
  ∀ c, ¬ Lawful c

/-- All lawful closures are equivalent under the declared presentation/gauge
equivalence. -/
def UniqueModulus {Closure : Type} (Lawful : Closure → Prop)
    (Equivalent : Closure → Closure → Prop) : Prop :=
  ∀ c c', Lawful c → Lawful c' → Equivalent c c'

/-- The base determines a closure up to equivalence: existence plus uniqueness
in the moduli quotient. -/
def DeterminingBase {Closure : Type} (Lawful : Closure → Prop)
    (Equivalent : Closure → Closure → Prop) : Prop :=
  HasLawfulClosure Lawful ∧ UniqueModulus Lawful Equivalent

/-- The base leaves a nontrivial moduli family: two lawful inequivalent
closures exist. -/
def NontrivialModuli {Closure : Type} (Lawful : Closure → Prop)
    (Equivalent : Closure → Closure → Prop) : Prop :=
  ∃ c c', Lawful c ∧ Lawful c' ∧ ¬ Equivalent c c'

/-- Multiple representatives but one modulus: presentation/gauge multiplicity
only, not real contingency. -/
def PresentationMultiplicityOnly {Closure : Type} (Lawful : Closure → Prop)
    (Equivalent : Closure → Closure → Prop) : Prop :=
  (∃ c c', Lawful c ∧ Lawful c' ∧ c ≠ c') ∧ UniqueModulus Lawful Equivalent

/-- A readout is well-defined on moduli when it is invariant under declared
equivalence between lawful closures. -/
def WellDefinedModuliReadout {Closure Value : Type} (Lawful : Closure → Prop)
    (Equivalent : Closure → Closure → Prop) (readout : Closure → Value) : Prop :=
  ∀ c c', Lawful c → Lawful c' → Equivalent c c' → readout c = readout c'

/-- A readout is necessary relative to the base when it is well-defined on
moduli and all inequivalent lawful closures also have the same value. -/
def NecessaryReadout {Closure Value : Type} (Lawful : Closure → Prop)
    (Equivalent : Closure → Closure → Prop) (readout : Closure → Value) : Prop :=
  WellDefinedModuliReadout Lawful Equivalent readout ∧
    ∀ c c', Lawful c → Lawful c' → ¬ Equivalent c c' → readout c = readout c'

/-- The contingency split-pair obstruction: lawful, inequivalent completions
with different readout values. -/
def ContingencySplitPair {Closure Value : Type} (Lawful : Closure → Prop)
    (Equivalent : Closure → Closure → Prop) (readout : Closure → Value) :
    (Closure × Closure) → Prop :=
  fun pair =>
    Lawful pair.1 ∧ Lawful pair.2 ∧ ¬ Equivalent pair.1 pair.2 ∧
      readout pair.1 ≠ readout pair.2

/-- No contingency split-pair obstruction is present. -/
def ContingencySplitPairEmpty {Closure Value : Type} (Lawful : Closure → Prop)
    (Equivalent : Closure → Closure → Prop) (readout : Closure → Value) :
    Prop :=
  ObstructionEmpty (ContingencySplitPair Lawful Equivalent readout)

/-- A contingent readout varies across two lawful inequivalent closures. -/
def ContingentReadout {Closure Value : Type} (Lawful : Closure → Prop)
    (Equivalent : Closure → Closure → Prop) (readout : Closure → Value) :
    Prop :=
  ∃ pair, ContingencySplitPair Lawful Equivalent readout pair

/-- A readout that separates equivalent lawful representatives is
presentation-dependent and therefore not a well-defined moduli readout. -/
def PresentationDependentReadout {Closure Value : Type} (Lawful : Closure → Prop)
    (Equivalent : Closure → Closure → Prop) (readout : Closure → Value) :
    Prop :=
  ∃ c c', Lawful c ∧ Lawful c' ∧ Equivalent c c' ∧ readout c ≠ readout c'

/-- A supplied quotient map to a moduli carrier supports ordinary descent
checks for readouts. -/
def ModuliReadoutDescends {Closure Moduli Value : Type} (p : Closure → Moduli)
    (readout : Closure → Value) : Prop :=
  Descends p (fun c : Closure => c) readout

/-- Split obstruction for descent through a supplied moduli quotient map. -/
def ModuliQuotientReadoutObstruction {Closure Moduli Value : Type}
    (p : Closure → Moduli) (readout : Closure → Value) : (Closure × Closure) → Prop :=
  splitPairObstruction p (fun c : Closure => c) readout

/-- No supplied-quotient readout obstruction is present. -/
def ModuliQuotientReadoutObstructionEmpty {Closure Moduli Value : Type}
    (p : Closure → Moduli) (readout : Closure → Value) : Prop :=
  ObstructionEmpty (ModuliQuotientReadoutObstruction p readout)

/-- Transport of moduli is stable when equivalent source closures have
equivalent transported target closures. -/
def ModuliTransportStable {Closure Closure' : Type} (Lawful : Closure → Prop)
    (Equivalent : Closure → Closure → Prop) (Lawful' : Closure' → Prop)
    (Equivalent' : Closure' → Closure' → Prop) (T : Closure → Closure') : Prop :=
  (∀ c, Lawful c → Lawful' (T c)) ∧
    ∀ c c', Lawful c → Lawful c' → Equivalent c c' → Equivalent' (T c) (T c')

/-- Obstruction to well-defined moduli transport. -/
def ModuliTransportObstruction {Closure Closure' : Type}
    (Lawful : Closure → Prop) (Equivalent : Closure → Closure → Prop)
    (Lawful' : Closure' → Prop) (Equivalent' : Closure' → Closure' → Prop)
    (T : Closure → Closure') : (Closure × Closure) → Prop :=
  fun pair =>
    Lawful pair.1 ∧ Lawful pair.2 ∧ Equivalent pair.1 pair.2 ∧
      (Lawful' (T pair.1) ∧ Lawful' (T pair.2) →
        ¬ Equivalent' (T pair.1) (T pair.2))

/-- No moduli transport obstruction is present. -/
def ModuliTransportObstructionEmpty {Closure Closure' : Type}
    (Lawful : Closure → Prop) (Equivalent : Closure → Closure → Prop)
    (Lawful' : Closure' → Prop) (Equivalent' : Closure' → Closure' → Prop)
    (T : Closure → Closure') : Prop :=
  ObstructionEmpty (ModuliTransportObstruction Lawful Equivalent Lawful' Equivalent' T)

/-- A chosen modulus requires selector data; it is not forced by the base alone. -/
def SelectedModulus {Closure : Type} (Lawful : Closure → Prop)
    (selectorStatus : Prop) (selected : Closure) : Prop :=
  Lawful selected ∧ selectorStatus

/-- A bare modulus choice is a lawful selected representative without selector
status. -/
def BareModulusChoice {Closure : Type} (Lawful : Closure → Prop)
    (selectorStatus : Prop) (selected : Closure) : Prop :=
  Lawful selected ∧ ¬ selectorStatus

/-- Source status vocabulary for moduli and contingency claims. -/
inductive ModuliContingencyStatus where
  | closureObstructed
  | uniqueClosure
  | moduliFamily
  | necessaryReadout
  | contingentReadout
  | selectedModulus
  | hiddenModulus
  | probabilisticModulus
  | presentationMultiplicity
  | bareModulusChoice
  | necessityOverclaim
  | closureCompletenessOverclaim
deriving DecidableEq

/-- Meaning assignment for the F26 status vocabulary. -/
def ModuliContingencyStatusHolds (obstructed unique family necessary contingent
    selected hidden probabilistic presentation bareChoice necessityOverclaim
    completenessOverclaim : Prop) : ModuliContingencyStatus → Prop
  | ModuliContingencyStatus.closureObstructed => obstructed
  | ModuliContingencyStatus.uniqueClosure => unique
  | ModuliContingencyStatus.moduliFamily => family
  | ModuliContingencyStatus.necessaryReadout => necessary
  | ModuliContingencyStatus.contingentReadout => contingent
  | ModuliContingencyStatus.selectedModulus => selected
  | ModuliContingencyStatus.hiddenModulus => hidden
  | ModuliContingencyStatus.probabilisticModulus => probabilistic
  | ModuliContingencyStatus.presentationMultiplicity => presentation
  | ModuliContingencyStatus.bareModulusChoice => bareChoice
  | ModuliContingencyStatus.necessityOverclaim => necessityOverclaim
  | ModuliContingencyStatus.closureCompletenessOverclaim => completenessOverclaim

/-- Obstruction is exactly the absence of lawful closures. -/
theorem closure_obstructed_iff_not_has_lawful {Closure : Type}
    (Lawful : Closure → Prop) :
    ClosureObstructed Lawful ↔ ¬ HasLawfulClosure Lawful := by
  constructor
  · intro hobstructed hhas
    rcases hhas with ⟨c, hc⟩
    exact hobstructed c hc
  · intro hnot c hc
    exact hnot ⟨c, hc⟩

/-- Nontrivial moduli are exactly failure of uniqueness up to equivalence. -/
theorem nontrivial_moduli_iff_not_unique {Closure : Type}
    (Lawful : Closure → Prop) (Equivalent : Closure → Closure → Prop) :
    NontrivialModuli Lawful Equivalent ↔ ¬ UniqueModulus Lawful Equivalent := by
  constructor
  · intro hnontriv hunique
    rcases hnontriv with ⟨c, c', hc, hc', hneqv⟩
    exact hneqv (hunique c c' hc hc')
  · intro hnotUnique
    classical
    exact Classical.byContradiction (fun hnoNontriv =>
      hnotUnique (fun c c' hc hc' =>
        Classical.byContradiction (fun hneqv =>
          hnoNontriv ⟨c, c', hc, hc', hneqv⟩)))

/-- A well-defined readout is necessary exactly when the contingency
split-pair obstruction is empty. -/
theorem necessary_readout_iff_no_contingency_split {Closure Value : Type}
    (Lawful : Closure → Prop) (Equivalent : Closure → Closure → Prop)
    (readout : Closure → Value)
    (hwell : WellDefinedModuliReadout Lawful Equivalent readout) :
    NecessaryReadout Lawful Equivalent readout ↔
      ContingencySplitPairEmpty Lawful Equivalent readout := by
  constructor
  · intro hnecessary pair hpair
    rcases hpair with ⟨hc, hc', hneqv, hdiff⟩
    exact hdiff (hnecessary.2 pair.1 pair.2 hc hc' hneqv)
  · intro hempty
    refine ⟨hwell, ?_⟩
    intro c c' hc hc' hneqv
    exact Classical.byContradiction (fun hdiff =>
      hempty (c, c') ⟨hc, hc', hneqv, hdiff⟩)

/-- A readout is contingent exactly when the contingency split-pair obstruction
is nonempty. -/
theorem contingent_readout_iff_split_nonempty {Closure Value : Type}
    (Lawful : Closure → Prop) (Equivalent : Closure → Closure → Prop)
    (readout : Closure → Value) :
    ContingentReadout Lawful Equivalent readout ↔
      ¬ ContingencySplitPairEmpty Lawful Equivalent readout := by
  constructor
  · intro hcontingent hempty
    rcases hcontingent with ⟨pair, hpair⟩
    exact hempty pair hpair
  · intro hnotEmpty
    classical
    exact Classical.byContradiction (fun hnoWitness =>
      hnotEmpty (fun pair hpair => hnoWitness ⟨pair, hpair⟩))

/-- Necessary and contingent statuses for the same well-defined readout are
exclusive. -/
theorem necessary_readout_excludes_contingent {Closure Value : Type}
    (Lawful : Closure → Prop) (Equivalent : Closure → Closure → Prop)
    (readout : Closure → Value) :
    NecessaryReadout Lawful Equivalent readout →
      ¬ ContingentReadout Lawful Equivalent readout := by
  intro hnecessary hcontingent
  rcases hcontingent with ⟨pair, hc, hc', hneqv, hdiff⟩
  exact hdiff (hnecessary.2 pair.1 pair.2 hc hc' hneqv)

/-- Descent through a supplied moduli quotient is exactly absence of the usual
same-modulus/different-readout split pair. -/
theorem moduli_readout_descends_iff_no_quotient_obstruction
    {Closure Moduli Value : Type} (p : Closure → Moduli)
    (readout : Closure → Value) (hp : Function.Surjective p) :
    ModuliReadoutDescends p readout ↔
      ModuliQuotientReadoutObstructionEmpty p readout :=
  descent_repair_normal_form p (fun c : Closure => c) readout hp

/-- Moduli transport is stable exactly when it creates no equivalent-source /
inequivalent-target obstruction, provided target lawfulness is supplied. -/
theorem moduli_transport_stable_iff_no_obstruction {Closure Closure' : Type}
    (Lawful : Closure → Prop) (Equivalent : Closure → Closure → Prop)
    (Lawful' : Closure' → Prop) (Equivalent' : Closure' → Closure' → Prop)
    (T : Closure → Closure') (htarget : ∀ c, Lawful c → Lawful' (T c)) :
    ModuliTransportStable Lawful Equivalent Lawful' Equivalent' T ↔
      ModuliTransportObstructionEmpty Lawful Equivalent Lawful' Equivalent' T := by
  constructor
  · intro hstable pair hobs
    exact hobs.2.2.2 ⟨hstable.1 pair.1 hobs.1,
      hstable.1 pair.2 hobs.2.1⟩ (hstable.2 pair.1 pair.2 hobs.1 hobs.2.1 hobs.2.2.1)
  · intro hempty
    refine ⟨htarget, ?_⟩
    intro c c' hc hc' heqv
    exact Classical.byContradiction (fun hneqv' =>
      hempty (c, c') ⟨hc, hc', heqv, fun _ => hneqv'⟩)

/-- Bare selection cannot be counted as selected-modulus status. -/
theorem bare_modulus_choice_not_selected {Closure : Type} (Lawful : Closure → Prop)
    (selectorStatus : Prop) (selected : Closure) :
    BareModulusChoice Lawful selectorStatus selected →
      ¬ SelectedModulus Lawful selectorStatus selected := by
  intro hbare hselected
  exact hbare.2 hselected.2

/--
Moduli / Contingency Normal Form. Closure obstruction is absence of solutions;
nontrivial moduli are failure of uniqueness up to the declared equivalence; a
well-defined readout is necessary exactly when its contingency split-pair
obstruction is empty, and contingent exactly when that obstruction is nonempty.
Selection requires additional selector status, and moduli transport must respect
declared equivalence.
-/
theorem moduli_contingency {Closure Moduli Value Closure' : Type}
    (Lawful : Closure → Prop) (Equivalent : Closure → Closure → Prop)
    (readout : Closure → Value) (p : Closure → Moduli)
    (T : Closure → Closure') (Lawful' : Closure' → Prop)
    (Equivalent' : Closure' → Closure' → Prop) (selectorStatus : Prop)
    (selected : Closure)
    (hwell : WellDefinedModuliReadout Lawful Equivalent readout)
    (hp : Function.Surjective p) (htarget : ∀ c, Lawful c → Lawful' (T c)) :
    (ClosureObstructed Lawful ↔ ¬ HasLawfulClosure Lawful) ∧
      (NontrivialModuli Lawful Equivalent ↔ ¬ UniqueModulus Lawful Equivalent) ∧
        (NecessaryReadout Lawful Equivalent readout ↔
          ContingencySplitPairEmpty Lawful Equivalent readout) ∧
          (ContingentReadout Lawful Equivalent readout ↔
            ¬ ContingencySplitPairEmpty Lawful Equivalent readout) ∧
            (NecessaryReadout Lawful Equivalent readout →
              ¬ ContingentReadout Lawful Equivalent readout) ∧
              (ModuliReadoutDescends p readout ↔
                ModuliQuotientReadoutObstructionEmpty p readout) ∧
                (ModuliTransportStable Lawful Equivalent Lawful' Equivalent' T ↔
                  ModuliTransportObstructionEmpty Lawful Equivalent Lawful' Equivalent' T) ∧
                  (BareModulusChoice Lawful selectorStatus selected →
                    ¬ SelectedModulus Lawful selectorStatus selected) := by
  exact ⟨closure_obstructed_iff_not_has_lawful Lawful,
    nontrivial_moduli_iff_not_unique Lawful Equivalent,
    necessary_readout_iff_no_contingency_split Lawful Equivalent readout hwell,
    contingent_readout_iff_split_nonempty Lawful Equivalent readout,
    necessary_readout_excludes_contingent Lawful Equivalent readout,
    moduli_readout_descends_iff_no_quotient_obstruction p readout hp,
    moduli_transport_stable_iff_no_obstruction Lawful Equivalent Lawful' Equivalent' T
      htarget,
    bare_modulus_choice_not_selected Lawful selectorStatus selected⟩


/-- Paper necessity is factorization through the lawful moduli quotient. -/
def PaperNecessaryReadout {C M V : Type} (Lawful : C → Prop)
    (p : C → M) (r : C → V) : Prop :=
  ∃ rbar : M → V, ∀ c, Lawful c → rbar (p c) = r c

/-- Paper contingency compares different moduli with different readouts. -/
def PaperContingentReadout {C M V : Type} (Lawful : C → Prop)
    (p : C → M) (r : C → V) : Prop :=
  ∃ c d, Lawful c ∧ Lawful d ∧ p c ≠ p d ∧ r c ≠ r d

/-- Failure of lawful factorization is witnessed inside one moduli fiber. -/
theorem paper_moduli_contingency {C M V : Type} (Lawful : C → Prop)
    (Equivalent : C → C → Prop) (p : C → M) (r : C → V)
    (hp : ∀ m, ∃ c, Lawful c ∧ p c = m) :
    (ClosureObstructed Lawful ↔ ¬ ∃ c, Lawful c) ∧
    (NontrivialModuli Lawful Equivalent ↔
      ∃ c d, Lawful c ∧ Lawful d ∧ ¬ Equivalent c d) ∧
    (PaperNecessaryReadout Lawful p r ↔
      ∃ rbar : M → V, ∀ c, Lawful c → rbar (p c) = r c) ∧
    (PaperContingentReadout Lawful p r ↔
      ∃ c d, Lawful c ∧ Lawful d ∧ p c ≠ p d ∧ r c ≠ r d) ∧
    (¬ PaperNecessaryReadout Lawful p r ↔
      ∃ c d, Lawful c ∧ Lawful d ∧ p c = p d ∧ r c ≠ r d) := by
  classical
  refine ⟨closure_obstructed_iff_not_has_lawful Lawful, Iff.rfl, Iff.rfl,
    Iff.rfl, ?_⟩
  constructor
  · intro hnot
    apply Classical.byContradiction
    intro hno
    have hconst : ∀ c d, Lawful c → Lawful d → p c = p d → r c = r d := by
      intro c d hc hd heq
      exact Classical.byContradiction (fun hne => hno ⟨c,d,hc,hd,heq,hne⟩)
    let choose : M → C := fun m => Classical.choose (hp m)
    refine hnot ⟨fun m => r (choose m), ?_⟩
    intro c hc
    exact hconst (choose (p c)) c (Classical.choose_spec (hp (p c))).1 hc
      ((Classical.choose_spec (hp (p c))).2)
  · rintro ⟨c,d,hc,hd,heq,hne⟩ ⟨rbar,hrbar⟩
    apply hne
    calc
      r c = rbar (p c) := (hrbar c hc).symm
      _ = rbar (p d) := by rw [heq]
      _ = r d := hrbar d hd

/-- A paper moduli readout is invariant on equivalent lawful closures. -/
def ModuliReadout {C V : Type} (Lawful : C → Prop)
    (Equivalent : C → C → Prop) (r : C → V) : Prop :=
  ∀ c d, Lawful c → Lawful d → Equivalent c d → r c = r d

/-- Presentation dependence is a same-modulus split in the readout. -/
def PresentationDependent {C V : Type} (Lawful : C → Prop)
    (Equivalent : C → C → Prop) (r : C → V) : Prop :=
  ∃ c d, Lawful c ∧ Lawful d ∧ Equivalent c d ∧ r c ≠ r d

/-- Paper necessity means constancy across all lawful closures. -/
def PaperNecessaryConst {C V : Type} (Lawful : C → Prop) (r : C → V) : Prop :=
  ∀ c d, Lawful c → Lawful d → r c = r d

/-- Paper contingency means variation across inequivalent lawful closures. -/
def PaperContingentAcross {C V : Type} (Lawful : C → Prop)
    (Equivalent : C → C → Prop) (r : C → V) : Prop :=
  ∃ c d, Lawful c ∧ Lawful d ∧ ¬ Equivalent c d ∧ r c ≠ r d

/-- Invariance on lawful equivalence classes is exactly factorization through
the supplied, lawfully surjective moduli quotient. -/
theorem moduli_readout_iff_lawful_factorization {C M V : Type}
    (Lawful : C → Prop) (Equivalent : C → C → Prop)
    (p : C → M) (r : C → V)
    (hp_equiv : ∀ c d, Lawful c → Lawful d →
      (p c = p d ↔ Equivalent c d))
    (hp_surj : ∀ m, ∃ c, Lawful c ∧ p c = m) :
    ModuliReadout Lawful Equivalent r ↔
      ∃ rbar : M → V, ∀ c, Lawful c → rbar (p c) = r c := by
  constructor
  · intro hreadout
    classical
    let choose : M → C := fun m => Classical.choose (hp_surj m)
    refine ⟨fun m => r (choose m), ?_⟩
    intro c hc
    have hchoose := Classical.choose_spec (hp_surj (p c))
    exact hreadout (choose (p c)) c hchoose.1 hc
      ((hp_equiv (choose (p c)) c hchoose.1 hc).1 hchoose.2)
  · intro ⟨rbar, hrbar⟩ c d hc hd hequiv
    have hp : p c = p d := (hp_equiv c d hc hd).2 hequiv
    calc
      r c = rbar (p c) := (hrbar c hc).symm
      _ = rbar (p d) := congrArg rbar hp
      _ = r d := hrbar d hd

/-- Presentation dependence is precisely failure of moduli invariance. -/
theorem presentation_dependent_iff_not_moduli_readout {C V : Type}
    (Lawful : C → Prop) (Equivalent : C → C → Prop) (r : C → V) :
    PresentationDependent Lawful Equivalent r ↔
      ¬ ModuliReadout Lawful Equivalent r := by
  constructor
  · intro ⟨c, d, hc, hd, hequiv, hdiff⟩ hreadout
    exact hdiff (hreadout c d hc hd hequiv)
  · intro hnot
    classical
    exact Classical.byContradiction (fun hno =>
      hnot (fun c d hc hd hequiv =>
        Classical.byContradiction (fun hdiff =>
          hno ⟨c, d, hc, hd, hequiv, hdiff⟩)))

/-- A moduli readout is either constant or varies across distinct moduli;
the two cases cannot coincide. -/
theorem moduli_readout_necessary_or_contingent {C V : Type}
    (Lawful : C → Prop) (Equivalent : C → C → Prop) (r : C → V)
    (hreadout : ModuliReadout Lawful Equivalent r) :
    (PaperNecessaryConst Lawful r ∨ PaperContingentAcross Lawful Equivalent r) ∧
      ¬ (PaperNecessaryConst Lawful r ∧
        PaperContingentAcross Lawful Equivalent r) := by
  classical
  constructor
  · by_cases hcont : PaperContingentAcross Lawful Equivalent r
    · exact Or.inr hcont
    · refine Or.inl (fun c d hc hd => ?_)
      by_cases hequiv : Equivalent c d
      · exact hreadout c d hc hd hequiv
      · exact Classical.byContradiction (fun hdiff =>
          hcont ⟨c, d, hc, hd, hequiv, hdiff⟩)
  · intro ⟨hnecessary, c, d, hc, hd, _, hdiff⟩
    exact hdiff (hnecessary c d hc hd)

/-- Without distinct lawful moduli, a moduli readout is necessary. -/
theorem moduli_readout_necessary_of_no_nontrivial {C V : Type}
    (Lawful : C → Prop) (Equivalent : C → C → Prop) (r : C → V)
    (hnontriv : ¬ NontrivialModuli Lawful Equivalent)
    (hreadout : ModuliReadout Lawful Equivalent r) :
    PaperNecessaryConst Lawful r := by
  intro c d hc hd
  have hequiv : Equivalent c d := Classical.byContradiction (fun hne =>
    hnontriv ⟨c, d, hc, hd, hne⟩)
  exact hreadout c d hc hd hequiv

/-- Obstructed closure makes all lawful-pair statuses empty. -/
theorem closure_obstructed_paper_split {C V : Type}
    (Lawful : C → Prop) (Equivalent : C → C → Prop) (r : C → V)
    (hobstructed : ClosureObstructed Lawful) :
    PaperNecessaryConst Lawful r ∧
      ¬ PaperContingentAcross Lawful Equivalent r ∧
      ¬ PresentationDependent Lawful Equivalent r := by
  refine ⟨?_, ?_, ?_⟩
  · intro c d hc hd
    exact False.elim (hobstructed c hc)
  · intro ⟨c, d, hc, hd, hneqv, hdiff⟩
    exact hobstructed c hc
  · intro ⟨c, d, hc, hd, hequiv, hdiff⟩
    exact hobstructed c hc

/-- Stability of lawful moduli transport is exactly absence of an equivalent
source pair whose images are inequivalent. -/
theorem paper_moduli_transport_iff_no_split {C C' : Type}
    (Lawful : C → Prop) (Equivalent : C → C → Prop)
    (T : C → C') (Lawful' : C' → Prop)
    (Equivalent' : C' → C' → Prop)
    (_htarget : ∀ c, Lawful c → Lawful' (T c)) :
    (∀ c d, Lawful c → Lawful d → Equivalent c d →
      Equivalent' (T c) (T d)) ↔
    ¬ ∃ c d, Lawful c ∧ Lawful d ∧ Equivalent c d ∧
      ¬ Equivalent' (T c) (T d) := by
  constructor
  · intro hstable ⟨c, d, hc, hd, hequiv, hnot⟩
    exact hnot (hstable c d hc hd hequiv)
  · intro hno c d hc hd hequiv
    exact Classical.byContradiction (fun hnot =>
      hno ⟨c, d, hc, hd, hequiv, hnot⟩)

/-- Revised paper F26, with lawful factorization, the necessity/contingency
split, the obstruction cases, and stable moduli transport. -/
theorem paper_moduli_contingency_split {C M V : Type}
    (Lawful : C → Prop) (Equivalent : C → C → Prop)
    (p : C → M) (r : C → V)
    (hp_equiv : ∀ c d, Lawful c → Lawful d →
      (p c = p d ↔ Equivalent c d))
    (hp_surj : ∀ m, ∃ c, Lawful c ∧ p c = m) :
    ((ModuliReadout Lawful Equivalent r ↔
      ∃ rbar : M → V, ∀ c, Lawful c → rbar (p c) = r c) ∧
      (PresentationDependent Lawful Equivalent r ↔
        ¬ ModuliReadout Lawful Equivalent r)) ∧
    (ModuliReadout Lawful Equivalent r →
      (PaperNecessaryConst Lawful r ∨
        PaperContingentAcross Lawful Equivalent r) ∧
      ¬ (PaperNecessaryConst Lawful r ∧
        PaperContingentAcross Lawful Equivalent r)) ∧
    ((¬ NontrivialModuli Lawful Equivalent →
      ModuliReadout Lawful Equivalent r → PaperNecessaryConst Lawful r) ∧
      (ClosureObstructed Lawful →
        PaperNecessaryConst Lawful r ∧
        ¬ PaperContingentAcross Lawful Equivalent r ∧
        ¬ PresentationDependent Lawful Equivalent r)) ∧
    (∀ {C' : Type} (T : C → C') (Lawful' : C' → Prop)
      (Equivalent' : C' → C' → Prop),
      (∀ c, Lawful c → Lawful' (T c)) →
      ((∀ c d, Lawful c → Lawful d → Equivalent c d →
        Equivalent' (T c) (T d)) ↔
        ¬ ∃ c d, Lawful c ∧ Lawful d ∧ Equivalent c d ∧
          ¬ Equivalent' (T c) (T d))) := by
  refine ⟨⟨moduli_readout_iff_lawful_factorization Lawful Equivalent p r
      hp_equiv hp_surj,
      presentation_dependent_iff_not_moduli_readout Lawful Equivalent r⟩,
    ?_, ?_, ?_⟩
  · exact moduli_readout_necessary_or_contingent Lawful Equivalent r
  · exact ⟨moduli_readout_necessary_of_no_nontrivial Lawful Equivalent r,
      closure_obstructed_paper_split Lawful Equivalent r⟩
  · intro C' T Lawful' Equivalent' htarget
    exact paper_moduli_transport_iff_no_split Lawful Equivalent T Lawful'
      Equivalent' htarget

/-- A concrete quotient with a two-point presentation fiber over each
modulus. -/
def exampleModuliLawful : Nat × Bool → Prop := fun _ => True

def exampleModuliEquivalent (c d : Nat × Bool) : Prop := c.1 = d.1

def exampleModuliQuotient : Nat × Bool → Nat := Prod.fst

def exampleContingentReadout : Nat × Bool → Nat := fun c => c.1 % 2

def examplePresentationReadout : Nat × Bool → Bool := Prod.snd

/-- The concrete quotient satisfies both lawful quotient hypotheses. -/
theorem example_moduli_quotient_hypotheses :
    (∀ c d, exampleModuliLawful c → exampleModuliLawful d →
      (exampleModuliQuotient c = exampleModuliQuotient d ↔
        exampleModuliEquivalent c d)) ∧
    (∀ m, ∃ c, exampleModuliLawful c ∧ exampleModuliQuotient c = m) := by
  constructor
  · intro c d _ _
    exact Iff.rfl
  · intro m
    exact ⟨(m, false), trivial, rfl⟩

/-- The parity readout is well defined on moduli and varies between them. -/
theorem example_contingent_moduli_readout :
    ModuliReadout exampleModuliLawful exampleModuliEquivalent
      exampleContingentReadout ∧
    PaperContingentAcross exampleModuliLawful exampleModuliEquivalent
      exampleContingentReadout := by
  constructor
  · intro c d _ _ hequiv
    exact congrArg (fun n : Nat => n % 2) hequiv
  · exact ⟨(0, false), (1, false), trivial, trivial,
      by
        change (0 : Nat) ≠ 1
        decide,
      by
        change (0 : Nat) % 2 ≠ 1 % 2
        decide⟩

/-- The second-coordinate readout depends on presentation within a modulus. -/
theorem example_presentation_dependent_readout :
    PresentationDependent exampleModuliLawful exampleModuliEquivalent
      examplePresentationReadout := by
  exact ⟨(0, false), (0, true), trivial, trivial, rfl, by decide⟩


/-- Lawful surjectivity leaves no moduli when no closure is lawful. -/
theorem closure_obstructed_moduli_empty {C M : Type}
    (Lawful : C → Prop) (p : C → M)
    (hp_surj : ∀ m, ∃ c, Lawful c ∧ p c = m) :
    ClosureObstructed Lawful → IsEmpty M := by
  intro hobstructed
  refine ⟨?_⟩
  intro m
  obtain ⟨c, hc, _⟩ := hp_surj m
  exact hobstructed c hc

/-- The full F26 conclusion also states emptiness of moduli under closure
obstruction, using the standing lawful-surjectivity hypothesis. -/
theorem paper_moduli_contingency_split_full {C M V : Type}
    (Lawful : C → Prop) (Equivalent : C → C → Prop)
    (p : C → M) (r : C → V)
    (hp_equiv : ∀ c d, Lawful c → Lawful d →
      (p c = p d ↔ Equivalent c d))
    (hp_surj : ∀ m, ∃ c, Lawful c ∧ p c = m) :
    (((ModuliReadout Lawful Equivalent r ↔
      ∃ rbar : M → V, ∀ c, Lawful c → rbar (p c) = r c) ∧
      (PresentationDependent Lawful Equivalent r ↔
        ¬ ModuliReadout Lawful Equivalent r)) ∧
    (ModuliReadout Lawful Equivalent r →
      (PaperNecessaryConst Lawful r ∨
        PaperContingentAcross Lawful Equivalent r) ∧
      ¬ (PaperNecessaryConst Lawful r ∧
        PaperContingentAcross Lawful Equivalent r)) ∧
    ((¬ NontrivialModuli Lawful Equivalent →
      ModuliReadout Lawful Equivalent r → PaperNecessaryConst Lawful r) ∧
      (ClosureObstructed Lawful →
        PaperNecessaryConst Lawful r ∧
        ¬ PaperContingentAcross Lawful Equivalent r ∧
        ¬ PresentationDependent Lawful Equivalent r)) ∧
    (∀ {C' : Type} (T : C → C') (Lawful' : C' → Prop)
      (Equivalent' : C' → C' → Prop),
      (∀ c, Lawful c → Lawful' (T c)) →
      ((∀ c d, Lawful c → Lawful d → Equivalent c d →
        Equivalent' (T c) (T d)) ↔
        ¬ ∃ c d, Lawful c ∧ Lawful d ∧ Equivalent c d ∧
          ¬ Equivalent' (T c) (T d)))) ∧
    (ClosureObstructed Lawful → IsEmpty M) := by
  exact ⟨paper_moduli_contingency_split Lawful Equivalent p r hp_equiv hp_surj,
    closure_obstructed_moduli_empty Lawful p hp_surj⟩

/-- With no lawful closure, every readout is necessary and neither contingent
nor presentation-dependent, independently of any moduli map or surjectivity. -/
theorem closure_obstructed_every_readout_paper_split {C : Type}
    (Lawful : C → Prop) (Equivalent : C → C → Prop)
    (hobstructed : ClosureObstructed Lawful) :
    ∀ {V : Type} (r : C → V),
      PaperNecessaryConst Lawful r ∧
        ¬ PaperContingentAcross Lawful Equivalent r ∧
        ¬ PresentationDependent Lawful Equivalent r := by
  intro V r
  exact closure_obstructed_paper_split Lawful Equivalent r hobstructed

/-- Lawful surjectivity and a total moduli map force the entire closure carrier
empty when no closure is lawful; equivalence of closures is not needed. -/
theorem closure_obstructed_closure_empty {C M : Type}
    (Lawful : C → Prop) (p : C → M)
    (hp_surj : ∀ m, ∃ c, Lawful c ∧ p c = m) :
    ClosureObstructed Lawful → IsEmpty C := by
  intro hobstructed
  refine ⟨?_⟩
  intro c
  obtain ⟨d, hd, _⟩ := hp_surj (p c)
  exact hobstructed d hd

/-- F26 with standing quotient assumptions only on the lawful factorization
and carrier-emptiness clauses. The readout split and the obstructed case apply
to arbitrary closure carriers without those assumptions. -/
theorem paper_moduli_contingency_split_full_general {C M V : Type}
    (Lawful : C → Prop) (Equivalent : C → C → Prop)
    (p : C → M) (r : C → V) :
    (((∀ c d, Lawful c → Lawful d →
        (p c = p d ↔ Equivalent c d)) →
      (∀ m, ∃ c, Lawful c ∧ p c = m) →
      (ModuliReadout Lawful Equivalent r ↔
        ∃ rbar : M → V, ∀ c, Lawful c → rbar (p c) = r c)) ∧
      (PresentationDependent Lawful Equivalent r ↔
        ¬ ModuliReadout Lawful Equivalent r)) ∧
    (ModuliReadout Lawful Equivalent r →
      (PaperNecessaryConst Lawful r ∨
        PaperContingentAcross Lawful Equivalent r) ∧
      ¬ (PaperNecessaryConst Lawful r ∧
        PaperContingentAcross Lawful Equivalent r)) ∧
    ((¬ NontrivialModuli Lawful Equivalent →
      ModuliReadout Lawful Equivalent r → PaperNecessaryConst Lawful r) ∧
      (ClosureObstructed Lawful →
        PaperNecessaryConst Lawful r ∧
        ¬ PaperContingentAcross Lawful Equivalent r ∧
        ¬ PresentationDependent Lawful Equivalent r) ∧
      ((∀ m, ∃ c, Lawful c ∧ p c = m) →
        ClosureObstructed Lawful → IsEmpty M ∧ IsEmpty C)) ∧
    (∀ {C' : Type} (T : C → C') (Lawful' : C' → Prop)
      (Equivalent' : C' → C' → Prop),
      (∀ c, Lawful c → Lawful' (T c)) →
      ((∀ c d, Lawful c → Lawful d → Equivalent c d →
        Equivalent' (T c) (T d)) ↔
        ¬ ∃ c d, Lawful c ∧ Lawful d ∧ Equivalent c d ∧
          ¬ Equivalent' (T c) (T d))) := by
  refine ⟨⟨?_, presentation_dependent_iff_not_moduli_readout Lawful Equivalent r⟩,
    moduli_readout_necessary_or_contingent Lawful Equivalent r,
    ⟨moduli_readout_necessary_of_no_nontrivial Lawful Equivalent r, ?_, ?_⟩, ?_⟩
  · intro hp_equiv hp_surj
    exact moduli_readout_iff_lawful_factorization Lawful Equivalent p r hp_equiv hp_surj
  · intro hobstructed
    exact closure_obstructed_every_readout_paper_split Lawful Equivalent hobstructed r
  · intro hp_surj hobstructed
    exact ⟨closure_obstructed_moduli_empty Lawful p hp_surj hobstructed,
      closure_obstructed_closure_empty Lawful p hp_surj hobstructed⟩
  · intro C' T Lawful' Equivalent' htarget
    exact paper_moduli_transport_iff_no_split Lawful Equivalent T Lawful'
      Equivalent' htarget

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ModuliContingency
