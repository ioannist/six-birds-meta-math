import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F46 Law-State Split.

Law is modeled as closure-invariance over the lawful moduli quotient of a base
package. State is modeled as selected-modulus dependence: the readout varies
over lawful moduli and becomes fixed only after a modulus is selected or
recorded.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.LawStateSplit

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- A closure readout is well-defined on moduli when it descends through the
lawful-closure quotient map. -/
def ReadoutRespectsModuli {Closure Moduli Value : Type}
    (moduliQuotient : Closure → Moduli) (readout : Closure → Value) : Prop :=
  Descends moduliQuotient (fun closure : Closure => closure) readout

/-- Obstruction to a closure readout respecting the moduli quotient. -/
def ModuliReadoutObstruction {Closure Moduli Value : Type}
    (moduliQuotient : Closure → Moduli) (readout : Closure → Value) :
    (Closure × Closure) → Prop :=
  splitPairObstruction moduliQuotient (fun closure : Closure => closure) readout

/-- No moduli-readout obstruction is present. -/
def ModuliReadoutObstructionEmpty {Closure Moduli Value : Type}
    (moduliQuotient : Closure → Moduli) (readout : Closure → Value) : Prop :=
  ObstructionEmpty (ModuliReadoutObstruction moduliQuotient readout)

/-- Law/state variation obstruction on the moduli readout. -/
def LawStateVariation {Moduli Value : Type} (moduliReadout : Moduli → Value) :
    (Moduli × Moduli) → Prop :=
  fun pair => moduliReadout pair.1 ≠ moduliReadout pair.2

/-- The moduli readout is law-determined by the base: it is invariant across
all lawful moduli. -/
def LawReadout {Moduli Value : Type} (moduliReadout : Moduli → Value) : Prop :=
  ObstructionEmpty (LawStateVariation moduliReadout)

/-- The moduli readout is state-dependent: it varies across lawful moduli. -/
def StateDependent {Moduli Value : Type} (moduliReadout : Moduli → Value) :
    Prop :=
  ∃ pair, LawStateVariation moduliReadout pair

/-- A selected closure is one whose moduli quotient equals the selected modulus. -/
def SelectedClosure {Closure Moduli : Type} (moduliQuotient : Closure → Moduli)
    (selected : Moduli) (closure : Closure) : Prop :=
  moduliQuotient closure = selected

/-- A selected state fixes a readout when every closure with the selected
modulus has the selected readout value. -/
def SelectedStateFixesReadout {Closure Moduli Value : Type}
    (moduliQuotient : Closure → Moduli) (moduliReadout : Moduli → Value)
    (readout : Closure → Value) (selected : Moduli) : Prop :=
  ∀ closure, SelectedClosure moduliQuotient selected closure →
    readout closure = moduliReadout selected

/-- A selected modulus is current-visible when the selector descends through
the current access quotient. -/
def SelectedStateVisible {Situation Current Moduli : Type}
    (currentAccess : Situation → Current) (selector : Situation → Moduli) :
    Prop :=
  Descends currentAccess (fun situation : Situation => situation) selector

/-- A hidden state is selected but not current-visible. -/
def HiddenState {Situation Current Moduli : Type}
    (currentAccess : Situation → Current) (selector : Situation → Moduli) :
    Prop :=
  ¬ SelectedStateVisible currentAccess selector

/-- A selected state is recorded when it descends through a stable record
quotient. -/
def RecordedState {Situation Record Moduli : Type} (record : Situation → Record)
    (selector : Situation → Moduli) : Prop :=
  Descends record (fun situation : Situation => situation) selector

/-- Probability over moduli is a state law, not a selected state. -/
def ProbabilisticState {Moduli Law : Type} (stateLaw : Moduli → Law)
    (StableLaw : (Moduli → Law) → Prop) : Prop :=
  StableLaw stateLaw

/-- Boundary/interface/initial data selects state when a selector descends
through that supplied quotient. -/
def InterfaceSelectedState {Source Interface Moduli : Type}
    (interfaceQuotient : Source → Interface) (selector : Source → Moduli) :
    Prop :=
  Descends interfaceQuotient (fun source : Source => source) selector

/-- Transport of selected moduli between stages. -/
def StateTransportDescends {Closure₁ Moduli₁ Closure₂ Moduli₂ : Type}
    (moduli₁ : Closure₁ → Moduli₁) (transport : Closure₁ → Closure₂)
    (moduli₂ : Closure₂ → Moduli₂) : Prop :=
  Descends moduli₁ transport moduli₂

/-- State-transport obstruction. -/
def StateTransportObstruction {Closure₁ Moduli₁ Closure₂ Moduli₂ : Type}
    (moduli₁ : Closure₁ → Moduli₁) (transport : Closure₁ → Closure₂)
    (moduli₂ : Closure₂ → Moduli₂) : (Closure₁ × Closure₁) → Prop :=
  splitPairObstruction moduli₁ transport moduli₂

/-- No state-transport obstruction is present. -/
def StateTransportObstructionEmpty {Closure₁ Moduli₁ Closure₂ Moduli₂ : Type}
    (moduli₁ : Closure₁ → Moduli₁) (transport : Closure₁ → Closure₂)
    (moduli₂ : Closure₂ → Moduli₂) : Prop :=
  ObstructionEmpty (StateTransportObstruction moduli₁ transport moduli₂)

/-- A law overclaim asserts law status while the readout varies over moduli. -/
def LawOverclaim {Moduli Value : Type} (moduliReadout : Moduli → Value)
    (claimedLaw : Prop) : Prop :=
  claimedLaw ∧ StateDependent moduliReadout

/-- State overread uses a selected state value without any declared selector,
record, probability, bridge, source, or hidden-state status. -/
def StateOverread (selectorDeclared recordDeclared probabilisticDeclared
    bridgeDeclared sourceDeclared hiddenStatusDeclared : Prop) : Prop :=
  ¬ (selectorDeclared ∨ recordDeclared ∨ probabilisticDeclared ∨ bridgeDeclared ∨
    sourceDeclared ∨ hiddenStatusDeclared)

/-- Source status vocabulary for law/state claims. -/
inductive LawStateStatus where
  | closureObstructed
  | uniqueClosure
  | lawReadout
  | stateDependent
  | selectedState
  | recordedState
  | hiddenState
  | probabilisticState
  | boundarySelectedState
  | initialState
  | interfaceState
  | branchSelectedState
  | lawOverclaim
  | stateOverread
  | stateTransportFailure
  | localState
  | globalStateObstructed
  | presentationStateArtifact
  | protocolSelectedState
  | lawStateRoleMismatch
deriving DecidableEq

/-- Meaning assignment for the F46 law/state status vocabulary. -/
def LawStateStatusHolds (closureObstructed unique law state selected recorded hidden
    probabilistic boundary initial interface branch overclaim stateOverread
    transportFailure localOnly globalObstructed presentationArtifact protocolSelected
    roleMismatch : Prop) : LawStateStatus → Prop
  | LawStateStatus.closureObstructed => closureObstructed
  | LawStateStatus.uniqueClosure => unique
  | LawStateStatus.lawReadout => law
  | LawStateStatus.stateDependent => state
  | LawStateStatus.selectedState => selected
  | LawStateStatus.recordedState => recorded
  | LawStateStatus.hiddenState => hidden
  | LawStateStatus.probabilisticState => probabilistic
  | LawStateStatus.boundarySelectedState => boundary
  | LawStateStatus.initialState => initial
  | LawStateStatus.interfaceState => interface
  | LawStateStatus.branchSelectedState => branch
  | LawStateStatus.lawOverclaim => overclaim
  | LawStateStatus.stateOverread => stateOverread
  | LawStateStatus.stateTransportFailure => transportFailure
  | LawStateStatus.localState => localOnly
  | LawStateStatus.globalStateObstructed => globalObstructed
  | LawStateStatus.presentationStateArtifact => presentationArtifact
  | LawStateStatus.protocolSelectedState => protocolSelected
  | LawStateStatus.lawStateRoleMismatch => roleMismatch

/-- A closure readout respects moduli iff the moduli split-pair obstruction is
empty. -/
theorem readout_respects_moduli_iff_no_obstruction
    {Closure Moduli Value : Type} (moduliQuotient : Closure → Moduli)
    (readout : Closure → Value) (hmoduli : Function.Surjective moduliQuotient) :
    ReadoutRespectsModuli moduliQuotient readout ↔
      ModuliReadoutObstructionEmpty moduliQuotient readout :=
  descent_repair_normal_form moduliQuotient (fun closure : Closure => closure)
    readout hmoduli

/-- Law readout iff no law/state variation obstruction is present. -/
theorem law_readout_iff_no_variation {Moduli Value : Type}
    (moduliReadout : Moduli → Value) :
    LawReadout moduliReadout ↔
      ObstructionEmpty (LawStateVariation moduliReadout) := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- State dependence is exactly failure of law invariance. -/
theorem state_dependent_iff_not_law {Moduli Value : Type}
    (moduliReadout : Moduli → Value) :
    StateDependent moduliReadout ↔ ¬ LawReadout moduliReadout := by
  constructor
  · intro hstate hlaw
    rcases hstate with ⟨pair, hpair⟩
    exact hlaw pair hpair
  · intro hnotLaw
    classical
    exact Classical.byContradiction (fun hnoState => by
      have hlaw : LawReadout moduliReadout := by
        intro pair hpair
        exact hnoState ⟨pair, hpair⟩
      exact hnotLaw hlaw)

/-- Every moduli readout is either law-determined or state-dependent. -/
theorem law_or_state_dependent {Moduli Value : Type}
    (moduliReadout : Moduli → Value) :
    LawReadout moduliReadout ∨ StateDependent moduliReadout := by
  classical
  by_cases hlaw : LawReadout moduliReadout
  · exact Or.inl hlaw
  · exact Or.inr ((state_dependent_iff_not_law moduliReadout).2 hlaw)

/-- Law and state-dependent statuses are mutually exclusive. -/
theorem not_law_and_state_dependent {Moduli Value : Type}
    (moduliReadout : Moduli → Value) :
    ¬ (LawReadout moduliReadout ∧ StateDependent moduliReadout) := by
  intro hboth
  exact (state_dependent_iff_not_law moduliReadout).1 hboth.2 hboth.1

/-- A selected modulus fixes the readout on the selected closure fiber. -/
theorem selected_state_fixes_readout {Closure Moduli Value : Type}
    (moduliQuotient : Closure → Moduli) (moduliReadout : Moduli → Value)
    (readout : Closure → Value) (selected : Moduli)
    (hreadout : moduliReadout ∘ moduliQuotient = readout) :
    SelectedStateFixesReadout moduliQuotient moduliReadout readout selected := by
  intro closure hselected
  have hpoint : moduliReadout (moduliQuotient closure) = readout closure :=
    congrFun hreadout closure
  calc
    readout closure = moduliReadout (moduliQuotient closure) := hpoint.symm
    _ = moduliReadout selected := by rw [hselected]

/-- State transport descends iff no state-transport obstruction is present. -/
theorem state_transport_descends_iff_no_obstruction
    {Closure₁ Moduli₁ Closure₂ Moduli₂ : Type}
    (moduli₁ : Closure₁ → Moduli₁) (transport : Closure₁ → Closure₂)
    (moduli₂ : Closure₂ → Moduli₂)
    (hmoduli₁ : Function.Surjective moduli₁) :
    StateTransportDescends moduli₁ transport moduli₂ ↔
      StateTransportObstructionEmpty moduli₁ transport moduli₂ :=
  descent_repair_normal_form moduli₁ transport moduli₂ hmoduli₁

/--
Law-State Split Normal Form. A closure readout must first descend to the moduli
quotient. It is law relative to the base exactly when its moduli readout has no
variation obstruction; it is state-dependent exactly when that obstruction has
a witness. Selecting a modulus fixes the readout on the selected closure fiber,
and selected moduli transport exactly when the state-transport obstruction is
empty.
-/
theorem law_state_split {Closure Moduli Value Closure₂ Moduli₂ : Type}
    (moduliQuotient : Closure → Moduli) (readout : Closure → Value)
    (moduliReadout : Moduli → Value) (selected : Moduli)
    (transport : Closure → Closure₂) (moduli₂ : Closure₂ → Moduli₂)
    (hmoduli : Function.Surjective moduliQuotient)
    (hreadout : moduliReadout ∘ moduliQuotient = readout) :
    (ReadoutRespectsModuli moduliQuotient readout ↔
      ModuliReadoutObstructionEmpty moduliQuotient readout) ∧
      (LawReadout moduliReadout ↔
        ObstructionEmpty (LawStateVariation moduliReadout)) ∧
        (StateDependent moduliReadout ↔ ¬ LawReadout moduliReadout) ∧
          (LawReadout moduliReadout ∨ StateDependent moduliReadout) ∧
            ¬ (LawReadout moduliReadout ∧ StateDependent moduliReadout) ∧
              SelectedStateFixesReadout moduliQuotient moduliReadout readout
                selected ∧
                (StateTransportDescends moduliQuotient transport moduli₂ ↔
                  StateTransportObstructionEmpty moduliQuotient transport
                    moduli₂) := by
  exact ⟨readout_respects_moduli_iff_no_obstruction moduliQuotient readout
      hmoduli,
    law_readout_iff_no_variation moduliReadout,
    state_dependent_iff_not_law moduliReadout,
    law_or_state_dependent moduliReadout,
    not_law_and_state_dependent moduliReadout,
    selected_state_fixes_readout moduliQuotient moduliReadout readout selected
      hreadout,
    state_transport_descends_iff_no_obstruction moduliQuotient transport moduli₂
      hmoduli⟩

/-- F46 without a preselected descended readout: descent is fiber constancy,
the descended map is unique, and law status is raw constancy. -/
theorem law_state_split_direct {Closure Moduli Value : Type}
    (moduliQuotient : Closure → Moduli) (readout : Closure → Value)
    (hmoduli : Function.Surjective moduliQuotient) :
    (ReadoutRespectsModuli moduliQuotient readout ↔
      ∀ x y, moduliQuotient x = moduliQuotient y → readout x = readout y) ∧
    (∀ rbar rbar' : Moduli → Value,
      rbar ∘ moduliQuotient = readout →
      rbar' ∘ moduliQuotient = readout → rbar = rbar') ∧
    (∀ rbar : Moduli → Value, rbar ∘ moduliQuotient = readout →
      (LawReadout rbar ↔ ∀ x y : Closure, readout x = readout y)) := by
  constructor
  · constructor
    · rintro ⟨rbar, hbar⟩ x y hxy
      have hx := congrFun hbar x
      have hy := congrFun hbar y
      exact hx.symm.trans ((congrArg rbar hxy).trans hy)
    · intro hconst
      apply (readout_respects_moduli_iff_no_obstruction moduliQuotient
        readout hmoduli).mpr
      rintro ⟨x, y⟩ ⟨hxy, hne⟩
      exact hne (hconst x y hxy)
  constructor
  · intro rbar rbar' hbar hbar'
    funext m
    obtain ⟨x, rfl⟩ := hmoduli m
    exact (congrFun hbar x).trans (congrFun hbar' x).symm
  · intro rbar hbar
    constructor
    · intro hlaw x y
      have hx := congrFun hbar x
      have hy := congrFun hbar y
      exact hx.symm.trans ((Classical.byContradiction
        (fun hne => hlaw (moduliQuotient x, moduliQuotient y) hne)).trans hy)
    · intro hconst pair hne
      obtain ⟨x, hx⟩ := hmoduli pair.1
      obtain ⟨y, hy⟩ := hmoduli pair.2
      apply hne
      calc
        rbar pair.1 = rbar (moduliQuotient x) := congrArg rbar hx.symm
        _ = readout x := congrFun hbar x
        _ = readout y := hconst x y
        _ = rbar (moduliQuotient y) := (congrFun hbar y).symm
        _ = rbar pair.2 := congrArg rbar hy

/-- F46 with descent and uniqueness established before selecting the
descended readout; the selected-state and transport clauses then follow. -/
theorem law_state_split_paper
    {Closure Moduli Value Closure₂ Moduli₂ : Type}
    (moduliQuotient : Closure → Moduli) (readout : Closure → Value)
    (selected : Moduli) (transport : Closure → Closure₂)
    (moduli₂ : Closure₂ → Moduli₂)
    (hmoduli : Function.Surjective moduliQuotient) :
    (ReadoutRespectsModuli moduliQuotient readout ↔
      ∀ x y, moduliQuotient x = moduliQuotient y → readout x = readout y) ∧
    (∀ rbar rbar' : Moduli → Value,
      rbar ∘ moduliQuotient = readout →
      rbar' ∘ moduliQuotient = readout → rbar = rbar') ∧
    (∀ rbar : Moduli → Value, rbar ∘ moduliQuotient = readout →
      (LawReadout rbar ↔ ∀ x y : Closure, readout x = readout y) ∧
      (LawReadout rbar ↔
        ObstructionEmpty (LawStateVariation rbar)) ∧
      (StateDependent rbar ↔ ¬ LawReadout rbar) ∧
      (LawReadout rbar ∨ StateDependent rbar) ∧
      ¬ (LawReadout rbar ∧ StateDependent rbar) ∧
      SelectedStateFixesReadout moduliQuotient rbar readout selected) ∧
    (StateTransportDescends moduliQuotient transport moduli₂ ↔
      StateTransportObstructionEmpty moduliQuotient transport moduli₂) := by
  have hdirect := law_state_split_direct moduliQuotient readout hmoduli
  refine ⟨hdirect.1, hdirect.2.1, ?_,
    state_transport_descends_iff_no_obstruction moduliQuotient transport
      moduli₂ hmoduli⟩
  intro rbar hbar
  have hold := law_state_split moduliQuotient readout rbar selected
    transport moduli₂ hmoduli hbar
  exact ⟨hdirect.2.2 rbar hbar, hold.2.1, hold.2.2.1,
    hold.2.2.2.1, hold.2.2.2.2.1, hold.2.2.2.2.2.1⟩

/-- A descended readout is state-dependent exactly when different moduli
are realized by closures with different readout values. -/
theorem state_dependent_iff_distinct_moduli_raw_readouts
    {Closure Moduli Value : Type}
    (moduliQuotient : Closure → Moduli) (readout : Closure → Value)
    (moduliReadout : Moduli → Value)
    (hmoduli : Function.Surjective moduliQuotient)
    (hreadout : moduliReadout ∘ moduliQuotient = readout) :
    StateDependent moduliReadout ↔
      ∃ x y, moduliQuotient x ≠ moduliQuotient y ∧ readout x ≠ readout y := by
  constructor
  · rintro ⟨⟨m, m'⟩, hdiff⟩
    obtain ⟨x, rfl⟩ := hmoduli m
    obtain ⟨y, rfl⟩ := hmoduli m'
    refine ⟨x, y, fun heq => hdiff (congrArg moduliReadout heq), ?_⟩
    intro heq
    apply hdiff
    calc
      moduliReadout (moduliQuotient x) = readout x := congrFun hreadout x
      _ = readout y := heq
      _ = moduliReadout (moduliQuotient y) := (congrFun hreadout y).symm
  · rintro ⟨x, y, _, hdiff⟩
    refine ⟨(moduliQuotient x, moduliQuotient y), ?_⟩
    intro heq
    apply hdiff
    calc
      readout x = moduliReadout (moduliQuotient x) := (congrFun hreadout x).symm
      _ = moduliReadout (moduliQuotient y) := heq
      _ = readout y := congrFun hreadout y

/-- Full F46: clause (ii) includes the raw-closure witness characterization
of state dependence for each descended readout. -/
theorem law_state_split_paper_full
    {Closure Moduli Value Closure₂ Moduli₂ : Type}
    (moduliQuotient : Closure → Moduli) (readout : Closure → Value)
    (selected : Moduli) (transport : Closure → Closure₂)
    (moduli₂ : Closure₂ → Moduli₂)
    (hmoduli : Function.Surjective moduliQuotient) :
    (ReadoutRespectsModuli moduliQuotient readout ↔
      ∀ x y, moduliQuotient x = moduliQuotient y → readout x = readout y) ∧
    (∀ rbar rbar' : Moduli → Value,
      rbar ∘ moduliQuotient = readout →
      rbar' ∘ moduliQuotient = readout → rbar = rbar') ∧
    (∀ rbar : Moduli → Value, rbar ∘ moduliQuotient = readout →
      (LawReadout rbar ↔ ∀ x y : Closure, readout x = readout y) ∧
      (LawReadout rbar ↔
        ObstructionEmpty (LawStateVariation rbar)) ∧
      (StateDependent rbar ↔ ¬ LawReadout rbar) ∧
      (StateDependent rbar ↔
        ∃ x y, moduliQuotient x ≠ moduliQuotient y ∧ readout x ≠ readout y) ∧
      (LawReadout rbar ∨ StateDependent rbar) ∧
      ¬ (LawReadout rbar ∧ StateDependent rbar) ∧
      SelectedStateFixesReadout moduliQuotient rbar readout selected) ∧
    (StateTransportDescends moduliQuotient transport moduli₂ ↔
      StateTransportObstructionEmpty moduliQuotient transport moduli₂) := by
  obtain ⟨hdescent, hunique, hreadouts, htransport⟩ :=
    law_state_split_paper moduliQuotient readout selected transport moduli₂ hmoduli
  refine ⟨hdescent, hunique, ?_, htransport⟩
  intro rbar hbar
  obtain ⟨hconst, hvariation, hstate, heither, hexclusive, hselected⟩ := hreadouts rbar hbar
  exact ⟨hconst, hvariation, hstate,
    state_dependent_iff_distinct_moduli_raw_readouts moduliQuotient readout rbar
      hmoduli hbar, heither, hexclusive, hselected⟩

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.LawStateSplit
