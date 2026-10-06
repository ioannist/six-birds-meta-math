import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F48 Topology as Global Gluing Invariant.

Topology is modeled as a readout of the declared global gluing quotient. It is
not merely local compatibility: local data must globalize, presentation
artifacts must be quotiented, and the readout must descend through the gluing
class.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Topology

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- A readout is topological when it descends through the global gluing
quotient. -/
def TopologicalReadout {Global Glue Value : Type} (gluingQuotient : Global → Glue)
    (readout : Global → Value) : Prop :=
  Descends gluingQuotient (fun global : Global => global) readout

/-- Topology descent obstruction: same gluing class but different readout. -/
def TopologyObstruction {Global Glue Value : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value) :
    (Global × Global) → Prop :=
  splitPairObstruction gluingQuotient (fun global : Global => global) readout

/-- No topology descent obstruction is present. -/
def TopologyObstructionEmpty {Global Glue Value : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value) : Prop :=
  ObstructionEmpty (TopologyObstruction gluingQuotient readout)

/-- Separation obstruction for completeness: distinct gluing classes have the
same invariant value. -/
def TopologySeparationObstruction {Global Glue Value : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value) :
    (Global × Global) → Prop :=
  fun pair => gluingQuotient pair.1 ≠ gluingQuotient pair.2 ∧
    readout pair.1 = readout pair.2

/-- No separation obstruction is present. -/
def TopologySeparationObstructionEmpty {Global Glue Value : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value) : Prop :=
  ObstructionEmpty (TopologySeparationObstruction gluingQuotient readout)

/-- A complete topological invariant both descends through and separates the
declared gluing quotient. -/
def CompleteTopologicalInvariant {Global Glue Value : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value) : Prop :=
  TopologicalReadout gluingQuotient readout ∧
    TopologySeparationObstructionEmpty gluingQuotient readout

/-- A coarse topological invariant descends but does not completely separate
gluing classes. -/
def CoarseTopologicalInvariant {Global Glue Value : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value) : Prop :=
  TopologicalReadout gluingQuotient readout ∧
    ∃ pair, TopologySeparationObstruction gluingQuotient readout pair

/-- Local matching data have a declared global filler. -/
def HasGlobalFiller {Global LocalFamily : Type} (restriction : Global → LocalFamily)
    (localData : LocalFamily) : Prop :=
  ∃ global, restriction global = localData

/-- Matching local data with no global filler. -/
def GlobalGluingObstructed {Global LocalFamily : Type}
    (compatible : LocalFamily → Prop) (restriction : Global → LocalFamily)
    (localData : LocalFamily) : Prop :=
  compatible localData ∧ ¬ HasGlobalFiller restriction localData

/-- Multiple inequivalent global gluing classes fill the same local data. -/
def MultipleGlobalTopologies {Global LocalFamily Glue : Type}
    (restriction : Global → LocalFamily) (gluingQuotient : Global → Glue)
    (localData : LocalFamily) : Prop :=
  ∃ global₁ global₂,
    restriction global₁ = localData ∧ restriction global₂ = localData ∧
      gluingQuotient global₁ ≠ gluingQuotient global₂

/-- Local data determine a unique global gluing class. -/
def UniqueGlobalTopology {Global LocalFamily Glue : Type}
    (restriction : Global → LocalFamily) (gluingQuotient : Global → Glue)
    (localData : LocalFamily) : Prop :=
  ∃ global, restriction global = localData ∧
    ∀ global', restriction global' = localData →
      gluingQuotient global' = gluingQuotient global

/-- A selected topology is an extra selected global gluing class compatible
with the local data. -/
def SelectedTopology {Global LocalFamily Glue : Type}
    (restriction : Global → LocalFamily) (gluingQuotient : Global → Glue)
    (localData : LocalFamily) (selected : Glue) (selectorStatus : Prop) : Prop :=
  selectorStatus ∧ ∃ global, restriction global = localData ∧
    gluingQuotient global = selected

/-- Topology transport descends when the target gluing class after transport is
determined by the source gluing class. -/
def TopologyTransportDescends {Global Glue Global' Glue' : Type}
    (sourceGlue : Global → Glue) (transport : Global → Global')
    (targetGlue : Global' → Glue') : Prop :=
  Descends sourceGlue transport targetGlue

/-- Topology transport obstruction. -/
def TopologyTransportObstruction {Global Glue Global' Glue' : Type}
    (sourceGlue : Global → Glue) (transport : Global → Global')
    (targetGlue : Global' → Glue') : (Global × Global) → Prop :=
  splitPairObstruction sourceGlue transport targetGlue

/-- No topology transport obstruction is present. -/
def TopologyTransportObstructionEmpty {Global Glue Global' Glue' : Type}
    (sourceGlue : Global → Glue) (transport : Global → Global')
    (targetGlue : Global' → Glue') : Prop :=
  ObstructionEmpty (TopologyTransportObstruction sourceGlue transport targetGlue)

/-- Topology is preserved when the transport leaves the gluing quotient value
unchanged. -/
def TopologyPreserved {Global Glue : Type} (gluingQuotient : Global → Glue)
    (transport : Global → Global) : Prop :=
  ∀ global, gluingQuotient (transport global) = gluingQuotient global

/-- Topology changes lawfully when gluing transport descends and some gluing
class changes. -/
def LawfulTopologyChange {Global Glue Global' Glue' : Type}
    (sourceGlue : Global → Glue) (transport : Global → Global')
    (targetGlue : Global' → Glue') (Changed : Glue → Glue' → Prop) : Prop :=
  TopologyTransportDescends sourceGlue transport targetGlue ∧
    ∃ global, Changed (sourceGlue global) (targetGlue (transport global))

/-- Source status vocabulary for topology claims. -/
inductive TopologyStatus where
  | topologicalInvariant
  | completeTopologicalInvariant
  | coarseTopologicalInvariant
  | localInvariantOnly
  | globalGluingObstructed
  | topologyModuli
  | uniqueGlobalTopology
  | selectedTopology
  | hiddenTopology
  | probabilisticTopology
  | topologyChange
  | topologyPreserved
  | singularTopologyChange
  | emergentTopology
  | topologyPresentationArtifact
  | protocolGluingArtifact
  | topologyRoleMismatch
  | topologyOverread
deriving DecidableEq

/-- Meaning assignment for the F48 topology status vocabulary. -/
def TopologyStatusHolds (topological complete coarse localOnly obstructed moduli
    unique selected hidden probabilistic change preserved singular emergent
    presentationArtifact protocolArtifact roleMismatch overread : Prop) :
    TopologyStatus → Prop
  | TopologyStatus.topologicalInvariant => topological
  | TopologyStatus.completeTopologicalInvariant => complete
  | TopologyStatus.coarseTopologicalInvariant => coarse
  | TopologyStatus.localInvariantOnly => localOnly
  | TopologyStatus.globalGluingObstructed => obstructed
  | TopologyStatus.topologyModuli => moduli
  | TopologyStatus.uniqueGlobalTopology => unique
  | TopologyStatus.selectedTopology => selected
  | TopologyStatus.hiddenTopology => hidden
  | TopologyStatus.probabilisticTopology => probabilistic
  | TopologyStatus.topologyChange => change
  | TopologyStatus.topologyPreserved => preserved
  | TopologyStatus.singularTopologyChange => singular
  | TopologyStatus.emergentTopology => emergent
  | TopologyStatus.topologyPresentationArtifact => presentationArtifact
  | TopologyStatus.protocolGluingArtifact => protocolArtifact
  | TopologyStatus.topologyRoleMismatch => roleMismatch
  | TopologyStatus.topologyOverread => overread

/-- A topological readout descends through the gluing quotient iff the topology
split-pair obstruction is empty. -/
theorem topological_readout_iff_no_obstruction {Global Glue Value : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value)
    (hglue : Function.Surjective gluingQuotient) :
    TopologicalReadout gluingQuotient readout ↔
      TopologyObstructionEmpty gluingQuotient readout :=
  descent_repair_normal_form gluingQuotient (fun global : Global => global)
    readout hglue

/-- Factorization form of topological readout. -/
theorem topological_readout_iff_factorization {Global Glue Value : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value) :
    TopologicalReadout gluingQuotient readout ↔
      ∃ readoutBar : Glue → Value, readoutBar ∘ gluingQuotient = readout := by
  constructor
  · intro htop
    rcases htop with ⟨readoutBar, hreadoutBar⟩
    exact ⟨readoutBar, by simpa [Function.comp] using hreadoutBar⟩
  · intro hfactor
    rcases hfactor with ⟨readoutBar, hreadoutBar⟩
    exact ⟨readoutBar, by simpa [Function.comp] using hreadoutBar⟩

/-- Complete invariant iff descent plus separation of gluing classes. -/
theorem complete_invariant_iff_descent_and_separation {Global Glue Value : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value) :
    CompleteTopologicalInvariant gluingQuotient readout ↔
      TopologicalReadout gluingQuotient readout ∧
        TopologySeparationObstructionEmpty gluingQuotient readout := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Coarse invariant iff descent plus a separation witness. -/
theorem coarse_invariant_iff_descent_and_unseparated {Global Glue Value : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value) :
    CoarseTopologicalInvariant gluingQuotient readout ↔
      TopologicalReadout gluingQuotient readout ∧
        ∃ pair, TopologySeparationObstruction gluingQuotient readout pair := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Topology transport descends iff no topology-transport obstruction is
present. -/
theorem topology_transport_descends_iff_no_obstruction
    {Global Glue Global' Glue' : Type} (sourceGlue : Global → Glue)
    (transport : Global → Global') (targetGlue : Global' → Glue')
    (hsource : Function.Surjective sourceGlue) :
    TopologyTransportDescends sourceGlue transport targetGlue ↔
      TopologyTransportObstructionEmpty sourceGlue transport targetGlue :=
  descent_repair_normal_form sourceGlue transport targetGlue hsource

/-- Preserved topology gives a descended transport on the same gluing quotient. -/
theorem topology_preserved_descends {Global Glue : Type}
    (gluingQuotient : Global → Glue) (transport : Global → Global)
    (hpreserved : TopologyPreserved gluingQuotient transport) :
    TopologyTransportDescends gluingQuotient transport gluingQuotient := by
  refine ⟨fun glue => glue, ?_⟩
  funext global
  exact (hpreserved global).symm

/--
Topology as Global Gluing Invariant Normal Form. A readout is topological
exactly when it descends through the declared global gluing quotient; complete
classification additionally requires separation of all gluing classes; and
topology transport/change is lawful exactly when gluing-class transport
descends.
-/
theorem topology_global_gluing_invariant {Global Glue Value Global' Glue' : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value)
    (transport : Global → Global') (targetGlue : Global' → Glue')
    (hglue : Function.Surjective gluingQuotient) :
    (TopologicalReadout gluingQuotient readout ↔
      TopologyObstructionEmpty gluingQuotient readout) ∧
      (CompleteTopologicalInvariant gluingQuotient readout ↔
        TopologicalReadout gluingQuotient readout ∧
          TopologySeparationObstructionEmpty gluingQuotient readout) ∧
        (CoarseTopologicalInvariant gluingQuotient readout ↔
          TopologicalReadout gluingQuotient readout ∧
            ∃ pair, TopologySeparationObstruction gluingQuotient readout pair) ∧
          (TopologyTransportDescends gluingQuotient transport targetGlue ↔
            TopologyTransportObstructionEmpty gluingQuotient transport targetGlue) := by
  exact ⟨topological_readout_iff_no_obstruction gluingQuotient readout hglue,
    complete_invariant_iff_descent_and_separation gluingQuotient readout,
    coarse_invariant_iff_descent_and_unseparated gluingQuotient readout,
    topology_transport_descends_iff_no_obstruction gluingQuotient transport
      targetGlue hglue⟩

/-- Every descending topological readout is exactly one of complete and
coarse, according to whether it separates gluing classes. -/
theorem topological_readout_complete_coarse_dichotomy
    {Global Glue Value : Type} (gluingQuotient : Global → Glue)
    (readout : Global → Value) :
    (TopologicalReadout gluingQuotient readout ↔
      CompleteTopologicalInvariant gluingQuotient readout ∨
        CoarseTopologicalInvariant gluingQuotient readout) ∧
    ¬ (CompleteTopologicalInvariant gluingQuotient readout ∧
      CoarseTopologicalInvariant gluingQuotient readout) := by
  classical
  constructor
  · constructor
    · intro htop
      by_cases hsep : TopologySeparationObstructionEmpty gluingQuotient readout
      · exact Or.inl ⟨htop, hsep⟩
      · right
        refine ⟨htop, Classical.byContradiction (fun hnone => ?_)⟩
        apply hsep
        intro pair hobs
        exact hnone ⟨pair, hobs⟩
    · rintro (⟨htop, _⟩ | ⟨htop, _⟩) <;> exact htop
  · rintro ⟨⟨_, hsep⟩, ⟨_, pair, hobs⟩⟩
    exact hsep pair hobs

/-- F48 obstruction and transport tests with the exhaustive, exclusive
complete/coarse classification. -/
theorem topology_global_gluing_invariant_paper
    {Global Glue Value Global' Glue' : Type}
    (gluingQuotient : Global → Glue) (readout : Global → Value)
    (transport : Global → Global') (targetGlue : Global' → Glue')
    (hglue : Function.Surjective gluingQuotient) :
    ((TopologicalReadout gluingQuotient readout ↔
      TopologyObstructionEmpty gluingQuotient readout) ∧
      (CompleteTopologicalInvariant gluingQuotient readout ↔
        TopologicalReadout gluingQuotient readout ∧
          TopologySeparationObstructionEmpty gluingQuotient readout) ∧
      (CoarseTopologicalInvariant gluingQuotient readout ↔
        TopologicalReadout gluingQuotient readout ∧
          ∃ pair, TopologySeparationObstruction gluingQuotient readout pair) ∧
      (TopologyTransportDescends gluingQuotient transport targetGlue ↔
        TopologyTransportObstructionEmpty gluingQuotient transport targetGlue)) ∧
    (TopologicalReadout gluingQuotient readout ↔
      CompleteTopologicalInvariant gluingQuotient readout ∨
        CoarseTopologicalInvariant gluingQuotient readout) ∧
    ¬ (CompleteTopologicalInvariant gluingQuotient readout ∧
      CoarseTopologicalInvariant gluingQuotient readout) := by
  exact ⟨topology_global_gluing_invariant gluingQuotient readout transport
      targetGlue hglue,
    (topological_readout_complete_coarse_dichotomy gluingQuotient readout).1,
    (topological_readout_complete_coarse_dichotomy gluingQuotient readout).2⟩

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Topology
