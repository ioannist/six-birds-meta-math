import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
import Mathlib.Logic.ExistsUnique

/-!
F22 Interface Mediation.

Cross-layer influence is lawful only through a declared interface quotient.
For an internal quotient `q`, outside/interface quotient `beta`, raw update
`U`, and target quotient `q'`, mediation is exactly descent of `q' ∘ U`
through the product quotient `(q, beta)`.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.InterfaceMediation

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- The declared interface source quotient `(x, y) ↦ (q x, beta y)`. -/
def productInterfaceQuotient {X Q Y B : Type} (q : X → Q) (beta : Y → B) :
    X × Y → Q × B :=
  fun pair => (q pair.1, beta pair.2)

/-- The target-visible effect of a raw interaction/update. -/
def interfaceTarget {X Y X' Q' : Type} (U : X × Y → X') (q' : X' → Q') :
    X × Y → Q' :=
  fun pair => q' (U pair)

/-- Interface mediation: the target-visible update descends through
`(q, beta)`. -/
def InterfaceMediated {X Q Y B X' Q' : Type} (q : X → Q) (beta : Y → B)
    (U : X × Y → X') (q' : X' → Q') : Prop :=
  Descends (productInterfaceQuotient q beta) (fun pair : X × Y => pair)
    (interfaceTarget U q')

/-- The source obstruction: same internal class and same interface class, but
different target-visible result. -/
def InterfaceObstruction {X Q Y B X' Q' : Type} (q : X → Q) (beta : Y → B)
    (U : X × Y → X') (q' : X' → Q') :
    ((X × Y) × (X × Y)) → Prop :=
  fun pair =>
    q pair.1.1 = q pair.2.1 ∧ beta pair.1.2 = beta pair.2.2 ∧
      q' (U pair.1) ≠ q' (U pair.2)

/-- No interface obstruction is present. -/
def InterfaceObstructionEmpty {X Q Y B X' Q' : Type} (q : X → Q)
    (beta : Y → B) (U : X × Y → X') (q' : X' → Q') : Prop :=
  ObstructionEmpty (InterfaceObstruction q beta U q')

/-- Outside distinctions invisible to `beta` must not change the target at a
fixed internal state. -/
def BoundaryLeakageObstruction {X Y B X' Q' : Type} (beta : Y → B)
    (U : X × Y → X') (q' : X' → Q') : X × (Y × Y) → Prop :=
  fun item =>
    beta item.2.1 = beta item.2.2 ∧
      q' (U (item.1, item.2.1)) ≠ q' (U (item.1, item.2.2))

/-- No one-sided boundary leakage is present. -/
def BoundaryLeakageAbsent {X Y B X' Q' : Type} (beta : Y → B)
    (U : X × Y → X') (q' : X' → Q') : Prop :=
  ObstructionEmpty (BoundaryLeakageObstruction beta U q')

/-- Internal quotient insufficiency: same internal class at a fixed outside
handle changes the target. -/
def InternalInsufficiencyObstruction {X Q Y X' Q' : Type} (q : X → Q)
    (U : X × Y → X') (q' : X' → Q') : (X × X) × Y → Prop :=
  fun item =>
    q item.1.1 = q item.1.2 ∧
      q' (U (item.1.1, item.2)) ≠ q' (U (item.1.2, item.2))

/-- No internal source insufficiency is present. -/
def InternalInsufficiencyAbsent {X Q Y X' Q' : Type} (q : X → Q)
    (U : X × Y → X') (q' : X' → Q') : Prop :=
  ObstructionEmpty (InternalInsufficiencyObstruction q U q')

/-- A mediated quotient-level update is actively outside-dependent when some
fixed internal class has two interface classes with different outputs. -/
def ActiveMediatedInfluence {Q B Q' : Type} (Ubar : Q × B → Q') : Prop :=
  ∃ q b b' : _, Ubar (q, b) ≠ Ubar (q, b')

/-- The mediated update is externally inert when the interface coordinate does
not affect the quotient-level output. -/
def ExternallyInert {Q B Q' : Type} (Ubar : Q × B → Q') : Prop :=
  ∀ q b b' : _, Ubar (q, b) = Ubar (q, b')

/-- The joint record repair stores both the declared interface class and the
target-visible effect. -/
def jointInterfaceRepair {X Q Y B X' Q' : Type} (q : X → Q) (beta : Y → B)
    (U : X × Y → X') (q' : X' → Q') : X × Y → (Q × B) × Q' :=
  fun pair => (productInterfaceQuotient q beta pair, interfaceTarget U q' pair)

/-- The joint repair retains the original declared interface quotient. -/
def RetainsInterface {X Q Y B E : Type} (q : X → Q) (beta : Y → B)
    (extension : X × Y → E) : Prop :=
  Descends extension (fun pair : X × Y => pair) (productInterfaceQuotient q beta)

/-- The joint repair carries the target-visible effect. -/
def CarriesTarget {X Y E X' Q' : Type} (extension : X × Y → E)
    (U : X × Y → X') (q' : X' → Q') : Prop :=
  Descends extension (fun pair : X × Y => pair) (interfaceTarget U q')

/-- The terminal/no-interface quotient. -/
def terminalInterface {Y : Type} : Y → Unit :=
  fun _ => ()

/-- The terminal target coarsening, used as the degenerate target repair. -/
def terminalTargetCoarsening {X' : Type} : X' → Unit :=
  fun _ => ()

/-- Relation-valued interface quotient on triples `(x, y, x')`. -/
def relationInterfaceQuotient {X Q Y B X' Q' : Type} (q : X → Q)
    (beta : Y → B) (q' : X' → Q') : X × (Y × X') → (Q × B) × Q' :=
  fun item => ((q item.1, beta item.2.1), q' item.2.2)

/-- A relation-valued interface constraint descends through the interface and
target quotients. -/
def RelationInterfaceMediated {X Q Y B X' Q' : Type} (q : X → Q)
    (beta : Y → B) (q' : X' → Q') (C : X × (Y × X') → Prop) : Prop :=
  Descends (relationInterfaceQuotient q beta q')
    (fun item : X × (Y × X') => item) C

/-- Relation-valued split-pair obstruction. -/
def RelationInterfaceObstruction {X Q Y B X' Q' : Type} (q : X → Q)
    (beta : Y → B) (q' : X' → Q') (C : X × (Y × X') → Prop) :
    (X × (Y × X')) × (X × (Y × X')) → Prop :=
  splitPairObstruction (relationInterfaceQuotient q beta q')
    (fun item : X × (Y × X') => item) C

/-- No relation-valued interface obstruction is present. -/
def RelationInterfaceObstructionEmpty {X Q Y B X' Q' : Type} (q : X → Q)
    (beta : Y → B) (q' : X' → Q') (C : X × (Y × X') → Prop) : Prop :=
  ObstructionEmpty (RelationInterfaceObstruction q beta q' C)

/-- Joint two-sided output quotient for an update of both sides. -/
def twoSidedInterfaceTarget {X Y X' Q' Y' B' : Type} (U : X × Y → X')
    (V : X × Y → Y') (q' : X' → Q') (beta' : Y' → B') :
    X × Y → Q' × B' :=
  fun pair => (q' (U pair), beta' (V pair))

/-- Two-sided interface mediation: both visible outputs factor through the
same input interface quotient `(q, beta)`. -/
def TwoSidedInterfaceMediated {X Q Y B X' Q' Y' B' : Type} (q : X → Q)
    (beta : Y → B) (U : X × Y → X') (V : X × Y → Y')
    (q' : X' → Q') (beta' : Y' → B') : Prop :=
  Descends (productInterfaceQuotient q beta) (fun pair : X × Y => pair)
    (twoSidedInterfaceTarget U V q' beta')

/-- Two-sided split-pair obstruction. -/
def TwoSidedInterfaceObstruction {X Q Y B X' Q' Y' B' : Type} (q : X → Q)
    (beta : Y → B) (U : X × Y → X') (V : X × Y → Y')
    (q' : X' → Q') (beta' : Y' → B') : (X × Y) × (X × Y) → Prop :=
  splitPairObstruction (productInterfaceQuotient q beta)
    (fun pair : X × Y => pair) (twoSidedInterfaceTarget U V q' beta')

/-- No two-sided interface obstruction is present. -/
def TwoSidedInterfaceObstructionEmpty {X Q Y B X' Q' Y' B' : Type}
    (q : X → Q) (beta : Y → B) (U : X × Y → X') (V : X × Y → Y')
    (q' : X' → Q') (beta' : Y' → B') : Prop :=
  ObstructionEmpty (TwoSidedInterfaceObstruction q beta U V q' beta')

/-- Source status vocabulary for interface mediation claims. -/
inductive InterfaceMediationStatus where
  | exactMediated
  | externallyInert
  | boundaryLeakage
  | internalSourceInsufficient
  | jointInterfaceDefect
  | coarsenedMediatedTarget
  | bridgeMediatedInfluence
  | hiddenInfluence
  | protocolArtifact
  | interfaceAbsent
  | interfaceOverread
deriving DecidableEq

/-- Meaning assignment for the F22 interface status vocabulary. -/
def InterfaceMediationStatusHolds (exact inert boundary internal joint coarsened
    bridge hidden protocol absent overread : Prop) : InterfaceMediationStatus → Prop
  | InterfaceMediationStatus.exactMediated => exact
  | InterfaceMediationStatus.externallyInert => inert
  | InterfaceMediationStatus.boundaryLeakage => boundary
  | InterfaceMediationStatus.internalSourceInsufficient => internal
  | InterfaceMediationStatus.jointInterfaceDefect => joint
  | InterfaceMediationStatus.coarsenedMediatedTarget => coarsened
  | InterfaceMediationStatus.bridgeMediatedInfluence => bridge
  | InterfaceMediationStatus.hiddenInfluence => hidden
  | InterfaceMediationStatus.protocolArtifact => protocol
  | InterfaceMediationStatus.interfaceAbsent => absent
  | InterfaceMediationStatus.interfaceOverread => overread

/-- Product interface quotients are surjective when both component quotient
maps are surjective. -/
theorem product_interface_quotient_surjective {X Q Y B : Type} (q : X → Q)
    (beta : Y → B) (hq : Function.Surjective q)
    (hbeta : Function.Surjective beta) :
    Function.Surjective (productInterfaceQuotient q beta) := by
  intro target
  rcases target with ⟨q0, b0⟩
  rcases hq q0 with ⟨x, hx⟩
  rcases hbeta b0 with ⟨y, hy⟩
  exact ⟨(x, y), Prod.ext hx hy⟩

/-- Interface mediation is exactly absence of the explicit interface
obstruction. -/
theorem interface_mediated_iff_no_obstruction {X Q Y B X' Q' : Type}
    (q : X → Q) (beta : Y → B) (U : X × Y → X') (q' : X' → Q')
    (hq : Function.Surjective q) (hbeta : Function.Surjective beta) :
    InterfaceMediated q beta U q' ↔ InterfaceObstructionEmpty q beta U q' := by
  constructor
  · intro hmediated
    rcases hmediated with ⟨Ubar, hcomm⟩
    intro pair hpair
    rcases pair with ⟨xy, xy'⟩
    rcases xy with ⟨x, y⟩
    rcases xy' with ⟨x', y'⟩
    rcases hpair with ⟨hx, hy, htarget_ne⟩
    have hxy : Ubar (q x, beta y) = q' (U (x, y)) := congrFun hcomm (x, y)
    have hxy' : Ubar (q x', beta y') = q' (U (x', y')) :=
      congrFun hcomm (x', y')
    have htarget : q' (U (x, y)) = q' (U (x', y')) := by
      calc
        q' (U (x, y)) = Ubar (q x, beta y) := hxy.symm
        _ = Ubar (q x', beta y') := by rw [hx, hy]
        _ = q' (U (x', y')) := hxy'
    exact htarget_ne htarget
  · intro hempty
    have hsplit :
        ObstructionEmpty
          (splitPairObstruction (productInterfaceQuotient q beta)
            (fun pair : X × Y => pair) (interfaceTarget U q')) := by
      intro pair hpair
      rcases pair with ⟨xy, xy'⟩
      rcases xy with ⟨x, y⟩
      rcases xy' with ⟨x', y'⟩
      have hx : q x = q x' := congrArg Prod.fst hpair.1
      have hy : beta y = beta y' := congrArg Prod.snd hpair.1
      exact hempty ((x, y), (x', y')) ⟨hx, hy, hpair.2⟩
    exact
      (descent_repair_normal_form (productInterfaceQuotient q beta)
        (fun pair : X × Y => pair) (interfaceTarget U q')
        (product_interface_quotient_surjective q beta hq hbeta)).2 hsplit

/-- Full interface mediation forbids one-sided boundary leakage. -/
theorem interface_empty_implies_boundary_absent {X Q Y B X' Q' : Type}
    (q : X → Q) (beta : Y → B) (U : X × Y → X') (q' : X' → Q') :
    InterfaceObstructionEmpty q beta U q' → BoundaryLeakageAbsent beta U q' := by
  intro hempty item hleak
  rcases item with ⟨x, yy'⟩
  rcases yy' with ⟨y, y'⟩
  exact hempty ((x, y), (x, y')) ⟨rfl, hleak.1, hleak.2⟩

/-- Full interface mediation forbids one-sided internal source
insufficiency. -/
theorem interface_empty_implies_internal_absent {X Q Y B X' Q' : Type}
    (q : X → Q) (beta : Y → B) (U : X × Y → X') (q' : X' → Q') :
    InterfaceObstructionEmpty q beta U q' →
      InternalInsufficiencyAbsent q U q' := by
  intro hempty item hinternal
  rcases item with ⟨xx', y⟩
  rcases xx' with ⟨x, x'⟩
  exact hempty ((x, y), (x', y)) ⟨hinternal.1, rfl, hinternal.2⟩

/-- Active mediated influence is precisely non-inertness of the quotient-level
update. -/
theorem active_mediated_influence_iff_not_inert {Q B Q' : Type}
    (Ubar : Q × B → Q') :
    ActiveMediatedInfluence Ubar ↔ ¬ ExternallyInert Ubar := by
  constructor
  · intro hactive hinert
    rcases hactive with ⟨q, b, b', hne⟩
    exact hne (hinert q b b')
  · intro hnotInert
    classical
    exact Classical.byContradiction (fun hnoActive =>
      hnotInert (fun q b b' =>
        Classical.byContradiction (fun hne =>
          hnoActive ⟨q, b, b', hne⟩)))

/-- The joint interface repair keeps the old interface quotient. -/
theorem joint_repair_retains_interface {X Q Y B X' Q' : Type} (q : X → Q)
    (beta : Y → B) (U : X × Y → X') (q' : X' → Q') :
    RetainsInterface q beta (jointInterfaceRepair q beta U q') := by
  refine ⟨Prod.fst, ?_⟩
  funext pair
  rfl

/-- The joint interface repair carries the target-visible update. -/
theorem joint_repair_carries_target {X Q Y B X' Q' : Type} (q : X → Q)
    (beta : Y → B) (U : X × Y → X') (q' : X' → Q') :
    CarriesTarget (jointInterfaceRepair q beta U q') U q' := by
  refine ⟨Prod.snd, ?_⟩
  funext pair
  rfl

/-- The terminal target coarsening is always mediated. -/
theorem terminal_target_coarsening_mediated {X Q Y B X' : Type} (q : X → Q)
    (beta : Y → B) (U : X × Y → X') :
    InterfaceMediated q beta U (terminalTargetCoarsening : X' → Unit) := by
  refine ⟨fun _ => (), ?_⟩
  funext pair
  rfl

/-- Relation interface quotients are surjective when all component quotients
are surjective. -/
theorem relation_interface_quotient_surjective {X Q Y B X' Q' : Type}
    (q : X → Q) (beta : Y → B) (q' : X' → Q')
    (hq : Function.Surjective q) (hbeta : Function.Surjective beta)
    (hq' : Function.Surjective q') :
    Function.Surjective (relationInterfaceQuotient q beta q') := by
  intro target
  rcases target with ⟨qb, q0'⟩
  rcases qb with ⟨q0, b0⟩
  rcases hq q0 with ⟨x, hx⟩
  rcases hbeta b0 with ⟨y, hy⟩
  rcases hq' q0' with ⟨x', hx'⟩
  exact ⟨(x, (y, x')), by simp [relationInterfaceQuotient, hx, hy, hx']⟩

/-- Relation-valued mediation is exactly relation descent through the
interface quotient. -/
theorem relation_interface_mediated_iff_no_obstruction
    {X Q Y B X' Q' : Type} (q : X → Q) (beta : Y → B) (q' : X' → Q')
    (C : X × (Y × X') → Prop) (hq : Function.Surjective q)
    (hbeta : Function.Surjective beta) (hq' : Function.Surjective q') :
    RelationInterfaceMediated q beta q' C ↔
      RelationInterfaceObstructionEmpty q beta q' C :=
  descent_repair_normal_form (relationInterfaceQuotient q beta q')
    (fun item : X × (Y × X') => item) C
    (relation_interface_quotient_surjective q beta q' hq hbeta hq')

/-- Two-sided interface mediation is exactly absence of the two-sided
split-pair obstruction. -/
theorem two_sided_interface_mediated_iff_no_obstruction
    {X Q Y B X' Q' Y' B' : Type} (q : X → Q) (beta : Y → B)
    (U : X × Y → X') (V : X × Y → Y') (q' : X' → Q') (beta' : Y' → B')
    (hq : Function.Surjective q) (hbeta : Function.Surjective beta) :
    TwoSidedInterfaceMediated q beta U V q' beta' ↔
      TwoSidedInterfaceObstructionEmpty q beta U V q' beta' :=
  descent_repair_normal_form (productInterfaceQuotient q beta)
    (fun pair : X × Y => pair) (twoSidedInterfaceTarget U V q' beta')
    (product_interface_quotient_surjective q beta hq hbeta)

/--
Interface Mediation Normal Form. The target-visible update is mediated by the
declared internal/interface quotient exactly when its interface obstruction is
empty. The theorem also records the one-sided consequences, active/inert
comparison, canonical joint and coarsened repairs, and the relation-valued and
two-sided variants from the source note.
-/
theorem interface_mediation {X Q Y B X' Q' Y' B' : Type} (q : X → Q)
    (beta : Y → B) (U : X × Y → X') (q' : X' → Q')
    (V : X × Y → Y') (beta' : Y' → B') (C : X × (Y × X') → Prop)
    (Ubar : Q × B → Q') (hq : Function.Surjective q)
    (hbeta : Function.Surjective beta) (hq' : Function.Surjective q') :
    (InterfaceMediated q beta U q' ↔ InterfaceObstructionEmpty q beta U q') ∧
      (InterfaceObstructionEmpty q beta U q' → BoundaryLeakageAbsent beta U q') ∧
        (InterfaceObstructionEmpty q beta U q' →
          InternalInsufficiencyAbsent q U q') ∧
          (ActiveMediatedInfluence Ubar ↔ ¬ ExternallyInert Ubar) ∧
            RetainsInterface q beta (jointInterfaceRepair q beta U q') ∧
              CarriesTarget (jointInterfaceRepair q beta U q') U q' ∧
                InterfaceMediated q beta U (terminalTargetCoarsening : X' → Unit) ∧
                  (RelationInterfaceMediated q beta q' C ↔
                    RelationInterfaceObstructionEmpty q beta q' C) ∧
                    (TwoSidedInterfaceMediated q beta U V q' beta' ↔
                      TwoSidedInterfaceObstructionEmpty q beta U V q' beta') := by
  exact ⟨interface_mediated_iff_no_obstruction q beta U q' hq hbeta,
    interface_empty_implies_boundary_absent q beta U q',
    interface_empty_implies_internal_absent q beta U q',
    active_mediated_influence_iff_not_inert Ubar,
    joint_repair_retains_interface q beta U q',
    joint_repair_carries_target q beta U q',
    terminal_target_coarsening_mediated q beta U,
    relation_interface_mediated_iff_no_obstruction q beta q' C hq hbeta hq',
    two_sided_interface_mediated_iff_no_obstruction q beta U V q' beta' hq hbeta⟩

/-- The joint obstruction is empty exactly when both one-coordinate
obstructions are empty. -/
theorem interface_empty_iff_boundary_and_internal_absent
    {X Q Y B X' Q' : Type} (q : X → Q) (beta : Y → B)
    (U : X × Y → X') (q' : X' → Q') :
    InterfaceObstructionEmpty q beta U q' ↔
      BoundaryLeakageAbsent beta U q' ∧ InternalInsufficiencyAbsent q U q' := by
  constructor
  · intro h
    exact ⟨interface_empty_implies_boundary_absent q beta U q' h,
      interface_empty_implies_internal_absent q beta U q' h⟩
  · rintro ⟨hboundary, hinternal⟩ ⟨⟨x,y⟩,⟨x',y'⟩⟩ ⟨hx,hy,hne⟩
    have hby : q' (U (x,y)) = q' (U (x,y')) := by
      exact Classical.byContradiction (fun h =>
        hboundary (x,(y,y')) ⟨hy,h⟩)
    have hix : q' (U (x,y')) = q' (U (x',y')) := by
      exact Classical.byContradiction (fun h =>
        hinternal ((x,x'),y') ⟨hx,h⟩)
    exact hne (hby.trans hix)

/-- F22 with the two one-way absence clauses replaced by their exact converse. -/
theorem paper_interface_mediation_split
    {X Q Y B X' Q' Y' B' : Type} (q : X → Q)
    (beta : Y → B) (U : X × Y → X') (q' : X' → Q')
    (V : X × Y → Y') (beta' : Y' → B') (C : X × (Y × X') → Prop)
    (Ubar : Q × B → Q') (hq : Function.Surjective q)
    (hbeta : Function.Surjective beta) (hq' : Function.Surjective q') :
    (InterfaceMediated q beta U q' ↔ InterfaceObstructionEmpty q beta U q') ∧
      (InterfaceObstructionEmpty q beta U q' ↔
        BoundaryLeakageAbsent beta U q' ∧ InternalInsufficiencyAbsent q U q') ∧
        (ActiveMediatedInfluence Ubar ↔ ¬ ExternallyInert Ubar) ∧
          RetainsInterface q beta (jointInterfaceRepair q beta U q') ∧
            CarriesTarget (jointInterfaceRepair q beta U q') U q' ∧
              InterfaceMediated q beta U (terminalTargetCoarsening : X' → Unit) ∧
                (RelationInterfaceMediated q beta q' C ↔
                  RelationInterfaceObstructionEmpty q beta q' C) ∧
                  (TwoSidedInterfaceMediated q beta U V q' beta' ↔
                    TwoSidedInterfaceObstructionEmpty q beta U V q' beta') := by
  rcases interface_mediation q beta U q' V beta' C Ubar hq hbeta hq' with
    ⟨hmediated, _, _, hactive, hretain, hcarry, hterminal, hrelation, htwo⟩
  exact ⟨hmediated, interface_empty_iff_boundary_and_internal_absent q beta U q',
    hactive, hretain, hcarry, hterminal, hrelation, htwo⟩

/-- Surjectivity of the source and boundary quotients makes the descended
interface update unique on the full product; the target quotient need not be
surjective for this equivalence. -/
theorem interface_mediated_iff_unique_update {X Q Y B X' Q' : Type}
    (q : X → Q) (beta : Y → B) (U : X × Y → X') (q' : X' → Q')
    (hq : Function.Surjective q) (hbeta : Function.Surjective beta) :
    InterfaceMediated q beta U q' ↔
      ∃! lower : Q × B → Q',
        ∀ x y, lower (q x, beta y) = q' (U (x,y)) := by
  constructor
  · rintro ⟨lower, hcomm⟩
    refine ⟨lower, fun x y => congrFun hcomm (x,y), ?_⟩
    intro lower' hpoint
    funext qb
    obtain ⟨⟨x, y⟩, rfl⟩ := product_interface_quotient_surjective q beta hq hbeta qb
    exact (hpoint x y).trans (congrFun hcomm (x,y)).symm
  · rintro ⟨lower, hpoint, _⟩
    refine ⟨lower, ?_⟩
    funext pair
    exact hpoint pair.1 pair.2

/-- Full F22 retains all mediation and repair clauses and strengthens the
quotient-update existence criterion to unique existence. -/
theorem paper_interface_mediation_split_full
    {X Q Y B X' Q' Y' B' : Type} (q : X → Q)
    (beta : Y → B) (U : X × Y → X') (q' : X' → Q')
    (V : X × Y → Y') (beta' : Y' → B') (C : X × (Y × X') → Prop)
    (Ubar : Q × B → Q') (hq : Function.Surjective q)
    (hbeta : Function.Surjective beta) (hq' : Function.Surjective q') :
    ((InterfaceMediated q beta U q' ↔ InterfaceObstructionEmpty q beta U q') ∧
      (InterfaceObstructionEmpty q beta U q' ↔
        BoundaryLeakageAbsent beta U q' ∧ InternalInsufficiencyAbsent q U q') ∧
        (ActiveMediatedInfluence Ubar ↔ ¬ ExternallyInert Ubar) ∧
          RetainsInterface q beta (jointInterfaceRepair q beta U q') ∧
            CarriesTarget (jointInterfaceRepair q beta U q') U q' ∧
              InterfaceMediated q beta U (terminalTargetCoarsening : X' → Unit) ∧
                (RelationInterfaceMediated q beta q' C ↔
                  RelationInterfaceObstructionEmpty q beta q' C) ∧
                  (TwoSidedInterfaceMediated q beta U V q' beta' ↔
                    TwoSidedInterfaceObstructionEmpty q beta U V q' beta')) ∧
    (InterfaceMediated q beta U q' ↔
      ∃! lower : Q × B → Q',
        ∀ x y, lower (q x, beta y) = q' (U (x,y))) ∧
    (InterfaceObstructionEmpty q beta U q' ↔
      ∃! lower : Q × B → Q',
        ∀ x y, lower (q x, beta y) = q' (U (x,y))) := by
  have hcore := paper_interface_mediation_split q beta U q' V beta' C Ubar hq hbeta hq'
  have hunique := interface_mediated_iff_unique_update q beta U q' hq hbeta
  exact ⟨hcore, hunique, hcore.1.symm.trans hunique⟩

/-- Predicate-valued relation descent does not require any quotient to be
surjective: the descended predicate can be false outside the quotient image. -/
theorem relation_interface_mediated_iff_no_obstruction_general
    {X Q Y B X' Q' : Type} (q : X → Q) (beta : Y → B) (q' : X' → Q')
    (C : X × (Y × X') → Prop) :
    RelationInterfaceMediated q beta q' C ↔
      RelationInterfaceObstructionEmpty q beta q' C := by
  constructor
  · rintro ⟨Cbar, hcomm⟩ pair hsplit
    exact hsplit.2 ((congrFun hcomm pair.1).symm.trans
      ((congrArg Cbar hsplit.1).trans (congrFun hcomm pair.2)))
  · intro hempty
    refine ⟨fun value => ∃ item, relationInterfaceQuotient q beta q' item = value ∧
      C item, ?_⟩
    funext item
    apply propext
    constructor
    · rintro ⟨item', hquotient, hC⟩
      have hsame : C item' = C item :=
        Classical.byContradiction (fun hne => hempty (item', item) ⟨hquotient, hne⟩)
      exact Eq.mp hsame hC
    · intro hC
      exact ⟨item, rfl, hC⟩

/-- Full F22, including the repair, relation-valued, and two-sided clauses,
needs only surjective source and boundary maps. Active/inert comparison holds
for every declared quotient update, and mediation gives a unique update. -/
theorem paper_interface_mediation_of_source_boundary_surjective
    {X Q Y B X' Q' Y' B' : Type} (q : X → Q)
    (beta : Y → B) (U : X × Y → X') (q' : X' → Q')
    (V : X × Y → Y') (beta' : Y' → B') (C : X × (Y × X') → Prop)
    (hq : Function.Surjective q) (hbeta : Function.Surjective beta) :
    (InterfaceMediated q beta U q' ↔ InterfaceObstructionEmpty q beta U q') ∧
    (InterfaceObstructionEmpty q beta U q' ↔
      ∃! lower : Q × B → Q',
        ∀ x y, lower (q x, beta y) = q' (U (x,y))) ∧
    (InterfaceMediated q beta U q' ↔
      ∃! lower : Q × B → Q',
        ∀ x y, lower (q x, beta y) = q' (U (x,y))) ∧
    (InterfaceObstructionEmpty q beta U q' ↔
      BoundaryLeakageAbsent beta U q' ∧ InternalInsufficiencyAbsent q U q') ∧
    (∀ Ubar : Q × B → Q',
      ActiveMediatedInfluence Ubar ↔ ¬ ExternallyInert Ubar) ∧
    RetainsInterface q beta (jointInterfaceRepair q beta U q') ∧
    CarriesTarget (jointInterfaceRepair q beta U q') U q' ∧
    InterfaceMediated q beta U (terminalTargetCoarsening : X' → Unit) ∧
    (RelationInterfaceMediated q beta q' C ↔
      RelationInterfaceObstructionEmpty q beta q' C) ∧
    (TwoSidedInterfaceMediated q beta U V q' beta' ↔
      TwoSidedInterfaceObstructionEmpty q beta U V q' beta') := by
  have hmediated := interface_mediated_iff_no_obstruction q beta U q' hq hbeta
  have hunique := interface_mediated_iff_unique_update q beta U q' hq hbeta
  exact ⟨hmediated, hmediated.symm.trans hunique, hunique,
    interface_empty_iff_boundary_and_internal_absent q beta U q',
    fun Ubar => active_mediated_influence_iff_not_inert Ubar,
    joint_repair_retains_interface q beta U q',
    joint_repair_carries_target q beta U q',
    terminal_target_coarsening_mediated q beta U,
    relation_interface_mediated_iff_no_obstruction_general q beta q' C,
    two_sided_interface_mediated_iff_no_obstruction q beta U V q' beta' hq hbeta⟩

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.InterfaceMediation
