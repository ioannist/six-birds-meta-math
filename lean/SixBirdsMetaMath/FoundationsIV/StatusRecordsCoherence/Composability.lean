import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
import Mathlib.Logic.ExistsUnique

/-!
F28 Composability.

Parts compose when the joint admissibility relation, composite outcome, and
declared cross-residuals all factor through the parts' object quotients and
interface quotients. Hidden interior coupling is exactly a failure of this
descent.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.Composability

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- The declared two-part source quotient carrying each part object and
interface class. -/
def partInterfaceQuotient {XA XB QA IA QB IB : Type} (qA : XA → QA)
    (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB) :
    XA × XB → (QA × IA) × (QB × IB) :=
  fun pair => ((qA pair.1, betaA pair.1), (qB pair.2, betaB pair.2))

/-- Target-visible composite outcome. -/
def compositeTarget {XA XB XAB QAB : Type} (U : XA × XB → XAB)
    (qAB : XAB → QAB) : XA × XB → QAB :=
  fun pair => qAB (U pair)

/-- Generic descent through the part/interface quotient. -/
def PartInterfaceDescends {XA XB QA IA QB IB Data : Type} (qA : XA → QA)
    (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (data : XA × XB → Data) : Prop :=
  Descends (partInterfaceQuotient qA betaA qB betaB)
    (fun pair : XA × XB => pair) data

/-- Explicit same-part/interface, different-data split obstruction. -/
def PartInterfaceObstruction {XA XB QA IA QB IB Data : Type} (qA : XA → QA)
    (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (data : XA × XB → Data) : (XA × XB) × (XA × XB) → Prop :=
  fun pair =>
    qA pair.1.1 = qA pair.2.1 ∧
      betaA pair.1.1 = betaA pair.2.1 ∧
        qB pair.1.2 = qB pair.2.2 ∧
          betaB pair.1.2 = betaB pair.2.2 ∧ data pair.1 ≠ data pair.2

/-- No part/interface obstruction is present. -/
def PartInterfaceObstructionEmpty {XA XB QA IA QB IB Data : Type} (qA : XA → QA)
    (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (data : XA × XB → Data) : Prop :=
  ObstructionEmpty (PartInterfaceObstruction qA betaA qB betaB data)

/-- Composite outcome descends through the part/interface quotient. -/
def CompositeOutcomeDescends {XA XB QA IA QB IB XAB QAB : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (U : XA × XB → XAB) (qAB : XAB → QAB) : Prop :=
  PartInterfaceDescends qA betaA qB betaB (compositeTarget U qAB)

/-- Composite outcome obstruction. -/
def CompositeOutcomeObstruction {XA XB QA IA QB IB XAB QAB : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (U : XA × XB → XAB) (qAB : XAB → QAB) :
    (XA × XB) × (XA × XB) → Prop :=
  PartInterfaceObstruction qA betaA qB betaB (compositeTarget U qAB)

/-- No composite outcome obstruction is present. -/
def CompositeOutcomeObstructionEmpty {XA XB QA IA QB IB XAB QAB : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (U : XA × XB → XAB) (qAB : XAB → QAB) : Prop :=
  ObstructionEmpty (CompositeOutcomeObstruction qA betaA qB betaB U qAB)

/-- A declared cross-residual factors through part/interface quotients. -/
def CrossResidualDescends {XA XB QA IA QB IB Residual : Type} (qA : XA → QA)
    (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (residual : XA × XB → Residual) : Prop :=
  PartInterfaceDescends qA betaA qB betaB residual

/-- Cross-residual obstruction. -/
def CrossResidualObstruction {XA XB QA IA QB IB Residual : Type} (qA : XA → QA)
    (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (residual : XA × XB → Residual) : (XA × XB) × (XA × XB) → Prop :=
  PartInterfaceObstruction qA betaA qB betaB residual

/-- No cross-residual obstruction is present. -/
def CrossResidualObstructionEmpty {XA XB QA IA QB IB Residual : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (residual : XA × XB → Residual) : Prop :=
  ObstructionEmpty (CrossResidualObstruction qA betaA qB betaB residual)

/-- The raw admissibility relation descends through part/interface quotients. -/
def AdmissibilityDescends {XA XB QA IA QB IB : Type} (qA : XA → QA)
    (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (admissible : XA × XB → Prop) : Prop :=
  PartInterfaceDescends qA betaA qB betaB admissible

/-- Admissibility obstruction. -/
def AdmissibilityObstruction {XA XB QA IA QB IB : Type} (qA : XA → QA)
    (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (admissible : XA × XB → Prop) : (XA × XB) × (XA × XB) → Prop :=
  PartInterfaceObstruction qA betaA qB betaB admissible

/-- No admissibility obstruction is present. -/
def AdmissibilityObstructionEmpty {XA XB QA IA QB IB : Type} (qA : XA → QA)
    (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (admissible : XA × XB → Prop) : Prop :=
  ObstructionEmpty (AdmissibilityObstruction qA betaA qB betaB admissible)

/-- Exact composability: admissibility, composite outcome, and declared
cross-residual all descend through the same part/interface quotient. -/
def ExactComposable {XA XB QA IA QB IB XAB QAB Residual : Type} (qA : XA → QA)
    (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (U : XA × XB → XAB) (qAB : XAB → QAB) (admissible : XA × XB → Prop)
    (residual : XA × XB → Residual) : Prop :=
  AdmissibilityDescends qA betaA qB betaB admissible ∧
    CompositeOutcomeDescends qA betaA qB betaB U qAB ∧
      CrossResidualDescends qA betaA qB betaB residual

/-- The obstruction-empty side of exact composability. -/
def ComposabilityObstructionsEmpty {XA XB QA IA QB IB XAB QAB Residual : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (U : XA × XB → XAB) (qAB : XAB → QAB) (admissible : XA × XB → Prop)
    (residual : XA × XB → Residual) : Prop :=
  AdmissibilityObstructionEmpty qA betaA qB betaB admissible ∧
    CompositeOutcomeObstructionEmpty qA betaA qB betaB U qAB ∧
      CrossResidualObstructionEmpty qA betaA qB betaB residual

/-- A joint repair record carries the declared part/interface source data and a
target datum that failed to factor through it. -/
def jointCompositionRecord {XA XB QA IA QB IB Data : Type} (qA : XA → QA)
    (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (data : XA × XB → Data) : XA × XB → ((QA × IA) × (QB × IB)) × Data :=
  fun pair => (partInterfaceQuotient qA betaA qB betaB pair, data pair)

/-- Associativity of two quotient-level composites. -/
def AssociativeComposition {Input Output : Type} (left right : Input → Output) :
    Prop :=
  ∀ input, left input = right input

/-- Associativity obstruction. -/
def AssociativityObstruction {Input Output : Type} (left right : Input → Output) :
    Input → Prop :=
  fun input => left input ≠ right input

/-- No associativity obstruction is present. -/
def AssociativityObstructionEmpty {Input Output : Type} (left right : Input → Output) :
    Prop :=
  ObstructionEmpty (AssociativityObstruction left right)

/-- A neutral/identity component is identity-like at quotient level. -/
def IdentityComponent {A E : Type} (compose : A × E → A) (neutral : E) : Prop :=
  ∀ a, compose (a, neutral) = a

/-- Identity component obstruction. -/
def IdentityComponentObstruction {A E : Type} (compose : A × E → A)
    (neutral : E) : A → Prop :=
  fun a => compose (a, neutral) ≠ a

/-- No identity component obstruction is present. -/
def IdentityComponentObstructionEmpty {A E : Type} (compose : A × E → A)
    (neutral : E) : Prop :=
  ObstructionEmpty (IdentityComponentObstruction compose neutral)

/-- Source status vocabulary for composition claims. -/
inductive ComposabilityStatus where
  | exactComposable
  | independentProduct
  | interfaceMediatedComposition
  | admissibilityMismatch
  | hiddenInteriorCoupling
  | unmediatedCrossResidual
  | coarsenedComposable
  | bridgeMediatedComposition
  | budgetedComposition
  | localComposition
  | nonassociativeComposition
  | protocolSupportedComposition
  | compositionOverread
deriving DecidableEq

/-- Meaning assignment for F28 composability statuses. -/
def ComposabilityStatusHolds (exact independent interfaceMediated admMismatch
    hiddenCoupling xres coarsened bridge budgeted localStatus nonassoc protocol
    overread : Prop) : ComposabilityStatus → Prop
  | ComposabilityStatus.exactComposable => exact
  | ComposabilityStatus.independentProduct => independent
  | ComposabilityStatus.interfaceMediatedComposition => interfaceMediated
  | ComposabilityStatus.admissibilityMismatch => admMismatch
  | ComposabilityStatus.hiddenInteriorCoupling => hiddenCoupling
  | ComposabilityStatus.unmediatedCrossResidual => xres
  | ComposabilityStatus.coarsenedComposable => coarsened
  | ComposabilityStatus.bridgeMediatedComposition => bridge
  | ComposabilityStatus.budgetedComposition => budgeted
  | ComposabilityStatus.localComposition => localStatus
  | ComposabilityStatus.nonassociativeComposition => nonassoc
  | ComposabilityStatus.protocolSupportedComposition => protocol
  | ComposabilityStatus.compositionOverread => overread

/-- Generic part/interface descent is exactly absence of the explicit
part/interface split obstruction. The surjectivity hypothesis is deliberately
on the joint quotient `(qA,betaA,qB,betaB)`, not on the four projections
separately. -/
theorem part_interface_descends_iff_no_obstruction {XA XB QA IA QB IB Data : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (data : XA × XB → Data)
    (hsource : Function.Surjective (partInterfaceQuotient qA betaA qB betaB)) :
    PartInterfaceDescends qA betaA qB betaB data ↔
      PartInterfaceObstructionEmpty qA betaA qB betaB data := by
  constructor
  · intro hdesc
    rcases hdesc with ⟨dataBar, hcomm⟩
    intro pair hpair
    rcases pair with ⟨xy, xy'⟩
    rcases xy with ⟨xa, xb⟩
    rcases xy' with ⟨xa', xb'⟩
    rcases hpair with ⟨hqa, hia, hqb, hib, hdata_ne⟩
    have hxy : dataBar ((qA xa, betaA xa), (qB xb, betaB xb)) = data (xa, xb) :=
      congrFun hcomm (xa, xb)
    have hxy' :
        dataBar ((qA xa', betaA xa'), (qB xb', betaB xb')) = data (xa', xb') :=
      congrFun hcomm (xa', xb')
    have hsourceEq :
        ((qA xa, betaA xa), (qB xb, betaB xb)) =
          ((qA xa', betaA xa'), (qB xb', betaB xb')) :=
      Prod.ext (Prod.ext hqa hia) (Prod.ext hqb hib)
    have hdata : data (xa, xb) = data (xa', xb') := by
      calc
        data (xa, xb) = dataBar ((qA xa, betaA xa), (qB xb, betaB xb)) := hxy.symm
        _ = dataBar ((qA xa', betaA xa'), (qB xb', betaB xb')) := by rw [hsourceEq]
        _ = data (xa', xb') := hxy'
    exact hdata_ne hdata
  · intro hempty
    have hsplit :
        ObstructionEmpty
          (splitPairObstruction (partInterfaceQuotient qA betaA qB betaB)
            (fun pair : XA × XB => pair) data) := by
      intro pair hpair
      rcases pair with ⟨xy, xy'⟩
      rcases xy with ⟨xa, xb⟩
      rcases xy' with ⟨xa', xb'⟩
      have hleft :
          (qA xa, betaA xa) = (qA xa', betaA xa') := congrArg Prod.fst hpair.1
      have hright :
          (qB xb, betaB xb) = (qB xb', betaB xb') := congrArg Prod.snd hpair.1
      have hqa : qA xa = qA xa' := congrArg Prod.fst hleft
      have hia : betaA xa = betaA xa' := congrArg Prod.snd hleft
      have hqb : qB xb = qB xb' := congrArg Prod.fst hright
      have hib : betaB xb = betaB xb' := congrArg Prod.snd hright
      exact hempty ((xa, xb), (xa', xb')) ⟨hqa, hia, hqb, hib, hpair.2⟩
    exact
      (descent_repair_normal_form (partInterfaceQuotient qA betaA qB betaB)
        (fun pair : XA × XB => pair) data hsource).2 hsplit

/-- Composite outcome factors through the declared part/interface quotient iff
its composability obstruction is empty. -/
theorem composite_outcome_descends_iff_no_obstruction
    {XA XB QA IA QB IB XAB QAB : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (U : XA × XB → XAB) (qAB : XAB → QAB)
    (hsource : Function.Surjective (partInterfaceQuotient qA betaA qB betaB)) :
    CompositeOutcomeDescends qA betaA qB betaB U qAB ↔
      CompositeOutcomeObstructionEmpty qA betaA qB betaB U qAB :=
  part_interface_descends_iff_no_obstruction qA betaA qB betaB
    (compositeTarget U qAB) hsource

/-- Cross-residual factorization criterion. -/
theorem cross_residual_descends_iff_no_obstruction
    {XA XB QA IA QB IB Residual : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (residual : XA × XB → Residual)
    (hsource : Function.Surjective (partInterfaceQuotient qA betaA qB betaB)) :
    CrossResidualDescends qA betaA qB betaB residual ↔
      CrossResidualObstructionEmpty qA betaA qB betaB residual :=
  part_interface_descends_iff_no_obstruction qA betaA qB betaB residual hsource

/-- Admissibility relation factorization criterion. -/
theorem admissibility_descends_iff_no_obstruction {XA XB QA IA QB IB : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (admissible : XA × XB → Prop)
    (hsource : Function.Surjective (partInterfaceQuotient qA betaA qB betaB)) :
    AdmissibilityDescends qA betaA qB betaB admissible ↔
      AdmissibilityObstructionEmpty qA betaA qB betaB admissible :=
  part_interface_descends_iff_no_obstruction qA betaA qB betaB admissible hsource

/-- Exact composability is exactly simultaneous absence of admissibility,
composite-outcome, and cross-residual obstructions. -/
theorem exact_composable_iff_obstructions_empty
    {XA XB QA IA QB IB XAB QAB Residual : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (U : XA × XB → XAB) (qAB : XAB → QAB) (admissible : XA × XB → Prop)
    (residual : XA × XB → Residual)
    (hsource : Function.Surjective (partInterfaceQuotient qA betaA qB betaB)) :
    ExactComposable qA betaA qB betaB U qAB admissible residual ↔
      ComposabilityObstructionsEmpty qA betaA qB betaB U qAB admissible residual := by
  constructor
  · intro hcomp
    exact ⟨(admissibility_descends_iff_no_obstruction qA betaA qB betaB admissible
        hsource).1 hcomp.1,
      (composite_outcome_descends_iff_no_obstruction qA betaA qB betaB U qAB
        hsource).1 hcomp.2.1,
      (cross_residual_descends_iff_no_obstruction qA betaA qB betaB residual
        hsource).1 hcomp.2.2⟩
  · intro hobs
    exact ⟨(admissibility_descends_iff_no_obstruction qA betaA qB betaB admissible
        hsource).2 hobs.1,
      (composite_outcome_descends_iff_no_obstruction qA betaA qB betaB U qAB
        hsource).2 hobs.2.1,
      (cross_residual_descends_iff_no_obstruction qA betaA qB betaB residual
        hsource).2 hobs.2.2⟩

/-- The joint composition repair retains the declared part/interface quotient. -/
theorem joint_record_retains_part_interface {XA XB QA IA QB IB Data : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (data : XA × XB → Data) :
    Descends (jointCompositionRecord qA betaA qB betaB data)
      (fun pair : XA × XB => pair) (partInterfaceQuotient qA betaA qB betaB) := by
  refine ⟨Prod.fst, ?_⟩
  funext pair
  rfl

/-- The joint composition repair carries the previously nonfactored datum. -/
theorem joint_record_carries_data {XA XB QA IA QB IB Data : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (data : XA × XB → Data) :
    Descends (jointCompositionRecord qA betaA qB betaB data)
      (fun pair : XA × XB => pair) data := by
  refine ⟨Prod.snd, ?_⟩
  funext pair
  rfl

/-- Associativity is exactly absence of associativity obstruction. -/
theorem associative_iff_no_obstruction {Input Output : Type} (left right : Input → Output) :
    AssociativeComposition left right ↔ AssociativityObstructionEmpty left right := by
  constructor
  · intro hassoc input hobs
    exact hobs (hassoc input)
  · intro hempty input
    exact Classical.byContradiction (fun hneq => hempty input hneq)

/-- Identity component criterion. -/
theorem identity_component_iff_no_obstruction {A E : Type} (compose : A × E → A)
    (neutral : E) :
    IdentityComponent compose neutral ↔ IdentityComponentObstructionEmpty compose neutral := by
  constructor
  · intro hid a hobs
    exact hobs (hid a)
  · intro hempty a
    exact Classical.byContradiction (fun hneq => hempty a hneq)

/--
Composability Normal Form. Two formed parts compose at the declared interfaces
exactly when admissibility, composite outcome, and declared cross-residuals all
descend through the common part/interface quotient. Associativity and identity
are separate quotient-level coherence gates, and a joint record repairs a
missing factored datum by carrying both the old interface and the datum.
-/
theorem composability {XA XB QA IA QB IB XAB QAB Residual AssocInput AssocOutput A E : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB) (betaB : XB → IB)
    (U : XA × XB → XAB) (qAB : XAB → QAB) (admissible : XA × XB → Prop)
    (residual : XA × XB → Residual) (left right : AssocInput → AssocOutput)
    (identityCompose : A × E → A) (neutral : E)
    (hsource : Function.Surjective (partInterfaceQuotient qA betaA qB betaB)) :
    (CompositeOutcomeDescends qA betaA qB betaB U qAB ↔
      CompositeOutcomeObstructionEmpty qA betaA qB betaB U qAB) ∧
      (CrossResidualDescends qA betaA qB betaB residual ↔
        CrossResidualObstructionEmpty qA betaA qB betaB residual) ∧
        (AdmissibilityDescends qA betaA qB betaB admissible ↔
          AdmissibilityObstructionEmpty qA betaA qB betaB admissible) ∧
          (ExactComposable qA betaA qB betaB U qAB admissible residual ↔
            ComposabilityObstructionsEmpty qA betaA qB betaB U qAB admissible residual) ∧
            Descends (jointCompositionRecord qA betaA qB betaB (compositeTarget U qAB))
              (fun pair : XA × XB => pair) (partInterfaceQuotient qA betaA qB betaB) ∧
              Descends (jointCompositionRecord qA betaA qB betaB (compositeTarget U qAB))
                (fun pair : XA × XB => pair) (compositeTarget U qAB) ∧
                (AssociativeComposition left right ↔ AssociativityObstructionEmpty left right) ∧
                  (IdentityComponent identityCompose neutral ↔
                    IdentityComponentObstructionEmpty identityCompose neutral) := by
  exact ⟨composite_outcome_descends_iff_no_obstruction qA betaA qB betaB U qAB
      hsource,
    cross_residual_descends_iff_no_obstruction qA betaA qB betaB residual hsource,
    admissibility_descends_iff_no_obstruction qA betaA qB betaB admissible hsource,
    exact_composable_iff_obstructions_empty qA betaA qB betaB U qAB admissible
      residual hsource,
    joint_record_retains_part_interface qA betaA qB betaB (compositeTarget U qAB),
    joint_record_carries_data qA betaA qB betaB (compositeTarget U qAB),
    associative_iff_no_obstruction left right,
    identity_component_iff_no_obstruction identityCompose neutral⟩


/-- Descent through the joint part/interface quotient is pointwise factorization. -/
theorem part_interface_descends_iff_pointwise_factorization
    {XA XB QA IA QB IB Data : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB)
    (betaB : XB → IB) (data : XA × XB → Data) :
    PartInterfaceDescends qA betaA qB betaB data ↔
      ∃ lower : (QA × IA) × (QB × IB) → Data,
        ∀ a b, lower (partInterfaceQuotient qA betaA qB betaB (a,b)) =
          data (a,b) := by
  constructor
  · rintro ⟨lower,hcomm⟩
    exact ⟨lower,fun a b => congrFun hcomm (a,b)⟩
  · rintro ⟨lower,hpoint⟩
    refine ⟨lower,?_⟩
    funext pair
    exact hpoint pair.1 pair.2

/-- Paper composability uses the same joint part/interface quotient for all data. -/
theorem paper_composability
    {XA XB QA IA QB IB XAB QAB D Y Y' Z E : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB)
    (betaB : XB → IB) (U : XA × XB → XAB) (qAB : XAB → QAB)
    (Adm : XA × XB → Prop) (delta : XA × XB → D)
    (left right : Y → Y') (compose : Z × E → Z) (neutral : E)
    (hκ : Function.Surjective (partInterfaceQuotient qA betaA qB betaB)) :
    (CompositeOutcomeDescends qA betaA qB betaB U qAB ↔
      CompositeOutcomeObstructionEmpty qA betaA qB betaB U qAB) ∧
    (CompositeOutcomeDescends qA betaA qB betaB U qAB ↔
      ∃ Ubar : (QA × IA) × (QB × IB) → QAB,
        ∀ a b, Ubar (partInterfaceQuotient qA betaA qB betaB (a,b)) =
          qAB (U (a,b))) ∧
    (CrossResidualDescends qA betaA qB betaB delta ↔
      CrossResidualObstructionEmpty qA betaA qB betaB delta) ∧
    (AdmissibilityDescends qA betaA qB betaB Adm ↔
      AdmissibilityObstructionEmpty qA betaA qB betaB Adm) ∧
    (ExactComposable qA betaA qB betaB U qAB Adm delta ↔
      AdmissibilityObstructionEmpty qA betaA qB betaB Adm ∧
      CompositeOutcomeObstructionEmpty qA betaA qB betaB U qAB ∧
      CrossResidualObstructionEmpty qA betaA qB betaB delta) ∧
    (AssociativeComposition left right ↔
      AssociativityObstructionEmpty left right) ∧
    (IdentityComponent compose neutral ↔
      IdentityComponentObstructionEmpty compose neutral) := by
  exact ⟨composite_outcome_descends_iff_no_obstruction qA betaA qB betaB U qAB hκ,
    part_interface_descends_iff_pointwise_factorization qA betaA qB betaB
      (compositeTarget U qAB),
    cross_residual_descends_iff_no_obstruction qA betaA qB betaB delta hκ,
    admissibility_descends_iff_no_obstruction qA betaA qB betaB Adm hκ,
    exact_composable_iff_obstructions_empty qA betaA qB betaB U qAB Adm delta hκ,
    associative_iff_no_obstruction left right,
    identity_component_iff_no_obstruction compose neutral⟩


/-- Surjectivity of the joint part/interface quotient makes any descended
datum unique on its whole quotient codomain. -/
theorem part_interface_descends_iff_unique_factorization
    {XA XB QA IA QB IB Data : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB)
    (betaB : XB → IB) (data : XA × XB → Data)
    (hκ : Function.Surjective (partInterfaceQuotient qA betaA qB betaB)) :
    PartInterfaceDescends qA betaA qB betaB data ↔
      ∃! lower : (QA × IA) × (QB × IB) → Data,
        ∀ a b, lower (partInterfaceQuotient qA betaA qB betaB (a,b)) =
          data (a,b) := by
  constructor
  · rintro ⟨lower, hcomm⟩
    refine ⟨lower, fun a b => congrFun hcomm (a,b), ?_⟩
    intro lower' hpoint
    funext value
    obtain ⟨⟨a, b⟩, rfl⟩ := hκ value
    exact (hpoint a b).trans (congrFun hcomm (a,b)).symm
  · rintro ⟨lower, hpoint, _⟩
    refine ⟨lower, ?_⟩
    funext pair
    exact hpoint pair.1 pair.2

/-- Full paper composability with unique quotient maps for composite outcome,
cross residual, and admissibility, each equivalent to its empty obstruction. -/
theorem paper_composability_unique
    {XA XB QA IA QB IB XAB QAB D Y Y' Z E : Type}
    (qA : XA → QA) (betaA : XA → IA) (qB : XB → QB)
    (betaB : XB → IB) (U : XA × XB → XAB) (qAB : XAB → QAB)
    (Adm : XA × XB → Prop) (delta : XA × XB → D)
    (left right : Y → Y') (compose : Z × E → Z) (neutral : E)
    (hκ : Function.Surjective (partInterfaceQuotient qA betaA qB betaB)) :
    ((CompositeOutcomeDescends qA betaA qB betaB U qAB ↔
      CompositeOutcomeObstructionEmpty qA betaA qB betaB U qAB) ∧
    (CompositeOutcomeDescends qA betaA qB betaB U qAB ↔
      ∃ Ubar : (QA × IA) × (QB × IB) → QAB,
        ∀ a b, Ubar (partInterfaceQuotient qA betaA qB betaB (a,b)) =
          qAB (U (a,b))) ∧
    (CrossResidualDescends qA betaA qB betaB delta ↔
      CrossResidualObstructionEmpty qA betaA qB betaB delta) ∧
    (AdmissibilityDescends qA betaA qB betaB Adm ↔
      AdmissibilityObstructionEmpty qA betaA qB betaB Adm) ∧
    (ExactComposable qA betaA qB betaB U qAB Adm delta ↔
      AdmissibilityObstructionEmpty qA betaA qB betaB Adm ∧
      CompositeOutcomeObstructionEmpty qA betaA qB betaB U qAB ∧
      CrossResidualObstructionEmpty qA betaA qB betaB delta) ∧
    (AssociativeComposition left right ↔
      AssociativityObstructionEmpty left right) ∧
    (IdentityComponent compose neutral ↔
      IdentityComponentObstructionEmpty compose neutral)) ∧
    (CompositeOutcomeObstructionEmpty qA betaA qB betaB U qAB ↔
      ∃! Ubar : (QA × IA) × (QB × IB) → QAB,
        ∀ a b, Ubar (partInterfaceQuotient qA betaA qB betaB (a,b)) =
          qAB (U (a,b))) ∧
    (CrossResidualObstructionEmpty qA betaA qB betaB delta ↔
      ∃! deltaBar : (QA × IA) × (QB × IB) → D,
        ∀ a b, deltaBar (partInterfaceQuotient qA betaA qB betaB (a,b)) =
          delta (a,b)) ∧
    (AdmissibilityObstructionEmpty qA betaA qB betaB Adm ↔
      ∃! AdmBar : (QA × IA) × (QB × IB) → Prop,
        ∀ a b, AdmBar (partInterfaceQuotient qA betaA qB betaB (a,b)) =
          Adm (a,b)) := by
  refine ⟨paper_composability qA betaA qB betaB U qAB Adm delta
    left right compose neutral hκ, ?_, ?_, ?_⟩
  · exact (composite_outcome_descends_iff_no_obstruction
      qA betaA qB betaB U qAB hκ).symm.trans
        (part_interface_descends_iff_unique_factorization qA betaA qB betaB
          (compositeTarget U qAB) hκ)
  · exact (cross_residual_descends_iff_no_obstruction
      qA betaA qB betaB delta hκ).symm.trans
        (part_interface_descends_iff_unique_factorization qA betaA qB betaB delta hκ)
  · exact (admissibility_descends_iff_no_obstruction
      qA betaA qB betaB Adm hκ).symm.trans
        (part_interface_descends_iff_unique_factorization qA betaA qB betaB Adm hκ)

/-- Descended bracketings are associative exactly when the raw bracketings
have equal target classes. A descended identity is an identity exactly when
its raw update leaves every visible class unchanged. -/
theorem assoc_identity_descent {RawTriple Triple RawOutcome Outcome RawZ Z E : Type}
    (κ3 : RawTriple → Triple) (q' : RawOutcome → Outcome)
    (L P : RawTriple → RawOutcome) (left right : Triple → Outcome)
    (hκ3 : Function.Surjective κ3)
    (hleft : left ∘ κ3 = q' ∘ L) (hright : right ∘ κ3 = q' ∘ P)
    (κZ : RawZ → Z) (ctilde : RawZ → RawZ) (compose : Z × E → Z) (e : E)
    (hκZ : Function.Surjective κZ)
    (hcompose : ∀ x, compose (κZ x, e) = κZ (ctilde x)) :
    (AssociativeComposition left right ↔ q' ∘ L = q' ∘ P) ∧
    (IdentityComponent compose e ↔ κZ ∘ ctilde = κZ) := by
  constructor
  · constructor
    · intro hassoc
      have heq : left = right := funext hassoc
      exact hleft.symm.trans ((congrArg (fun f => f ∘ κ3) heq).trans hright)
    · intro hraw value
      obtain ⟨x, rfl⟩ := hκ3 value
      exact (congrFun hleft x).trans
        ((congrFun hraw x).trans (congrFun hright x).symm)
  · constructor
    · intro hid
      funext x
      exact (hcompose x).symm.trans (hid (κZ x))
    · intro hraw value
      obtain ⟨x, rfl⟩ := hκZ value
      exact (hcompose x).trans (congrFun hraw x)

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.Composability
