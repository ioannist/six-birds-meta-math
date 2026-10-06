import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F33 Horizon Sufficiency / Holographic Compression.

A horizon is modeled as an access cut: the hidden/interior side may be replaced
by a boundary quotient for declared exterior targets exactly when those targets
descend through the product of boundary quotient and exterior quotient.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.HorizonSufficiency

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- The product quotient exposed at the horizon: boundary data together with
the exterior current quotient. -/
def boundaryExteriorQuotient {I B E Q : Type} (boundary : I → B)
    (exterior : E → Q) : I × E → B × Q :=
  fun pair => (boundary pair.1, exterior pair.2)

/-- A single exterior target is horizon-sufficient when it descends through the
boundary/exterior product quotient. -/
def HorizonSufficient {I B E Q T : Type} (boundary : I → B)
    (exterior : E → Q) (target : I × E → T) : Prop :=
  Descends (boundaryExteriorQuotient boundary exterior) (fun pair : I × E => pair)
    target

/-- Horizon split-pair obstruction: same boundary and exterior quotient, but
different exterior-relevant target value. -/
def HorizonObstruction {I B E Q T : Type} (boundary : I → B)
    (exterior : E → Q) (target : I × E → T) : (I × E) × (I × E) → Prop :=
  splitPairObstruction (boundaryExteriorQuotient boundary exterior)
    (fun pair : I × E => pair) target

/-- No horizon split-pair obstruction is present. -/
def HorizonObstructionEmpty {I B E Q T : Type} (boundary : I → B)
    (exterior : E → Q) (target : I × E → T) : Prop :=
  ObstructionEmpty (HorizonObstruction boundary exterior target)

/-- Target-family horizon sufficiency, represented by a joint signature of all
declared exterior targets. -/
def HorizonFamilySufficient {I B E Q Signature : Type} (boundary : I → B)
    (exterior : E → Q) (signature : I × E → Signature) : Prop :=
  HorizonSufficient boundary exterior signature

/-- Target-family obstruction for the joint signature. -/
def HorizonFamilyObstruction {I B E Q Signature : Type} (boundary : I → B)
    (exterior : E → Q) (signature : I × E → Signature) :
    (I × E) × (I × E) → Prop :=
  HorizonObstruction boundary exterior signature

/-- No target-family horizon obstruction is present. -/
def HorizonFamilyObstructionEmpty {I B E Q Signature : Type} (boundary : I → B)
    (exterior : E → Q) (signature : I × E → Signature) : Prop :=
  HorizonObstructionEmpty boundary exterior signature

/-- Dynamic horizon sufficiency: the later exterior quotient of an update
descends through the current boundary/exterior product quotient. -/
def DynamicHorizonSufficient {I B E Q E' Q' : Type} (boundary : I → B)
    (exterior : E → Q) (update : I × E → E') (laterExterior : E' → Q') :
    Prop :=
  Descends (boundaryExteriorQuotient boundary exterior) update laterExterior

/-- Dynamic horizon obstruction for a hidden-side/exterior update. -/
def DynamicHorizonObstruction {I B E Q E' Q' : Type} (boundary : I → B)
    (exterior : E → Q) (update : I × E → E') (laterExterior : E' → Q') :
    (I × E) × (I × E) → Prop :=
  splitPairObstruction (boundaryExteriorQuotient boundary exterior) update laterExterior

/-- No dynamic horizon obstruction is present. -/
def DynamicHorizonObstructionEmpty {I B E Q E' Q' : Type} (boundary : I → B)
    (exterior : E → Q) (update : I × E → E') (laterExterior : E' → Q') :
    Prop :=
  ObstructionEmpty (DynamicHorizonObstruction boundary exterior update laterExterior)

/-- Degenerate isolation: the target ignores the hidden side and is already an
exterior-quotient readout. -/
def InteriorIrrelevant {I E Q T : Type} (exterior : E → Q)
    (target : I × E → T) : Prop :=
  ∃ targetBar : Q → T, ∀ pair, target pair = targetBar (exterior pair.2)

/-- Boundary-hidden residue: raw interior states may differ inside one boundary
fiber. -/
def HiddenInteriorResidue {I B : Type} (boundary : I → B) : Prop :=
  ∃ i i', boundary i = boundary i' ∧ i ≠ i'

/-- The hidden residue is harmless for a declared target when that target is
horizon-sufficient. -/
def HiddenResidueIrrelevantForTarget {I B E Q T : Type} (boundary : I → B)
    (exterior : E → Q) (target : I × E → T) : Prop :=
  HiddenInteriorResidue boundary ∧ HorizonSufficient boundary exterior target

/-- Holographic compression is horizon sufficiency for a declared bulk/interior
target family plus an explicitly supplied compression/size discipline. -/
def HolographicCompression {I B E Q Signature : Type} (boundary : I → B)
    (exterior : E → Q) (signature : I × E → Signature)
    (BoundaryCompression : (I → B) → Prop) : Prop :=
  HorizonFamilySufficient boundary exterior signature ∧ BoundaryCompression boundary

/-- Abstract probabilistic horizon status: deterministic target descent may fail,
but a stable fiber law is supplied at the boundary/exterior quotient. -/
def ProbabilisticHorizon {B Q Law : Type} (fiberLaw : B × Q → Law)
    (Stable : (B × Q → Law) → Prop) : Prop :=
  Stable fiberLaw

/-- Canonical product repair that records the old boundary/exterior quotient
and the missing target value. -/
def horizonPairRepairQuotient {I B E Q T : Type} (boundary : I → B)
    (exterior : E → Q) (target : I × E → T) : I × E → (B × Q) × T :=
  sourceRepairQuotient (boundaryExteriorQuotient boundary exterior)
    (fun pair : I × E => pair) target

/-- Source status vocabulary for horizon claims. -/
inductive HorizonStatus where
  | exactHorizonSufficient
  | interiorIrrelevant
  | transparentBoundary
  | holographicSufficiency
  | partialHorizonSufficiency
  | horizonLeakage
  | boundaryInsufficient
  | exteriorTargetOverreach
  | redundantBoundary
  | hiddenIrrelevantInterior
  | futureTargetSensitivity
  | bridgeMediatedHorizon
  | probabilisticHorizon
  | entropyBearingHorizon
  | localHorizonSufficiency
  | globalHorizonObstructed
  | horizonTransportFailure
  | protocolHorizonArtifact
  | horizonOverread
deriving DecidableEq

/-- Meaning assignment for the F33 horizon status vocabulary. -/
def HorizonStatusHolds (exact isolated transparent holographic partialStatus leakage
    insufficient targetOverreach redundant hiddenIrrelevant futureSensitive bridge
    probabilistic entropy localOnly globalObstructed transportFailure protocol overread :
    Prop) : HorizonStatus → Prop
  | HorizonStatus.exactHorizonSufficient => exact
  | HorizonStatus.interiorIrrelevant => isolated
  | HorizonStatus.transparentBoundary => transparent
  | HorizonStatus.holographicSufficiency => holographic
  | HorizonStatus.partialHorizonSufficiency => partialStatus
  | HorizonStatus.horizonLeakage => leakage
  | HorizonStatus.boundaryInsufficient => insufficient
  | HorizonStatus.exteriorTargetOverreach => targetOverreach
  | HorizonStatus.redundantBoundary => redundant
  | HorizonStatus.hiddenIrrelevantInterior => hiddenIrrelevant
  | HorizonStatus.futureTargetSensitivity => futureSensitive
  | HorizonStatus.bridgeMediatedHorizon => bridge
  | HorizonStatus.probabilisticHorizon => probabilistic
  | HorizonStatus.entropyBearingHorizon => entropy
  | HorizonStatus.localHorizonSufficiency => localOnly
  | HorizonStatus.globalHorizonObstructed => globalObstructed
  | HorizonStatus.horizonTransportFailure => transportFailure
  | HorizonStatus.protocolHorizonArtifact => protocol
  | HorizonStatus.horizonOverread => overread

/-- Single-target Horizon Sufficiency Normal Form. -/
theorem horizon_sufficient_iff_no_obstruction {I B E Q T : Type}
    (boundary : I → B) (exterior : E → Q) (target : I × E → T)
    (hboundaryExterior :
      Function.Surjective (boundaryExteriorQuotient boundary exterior)) :
    HorizonSufficient boundary exterior target ↔
      HorizonObstructionEmpty boundary exterior target :=
  descent_repair_normal_form (boundaryExteriorQuotient boundary exterior)
    (fun pair : I × E => pair) target hboundaryExterior

/-- Factorization form of horizon sufficiency. -/
theorem horizon_sufficient_iff_factorization {I B E Q T : Type}
    (boundary : I → B) (exterior : E → Q) (target : I × E → T) :
    HorizonSufficient boundary exterior target ↔
      ∃ targetBar : B × Q → T,
        targetBar ∘ boundaryExteriorQuotient boundary exterior = target := by
  constructor
  · intro hsuff
    rcases hsuff with ⟨targetBar, htargetBar⟩
    exact ⟨targetBar, by simpa [Function.comp] using htargetBar⟩
  · intro hfactor
    rcases hfactor with ⟨targetBar, htargetBar⟩
    exact ⟨targetBar, by simpa [Function.comp] using htargetBar⟩

/-- Target-family Horizon Sufficiency Normal Form, using the joint signature. -/
theorem horizon_family_sufficient_iff_no_obstruction {I B E Q Signature : Type}
    (boundary : I → B) (exterior : E → Q) (signature : I × E → Signature)
    (hboundaryExterior :
      Function.Surjective (boundaryExteriorQuotient boundary exterior)) :
    HorizonFamilySufficient boundary exterior signature ↔
      HorizonFamilyObstructionEmpty boundary exterior signature :=
  horizon_sufficient_iff_no_obstruction boundary exterior signature hboundaryExterior

/-- Dynamic Horizon Sufficiency Normal Form. -/
theorem dynamic_horizon_sufficient_iff_no_obstruction {I B E Q E' Q' : Type}
    (boundary : I → B) (exterior : E → Q) (update : I × E → E')
    (laterExterior : E' → Q')
    (hboundaryExterior :
      Function.Surjective (boundaryExteriorQuotient boundary exterior)) :
    DynamicHorizonSufficient boundary exterior update laterExterior ↔
      DynamicHorizonObstructionEmpty boundary exterior update laterExterior :=
  descent_repair_normal_form (boundaryExteriorQuotient boundary exterior) update
    laterExterior hboundaryExterior

/-- The canonical pair repair refines the old boundary/exterior product
quotient. -/
theorem horizon_pair_repair_refines {I B E Q T : Type} (boundary : I → B)
    (exterior : E → Q) (target : I × E → T) :
    SourceRefinement (horizonPairRepairQuotient boundary exterior target)
      (boundaryExteriorQuotient boundary exterior) :=
  source_repair_refines (boundaryExteriorQuotient boundary exterior)
    (fun pair : I × E => pair) target

/-- After canonical repair, the target descends by projecting the stored target
value. -/
theorem horizon_pair_repair_descends {I B E Q T : Type} (boundary : I → B)
    (exterior : E → Q) (target : I × E → T) :
    Descends (horizonPairRepairQuotient boundary exterior target)
      (fun pair : I × E => pair) target :=
  source_repair_descends (boundaryExteriorQuotient boundary exterior)
    (fun pair : I × E => pair) target

/-- Hidden interior residue is target-irrelevant exactly when hidden residue is
present and the target descends through the boundary/exterior quotient. -/
theorem hidden_residue_irrelevant_iff_hidden_and_sufficient {I B E Q T : Type}
    (boundary : I → B) (exterior : E → Q) (target : I × E → T) :
    HiddenResidueIrrelevantForTarget boundary exterior target ↔
      HiddenInteriorResidue boundary ∧ HorizonSufficient boundary exterior target := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
Horizon Sufficiency Normal Form. A boundary quotient is sufficient for a
declared exterior target exactly when the target descends through the
boundary/exterior product quotient, equivalently when the horizon split-pair
obstruction is empty. The same normal form applies to joint target signatures
and dynamic exterior updates.
-/
theorem horizon_sufficiency {I B E Q T Signature E' Q' : Type}
    (boundary : I → B) (exterior : E → Q) (target : I × E → T)
    (signature : I × E → Signature) (update : I × E → E')
    (laterExterior : E' → Q')
    (hboundaryExterior :
      Function.Surjective (boundaryExteriorQuotient boundary exterior)) :
    (HorizonSufficient boundary exterior target ↔
      HorizonObstructionEmpty boundary exterior target) ∧
      (HorizonSufficient boundary exterior target ↔
        ∃ targetBar : B × Q → T,
          targetBar ∘ boundaryExteriorQuotient boundary exterior = target) ∧
        (HorizonFamilySufficient boundary exterior signature ↔
          HorizonFamilyObstructionEmpty boundary exterior signature) ∧
          (DynamicHorizonSufficient boundary exterior update laterExterior ↔
            DynamicHorizonObstructionEmpty boundary exterior update laterExterior) ∧
            SourceRefinement (horizonPairRepairQuotient boundary exterior target)
              (boundaryExteriorQuotient boundary exterior) ∧
              Descends (horizonPairRepairQuotient boundary exterior target)
                (fun pair : I × E => pair) target := by
  exact ⟨horizon_sufficient_iff_no_obstruction boundary exterior target
      hboundaryExterior,
    horizon_sufficient_iff_factorization boundary exterior target,
    horizon_family_sufficient_iff_no_obstruction boundary exterior signature
      hboundaryExterior,
    dynamic_horizon_sufficient_iff_no_obstruction boundary exterior update
      laterExterior hboundaryExterior,
    horizon_pair_repair_refines boundary exterior target,
    horizon_pair_repair_descends boundary exterior target⟩

/-- Family sufficiency is precisely sufficiency of each declared probe, even
when probe codomains vary with the index. -/
theorem horizon_family_sufficient_iff_each_probe
    {I B E Q Sigma : Type} {T : Sigma → Type}
    (boundary : I → B) (exterior : E → Q)
    (t : ∀ σ, I × E → T σ) :
    (∀ σ, HorizonSufficient boundary exterior (t σ)) ↔
      HorizonFamilySufficient boundary exterior (fun x σ => t σ x) := by
  classical
  constructor
  · intro h
    let bar : B × Q → ∀ σ, T σ :=
      fun z σ => Classical.choose (h σ) z
    refine ⟨bar, ?_⟩
    funext x σ
    exact congrFun (Classical.choose_spec (h σ)) x
  · rintro ⟨bar, hbar⟩ σ
    refine ⟨fun z => bar z σ, ?_⟩
    funext x
    exact congrArg (fun f => f σ) (congrFun hbar x)

/-- F33 with the per-probe and bundled-family equivalence. -/
theorem horizon_sufficiency_paper {I B E Q T Signature E' Q' Sigma : Type}
    {Probe : Sigma → Type}
    (boundary : I → B) (exterior : E → Q) (target : I × E → T)
    (signature : I × E → Signature) (update : I × E → E')
    (laterExterior : E' → Q') (probe : ∀ σ, I × E → Probe σ)
    (hboundaryExterior :
      Function.Surjective (boundaryExteriorQuotient boundary exterior)) :
    (HorizonSufficient boundary exterior target ↔
      HorizonObstructionEmpty boundary exterior target) ∧
    (HorizonSufficient boundary exterior target ↔
      ∃ targetBar : B × Q → T,
        targetBar ∘ boundaryExteriorQuotient boundary exterior = target) ∧
    (HorizonFamilySufficient boundary exterior signature ↔
      HorizonFamilyObstructionEmpty boundary exterior signature) ∧
    (DynamicHorizonSufficient boundary exterior update laterExterior ↔
      DynamicHorizonObstructionEmpty boundary exterior update laterExterior) ∧
    SourceRefinement (horizonPairRepairQuotient boundary exterior target)
      (boundaryExteriorQuotient boundary exterior) ∧
    Descends (horizonPairRepairQuotient boundary exterior target)
      (fun pair : I × E => pair) target ∧
    ((∀ σ, HorizonSufficient boundary exterior (probe σ)) ↔
      HorizonFamilySufficient boundary exterior (fun x σ => probe σ x)) := by
  rcases horizon_sufficiency boundary exterior target signature update
      laterExterior hboundaryExterior with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, h4, h5, h6,
    horizon_family_sufficient_iff_each_probe boundary exterior probe⟩

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.HorizonSufficiency
