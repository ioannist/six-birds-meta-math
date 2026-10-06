import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
import SixBirdsMetaMath.FoundationsIV.Transport.LocalGlobalObstruction

/-!
F41 Duality Equivalence.

Duality is role-preserving equivalence of formed packages: object quotient
translations descend and invert, while roles, transports, claim/statuses,
residual/audit records, source/readout discipline, and local-global gluing are
preserved.
-/

namespace SixBirdsMetaMath.FoundationsIV.Symmetry.DualityEquivalence

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
open SixBirdsMetaMath.FoundationsIV.Transport.LocalGlobalObstruction

/-- A formed package carries the structural slots whose preservation is audited
by a duality claim. The theorem below keeps the operations abstract. -/
structure FormedPackage where
  Carrier : Type
  Quotient : Type
  Route : Type
  Role : Type
  Claim : Type
  Residual : Type
  Status : Type
  SourceReadoutRole : Type
  Instrument : Type
  quotient : Carrier → Quotient

/-- Object translation descends through the source and target quotients. -/
def ObjectTranslationDescends {HA QA HB QB : Type} (qA : HA → QA)
    (F : HA → HB) (qB : HB → QB) : Prop :=
  Descends qA F qB

/-- The object-translation split-pair obstruction. -/
def ObjectTranslationObstruction {HA QA HB QB : Type} (qA : HA → QA)
    (F : HA → HB) (qB : HB → QB) : (HA × HA) → Prop :=
  splitPairObstruction qA F qB

/-- No object-translation obstruction is present. -/
def ObjectTranslationObstructionEmpty {HA QA HB QB : Type} (qA : HA → QA)
    (F : HA → HB) (qB : HB → QB) : Prop :=
  ObstructionEmpty (ObjectTranslationObstruction qA F qB)

/-- The quotient-level translations are inverse equivalences. -/
def QuotientInverseEquivalence {QA QB : Type} (Fbar : QA → QB)
    (Gbar : QB → QA) : Prop :=
  (∀ a : QA, Gbar (Fbar a) = a) ∧ ∀ b : QB, Fbar (Gbar b) = b

/-- Failure of quotient inverse equivalence on either side. -/
def InverseDefect {QA QB : Type} (Fbar : QA → QB) (Gbar : QB → QA) :
    Sum QA QB → Prop
  | Sum.inl a => Gbar (Fbar a) ≠ a
  | Sum.inr b => Fbar (Gbar b) ≠ b

/-- No quotient inverse defect is present. -/
def InverseDefectEmpty {QA QB : Type} (Fbar : QA → QB) (Gbar : QB → QA) :
    Prop :=
  ObstructionEmpty (InverseDefect Fbar Gbar)

/-- A translation preserves typed labels through a declared label map. -/
def LabelPreserved {A B LA LB : Type} (labelA : A → LA)
    (translate : A → B) (labelMap : LA → LB) (labelB : B → LB) : Prop :=
  ∀ x : A, labelB (translate x) = labelMap (labelA x)

/-- Generic typed label mismatch. -/
def LabelMismatch {A B LA LB : Type} (labelA : A → LA)
    (translate : A → B) (labelMap : LA → LB) (labelB : B → LB) :
    A → Prop :=
  fun x => labelB (translate x) ≠ labelMap (labelA x)

/-- No typed label mismatch is present. -/
def LabelMismatchEmpty {A B LA LB : Type} (labelA : A → LA)
    (translate : A → B) (labelMap : LA → LB) (labelB : B → LB) : Prop :=
  ObstructionEmpty (LabelMismatch labelA translate labelMap labelB)

/-- Role preservation is typed label preservation for role registries. -/
def RolePreserved {A B RoleA RoleB : Type} (roleA : A → RoleA)
    (translate : A → B) (roleMap : RoleA → RoleB) (roleB : B → RoleB) :
    Prop :=
  LabelPreserved roleA translate roleMap roleB

/-- Role mismatch obstruction. -/
def RoleMismatch {A B RoleA RoleB : Type} (roleA : A → RoleA)
    (translate : A → B) (roleMap : RoleA → RoleB) (roleB : B → RoleB) :
    A → Prop :=
  LabelMismatch roleA translate roleMap roleB

/-- No role mismatch is present. -/
def RoleMismatchEmpty {A B RoleA RoleB : Type} (roleA : A → RoleA)
    (translate : A → B) (roleMap : RoleA → RoleB) (roleB : B → RoleB) :
    Prop :=
  ObstructionEmpty (RoleMismatch roleA translate roleMap roleB)

/-- Route transport commutes with the quotient translation. -/
def TransportPreserved {QA QB RouteA RouteB : Type} (Fbar : QA → QB)
    (routeA : RouteA → QA → QA) (routeB : RouteB → QB → QB)
    (routeMap : RouteA → RouteB) : Prop :=
  ∀ γ : RouteA, ∀ a : QA, Fbar (routeA γ a) = routeB (routeMap γ) (Fbar a)

/-- Transport commutation obstruction. -/
def TransportMismatch {QA QB RouteA RouteB : Type} (Fbar : QA → QB)
    (routeA : RouteA → QA → QA) (routeB : RouteB → QB → QB)
    (routeMap : RouteA → RouteB) : RouteA × QA → Prop :=
  fun item => Fbar (routeA item.1 item.2) ≠ routeB (routeMap item.1) (Fbar item.2)

/-- No transport mismatch is present. -/
def TransportMismatchEmpty {QA QB RouteA RouteB : Type} (Fbar : QA → QB)
    (routeA : RouteA → QA → QA) (routeB : RouteB → QB → QB)
    (routeMap : RouteA → RouteB) : Prop :=
  ObstructionEmpty (TransportMismatch Fbar routeA routeB routeMap)

/-- Claim/readout status preservation. -/
def ClaimStatusPreserved {ClaimA ClaimB StatusA StatusB : Type}
    (statusA : ClaimA → StatusA) (claimMap : ClaimA → ClaimB)
    (statusMap : StatusA → StatusB) (statusB : ClaimB → StatusB) : Prop :=
  LabelPreserved statusA claimMap statusMap statusB

/-- Claim/readout status mismatch. -/
def ClaimStatusMismatch {ClaimA ClaimB StatusA StatusB : Type}
    (statusA : ClaimA → StatusA) (claimMap : ClaimA → ClaimB)
    (statusMap : StatusA → StatusB) (statusB : ClaimB → StatusB) :
    ClaimA → Prop :=
  LabelMismatch statusA claimMap statusMap statusB

/-- No claim/readout status mismatch is present. -/
def ClaimStatusMismatchEmpty {ClaimA ClaimB StatusA StatusB : Type}
    (statusA : ClaimA → StatusA) (claimMap : ClaimA → ClaimB)
    (statusMap : StatusA → StatusB) (statusB : ClaimB → StatusB) : Prop :=
  ObstructionEmpty (ClaimStatusMismatch statusA claimMap statusMap statusB)

/-- Residual/audit status preservation. -/
def ResidualAuditPreserved {ResA ResB StatusA StatusB : Type}
    (statusA : ResA → StatusA) (residualMap : ResA → ResB)
    (statusMap : StatusA → StatusB) (statusB : ResB → StatusB) : Prop :=
  LabelPreserved statusA residualMap statusMap statusB

/-- Residual/audit status mismatch. -/
def ResidualAuditMismatch {ResA ResB StatusA StatusB : Type}
    (statusA : ResA → StatusA) (residualMap : ResA → ResB)
    (statusMap : StatusA → StatusB) (statusB : ResB → StatusB) : ResA → Prop :=
  LabelMismatch statusA residualMap statusMap statusB

/-- No residual/audit status mismatch is present. -/
def ResidualAuditMismatchEmpty {ResA ResB StatusA StatusB : Type}
    (statusA : ResA → StatusA) (residualMap : ResA → ResB)
    (statusMap : StatusA → StatusB) (statusB : ResB → StatusB) : Prop :=
  ObstructionEmpty (ResidualAuditMismatch statusA residualMap statusMap statusB)

/-- Source/readout role preservation. -/
def SourceReadoutPreserved {X Y SRA SRB : Type} (srA : X → SRA)
    (translate : X → Y) (srMap : SRA → SRB) (srB : Y → SRB) : Prop :=
  LabelPreserved srA translate srMap srB

/-- Source/readout role mismatch. -/
def SourceReadoutMismatch {X Y SRA SRB : Type} (srA : X → SRA)
    (translate : X → Y) (srMap : SRA → SRB) (srB : Y → SRB) : X → Prop :=
  LabelMismatch srA translate srMap srB

/-- No source/readout mismatch is present. -/
def SourceReadoutMismatchEmpty {X Y SRA SRB : Type} (srA : X → SRA)
    (translate : X → Y) (srMap : SRA → SRB) (srB : Y → SRB) : Prop :=
  ObstructionEmpty (SourceReadoutMismatch srA translate srMap srB)

/-- Patchwise duality data globalizes when it lies in the declared global image. -/
def LocalDualityGlobalizes {Global Local : Type} (restrict : Global → Local)
    (localData : Local) : Prop :=
  ∃ global : Global, restrict global = localData

/-- Image-membership spelling of local-global duality gluing. -/
def InGlobalDualityImage {Global Local : Type} (restrict : Global → Local)
    (localData : Local) : Prop :=
  InDeclaredImage restrict localData

/-- Local duality gluing obstruction. -/
def LocalDualityGluingObstruction {Global Local : Type}
    (compatible : Local → Prop) (restrict : Global → Local)
    (localData : Local) : Prop :=
  compatible localData ∧ ¬ LocalDualityGlobalizes restrict localData

/-- Exact duality: the specified quotient maps realize the history translations,
descend both ways, invert on formed
objects, and all role/status/transport/gluing gates pass. -/
def ExactDuality {HA QA HB QB RoleObjA RoleObjB RoleA RoleB RouteA RouteB
    ClaimA ClaimB ClaimStatusA ClaimStatusB ResA ResB ResStatusA ResStatusB
    SourceObjA SourceObjB SRA SRB Global Local : Type}
    (qA : HA → QA) (qB : HB → QB) (F : HA → HB) (G : HB → HA)
    (Fbar : QA → QB) (Gbar : QB → QA)
    (roleA : RoleObjA → RoleA) (roleTranslate : RoleObjA → RoleObjB)
    (roleMap : RoleA → RoleB) (roleB : RoleObjB → RoleB)
    (routeA : RouteA → QA → QA) (routeB : RouteB → QB → QB)
    (routeMap : RouteA → RouteB)
    (claimStatusA : ClaimA → ClaimStatusA) (claimMap : ClaimA → ClaimB)
    (claimStatusMap : ClaimStatusA → ClaimStatusB)
    (claimStatusB : ClaimB → ClaimStatusB)
    (resStatusA : ResA → ResStatusA) (residualMap : ResA → ResB)
    (resStatusMap : ResStatusA → ResStatusB) (resStatusB : ResB → ResStatusB)
    (srA : SourceObjA → SRA) (srTranslate : SourceObjA → SourceObjB)
    (srMap : SRA → SRB) (srB : SourceObjB → SRB)
    (restrict : Global → Local) (localData : Local) : Prop :=
  (Fbar ∘ qA = qB ∘ F) ∧ (Gbar ∘ qB = qA ∘ G) ∧
    ObjectTranslationDescends qA F qB ∧
    ObjectTranslationDescends qB G qA ∧
      QuotientInverseEquivalence Fbar Gbar ∧
        RolePreserved roleA roleTranslate roleMap roleB ∧
          TransportPreserved Fbar routeA routeB routeMap ∧
            ClaimStatusPreserved claimStatusA claimMap claimStatusMap claimStatusB ∧
              ResidualAuditPreserved resStatusA residualMap resStatusMap resStatusB ∧
                SourceReadoutPreserved srA srTranslate srMap srB ∧
                  LocalDualityGlobalizes restrict localData

/-- The obstruction-empty side of exact duality, including compatibility of
the specified quotient maps with the actual history translations. -/
def DualityObstructionsEmpty {HA QA HB QB RoleObjA RoleObjB RoleA RoleB RouteA RouteB
    ClaimA ClaimB ClaimStatusA ClaimStatusB ResA ResB ResStatusA ResStatusB
    SourceObjA SourceObjB SRA SRB Global Local : Type}
    (qA : HA → QA) (qB : HB → QB) (F : HA → HB) (G : HB → HA)
    (Fbar : QA → QB) (Gbar : QB → QA)
    (roleA : RoleObjA → RoleA) (roleTranslate : RoleObjA → RoleObjB)
    (roleMap : RoleA → RoleB) (roleB : RoleObjB → RoleB)
    (routeA : RouteA → QA → QA) (routeB : RouteB → QB → QB)
    (routeMap : RouteA → RouteB)
    (claimStatusA : ClaimA → ClaimStatusA) (claimMap : ClaimA → ClaimB)
    (claimStatusMap : ClaimStatusA → ClaimStatusB)
    (claimStatusB : ClaimB → ClaimStatusB)
    (resStatusA : ResA → ResStatusA) (residualMap : ResA → ResB)
    (resStatusMap : ResStatusA → ResStatusB) (resStatusB : ResB → ResStatusB)
    (srA : SourceObjA → SRA) (srTranslate : SourceObjA → SourceObjB)
    (srMap : SRA → SRB) (srB : SourceObjB → SRB)
    (restrict : Global → Local) (localData : Local) : Prop :=
  (Fbar ∘ qA = qB ∘ F) ∧ (Gbar ∘ qB = qA ∘ G) ∧
    ObjectTranslationObstructionEmpty qA F qB ∧
    ObjectTranslationObstructionEmpty qB G qA ∧
      InverseDefectEmpty Fbar Gbar ∧
        RoleMismatchEmpty roleA roleTranslate roleMap roleB ∧
          TransportMismatchEmpty Fbar routeA routeB routeMap ∧
            ClaimStatusMismatchEmpty claimStatusA claimMap claimStatusMap claimStatusB ∧
              ResidualAuditMismatchEmpty resStatusA residualMap resStatusMap resStatusB ∧
                SourceReadoutMismatchEmpty srA srTranslate srMap srB ∧
                  InGlobalDualityImage restrict localData

/-- F41 status vocabulary for accepted and nonclaim duality classifications. -/
inductive DualityStatus where
  | exactDuality
  | presentationEquivalence
  | contravariantDuality
  | varianceDeclaredDuality
  | partialDuality
  | targetDuality
  | bridgeEquivalence
  | bidirectionalBridge
  | embedding
  | projection
  | approximateDuality
  | asymptoticDuality
  | localDuality
  | globalDualityObstructed
  | holographicDuality
  | dualityAnomaly
  | sourceReadoutMismatch
  | residualMismatch
  | analogy
  | dualityOverread
  | completedDuality
deriving DecidableEq

/-- Meaning assignment for the F41 duality status vocabulary. -/
def DualityStatusHolds (exact presentation contravariant variance partialStatus target
    bridge bidirectional embedding projection approximate asymptotic localOnly
    globalObstructed holographic anomaly sourceReadoutMismatch residualMismatch
    analogy overread completed : Prop) : DualityStatus → Prop
  | DualityStatus.exactDuality => exact
  | DualityStatus.presentationEquivalence => presentation
  | DualityStatus.contravariantDuality => contravariant
  | DualityStatus.varianceDeclaredDuality => variance
  | DualityStatus.partialDuality => partialStatus
  | DualityStatus.targetDuality => target
  | DualityStatus.bridgeEquivalence => bridge
  | DualityStatus.bidirectionalBridge => bidirectional
  | DualityStatus.embedding => embedding
  | DualityStatus.projection => projection
  | DualityStatus.approximateDuality => approximate
  | DualityStatus.asymptoticDuality => asymptotic
  | DualityStatus.localDuality => localOnly
  | DualityStatus.globalDualityObstructed => globalObstructed
  | DualityStatus.holographicDuality => holographic
  | DualityStatus.dualityAnomaly => anomaly
  | DualityStatus.sourceReadoutMismatch => sourceReadoutMismatch
  | DualityStatus.residualMismatch => residualMismatch
  | DualityStatus.analogy => analogy
  | DualityStatus.dualityOverread => overread
  | DualityStatus.completedDuality => completed

/-- Object translation descent is exactly absence of its split-pair obstruction. -/
theorem object_translation_descends_iff_no_obstruction {HA QA HB QB : Type}
    (qA : HA → QA) (F : HA → HB) (qB : HB → QB)
    (hqA : Function.Surjective qA) :
    ObjectTranslationDescends qA F qB ↔
      ObjectTranslationObstructionEmpty qA F qB :=
  descent_repair_normal_form qA F qB hqA

/-- Quotient inverse equivalence is exactly absence of inverse defects. -/
theorem quotient_inverse_equivalence_iff_no_defect {QA QB : Type}
    (Fbar : QA → QB) (Gbar : QB → QA) :
    QuotientInverseEquivalence Fbar Gbar ↔ InverseDefectEmpty Fbar Gbar := by
  constructor
  · intro hequiv item hdefect
    cases item with
    | inl a => exact hdefect (hequiv.1 a)
    | inr b => exact hdefect (hequiv.2 b)
  · intro hempty
    constructor
    · intro a
      exact Classical.byContradiction (fun hneq => hempty (Sum.inl a) hneq)
    · intro b
      exact Classical.byContradiction (fun hneq => hempty (Sum.inr b) hneq)

/-- Generic label preservation is exactly absence of typed label mismatches. -/
theorem label_preserved_iff_no_mismatch {A B LA LB : Type} (labelA : A → LA)
    (translate : A → B) (labelMap : LA → LB) (labelB : B → LB) :
    LabelPreserved labelA translate labelMap labelB ↔
      LabelMismatchEmpty labelA translate labelMap labelB := by
  constructor
  · intro hpres x hmismatch
    exact hmismatch (hpres x)
  · intro hempty x
    exact Classical.byContradiction (fun hneq => hempty x hneq)

/-- Role preservation is exactly absence of role mismatches. -/
theorem role_preserved_iff_no_mismatch {A B RoleA RoleB : Type}
    (roleA : A → RoleA) (translate : A → B) (roleMap : RoleA → RoleB)
    (roleB : B → RoleB) :
    RolePreserved roleA translate roleMap roleB ↔
      RoleMismatchEmpty roleA translate roleMap roleB :=
  label_preserved_iff_no_mismatch roleA translate roleMap roleB

/-- Transport preservation is exactly absence of route-diagram mismatches. -/
theorem transport_preserved_iff_no_mismatch {QA QB RouteA RouteB : Type}
    (Fbar : QA → QB) (routeA : RouteA → QA → QA)
    (routeB : RouteB → QB → QB) (routeMap : RouteA → RouteB) :
    TransportPreserved Fbar routeA routeB routeMap ↔
      TransportMismatchEmpty Fbar routeA routeB routeMap := by
  constructor
  · intro hpres item hmismatch
    exact hmismatch (hpres item.1 item.2)
  · intro hempty γ a
    exact Classical.byContradiction (fun hneq => hempty (γ, a) hneq)

/-- Claim/status preservation is exactly absence of claim/status mismatches. -/
theorem claim_status_preserved_iff_no_mismatch {ClaimA ClaimB StatusA StatusB : Type}
    (statusA : ClaimA → StatusA) (claimMap : ClaimA → ClaimB)
    (statusMap : StatusA → StatusB) (statusB : ClaimB → StatusB) :
    ClaimStatusPreserved statusA claimMap statusMap statusB ↔
      ClaimStatusMismatchEmpty statusA claimMap statusMap statusB :=
  label_preserved_iff_no_mismatch statusA claimMap statusMap statusB

/-- Residual/audit preservation is exactly absence of residual/status mismatches. -/
theorem residual_audit_preserved_iff_no_mismatch {ResA ResB StatusA StatusB : Type}
    (statusA : ResA → StatusA) (residualMap : ResA → ResB)
    (statusMap : StatusA → StatusB) (statusB : ResB → StatusB) :
    ResidualAuditPreserved statusA residualMap statusMap statusB ↔
      ResidualAuditMismatchEmpty statusA residualMap statusMap statusB :=
  label_preserved_iff_no_mismatch statusA residualMap statusMap statusB

/-- Source/readout preservation is exactly absence of source/readout mismatches. -/
theorem source_readout_preserved_iff_no_mismatch {X Y SRA SRB : Type}
    (srA : X → SRA) (translate : X → Y) (srMap : SRA → SRB)
    (srB : Y → SRB) :
    SourceReadoutPreserved srA translate srMap srB ↔
      SourceReadoutMismatchEmpty srA translate srMap srB :=
  label_preserved_iff_no_mismatch srA translate srMap srB

/-- Patchwise duality data globalizes exactly when it lies in the declared
global restriction image. -/
theorem local_duality_globalizes_iff_image {Global Local : Type}
    (restrict : Global → Local) (localData : Local) :
    LocalDualityGlobalizes restrict localData ↔
      InGlobalDualityImage restrict localData := by
  rfl

/--
Duality Equivalence Normal Form. A proposed duality is exact precisely when
the object translations descend to quotient equivalences and every formed
package gate has empty typed obstruction: roles, transports, claims/statuses,
residual/audit records, source/readout discipline, and local-global gluing.
-/
theorem duality_equivalence {HA QA HB QB RoleObjA RoleObjB RoleA RoleB RouteA RouteB
    ClaimA ClaimB ClaimStatusA ClaimStatusB ResA ResB ResStatusA ResStatusB
    SourceObjA SourceObjB SRA SRB Global Local : Type}
    (qA : HA → QA) (qB : HB → QB) (F : HA → HB) (G : HB → HA)
    (hqA : Function.Surjective qA) (hqB : Function.Surjective qB)
    (Fbar : QA → QB) (Gbar : QB → QA)
    (roleA : RoleObjA → RoleA) (roleTranslate : RoleObjA → RoleObjB)
    (roleMap : RoleA → RoleB) (roleB : RoleObjB → RoleB)
    (routeA : RouteA → QA → QA) (routeB : RouteB → QB → QB)
    (routeMap : RouteA → RouteB)
    (claimStatusA : ClaimA → ClaimStatusA) (claimMap : ClaimA → ClaimB)
    (claimStatusMap : ClaimStatusA → ClaimStatusB)
    (claimStatusB : ClaimB → ClaimStatusB)
    (resStatusA : ResA → ResStatusA) (residualMap : ResA → ResB)
    (resStatusMap : ResStatusA → ResStatusB) (resStatusB : ResB → ResStatusB)
    (srA : SourceObjA → SRA) (srTranslate : SourceObjA → SourceObjB)
    (srMap : SRA → SRB) (srB : SourceObjB → SRB)
    (restrict : Global → Local) (localData : Local) :
    ExactDuality qA qB F G Fbar Gbar roleA roleTranslate roleMap roleB routeA
        routeB routeMap claimStatusA claimMap claimStatusMap claimStatusB
        resStatusA residualMap resStatusMap resStatusB srA srTranslate srMap srB
        restrict localData ↔
      DualityObstructionsEmpty qA qB F G Fbar Gbar roleA roleTranslate roleMap
        roleB routeA routeB routeMap claimStatusA claimMap claimStatusMap
        claimStatusB resStatusA residualMap resStatusMap resStatusB srA
        srTranslate srMap srB restrict localData := by
  constructor
  · intro h
    rcases h with
      ⟨hFbar, hGbar, hF, hG, hinv, hrole, htransport, hclaim, hresidual, hsource, hlocal⟩
    exact ⟨hFbar, hGbar,
      (object_translation_descends_iff_no_obstruction qA F qB hqA).1 hF,
      (object_translation_descends_iff_no_obstruction qB G qA hqB).1 hG,
      (quotient_inverse_equivalence_iff_no_defect Fbar Gbar).1 hinv,
      (role_preserved_iff_no_mismatch roleA roleTranslate roleMap roleB).1 hrole,
      (transport_preserved_iff_no_mismatch Fbar routeA routeB routeMap).1
        htransport,
      (claim_status_preserved_iff_no_mismatch claimStatusA claimMap
        claimStatusMap claimStatusB).1 hclaim,
      (residual_audit_preserved_iff_no_mismatch resStatusA residualMap
        resStatusMap resStatusB).1 hresidual,
      (source_readout_preserved_iff_no_mismatch srA srTranslate srMap srB).1
        hsource,
      (local_duality_globalizes_iff_image restrict localData).1 hlocal⟩
  · intro h
    rcases h with
      ⟨hFbar, hGbar, hF, hG, hinv, hrole, htransport, hclaim, hresidual, hsource, hlocal⟩
    exact ⟨hFbar, hGbar,
      (object_translation_descends_iff_no_obstruction qA F qB hqA).2 hF,
      (object_translation_descends_iff_no_obstruction qB G qA hqB).2 hG,
      (quotient_inverse_equivalence_iff_no_defect Fbar Gbar).2 hinv,
      (role_preserved_iff_no_mismatch roleA roleTranslate roleMap roleB).2 hrole,
      (transport_preserved_iff_no_mismatch Fbar routeA routeB routeMap).2
        htransport,
      (claim_status_preserved_iff_no_mismatch claimStatusA claimMap
        claimStatusMap claimStatusB).2 hclaim,
      (residual_audit_preserved_iff_no_mismatch resStatusA residualMap
        resStatusMap resStatusB).2 hresidual,
      (source_readout_preserved_iff_no_mismatch srA srTranslate srMap srB).2
        hsource,
      (local_duality_globalizes_iff_image restrict localData).2 hlocal⟩


/-- An actual inverse pair on object quotient carriers. -/
structure PaperQuotientEquivalence (QA QB : Type) where
  toFun : QA → QB
  invFun : QB → QA
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

/-- Paper role-preserving equivalence: the specified maps realize the history
translations and form an object
quotient equivalence and preserve roles, route actions, and claim statuses. -/
def RolePreservingDuality {HA QA HB QB RA RB VA VB RouteA RouteB KA KB SA SB : Type}
    (qA : HA → QA) (qB : HB → QB) (F : HA → HB) (G : HB → HA)
    (Fbar : QA → QB) (Gbar : QB → QA)
    (rA : RA → VA) (τ : RA → RB) (ρ : VA → VB) (rB : RB → VB)
    (actA : RouteA → QA → QA) (actB : RouteB → QB → QB)
    (φ : RouteA → RouteB) (statusA : KA → SA) (κ : KA → KB)
    (σ : SA → SB) (statusB : KB → SB) : Prop :=
  (Fbar ∘ qA = qB ∘ F) ∧ (Gbar ∘ qB = qA ∘ G) ∧
  ObjectTranslationDescends qA F qB ∧ ObjectTranslationDescends qB G qA ∧
  (∃ e : PaperQuotientEquivalence QA QB, e.toFun = Fbar ∧ e.invFun = Gbar) ∧
  RolePreserved rA τ ρ rB ∧ TransportPreserved Fbar actA actB φ ∧
  ClaimStatusPreserved statusA κ σ statusB

/-- The four paper conditions characterize role-preserving duality. -/
theorem paper_duality_equivalence
    {HA QA HB QB RA RB VA VB RouteA RouteB KA KB SA SB : Type}
    (qA : HA → QA) (qB : HB → QB) (F : HA → HB) (G : HB → HA)
    (Fbar : QA → QB) (Gbar : QB → QA)
    (rA : RA → VA) (τ : RA → RB) (ρ : VA → VB) (rB : RB → VB)
    (actA : RouteA → QA → QA) (actB : RouteB → QB → QB)
    (φ : RouteA → RouteB) (statusA : KA → SA) (κ : KA → KB)
    (σ : SA → SB) (statusB : KB → SB)
    (hF : Fbar ∘ qA = qB ∘ F) (hG : Gbar ∘ qB = qA ∘ G) :
    RolePreservingDuality qA qB F G Fbar Gbar rA τ ρ rB actA actB φ
        statusA κ σ statusB ↔
      ((∀ x, Gbar (Fbar x) = x) ∧ (∀ y, Fbar (Gbar y) = y)) ∧
      (∀ a, rB (τ a) = ρ (rA a)) ∧
      (∀ γ x, Fbar (actA γ x) = actB (φ γ) (Fbar x)) ∧
      (∀ k, statusB (κ k) = σ (statusA k)) := by
  constructor
  · rintro ⟨_,_,_,_,⟨e,heF,heG⟩,hr,ht,hs⟩
    subst Fbar
    subst Gbar
    exact ⟨⟨e.left_inv,e.right_inv⟩,hr,ht,hs⟩
  · rintro ⟨⟨hl,hr⟩,hrole,hroute,hstatus⟩
    refine ⟨hF,hG,⟨Fbar,hF⟩,⟨Gbar,hG⟩,?_,hrole,hroute,hstatus⟩
    exact ⟨⟨Fbar,Gbar,hl,hr⟩,rfl,rfl⟩


/-- The inverse descended equivalence intertwines the corresponding routes. -/
theorem inverse_descended_equivalence_preserves_routes
    {QA QB RouteA RouteB : Type}
    (Fbar : QA → QB) (Gbar : QB → QA)
    (actA : RouteA → QA → QA) (actB : RouteB → QB → QB)
    (φ : RouteA → RouteB)
    (hleft : ∀ x, Gbar (Fbar x) = x)
    (hright : ∀ y, Fbar (Gbar y) = y)
    (hforward : ∀ γ x, Fbar (actA γ x) = actB (φ γ) (Fbar x)) :
    ∀ γ y, Gbar (actB (φ γ) y) = actA γ (Gbar y) := by
  intro γ y
  calc
    Gbar (actB (φ γ) y) = Gbar (actB (φ γ) (Fbar (Gbar y))) :=
      congrArg (fun z => Gbar (actB (φ γ) z)) (hright y).symm
    _ = Gbar (Fbar (actA γ (Gbar y))) :=
      congrArg Gbar (hforward γ (Gbar y)).symm
    _ = actA γ (Gbar y) := hleft _

/-- F41 also records the route law forced on the inverse equivalence. -/
theorem paper_duality_equivalence_with_inverse_routes
    {HA QA HB QB RA RB VA VB RouteA RouteB KA KB SA SB : Type}
    (qA : HA → QA) (qB : HB → QB) (F : HA → HB) (G : HB → HA)
    (Fbar : QA → QB) (Gbar : QB → QA)
    (rA : RA → VA) (τ : RA → RB) (ρ : VA → VB) (rB : RB → VB)
    (actA : RouteA → QA → QA) (actB : RouteB → QB → QB)
    (φ : RouteA → RouteB) (statusA : KA → SA) (κ : KA → KB)
    (σ : SA → SB) (statusB : KB → SB)
    (hF : Fbar ∘ qA = qB ∘ F) (hG : Gbar ∘ qB = qA ∘ G) :
    (RolePreservingDuality qA qB F G Fbar Gbar rA τ ρ rB actA actB φ
        statusA κ σ statusB ↔
      ((∀ x, Gbar (Fbar x) = x) ∧ (∀ y, Fbar (Gbar y) = y)) ∧
      (∀ a, rB (τ a) = ρ (rA a)) ∧
      (∀ γ x, Fbar (actA γ x) = actB (φ γ) (Fbar x)) ∧
      (∀ k, statusB (κ k) = σ (statusA k))) ∧
    (RolePreservingDuality qA qB F G Fbar Gbar rA τ ρ rB actA actB φ
        statusA κ σ statusB →
      ∀ γ y, Gbar (actB (φ γ) y) = actA γ (Gbar y)) := by
  have hcore := paper_duality_equivalence qA qB F G Fbar Gbar
    rA τ ρ rB actA actB φ statusA κ σ statusB hF hG
  refine ⟨hcore, ?_⟩
  intro hdual
  rcases hcore.mp hdual with ⟨⟨hleft, hright⟩, _, hforward, _⟩
  exact inverse_descended_equivalence_preserves_routes Fbar Gbar actA actB φ
    hleft hright hforward

/-- Quotient-level role preservation also determines the target role readout
through the inverse descended equivalence. -/
theorem inverse_quotient_role_readout
    {QA QB VA VB : Type} (Fbar : QA → QB) (Gbar : QB → QA)
    (rA : QA → VA) (rB : QB → VB) (ρ : VA → VB)
    (hright : ∀ y, Fbar (Gbar y) = y)
    (hrole : ∀ x, rB (Fbar x) = ρ (rA x)) :
    rB = ρ ∘ rA ∘ Gbar := by
  funext y
  calc
    rB y = rB (Fbar (Gbar y)) := congrArg rB (hright y).symm
    _ = ρ (rA (Gbar y)) := hrole _

/-- F41 with role readouts on the object quotients and both inverse laws. -/
theorem paper_duality_equivalence_quotient_roles
    {HA QA HB QB VA VB RouteA RouteB KA KB StatusA StatusB : Type}
    (qA : HA → QA) (qB : HB → QB) (F : HA → HB) (G : HB → HA)
    (Fbar : QA → QB) (Gbar : QB → QA)
    (rA : QA → VA) (ρ : VA → VB) (rB : QB → VB)
    (actA : RouteA → QA → QA) (actB : RouteB → QB → QB)
    (φ : RouteA → RouteB) (statusA : KA → StatusA) (κ : KA → KB)
    (σ : StatusA → StatusB) (statusB : KB → StatusB)
    (hF : Fbar ∘ qA = qB ∘ F) (hG : Gbar ∘ qB = qA ∘ G) :
    (RolePreservingDuality qA qB F G Fbar Gbar rA Fbar ρ rB actA actB φ
        statusA κ σ statusB ↔
      ((∀ x, Gbar (Fbar x) = x) ∧ (∀ y, Fbar (Gbar y) = y)) ∧
      (∀ x, rB (Fbar x) = ρ (rA x)) ∧
      (∀ γ x, Fbar (actA γ x) = actB (φ γ) (Fbar x)) ∧
      (∀ k, statusB (κ k) = σ (statusA k))) ∧
    (RolePreservingDuality qA qB F G Fbar Gbar rA Fbar ρ rB actA actB φ
        statusA κ σ statusB →
      rB = ρ ∘ rA ∘ Gbar ∧
      (∀ γ y, Gbar (actB (φ γ) y) = actA γ (Gbar y))) := by
  have hcore := paper_duality_equivalence qA qB F G Fbar Gbar
    rA Fbar ρ rB actA actB φ statusA κ σ statusB hF hG
  refine ⟨hcore, ?_⟩
  intro hdual
  rcases hcore.mp hdual with ⟨⟨hleft, hright⟩, hrole, hroute, _⟩
  exact ⟨inverse_quotient_role_readout Fbar Gbar rA rB ρ hright hrole,
    inverse_descended_equivalence_preserves_routes Fbar Gbar actA actB φ
      hleft hright hroute⟩

/-- An inverse class map is unique; the opposite one-sided inverse laws
already suffice. -/
theorem inverse_class_map_unique {QA QB : Type}
    (Fbar : QA → QB) (Gbar Gbar' : QB → QA)
    (hright : ∀ y, Fbar (Gbar y) = y)
    (hleft' : ∀ x, Gbar' (Fbar x) = x) :
    Gbar' = Gbar := by
  funext y
  calc
    Gbar' y = Gbar' (Fbar (Gbar y)) := congrArg Gbar' (hright y).symm
    _ = Gbar y := hleft' _

/-- The role condition fixes every realized role value, without surjectivity. -/
theorem quotient_role_value_determined {QA QB VA VB : Type}
    (Fbar : QA → QB) (rA : QA → VA) (rB : QB → VB) (ρ : VA → VB)
    (hrole : ∀ a, rB (Fbar a) = ρ (rA a)) :
    ∀ a, ρ (rA a) = rB (Fbar a) := by
  intro a
  exact (hrole a).symm

/-- Surjective source role readout makes the entire role-value map unique
relative to the declared source and target readouts. -/
theorem quotient_role_map_unique {QA QB VA VB : Type}
    (Fbar : QA → QB) (rA : QA → VA) (rB : QB → VB) (ρ ρ' : VA → VB)
    (hrA : Function.Surjective rA)
    (hrole : ∀ a, rB (Fbar a) = ρ (rA a))
    (hrole' : ∀ a, rB (Fbar a) = ρ' (rA a)) :
    ρ' = ρ := by
  funext v
  obtain ⟨a, rfl⟩ := hrA v
  exact (hrole' a).symm.trans (hrole a)

/-- The coverage statement extended by the new canonicality clauses. -/
theorem paper_duality_equivalence_quotient_roles_strengthened
    {HA QA HB QB VA VB RouteA RouteB KA KB StatusA StatusB : Type}
    (qA : HA → QA) (qB : HB → QB) (F : HA → HB) (G : HB → HA)
    (Fbar : QA → QB) (Gbar : QB → QA)
    (rA : QA → VA) (ρ : VA → VB) (rB : QB → VB)
    (actA : RouteA → QA → QA) (actB : RouteB → QB → QB)
    (φ : RouteA → RouteB) (statusA : KA → StatusA) (κ : KA → KB)
    (σ : StatusA → StatusB) (statusB : KB → StatusB)
    (hF : Fbar ∘ qA = qB ∘ F) (hG : Gbar ∘ qB = qA ∘ G) :
    ((RolePreservingDuality qA qB F G Fbar Gbar rA Fbar ρ rB actA actB φ
        statusA κ σ statusB ↔
      ((∀ x, Gbar (Fbar x) = x) ∧ (∀ y, Fbar (Gbar y) = y)) ∧
      (∀ x, rB (Fbar x) = ρ (rA x)) ∧
      (∀ γ x, Fbar (actA γ x) = actB (φ γ) (Fbar x)) ∧
      (∀ k, statusB (κ k) = σ (statusA k))) ∧
    (RolePreservingDuality qA qB F G Fbar Gbar rA Fbar ρ rB actA actB φ
        statusA κ σ statusB →
      rB = ρ ∘ rA ∘ Gbar ∧
      (∀ γ y, Gbar (actB (φ γ) y) = actA γ (Gbar y)))) ∧
    (RolePreservingDuality qA qB F G Fbar Gbar rA Fbar ρ rB actA actB φ
        statusA κ σ statusB →
      (∀ Gbar' : QB → QA,
        ((∀ x, Gbar' (Fbar x) = x) ∧ (∀ y, Fbar (Gbar' y) = y)) →
          Gbar' = Gbar) ∧
      (∀ a, ρ (rA a) = rB (Fbar a)) ∧
      (Function.Surjective rA → ∀ ρ' : VA → VB,
        (∀ a, rB (Fbar a) = ρ' (rA a)) → ρ' = ρ)) := by
  have hcore := paper_duality_equivalence_quotient_roles qA qB F G Fbar Gbar
    rA ρ rB actA actB φ statusA κ σ statusB hF hG
  refine ⟨hcore, ?_⟩
  intro hdual
  obtain ⟨⟨_, hright⟩, hrole, _, _⟩ := hcore.1.mp hdual
  exact ⟨fun Gbar' hinv => inverse_class_map_unique Fbar Gbar Gbar' hright hinv.1,
    quotient_role_value_determined Fbar rA rB ρ hrole,
    fun hrA ρ' hrole' => quotient_role_map_unique Fbar rA rB ρ ρ' hrA hrole hrole'⟩

/-- Actual two-point false-target control: collapsed history translations
cannot be represented by identity maps on their identity quotients. -/
theorem collapsed_histories_not_identity_duality :
    ¬ RolePreservingDuality (id : Bool → Bool) id
      (fun _ => false) (fun _ => false) id id
      (id : Unit → Unit) id id id
      (fun _ : Unit => id) (fun _ : Unit => id) id
      (id : Unit → Unit) id id id := by
  intro h
  have heq := congrFun h.1 true
  cases heq

/-- The repaired definition remains inhabited on a genuine two-point identity
carrier, with identity roles, routes and status maps. -/
theorem identity_two_point_duality :
    RolePreservingDuality (id : Bool → Bool) id id id id id
      (id : Unit → Unit) id id id
      (fun _ : Unit => id) (fun _ : Unit => id) id
      (id : Unit → Unit) id id id := by
  refine ⟨rfl, rfl, ⟨id, rfl⟩, ⟨id, rfl⟩,
    ⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩, rfl, rfl⟩, ?_, ?_, ?_⟩
  · exact fun _ => rfl
  · exact fun _ _ => rfl
  · exact fun _ => rfl

/-- An injective descended class map preserves and reflects equality of
quotient classes along its raw translation. No quotient surjectivity is needed. -/
theorem descended_injective_map_preserves_quotient_fibers
    {HA QA HB QB : Type} (qA : HA → QA) (qB : HB → QB)
    (F : HA → HB) (Fbar : QA → QB)
    (hF : Fbar ∘ qA = qB ∘ F) (hinj : Function.Injective Fbar) :
    ∀ x x', qA x = qA x' ↔ qB (F x) = qB (F x') := by
  intro x x'
  constructor
  · intro heq
    calc
      qB (F x) = Fbar (qA x) := (congrFun hF x).symm
      _ = Fbar (qA x') := congrArg Fbar heq
      _ = qB (F x') := congrFun hF x'
  · intro heq
    apply hinj
    calc
      Fbar (qA x) = qB (F x) := congrFun hF x
      _ = qB (F x') := heq
      _ = Fbar (qA x') := (congrFun hF x').symm

/-- Full F41 extends the quotient-role and canonicality bundle by preservation
and reflection of raw quotient fibers in both translation directions. -/
theorem paper_duality_equivalence_quotient_roles_full
    {HA QA HB QB VA VB RouteA RouteB KA KB StatusA StatusB : Type}
    (qA : HA → QA) (qB : HB → QB) (F : HA → HB) (G : HB → HA)
    (Fbar : QA → QB) (Gbar : QB → QA)
    (rA : QA → VA) (ρ : VA → VB) (rB : QB → VB)
    (actA : RouteA → QA → QA) (actB : RouteB → QB → QB)
    (φ : RouteA → RouteB) (statusA : KA → StatusA) (κ : KA → KB)
    (σ : StatusA → StatusB) (statusB : KB → StatusB)
    (hF : Fbar ∘ qA = qB ∘ F) (hG : Gbar ∘ qB = qA ∘ G) :
    (((RolePreservingDuality qA qB F G Fbar Gbar rA Fbar ρ rB actA actB φ
        statusA κ σ statusB ↔
      ((∀ x, Gbar (Fbar x) = x) ∧ (∀ y, Fbar (Gbar y) = y)) ∧
      (∀ x, rB (Fbar x) = ρ (rA x)) ∧
      (∀ γ x, Fbar (actA γ x) = actB (φ γ) (Fbar x)) ∧
      (∀ k, statusB (κ k) = σ (statusA k))) ∧
    (RolePreservingDuality qA qB F G Fbar Gbar rA Fbar ρ rB actA actB φ
        statusA κ σ statusB →
      rB = ρ ∘ rA ∘ Gbar ∧
      (∀ γ y, Gbar (actB (φ γ) y) = actA γ (Gbar y)))) ∧
    (RolePreservingDuality qA qB F G Fbar Gbar rA Fbar ρ rB actA actB φ
        statusA κ σ statusB →
      (∀ Gbar' : QB → QA,
        ((∀ x, Gbar' (Fbar x) = x) ∧ (∀ y, Fbar (Gbar' y) = y)) →
          Gbar' = Gbar) ∧
      (∀ a, ρ (rA a) = rB (Fbar a)) ∧
      (Function.Surjective rA → ∀ ρ' : VA → VB,
        (∀ a, rB (Fbar a) = ρ' (rA a)) → ρ' = ρ))) ∧
    (RolePreservingDuality qA qB F G Fbar Gbar rA Fbar ρ rB actA actB φ
        statusA κ σ statusB →
      (∀ x x', qA x = qA x' ↔ qB (F x) = qB (F x')) ∧
      (∀ y y', qB y = qB y' ↔ qA (G y) = qA (G y'))) := by
  have hcore := paper_duality_equivalence_quotient_roles_strengthened
    qA qB F G Fbar Gbar rA ρ rB actA actB φ statusA κ σ statusB hF hG
  refine ⟨hcore, ?_⟩
  intro hdual
  obtain ⟨⟨hleft, hright⟩, _, _, _⟩ := hcore.1.1.mp hdual
  have hinjF : Function.Injective Fbar := by
    intro a a' heq
    exact (hleft a).symm.trans ((congrArg Gbar heq).trans (hleft a'))
  have hinjG : Function.Injective Gbar := by
    intro b b' heq
    exact (hright b).symm.trans ((congrArg Fbar heq).trans (hright b'))
  exact ⟨descended_injective_map_preserves_quotient_fibers qA qB F Fbar hF hinjF,
    descended_injective_map_preserves_quotient_fibers qB qA G Gbar hG hinjG⟩

end SixBirdsMetaMath.FoundationsIV.Symmetry.DualityEquivalence
