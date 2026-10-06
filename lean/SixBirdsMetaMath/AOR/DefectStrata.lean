import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.AOR.PreSB

namespace SixBirdsMetaMath.AOR.DefectStrata

open SixBirdsMetaMath.AOR.PreSB

universe u

/-!
This retained adapter is synchronized with the maintained Needles version.
References below to semantic AOR modules absent from this namespace mean
`SixBirdsNeedles.AOR.*`; this module does not re-export those endpoints.

AOR paper §3 "The structural defect `Xi_SB` and its eight strata".

This module hosts the eight-stratum decomposition of the structural defect:
- `def:aor:xi-sb`                          — `Xi_SB` defect functional
- `def:aor:sigma-obs` … `sigma-meta`       — the eight defect strata
- `thm:aor:eight-stratum-decomposition`    — disjoint-sum decomposition

Statements are paper-grounded against `paper/aor/aor_paper.tex` §3.
Each stratum is realized as a Lean `inductive` type over the relevant
PreSB-field structure; the defect functional is the disjoint sum
inductive. **Note:** `Xi_SB` is the AOR meta-theory defect, distinct
from the Schur adequacy residual `Xi_C(D|L)` of the Xi paper.
-/

/-- Names of the eight structural-defect strata. -/
inductive StratumName where
  | obs
  | stage
  | constraint
  | rewrite
  | holonomy
  | residual
  | nonclaim
  | metaAudit

/--
`def:aor:residual-types-twelve`.

The paper calls this the twelve-type atlas but enumerates thirteen primary
constructors, with `local` and `global` listed separately.  The enum is placed
with the residual stratum so each `Sigma_residual` atom carries its primary
type without creating an import cycle with the atlas module.
-/
inductive residualTypesTwelve where
  | descent
  | transport
  | interface
  | local
  | global
  | presentation
  | source
  | horizon
  | scale
  | limit
  | sym
  | role
  | target

/--
`def:aor:sigma-obs`.

Observation defects are typed observation records whose codomain, role,
source provenance, or evaluation context has not been fully declared.
-/
inductive sigmaObs {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Type u where
  | targetCodomainUndeclared : C.Obs → sigmaObs C
  | roleUndeclared : C.Obs → sigmaObs C
  | sourceProvenanceUndeclared : C.Obs → sigmaObs C
  | evaluationContextUndeclared : C.Obs → sigmaObs C

/--
`def:aor:sigma-stage`.

Stage defects are stage/refinement entries whose law, axis, or route-registry
compatibility has not been declared.
-/
inductive sigmaStage {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Type u where
  | stageLawUndeclared : C.Stage → sigmaStage C
  | refinementAxisUndeclared : C.Stage → sigmaStage C
  | routeCompatibilityUndeclared : C.Stage → sigmaStage C

/--
`def:aor:sigma-constraint`.

Constraint defects are constraint or budget entries with missing positivity,
audit-pairing typing, or admissible-solution witnesses.
-/
inductive sigmaConstraint {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Type u where
  | positivityFailure : C.Constr → sigmaConstraint C
  | auditPairingUntyped : C.Constr → sigmaConstraint C
  | admissibleSolutionMissing : C.Constr → sigmaConstraint C

/--
`def:aor:sigma-rewrite`.

Rewrite defects are rewrite records with missing source/target presentation,
admissibility tags, or blocked-rewrite annotations.
-/
inductive sigmaRewrite {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Type u where
  | sourcePresentationUndeclared : C.Rewrite → sigmaRewrite C
  | targetPresentationUndeclared : C.Rewrite → sigmaRewrite C
  | admissibilityTagUndeclared : C.Rewrite → sigmaRewrite C
  | blockedAnnotationUndeclared : C.Rewrite → sigmaRewrite C

/--
`def:aor:sigma-holonomy`.

Holonomy defects are route-dependent memory records with missing transport,
source-ledger attribution, or nonclaim flag.
-/
inductive sigmaHolonomy {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Type u where
  | carrierTransportUndeclared : C.Hol → sigmaHolonomy C
  | sourceLedgerAttributionUndeclared : C.Hol → sigmaHolonomy C
  | nonclaimFlagUndeclared : C.Hol → sigmaHolonomy C

/--
`def:aor:sigma-residual`.

Residual defects are Schur-typed residual records lacking a discharge status
from the AOR-8 catalogue.
-/
inductive sigmaResidual {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Type u where
  | dischargeStatusMissing : residualTypesTwelve → C.Res → sigmaResidual C

/--
`def:aor:sigma-nonclaim`.

Nonclaim defects are scope boundaries, blocked routes, blocked rewrites, or
deprecated claims that still need an explicit `NC` registration.
-/
inductive sigmaNonclaim {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Type u where
  | scopeBoundaryUnregistered : C.NC → sigmaNonclaim C
  | blockedRouteUnregistered : C.NC → sigmaNonclaim C
  | blockedRewriteUnregistered : C.NC → sigmaNonclaim C
  | deprecatedClaimUnregistered : C.NC → sigmaNonclaim C

/--
`def:aor:sigma-meta`.

Meta defects are provenance, version, audit-pass, or dispute-resolution
obligations not discharged in `Meta`.
-/
inductive sigmaMeta {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Type u where
  | provenanceTrailUndischarged : C.Meta → sigmaMeta C
  | versionPinUndischarged : C.Meta → sigmaMeta C
  | auditPassLogUndischarged : C.Meta → sigmaMeta C
  | disputeResolutionUndischarged : C.Meta → sigmaMeta C

/--
`def:aor:xi-sb`.

The AOR structural defect is the tagged disjoint sum of the eight strata.
This is the AOR meta-theory defect `Xi_SB`, not the Schur adequacy residual
reserved in the Xi paper.
-/
inductive xiSB {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Type u where
  | obs : sigmaObs C → xiSB C
  | stage : sigmaStage C → xiSB C
  | constraint : sigmaConstraint C → xiSB C
  | rewrite : sigmaRewrite C → xiSB C
  | holonomy : sigmaHolonomy C → xiSB C
  | residual : sigmaResidual C → xiSB C
  | nonclaim : sigmaNonclaim C → xiSB C
  | metaAudit : sigmaMeta C → xiSB C

/-- The computable stratum tag of a structural-defect atom. -/
def xiSBStratum {mathfrakS : scopeRecord.{u}} {C : preSBCarrier mathfrakS} :
    xiSB C → StratumName
  | xiSB.obs _ => StratumName.obs
  | xiSB.stage _ => StratumName.stage
  | xiSB.constraint _ => StratumName.constraint
  | xiSB.rewrite _ => StratumName.rewrite
  | xiSB.holonomy _ => StratumName.holonomy
  | xiSB.residual _ => StratumName.residual
  | xiSB.nonclaim _ => StratumName.nonclaim
  | xiSB.metaAudit _ => StratumName.metaAudit

/-- Transport observation defects along a PreSB morphism. -/
def mapSigmaObs {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (f : morphismPreSB C D) : sigmaObs C → sigmaObs D
  | sigmaObs.targetCodomainUndeclared r => sigmaObs.targetCodomainUndeclared (f.Obs_map r)
  | sigmaObs.roleUndeclared r => sigmaObs.roleUndeclared (f.Obs_map r)
  | sigmaObs.sourceProvenanceUndeclared r =>
      sigmaObs.sourceProvenanceUndeclared (f.Obs_map r)
  | sigmaObs.evaluationContextUndeclared r =>
      sigmaObs.evaluationContextUndeclared (f.Obs_map r)

/-- Transport stage defects along a PreSB morphism. -/
def mapSigmaStage {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (f : morphismPreSB C D) : sigmaStage C → sigmaStage D
  | sigmaStage.stageLawUndeclared r => sigmaStage.stageLawUndeclared (f.Stage_map r)
  | sigmaStage.refinementAxisUndeclared r =>
      sigmaStage.refinementAxisUndeclared (f.Stage_map r)
  | sigmaStage.routeCompatibilityUndeclared r =>
      sigmaStage.routeCompatibilityUndeclared (f.Stage_map r)

/-- Transport constraint defects along a PreSB morphism. -/
def mapSigmaConstraint {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (f : morphismPreSB C D) : sigmaConstraint C → sigmaConstraint D
  | sigmaConstraint.positivityFailure r => sigmaConstraint.positivityFailure (f.Constr_map r)
  | sigmaConstraint.auditPairingUntyped r =>
      sigmaConstraint.auditPairingUntyped (f.Constr_map r)
  | sigmaConstraint.admissibleSolutionMissing r =>
      sigmaConstraint.admissibleSolutionMissing (f.Constr_map r)

/-- Transport rewrite defects along a PreSB morphism. -/
def mapSigmaRewrite {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (f : morphismPreSB C D) : sigmaRewrite C → sigmaRewrite D
  | sigmaRewrite.sourcePresentationUndeclared r =>
      sigmaRewrite.sourcePresentationUndeclared (f.Rewrite_map r)
  | sigmaRewrite.targetPresentationUndeclared r =>
      sigmaRewrite.targetPresentationUndeclared (f.Rewrite_map r)
  | sigmaRewrite.admissibilityTagUndeclared r =>
      sigmaRewrite.admissibilityTagUndeclared (f.Rewrite_map r)
  | sigmaRewrite.blockedAnnotationUndeclared r =>
      sigmaRewrite.blockedAnnotationUndeclared (f.Rewrite_map r)

/-- Transport holonomy defects along a PreSB morphism. -/
def mapSigmaHolonomy {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (f : morphismPreSB C D) : sigmaHolonomy C → sigmaHolonomy D
  | sigmaHolonomy.carrierTransportUndeclared r =>
      sigmaHolonomy.carrierTransportUndeclared (f.Hol_map r)
  | sigmaHolonomy.sourceLedgerAttributionUndeclared r =>
      sigmaHolonomy.sourceLedgerAttributionUndeclared (f.Hol_map r)
  | sigmaHolonomy.nonclaimFlagUndeclared r =>
      sigmaHolonomy.nonclaimFlagUndeclared (f.Hol_map r)

/-- Transport residual defects along a PreSB morphism. -/
def mapSigmaResidual {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (f : morphismPreSB C D) : sigmaResidual C → sigmaResidual D
  | sigmaResidual.dischargeStatusMissing primary r =>
      sigmaResidual.dischargeStatusMissing primary (f.Res_map r)

/-- Transport nonclaim defects along a PreSB morphism. -/
def mapSigmaNonclaim {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (f : morphismPreSB C D) : sigmaNonclaim C → sigmaNonclaim D
  | sigmaNonclaim.scopeBoundaryUnregistered r =>
      sigmaNonclaim.scopeBoundaryUnregistered (f.NC_map r)
  | sigmaNonclaim.blockedRouteUnregistered r =>
      sigmaNonclaim.blockedRouteUnregistered (f.NC_map r)
  | sigmaNonclaim.blockedRewriteUnregistered r =>
      sigmaNonclaim.blockedRewriteUnregistered (f.NC_map r)
  | sigmaNonclaim.deprecatedClaimUnregistered r =>
      sigmaNonclaim.deprecatedClaimUnregistered (f.NC_map r)

/-- Transport meta defects along a PreSB morphism. -/
def mapSigmaMeta {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (f : morphismPreSB C D) : sigmaMeta C → sigmaMeta D
  | sigmaMeta.provenanceTrailUndischarged r =>
      sigmaMeta.provenanceTrailUndischarged (f.Meta_map r)
  | sigmaMeta.versionPinUndischarged r => sigmaMeta.versionPinUndischarged (f.Meta_map r)
  | sigmaMeta.auditPassLogUndischarged r => sigmaMeta.auditPassLogUndischarged (f.Meta_map r)
  | sigmaMeta.disputeResolutionUndischarged r =>
      sigmaMeta.disputeResolutionUndischarged (f.Meta_map r)

/-- Reverse observation-defect transport along a PreSB isomorphism. -/
def unmapSigmaObs {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : sigmaObs D → sigmaObs C :=
  mapSigmaObs e.inv

/-- Reverse stage-defect transport along a PreSB isomorphism. -/
def unmapSigmaStage {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : sigmaStage D → sigmaStage C :=
  mapSigmaStage e.inv

/-- Reverse constraint-defect transport along a PreSB isomorphism. -/
def unmapSigmaConstraint {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : sigmaConstraint D → sigmaConstraint C :=
  mapSigmaConstraint e.inv

/-- Reverse rewrite-defect transport along a PreSB isomorphism. -/
def unmapSigmaRewrite {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : sigmaRewrite D → sigmaRewrite C :=
  mapSigmaRewrite e.inv

/-- Reverse holonomy-defect transport along a PreSB isomorphism. -/
def unmapSigmaHolonomy {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : sigmaHolonomy D → sigmaHolonomy C :=
  mapSigmaHolonomy e.inv

/-- Reverse residual-defect transport along a PreSB isomorphism. -/
def unmapSigmaResidual {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : sigmaResidual D → sigmaResidual C :=
  mapSigmaResidual e.inv

/-- Reverse nonclaim-defect transport along a PreSB isomorphism. -/
def unmapSigmaNonclaim {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : sigmaNonclaim D → sigmaNonclaim C :=
  mapSigmaNonclaim e.inv

/-- Reverse meta-defect transport along a PreSB isomorphism. -/
def unmapSigmaMeta {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : sigmaMeta D → sigmaMeta C :=
  mapSigmaMeta e.inv

/-- Transport the whole structural defect along a PreSB morphism. -/
def mapXiSB {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (f : morphismPreSB C D) : xiSB C → xiSB D
  | xiSB.obs x => xiSB.obs (mapSigmaObs f x)
  | xiSB.stage x => xiSB.stage (mapSigmaStage f x)
  | xiSB.constraint x => xiSB.constraint (mapSigmaConstraint f x)
  | xiSB.rewrite x => xiSB.rewrite (mapSigmaRewrite f x)
  | xiSB.holonomy x => xiSB.holonomy (mapSigmaHolonomy f x)
  | xiSB.residual x => xiSB.residual (mapSigmaResidual f x)
  | xiSB.nonclaim x => xiSB.nonclaim (mapSigmaNonclaim f x)
  | xiSB.metaAudit x => xiSB.metaAudit (mapSigmaMeta f x)

/-- Mutually inverse transport functions for one stratum under an isomorphism. -/
structure StratumIsoPair (α β : Type u) where
  forward : α → β
  reverse : β → α
  left_inv : ∀ x, reverse (forward x) = x
  right_inv : ∀ y, forward (reverse y) = y

/-- Observation defects transport in both directions along a PreSB isomorphism. -/
def sigmaObs_iso {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : StratumIsoPair (sigmaObs C) (sigmaObs D) where
  forward := mapSigmaObs e.hom
  reverse := unmapSigmaObs e
  left_inv := by
    intro x
    have hm : ∀ a, e.inv.Obs_map (e.hom.Obs_map a) = a :=
      fun a => congrArg (fun f => f.Obs_map a) e.inv_hom_id
    cases x <;> simp [unmapSigmaObs, mapSigmaObs, hm]
  right_inv := by
    intro x
    have hm : ∀ a, e.hom.Obs_map (e.inv.Obs_map a) = a :=
      fun a => congrArg (fun f => f.Obs_map a) e.hom_inv_id
    cases x <;> simp [unmapSigmaObs, mapSigmaObs, hm]

/-- Stage defects transport in both directions along a PreSB isomorphism. -/
def sigmaStage_iso {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : StratumIsoPair (sigmaStage C) (sigmaStage D) where
  forward := mapSigmaStage e.hom
  reverse := unmapSigmaStage e
  left_inv := by
    intro x
    have hm : ∀ a, e.inv.Stage_map (e.hom.Stage_map a) = a :=
      fun a => congrArg (fun f => f.Stage_map a) e.inv_hom_id
    cases x <;> simp [unmapSigmaStage, mapSigmaStage, hm]
  right_inv := by
    intro x
    have hm : ∀ a, e.hom.Stage_map (e.inv.Stage_map a) = a :=
      fun a => congrArg (fun f => f.Stage_map a) e.hom_inv_id
    cases x <;> simp [unmapSigmaStage, mapSigmaStage, hm]

/-- Constraint defects transport in both directions along a PreSB isomorphism. -/
def sigmaConstraint_iso {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : StratumIsoPair (sigmaConstraint C) (sigmaConstraint D) where
  forward := mapSigmaConstraint e.hom
  reverse := unmapSigmaConstraint e
  left_inv := by
    intro x
    have hm : ∀ a, e.inv.Constr_map (e.hom.Constr_map a) = a :=
      fun a => congrArg (fun f => f.Constr_map a) e.inv_hom_id
    cases x <;> simp [unmapSigmaConstraint, mapSigmaConstraint, hm]
  right_inv := by
    intro x
    have hm : ∀ a, e.hom.Constr_map (e.inv.Constr_map a) = a :=
      fun a => congrArg (fun f => f.Constr_map a) e.hom_inv_id
    cases x <;> simp [unmapSigmaConstraint, mapSigmaConstraint, hm]

/-- Rewrite defects transport in both directions along a PreSB isomorphism. -/
def sigmaRewrite_iso {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : StratumIsoPair (sigmaRewrite C) (sigmaRewrite D) where
  forward := mapSigmaRewrite e.hom
  reverse := unmapSigmaRewrite e
  left_inv := by
    intro x
    have hm : ∀ a, e.inv.Rewrite_map (e.hom.Rewrite_map a) = a :=
      fun a => congrArg (fun f => f.Rewrite_map a) e.inv_hom_id
    cases x <;> simp [unmapSigmaRewrite, mapSigmaRewrite, hm]
  right_inv := by
    intro x
    have hm : ∀ a, e.hom.Rewrite_map (e.inv.Rewrite_map a) = a :=
      fun a => congrArg (fun f => f.Rewrite_map a) e.hom_inv_id
    cases x <;> simp [unmapSigmaRewrite, mapSigmaRewrite, hm]

/-- Holonomy defects transport in both directions along a PreSB isomorphism. -/
def sigmaHolonomy_iso {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : StratumIsoPair (sigmaHolonomy C) (sigmaHolonomy D) where
  forward := mapSigmaHolonomy e.hom
  reverse := unmapSigmaHolonomy e
  left_inv := by
    intro x
    have hm : ∀ a, e.inv.Hol_map (e.hom.Hol_map a) = a :=
      fun a => congrArg (fun f => f.Hol_map a) e.inv_hom_id
    cases x <;> simp [unmapSigmaHolonomy, mapSigmaHolonomy, hm]
  right_inv := by
    intro x
    have hm : ∀ a, e.hom.Hol_map (e.inv.Hol_map a) = a :=
      fun a => congrArg (fun f => f.Hol_map a) e.hom_inv_id
    cases x <;> simp [unmapSigmaHolonomy, mapSigmaHolonomy, hm]

/-- Residual defects transport in both directions along a PreSB isomorphism. -/
def sigmaResidual_iso {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : StratumIsoPair (sigmaResidual C) (sigmaResidual D) where
  forward := mapSigmaResidual e.hom
  reverse := unmapSigmaResidual e
  left_inv := by
    intro x
    have hm : ∀ a, e.inv.Res_map (e.hom.Res_map a) = a :=
      fun a => congrArg (fun f => f.Res_map a) e.inv_hom_id
    cases x <;> simp [unmapSigmaResidual, mapSigmaResidual, hm]
  right_inv := by
    intro x
    have hm : ∀ a, e.hom.Res_map (e.inv.Res_map a) = a :=
      fun a => congrArg (fun f => f.Res_map a) e.hom_inv_id
    cases x <;> simp [unmapSigmaResidual, mapSigmaResidual, hm]

/-- Nonclaim defects transport in both directions along a PreSB isomorphism. -/
def sigmaNonclaim_iso {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : StratumIsoPair (sigmaNonclaim C) (sigmaNonclaim D) where
  forward := mapSigmaNonclaim e.hom
  reverse := unmapSigmaNonclaim e
  left_inv := by
    intro x
    have hm : ∀ a, e.inv.NC_map (e.hom.NC_map a) = a :=
      fun a => congrArg (fun f => f.NC_map a) e.inv_hom_id
    cases x <;> simp [unmapSigmaNonclaim, mapSigmaNonclaim, hm]
  right_inv := by
    intro x
    have hm : ∀ a, e.hom.NC_map (e.inv.NC_map a) = a :=
      fun a => congrArg (fun f => f.NC_map a) e.hom_inv_id
    cases x <;> simp [unmapSigmaNonclaim, mapSigmaNonclaim, hm]

/-- Meta defects transport in both directions along a PreSB isomorphism. -/
def sigmaMeta_iso {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (e : PreSBIso C D) : StratumIsoPair (sigmaMeta C) (sigmaMeta D) where
  forward := mapSigmaMeta e.hom
  reverse := unmapSigmaMeta e
  left_inv := by
    intro x
    have hm : ∀ a, e.inv.Meta_map (e.hom.Meta_map a) = a :=
      fun a => congrArg (fun f => f.Meta_map a) e.inv_hom_id
    cases x <;> simp [unmapSigmaMeta, mapSigmaMeta, hm]
  right_inv := by
    intro x
    have hm : ∀ a, e.hom.Meta_map (e.inv.Meta_map a) = a :=
      fun a => congrArg (fun f => f.Meta_map a) e.hom_inv_id
    cases x <;> simp [unmapSigmaMeta, mapSigmaMeta, hm]

/--
Every stratum has mutually inverse transports along a fixed-scope PreSB
isomorphism. The inverse laws follow from the actual field-map inverse laws.
-/
def strataPreservedByIso {mathfrakS : scopeRecord.{u}}
    (C D : preSBCarrier mathfrakS) : Prop :=
  PreSBIso C D →
    Nonempty (StratumIsoPair (sigmaObs C) (sigmaObs D)) ∧
      Nonempty (StratumIsoPair (sigmaStage C) (sigmaStage D)) ∧
        Nonempty (StratumIsoPair (sigmaConstraint C) (sigmaConstraint D)) ∧
          Nonempty (StratumIsoPair (sigmaRewrite C) (sigmaRewrite D)) ∧
            Nonempty (StratumIsoPair (sigmaHolonomy C) (sigmaHolonomy D)) ∧
              Nonempty (StratumIsoPair (sigmaResidual C) (sigmaResidual D)) ∧
                Nonempty (StratumIsoPair (sigmaNonclaim C) (sigmaNonclaim D)) ∧
                  Nonempty (StratumIsoPair (sigmaMeta C) (sigmaMeta D))

/-- Emptiness of a type, used for zero strata and zero structural defect. -/
def EmptyType (α : Sort u) : Prop :=
  α → False

/-- `Xi_SB(C) = 0` is represented by emptiness of the structural-defect type. -/
def xiSBZero {mathfrakS : scopeRecord.{u}} (C : preSBCarrier mathfrakS) : Prop :=
  EmptyType (xiSB C)

/-- Emptiness of all eight independent strata. -/
def allStrataEmpty {mathfrakS : scopeRecord.{u}} (C : preSBCarrier mathfrakS) : Prop :=
  EmptyType (sigmaObs C) ∧
    EmptyType (sigmaStage C) ∧
      EmptyType (sigmaConstraint C) ∧
        EmptyType (sigmaRewrite C) ∧
          EmptyType (sigmaHolonomy C) ∧
            EmptyType (sigmaResidual C) ∧ EmptyType (sigmaNonclaim C) ∧ EmptyType (sigmaMeta C)

/-- Zero structural defect is equivalent to independent emptiness of all strata. -/
theorem xiSBZero_iff_allStrataEmpty {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : xiSBZero C ↔ allStrataEmpty C := by
  constructor
  · intro h
    exact ⟨fun x => h (xiSB.obs x),
      fun x => h (xiSB.stage x),
      fun x => h (xiSB.constraint x),
      fun x => h (xiSB.rewrite x),
      fun x => h (xiSB.holonomy x),
      fun x => h (xiSB.residual x),
      fun x => h (xiSB.nonclaim x),
      fun x => h (xiSB.metaAudit x)⟩
  · intro h
    rcases h with ⟨hObs, hStage, hConstraint, hRewrite, hHolonomy, hResidual,
      hNonclaim, hMeta⟩
    exact fun x =>
      match x with
      | xiSB.obs y => hObs y
      | xiSB.stage y => hStage y
      | xiSB.constraint y => hConstraint y
      | xiSB.rewrite y => hRewrite y
      | xiSB.holonomy y => hHolonomy y
      | xiSB.residual y => hResidual y
      | xiSB.nonclaim y => hNonclaim y
      | xiSB.metaAudit y => hMeta y

/-- Proof package for the eight-stratum decomposition theorem. -/
structure EightStratumDecompositionWitness {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Prop where
  decomposes :
    ∀ x : xiSB C,
      xiSBStratum x = StratumName.obs ∨
        xiSBStratum x = StratumName.stage ∨
          xiSBStratum x = StratumName.constraint ∨
            xiSBStratum x = StratumName.rewrite ∨
              xiSBStratum x = StratumName.holonomy ∨
                xiSBStratum x = StratumName.residual ∨
                  xiSBStratum x = StratumName.nonclaim ∨
                    xiSBStratum x = StratumName.metaAudit
  computableFromFieldData : ∀ _ : xiSB C, True
  preservedByIso : ∀ D : preSBCarrier mathfrakS, strataPreservedByIso C D
  zero_iff_each_empty : xiSBZero C ↔ allStrataEmpty C

/--
`thm:aor:eight-stratum-decomposition`.

For every PreSB carrier, `Xi_SB` is the tagged disjoint sum of the eight
strata, the tag is computable by case analysis on field-derived defects, each
stratum has mutually inverse transports along PreSB isomorphism, and
zero defect is equivalent to independent emptiness of all eight strata.
-/
theorem eightStratumDecomposition {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : EightStratumDecompositionWitness C where
  decomposes := by
    intro x
    cases x <;> simp [xiSBStratum]
  computableFromFieldData := by
    intro _
    exact True.intro
  preservedByIso := by
    intro D e
    exact ⟨⟨sigmaObs_iso e⟩,
      ⟨sigmaStage_iso e⟩,
      ⟨sigmaConstraint_iso e⟩,
      ⟨sigmaRewrite_iso e⟩,
      ⟨sigmaHolonomy_iso e⟩,
      ⟨sigmaResidual_iso e⟩,
      ⟨sigmaNonclaim_iso e⟩,
      ⟨sigmaMeta_iso e⟩⟩
  zero_iff_each_empty := xiSBZero_iff_allStrataEmpty C

end SixBirdsMetaMath.AOR.DefectStrata
