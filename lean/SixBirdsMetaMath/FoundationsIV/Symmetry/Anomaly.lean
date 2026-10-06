import SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure
import SixBirdsMetaMath.FoundationsIV.Transport.LocalGlobalObstruction

/-!
F40 Anomaly / Symmetry Obstruction.

Layer-agnostic anomaly: a would-be symmetry source fails to become a symmetry
of a formed layer because descent, gluing, group-law, readout, audit, or
residual-status preservation fails.
-/

namespace SixBirdsMetaMath.FoundationsIV.Symmetry.Anomaly

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
open SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure
open SixBirdsMetaMath.FoundationsIV.Transport.LocalGlobalObstruction

/-- Same layer object, different transformed layer object. -/
def SymmetryDescentSplit {G H Q : Type} (q : H → Q) (act : G → H → H) :
    G × (H × H) → Prop :=
  fun item =>
    q item.2.1 = q item.2.2 ∧
      q (act item.1 item.2.1) ≠ q (act item.1 item.2.2)

/-- A raw symmetry action descends through the layer quotient. -/
def SymmetryDescends {G H Q : Type} (q : H → Q) (act : G → H → H) :
    Prop :=
  ∀ g : G, FactorsThroughQ q (fun h => q (act g h))

/-- No symmetry descent obstruction is present. -/
def SymmetryDescentObstructionEmpty {G H Q : Type} (q : H → Q)
    (act : G → H → H) : Prop :=
  ObstructionEmpty (SymmetryDescentSplit q act)

/-- Domain admissibility for a partial symmetry action descends through the
layer quotient. Boolean domains avoid adding decidability hypotheses. -/
def DomainDescends {G H Q : Type} (q : H → Q) (domain : G → H → Bool) :
    Prop :=
  ∀ g : G, FactorsThroughQ q (domain g)

/-- Same layer object, different symmetry-domain admissibility. -/
def DomainDescentSplit {G H Q : Type} (q : H → Q)
    (domain : G → H → Bool) : G × (H × H) → Prop :=
  fun item =>
    q item.2.1 = q item.2.2 ∧
      domain item.1 item.2.1 ≠ domain item.1 item.2.2

/-- No domain-descent obstruction is present. -/
def DomainObstructionEmpty {G H Q : Type} (q : H → Q)
    (domain : G → H → Bool) : Prop :=
  ObstructionEmpty (DomainDescentSplit q domain)

/-- Descended actions preserve the declared group/monoid law. -/
def GroupLawPreserved {G Q : Type} (mul : G → G → G) (actQ : G → Q → Q) :
    Prop :=
  ∀ g h : G, ∀ q : Q, actQ (mul g h) q = actQ g (actQ h q)

/-- Group-law/cocycle obstruction at the layer. -/
def GroupLawObstruction {G Q : Type} (mul : G → G → G) (actQ : G → Q → Q) :
    G × (G × Q) → Prop :=
  fun item =>
    actQ (mul item.1 item.2.1) item.2.2 ≠
      actQ item.1 (actQ item.2.1 item.2.2)

/-- No group-law/cocycle obstruction is present. -/
def GroupLawObstructionEmpty {G Q : Type} (mul : G → G → G)
    (actQ : G → Q → Q) : Prop :=
  ObstructionEmpty (GroupLawObstruction mul actQ)

/-- A readout is invariant/covariant under the raw symmetry action. -/
def ReadoutPreserved {G H V : Type} (readout : H → V) (act : G → H → H)
    (rho : G → V → V) : Prop :=
  ∀ g : G, ∀ h : H, readout (act g h) = rho g (readout h)

/-- Readout/law preservation obstruction. -/
def ReadoutObstruction {G H V : Type} (readout : H → V) (act : G → H → H)
    (rho : G → V → V) : G × H → Prop :=
  fun item => readout (act item.1 item.2) ≠ rho item.1 (readout item.2)

/-- No readout preservation obstruction is present. -/
def ReadoutObstructionEmpty {G H V : Type} (readout : H → V)
    (act : G → H → H) (rho : G → V → V) : Prop :=
  ObstructionEmpty (ReadoutObstruction readout act rho)

/-- Residual/audit status preservation under a symmetry action. -/
def AuditPreserved {G Rec Status : Type} (status : Rec → Status)
    (actRec : G → Rec → Rec) (actStatus : G → Status → Status) : Prop :=
  ∀ g : G, ∀ r : Rec, status (actRec g r) = actStatus g (status r)

/-- Audit/residual status preservation obstruction. -/
def AuditObstruction {G Rec Status : Type} (status : Rec → Status)
    (actRec : G → Rec → Rec) (actStatus : G → Status → Status) :
    G × Rec → Prop :=
  fun item => status (actRec item.1 item.2) ≠ actStatus item.1 (status item.2)

/-- No audit preservation obstruction is present. -/
def AuditObstructionEmpty {G Rec Status : Type} (status : Rec → Status)
    (actRec : G → Rec → Rec) (actStatus : G → Status → Status) : Prop :=
  ObstructionEmpty (AuditObstruction status actRec actStatus)

/-- A local symmetry family globalizes when it lies in the declared image of the
global restriction map. -/
def LocalSymmetryGlobalizes {Global Local : Type} (restrict : Global → Local)
    (localData : Local) : Prop :=
  ∃ global : Global, restrict global = localData

/-- Image-membership spelling of local-global symmetry gluing. -/
def InGlobalSymmetryImage {Global Local : Type} (restrict : Global → Local)
    (localData : Local) : Prop :=
  InDeclaredImage restrict localData

/-- Local symmetry gluing obstruction: compatible local data not in the global
restriction image. -/
def SymmetryGluingObstruction {Global Local : Type} (compatible : Local → Prop)
    (restrict : Global → Local) (localData : Local) : Prop :=
  compatible localData ∧ ¬ LocalSymmetryGlobalizes restrict localData

/-- Gates that must pass for a would-be symmetry to be a formed layer symmetry. -/
structure SymmetryGateProfile where
  symmetrySourceClaimed : Prop
  explicitBreakingRecorded : Prop
  domainDescent : Prop
  actionDescent : Prop
  groupLaw : Prop
  readoutPreservation : Prop
  auditPreservation : Prop
  localGlobalGluing : Prop

/-- A lawful layer symmetry has all declared gates passing. -/
def LawfulLayerSymmetry (profile : SymmetryGateProfile) : Prop :=
  profile.domainDescent ∧ profile.actionDescent ∧ profile.groupLaw ∧
    profile.readoutPreservation ∧ profile.auditPreservation ∧
      profile.localGlobalGluing

/-- An anomaly is a claimed symmetry source with failed layer realization, not
merely explicit breaking. -/
def Anomaly (profile : SymmetryGateProfile) : Prop :=
  profile.symmetrySourceClaimed ∧ ¬ profile.explicitBreakingRecorded ∧
    ¬ LawfulLayerSymmetry profile

/-- F40's displayed four conditions, without the additional audit and gluing
gates of `LawfulLayerSymmetry`. -/
def PaperFourConditions (profile : SymmetryGateProfile) : Prop :=
  profile.actionDescent ∧ profile.domainDescent ∧ profile.groupLaw ∧
    profile.readoutPreservation

/-- Anomaly relative to precisely the four conditions displayed in F40. -/
def PaperFourConditionAnomaly (profile : SymmetryGateProfile) : Prop :=
  profile.symmetrySourceClaimed ∧ ¬ profile.explicitBreakingRecorded ∧
    ¬ PaperFourConditions profile

/-- F40's anomaly test applied to the actual four displayed conditions. -/
def PaperAnomaly {G H Q V : Type} (q : H → Q) (act : G → H → H)
    (domain : G → H → Bool) (mul : G → G → G) (actQ : G → Q → Q)
    (readout : H → V) (rho : G → V → V)
    (claimed explicitBreaking : Prop) : Prop :=
  claimed ∧ ¬ explicitBreaking ∧
    ¬ (SymmetryDescends q act ∧ DomainDescends q domain ∧
      GroupLawPreserved mul actQ ∧ ReadoutPreserved readout act rho)

/-- F40 anomaly status vocabulary. -/
inductive AnomalyStatus where
  | exactLayerSymmetry
  | covariantSymmetry
  | projectiveOrExtendedSymmetry
  | explicitSymmetryBreaking
  | descentAnomaly
  | domainAnomaly
  | cocycleAnomaly
  | lawSymmetryAnomaly
  | measureOrLedgerAnomaly
  | auditAnomaly
  | localGlobalAnomaly
  | boundarySymmetryAnomaly
  | anomalyCancelled
  | budgetedSymmetry
  | hiddenRestoredSymmetry
  | presentationArtifact
  | protocolSymmetryArtifact
  | anomalyOverread
deriving DecidableEq

/-- Meaning of each anomaly status. -/
def AnomalyStatusHolds (exact covariant projective explicitBreaking descent
    domain cocycle law ledger audit localGlobal boundary cancelled budgeted
    hiddenRestored presentationArtifact protocolArtifact overread : Prop) :
    AnomalyStatus → Prop
  | AnomalyStatus.exactLayerSymmetry => exact
  | AnomalyStatus.covariantSymmetry => covariant
  | AnomalyStatus.projectiveOrExtendedSymmetry => projective
  | AnomalyStatus.explicitSymmetryBreaking => explicitBreaking
  | AnomalyStatus.descentAnomaly => descent
  | AnomalyStatus.domainAnomaly => domain
  | AnomalyStatus.cocycleAnomaly => cocycle
  | AnomalyStatus.lawSymmetryAnomaly => law
  | AnomalyStatus.measureOrLedgerAnomaly => ledger
  | AnomalyStatus.auditAnomaly => audit
  | AnomalyStatus.localGlobalAnomaly => localGlobal
  | AnomalyStatus.boundarySymmetryAnomaly => boundary
  | AnomalyStatus.anomalyCancelled => cancelled
  | AnomalyStatus.budgetedSymmetry => budgeted
  | AnomalyStatus.hiddenRestoredSymmetry => hiddenRestored
  | AnomalyStatus.presentationArtifact => presentationArtifact
  | AnomalyStatus.protocolSymmetryArtifact => protocolArtifact
  | AnomalyStatus.anomalyOverread => overread

/-- Raw action descent is equivalent to absence of the symmetry descent
split-pair obstruction. -/
theorem symmetry_descends_iff_no_obstruction {G H Q : Type} (q : H → Q)
    (act : G → H → H) (hq : Function.Surjective q) :
    SymmetryDescends q act ↔ SymmetryDescentObstructionEmpty q act := by
  constructor
  · intro hdesc item hsplit
    rcases hdesc item.1 with ⟨actBar, hcomm⟩
    have hx : actBar (q item.2.1) = q (act item.1 item.2.1) :=
      congrFun hcomm item.2.1
    have hy : actBar (q item.2.2) = q (act item.1 item.2.2) :=
      congrFun hcomm item.2.2
    exact hsplit.2 (by
      calc
        q (act item.1 item.2.1) = actBar (q item.2.1) := hx.symm
        _ = actBar (q item.2.2) := by rw [hsplit.1]
        _ = q (act item.1 item.2.2) := hy)
  · intro hempty g
    have hclosed : PackageClosed q (fun h => q (act g h)) := by
      intro x y hxy
      exact Classical.byContradiction (fun hneq =>
        hempty (g, (x, y)) ⟨hxy, hneq⟩)
    exact (sufficiency_closure q (fun h => q (act g h)) hq).1.1 hclosed

/-- Partial-domain descent is equivalent to absence of domain obstruction. -/
theorem domain_descends_iff_no_obstruction {G H Q : Type} (q : H → Q)
    (domain : G → H → Bool) (hq : Function.Surjective q) :
    DomainDescends q domain ↔ DomainObstructionEmpty q domain := by
  constructor
  · intro hdesc item hsplit
    rcases hdesc item.1 with ⟨domainBar, hcomm⟩
    have hx : domainBar (q item.2.1) = domain item.1 item.2.1 :=
      congrFun hcomm item.2.1
    have hy : domainBar (q item.2.2) = domain item.1 item.2.2 :=
      congrFun hcomm item.2.2
    exact hsplit.2 (by
      calc
        domain item.1 item.2.1 = domainBar (q item.2.1) := hx.symm
        _ = domainBar (q item.2.2) := by rw [hsplit.1]
        _ = domain item.1 item.2.2 := hy)
  · intro hempty g
    have hclosed : PackageClosed q (domain g) := by
      intro x y hxy
      exact Classical.byContradiction (fun hneq =>
        hempty (g, (x, y)) ⟨hxy, hneq⟩)
    exact (sufficiency_closure q (domain g) hq).1.1 hclosed

/-- Group-law preservation is equivalent to empty group-law obstruction. -/
theorem group_law_iff_no_obstruction {G Q : Type} (mul : G → G → G)
    (actQ : G → Q → Q) :
    GroupLawPreserved mul actQ ↔ GroupLawObstructionEmpty mul actQ := by
  constructor
  · intro hpres item hobs
    exact hobs (hpres item.1 item.2.1 item.2.2)
  · intro hempty g h q
    exact Classical.byContradiction (fun hneq =>
      hempty (g, (h, q)) hneq)

/-- Readout/law preservation is equivalent to empty readout obstruction. -/
theorem readout_preserved_iff_no_obstruction {G H V : Type} (readout : H → V)
    (act : G → H → H) (rho : G → V → V) :
    ReadoutPreserved readout act rho ↔
      ReadoutObstructionEmpty readout act rho := by
  constructor
  · intro hpres item hobs
    exact hobs (hpres item.1 item.2)
  · intro hempty g h
    exact Classical.byContradiction (fun hneq =>
      hempty (g, h) hneq)

/-- Audit preservation is equivalent to empty audit obstruction. -/
theorem audit_preserved_iff_no_obstruction {G Rec Status : Type}
    (status : Rec → Status) (actRec : G → Rec → Rec)
    (actStatus : G → Status → Status) :
    AuditPreserved status actRec actStatus ↔
      AuditObstructionEmpty status actRec actStatus := by
  constructor
  · intro hpres item hobs
    exact hobs (hpres item.1 item.2)
  · intro hempty g r
    exact Classical.byContradiction (fun hneq =>
      hempty (g, r) hneq)

/-- Local symmetry data globalizes exactly when it lies in the image of the
global restriction map. -/
theorem local_symmetry_globalizes_iff_image {Global Local : Type}
    (restrict : Global → Local) (localData : Local) :
    LocalSymmetryGlobalizes restrict localData ↔
      InGlobalSymmetryImage restrict localData := by
  rfl

/-- The gate profile expands to the six formed-layer symmetry gates. -/
theorem lawful_layer_symmetry_iff_gates (profile : SymmetryGateProfile) :
    LawfulLayerSymmetry profile ↔
      profile.domainDescent ∧ profile.actionDescent ∧ profile.groupLaw ∧
        profile.readoutPreservation ∧ profile.auditPreservation ∧
          profile.localGlobalGluing := by
  rfl

/-- The anomaly predicate expands to source-present, not explicit breaking, and
failed formed-layer symmetry. -/
theorem anomaly_iff_failed_gate (profile : SymmetryGateProfile) :
    Anomaly profile ↔
      profile.symmetrySourceClaimed ∧ ¬ profile.explicitBreakingRecorded ∧
        ¬ LawfulLayerSymmetry profile := by
  rfl

/--
Anomaly / Symmetry Obstruction Normal Form. A raw/local/upstairs symmetry is a
formed layer symmetry exactly when descent, domain, group-law, readout, audit,
and local-global gates pass. Each gate is characterized by an empty typed
obstruction; anomaly means a symmetry source is claimed, explicit breaking is
not the status, and at least one formed-layer gate fails.
-/
theorem anomaly_symmetry_obstruction {G H Q V Rec Status Global Local : Type}
    (q : H → Q) (act : G → H → H) (domain : G → H → Bool)
    (hq : Function.Surjective q)
    (mul : G → G → G) (actQ : G → Q → Q)
    (readout : H → V) (rho : G → V → V)
    (status : Rec → Status) (actRec : G → Rec → Rec)
    (actStatus : G → Status → Status)
    (restrict : Global → Local) (localData : Local)
    (profile : SymmetryGateProfile) :
    (SymmetryDescends q act ↔ SymmetryDescentObstructionEmpty q act) ∧
      (DomainDescends q domain ↔ DomainObstructionEmpty q domain) ∧
        (GroupLawPreserved mul actQ ↔ GroupLawObstructionEmpty mul actQ) ∧
          (ReadoutPreserved readout act rho ↔
            ReadoutObstructionEmpty readout act rho) ∧
            (AuditPreserved status actRec actStatus ↔
              AuditObstructionEmpty status actRec actStatus) ∧
              (LocalSymmetryGlobalizes restrict localData ↔
                InGlobalSymmetryImage restrict localData) ∧
                (LawfulLayerSymmetry profile ↔
                  profile.domainDescent ∧ profile.actionDescent ∧
                    profile.groupLaw ∧ profile.readoutPreservation ∧
                      profile.auditPreservation ∧ profile.localGlobalGluing) ∧
                  (Anomaly profile ↔
                    profile.symmetrySourceClaimed ∧
                      ¬ profile.explicitBreakingRecorded ∧
                        ¬ LawfulLayerSymmetry profile) := by
  exact ⟨symmetry_descends_iff_no_obstruction q act hq,
    domain_descends_iff_no_obstruction q domain hq,
    group_law_iff_no_obstruction mul actQ,
    readout_preserved_iff_no_obstruction readout act rho,
    audit_preserved_iff_no_obstruction status actRec actStatus,
    local_symmetry_globalizes_iff_image restrict localData,
    lawful_layer_symmetry_iff_gates profile,
    anomaly_iff_failed_gate profile⟩

/-- The four obstruction tests and the qualified anomaly clause in the repaired
paper statement F40. The profile's four fields denote the four displayed
conditions; audit and gluing fields are deliberately absent from this test. -/
theorem anomaly_symmetry_obstruction_paper {G H Q V : Type}
    (q : H → Q) (act : G → H → H) (domain : G → H → Bool)
    (hq : Function.Surjective q) (mul : G → G → G) (actQ : G → Q → Q)
    (readout : H → V) (rho : G → V → V)
    (claimed explicitBreaking : Prop) :
    (SymmetryDescends q act ↔ SymmetryDescentObstructionEmpty q act) ∧
      (DomainDescends q domain ↔ DomainObstructionEmpty q domain) ∧
        (GroupLawPreserved mul actQ ↔ GroupLawObstructionEmpty mul actQ) ∧
          (ReadoutPreserved readout act rho ↔
            ReadoutObstructionEmpty readout act rho) ∧
            (PaperAnomaly q act domain mul actQ readout rho claimed explicitBreaking ↔
              claimed ∧ ¬ explicitBreaking ∧
                (¬ SymmetryDescends q act ∨ ¬ DomainDescends q domain ∨
                  ¬ GroupLawPreserved mul actQ ∨
                    ¬ ReadoutPreserved readout act rho)) := by
  refine ⟨symmetry_descends_iff_no_obstruction q act hq,
    domain_descends_iff_no_obstruction q domain hq,
    group_law_iff_no_obstruction mul actQ,
    readout_preserved_iff_no_obstruction readout act rho, ?_⟩
  classical
  by_cases ha : SymmetryDescends q act
  · by_cases hd : DomainDescends q domain
    · by_cases hg : GroupLawPreserved mul actQ
      · by_cases hr : ReadoutPreserved readout act rho
        · simp [PaperAnomaly, ha, hd, hg, hr]
        · simp [PaperAnomaly, ha, hd, hg, hr]
      · simp [PaperAnomaly, ha, hd, hg]
    · simp [PaperAnomaly, ha, hd]
  · simp [PaperAnomaly, ha]

/-- Paper F40, including preservation of multiplication by a descended action. -/
theorem anomaly_symmetry_obstruction_descended {G H Q V : Type}
    (q : H → Q) (act : G → H → H) (domain : G → H → Bool)
    (hq : Function.Surjective q) (mul : G → G → G) (actQ : G → Q → Q)
    (readout : H → V) (rho : G → V → V)
    (claimed explicitBreaking : Prop) :
    (SymmetryDescends q act ↔ SymmetryDescentObstructionEmpty q act) ∧
    (DomainDescends q domain ↔ DomainObstructionEmpty q domain) ∧
    (GroupLawPreserved mul actQ ↔ GroupLawObstructionEmpty mul actQ) ∧
    (ReadoutPreserved readout act rho ↔
      ReadoutObstructionEmpty readout act rho) ∧
    (PaperAnomaly q act domain mul actQ readout rho claimed explicitBreaking ↔
      claimed ∧ ¬ explicitBreaking ∧
        (¬ SymmetryDescends q act ∨ ¬ DomainDescends q domain ∨
          ¬ GroupLawPreserved mul actQ ∨ ¬ ReadoutPreserved readout act rho)) ∧
    ((∀ g g' h, act (mul g g') h = act g (act g' h)) →
      (∀ g h, actQ g (q h) = q (act g h)) →
        GroupLawPreserved mul actQ) := by
  refine ⟨(anomaly_symmetry_obstruction_paper q act domain hq mul actQ
    readout rho claimed explicitBreaking).1,
    (anomaly_symmetry_obstruction_paper q act domain hq mul actQ
    readout rho claimed explicitBreaking).2.1,
    (anomaly_symmetry_obstruction_paper q act domain hq mul actQ
    readout rho claimed explicitBreaking).2.2.1,
    (anomaly_symmetry_obstruction_paper q act domain hq mul actQ
    readout rho claimed explicitBreaking).2.2.2.1,
    (anomaly_symmetry_obstruction_paper q act domain hq mul actQ
    readout rho claimed explicitBreaking).2.2.2.2, ?_⟩
  intro haction hdesc g g' a
  obtain ⟨h, rfl⟩ := hq a
  calc
    actQ (mul g g') (q h) = q (act (mul g g') h) := hdesc (mul g g') h
    _ = q (act g (act g' h)) := congrArg q (haction g g' h)
    _ = actQ g (q (act g' h)) := (hdesc g (act g' h)).symm
    _ = actQ g (actQ g' (q h)) := congrArg (actQ g) (hdesc g' h).symm

/-- A candidate descended action forces the raw action-descent split to vanish. -/
theorem descended_action_obstruction_empty {G H Q : Type}
    (q : H → Q) (act : G → H → H) (actQ : G → Q → Q)
    (hdesc : ∀ g h, actQ g (q h) = q (act g h)) :
    SymmetryDescentObstructionEmpty q act := by
  intro ⟨g,h,h'⟩ ⟨hqq,hne⟩
  apply hne
  calc
    q (act g h) = actQ g (q h) := (hdesc g h).symm
    _ = actQ g (q h') := congrArg (actQ g) hqq
    _ = q (act g h') := hdesc g h'

/-- F40 also records that the descent equation empties the action obstruction. -/
theorem anomaly_symmetry_obstruction_descended_complete {G H Q V : Type}
    (q : H → Q) (act : G → H → H) (domain : G → H → Bool)
    (hq : Function.Surjective q) (mul : G → G → G) (actQ : G → Q → Q)
    (readout : H → V) (rho : G → V → V)
    (claimed explicitBreaking : Prop) :
    ((SymmetryDescends q act ↔ SymmetryDescentObstructionEmpty q act) ∧
    (DomainDescends q domain ↔ DomainObstructionEmpty q domain) ∧
    (GroupLawPreserved mul actQ ↔ GroupLawObstructionEmpty mul actQ) ∧
    (ReadoutPreserved readout act rho ↔
      ReadoutObstructionEmpty readout act rho) ∧
    (PaperAnomaly q act domain mul actQ readout rho claimed explicitBreaking ↔
      claimed ∧ ¬ explicitBreaking ∧
        (¬ SymmetryDescends q act ∨ ¬ DomainDescends q domain ∨
          ¬ GroupLawPreserved mul actQ ∨ ¬ ReadoutPreserved readout act rho)) ∧
    ((∀ g g' h, act (mul g g') h = act g (act g' h)) →
      (∀ g h, actQ g (q h) = q (act g h)) →
        GroupLawPreserved mul actQ)) ∧
    ((∀ g h, actQ g (q h) = q (act g h)) →
      SymmetryDescentObstructionEmpty q act) := by
  exact ⟨anomaly_symmetry_obstruction_descended q act domain hq mul actQ
      readout rho claimed explicitBreaking,
    descended_action_obstruction_empty q act actQ⟩

/-- The action induced by an empty action-descent obstruction. -/
noncomputable def inducedAction {G H Q : Type} (q : H → Q)
    (act : G → H → H) (hq : Function.Surjective q)
    (hO : SymmetryDescentObstructionEmpty q act) : G → Q → Q :=
  fun g => Classical.choose
    (((symmetry_descends_iff_no_obstruction q act hq).mpr hO) g)

theorem inducedAction_commutes {G H Q : Type} (q : H → Q)
    (act : G → H → H) (hq : Function.Surjective q)
    (hO : SymmetryDescentObstructionEmpty q act) :
    ∀ g h, inducedAction q act hq hO g (q h) = q (act g h) := by
  intro g h
  exact congrFun (Classical.choose_spec
    (((symmetry_descends_iff_no_obstruction q act hq).mpr hO) g)) h

/-- F40 for the induced action: a raw group law automatically descends, so
the only remaining anomaly tests are action/domain descent and readout. -/
theorem anomaly_symmetry_obstruction_induced {G H Q V : Type}
    (q : H → Q) (act : G → H → H) (domain : G → H → Bool)
    (hq : Function.Surjective q) (mul : G → G → G)
    (readout : H → V) (rho : G → V → V)
    (claimed explicitBreaking : Prop)
    (hO : SymmetryDescentObstructionEmpty q act)
    (haction : ∀ g g' h, act (mul g g') h = act g (act g' h)) :
    GroupLawPreserved mul (inducedAction q act hq hO) ∧
    (SymmetryDescends q act ↔ SymmetryDescentObstructionEmpty q act) ∧
    (DomainDescends q domain ↔ DomainObstructionEmpty q domain) ∧
    (ReadoutPreserved readout act rho ↔
      ReadoutObstructionEmpty readout act rho) ∧
    (PaperAnomaly q act domain mul (inducedAction q act hq hO)
      readout rho claimed explicitBreaking ↔
      claimed ∧ ¬ explicitBreaking ∧
        (¬ SymmetryDescentObstructionEmpty q act ∨
          ¬ DomainObstructionEmpty q domain ∨
            ¬ ReadoutPreserved readout act rho)) := by
  have hdesc := inducedAction_commutes q act hq hO
  have hg : GroupLawPreserved mul (inducedAction q act hq hO) :=
    (anomaly_symmetry_obstruction_descended q act domain hq mul
      (inducedAction q act hq hO) readout rho claimed explicitBreaking).2.2.2.2.2
        haction hdesc
  refine ⟨hg, symmetry_descends_iff_no_obstruction q act hq,
    domain_descends_iff_no_obstruction q domain hq,
    readout_preserved_iff_no_obstruction readout act rho, ?_⟩
  have hs : SymmetryDescends q act :=
    (symmetry_descends_iff_no_obstruction q act hq).mpr hO
  have hd := domain_descends_iff_no_obstruction q domain hq
  rw [PaperAnomaly]
  simp [hs, hg, hO, ← hd]
  intro _ _
  by_cases hdomain : DomainDescends q domain <;> simp [hdomain]

/-- F40 anomaly with the induced descended action: only the action, domain,
and readout obstructions can remain for a genuine raw group action. -/
def InducedAnomaly {G H Q V : Type} (q : H → Q) (act : G → H → H)
    (domain : G → H → Bool) (readout : H → V)
    (rho : G → V → V) : Prop :=
  ¬ SymmetryDescentObstructionEmpty q act ∨
    ¬ DomainObstructionEmpty q domain ∨
      ¬ ReadoutPreserved readout act rho

/-- The induced group law makes F40's fourth gate automatic. -/
theorem anomaly_induced_group_action_paper {G H Q V : Type}
    (q : H → Q) (act : G → H → H) (domain : G → H → Bool)
    (hq : Function.Surjective q) (mul : G → G → G)
    (readout : H → V) (rho : G → V → V)
    (hO : SymmetryDescentObstructionEmpty q act)
    (haction : ∀ g g' h, act (mul g g') h = act g (act g' h)) :
    (∀ g h, inducedAction q act hq hO g (q h) = q (act g h)) ∧
    GroupLawPreserved mul (inducedAction q act hq hO) ∧
    (SymmetryDescends q act ↔ SymmetryDescentObstructionEmpty q act) ∧
    (DomainDescends q domain ↔ DomainObstructionEmpty q domain) ∧
    (ReadoutPreserved readout act rho ↔
      ReadoutObstructionEmpty readout act rho) ∧
    (InducedAnomaly q act domain readout rho ↔
      ¬ (SymmetryDescends q act ∧ DomainDescends q domain ∧
        GroupLawPreserved mul (inducedAction q act hq hO) ∧
          ReadoutPreserved readout act rho)) := by
  have hprev := anomaly_symmetry_obstruction_induced q act domain hq mul
    readout rho True False hO haction
  refine ⟨inducedAction_commutes q act hq hO, hprev.1,
    hprev.2.1, hprev.2.2.1, hprev.2.2.2.1, ?_⟩
  have hs : SymmetryDescends q act :=
    (symmetry_descends_iff_no_obstruction q act hq).mpr hO
  simp [InducedAnomaly, hO, hs, hprev.1,
    ← (domain_descends_iff_no_obstruction q domain hq)]
  by_cases hdomain : DomainDescends q domain <;> simp [hdomain]

/-- The action obstruction itself is an anomaly and blocks descent. -/
theorem action_obstruction_forces_induced_anomaly {G H Q V : Type}
    (q : H → Q) (act : G → H → H) (domain : G → H → Bool)
    (readout : H → V) (rho : G → V → V)
    (hq : Function.Surjective q)
    (hO : ¬ SymmetryDescentObstructionEmpty q act) :
    ¬ SymmetryDescends q act ∧
      InducedAnomaly q act domain readout rho := by
  exact ⟨fun hdesc => hO ((symmetry_descends_iff_no_obstruction q act hq).mp hdesc),
    Or.inl hO⟩

/-- F40's induced-action case and obstructed case in one theorem. -/
theorem anomaly_induced_group_action_full {G H Q V : Type}
    (q : H → Q) (act : G → H → H) (domain : G → H → Bool)
    (hq : Function.Surjective q) (mul : G → G → G)
    (readout : H → V) (rho : G → V → V)
    (haction : ∀ g g' h, act (mul g g') h = act g (act g' h)) :
    (SymmetryDescends q act ↔ SymmetryDescentObstructionEmpty q act) ∧
    (DomainDescends q domain ↔ DomainObstructionEmpty q domain) ∧
    (ReadoutPreserved readout act rho ↔
      ReadoutObstructionEmpty readout act rho) ∧
    (¬ SymmetryDescentObstructionEmpty q act →
      ¬ SymmetryDescends q act ∧
        InducedAnomaly q act domain readout rho) ∧
    (∀ hO : SymmetryDescentObstructionEmpty q act,
      (∀ g h, inducedAction q act hq hO g (q h) = q (act g h)) ∧
      GroupLawPreserved mul (inducedAction q act hq hO) ∧
      (InducedAnomaly q act domain readout rho ↔
        ¬ (SymmetryDescends q act ∧ DomainDescends q domain ∧
          GroupLawPreserved mul (inducedAction q act hq hO) ∧
            ReadoutPreserved readout act rho))) := by
  refine ⟨symmetry_descends_iff_no_obstruction q act hq,
    domain_descends_iff_no_obstruction q domain hq,
    readout_preserved_iff_no_obstruction readout act rho,
    action_obstruction_forces_induced_anomaly q act domain readout rho hq,
    ?_⟩
  intro hO
  have h := anomaly_induced_group_action_paper q act domain hq mul readout
    rho hO haction
  exact ⟨h.1, h.2.1, h.2.2.2.2.2⟩

/-- A candidate quotient action satisfying the descent equation inherits the
identity action from the raw history action. -/
theorem descended_action_preserves_identity {G H Q : Type}
    (q : H → Q) (act : G → H → H) (actQ : G → Q → Q)
    (hq : Function.Surjective q)
    (hdesc : ∀ g h, actQ g (q h) = q (act g h))
    (e : G) (he : ∀ h, act e h = h) :
    ∀ x, actQ e x = x := by
  intro x
  obtain ⟨h, rfl⟩ := hq x
  rw [hdesc, he]

/-- F40 with an arbitrary descended candidate, its inherited multiplication
and identity laws, and the complete induced-action/obstructed case split. -/
theorem anomaly_symmetry_obstruction_full_paper {G H Q V : Type}
    (q : H → Q) (act : G → H → H) (domain : G → H → Bool)
    (hq : Function.Surjective q) (mul : G → G → G)
    (actQ : G → Q → Q) (readout : H → V) (rho : G → V → V)
    (haction : ∀ g g' h, act (mul g g') h = act g (act g' h)) :
    (SymmetryDescends q act ↔ SymmetryDescentObstructionEmpty q act) ∧
    (DomainDescends q domain ↔ DomainObstructionEmpty q domain) ∧
    (ReadoutPreserved readout act rho ↔
      ReadoutObstructionEmpty readout act rho) ∧
    ((∀ g h, actQ g (q h) = q (act g h)) →
      SymmetryDescentObstructionEmpty q act ∧
      GroupLawPreserved mul actQ ∧
      (∀ e : G, (∀ h, act e h = h) → ∀ x, actQ e x = x)) ∧
    (¬ SymmetryDescentObstructionEmpty q act →
      ¬ SymmetryDescends q act ∧
        InducedAnomaly q act domain readout rho) ∧
    (∀ hO : SymmetryDescentObstructionEmpty q act,
      (∀ g h, inducedAction q act hq hO g (q h) = q (act g h)) ∧
      GroupLawPreserved mul (inducedAction q act hq hO) ∧
      (InducedAnomaly q act domain readout rho ↔
        ¬ (SymmetryDescends q act ∧ DomainDescends q domain ∧
          GroupLawPreserved mul (inducedAction q act hq hO) ∧
            ReadoutPreserved readout act rho))) := by
  have hfull := anomaly_induced_group_action_full q act domain hq mul
    readout rho haction
  refine ⟨hfull.1, hfull.2.1, hfull.2.2.1, ?_,
    hfull.2.2.2.1, hfull.2.2.2.2⟩
  intro hdesc
  refine ⟨descended_action_obstruction_empty q act actQ hdesc, ?_, ?_⟩
  · exact (anomaly_symmetry_obstruction_descended q act domain hq mul actQ
      readout rho True False).2.2.2.2.2 haction hdesc
  · intro e he
    exact descended_action_preserves_identity q act actQ hq hdesc e he

end SixBirdsMetaMath.FoundationsIV.Symmetry.Anomaly
