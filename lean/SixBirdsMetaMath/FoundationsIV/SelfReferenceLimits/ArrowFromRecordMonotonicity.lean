import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F38 Arrow From Record Monotonicity.

A layer arrow is record transport together with monotone transport of
record-defined status. External order, protocol order, or presentation order is
not an autonomous arrow unless it descends to record-status transport.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.ArrowFromRecordMonotonicity

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- Record transport descends when the later record is determined by the
earlier record. -/
def RecordTransportDescends {Hs Rs Ht Rt : Type} (recordSource : Hs → Rs)
    (continuation : Hs → Ht) (recordTarget : Ht → Rt) : Prop :=
  Descends recordSource continuation recordTarget

/-- Record-transport obstruction. -/
def RecordTransportObstruction {Hs Rs Ht Rt : Type} (recordSource : Hs → Rs)
    (continuation : Hs → Ht) (recordTarget : Ht → Rt) : (Hs × Hs) → Prop :=
  splitPairObstruction recordSource continuation recordTarget

/-- No record-transport obstruction is present. -/
def RecordTransportObstructionEmpty {Hs Rs Ht Rt : Type} (recordSource : Hs → Rs)
    (continuation : Hs → Ht) (recordTarget : Ht → Rt) : Prop :=
  ObstructionEmpty (RecordTransportObstruction recordSource continuation recordTarget)

/-- A raw status readout is record-defined when it descends through the record
quotient. -/
def StatusReadoutDescends {H R S : Type} (record : H → R) (status : H → S) :
    Prop :=
  Descends record (fun h : H => h) status

/-- F38's fiber-constancy criterion for factorization through a surjective
record quotient. -/
theorem status_readout_descends_iff_fiber_constant {H R S : Type}
    (record : H → R) (status : H → S)
    (hrecord : Function.Surjective record) :
    StatusReadoutDescends record status ↔
      ∀ h h', record h = record h' → status h = status h' := by
  constructor
  · rintro ⟨sbar, hbar⟩ h h' heq
    calc
      status h = sbar (record h) := (congrFun hbar h).symm
      _ = sbar (record h') := congrArg sbar heq
      _ = status h' := congrFun hbar h'
  · intro hconstant
    apply (descent_repair_normal_form record (fun h : H => h) status
      hrecord).mpr
    rintro ⟨h, h'⟩ ⟨heq, hne⟩
    exact hne (hconstant h h' heq)

/-- Status-overread obstruction: same record, different claimed status. -/
def StatusReadoutObstruction {H R S : Type} (record : H → R) (status : H → S) :
    (H × H) → Prop :=
  splitPairObstruction record (fun h : H => h) status

/-- No status-overread obstruction is present. -/
def StatusReadoutObstructionEmpty {H R S : Type} (record : H → R)
    (status : H → S) : Prop :=
  ObstructionEmpty (StatusReadoutObstruction record status)

/-- Status readout induced by a record-level status map. -/
def recordStatusSignature {H R S : Type} (record : H → R) (statusOfRecord : R → S) :
    H → S :=
  statusOfRecord ∘ record

/-- Raw arrow monotonicity along a continuation. -/
def ArrowMonotone {Hs Ht S : Type} (continuation : Hs → Ht)
    (statusSource : Hs → S) (statusTarget : Ht → S) (Le : S → S → Prop) :
    Prop :=
  ∀ h, Le (statusSource h) (statusTarget (continuation h))

/-- Monotonicity obstruction. -/
def ArrowMonotonicityObstruction {Hs Ht S : Type} (continuation : Hs → Ht)
    (statusSource : Hs → S) (statusTarget : Ht → S) (Le : S → S → Prop) :
    Hs → Prop :=
  fun h => ¬ Le (statusSource h) (statusTarget (continuation h))

/-- No monotonicity obstruction is present. -/
def ArrowMonotonicityObstructionEmpty {Hs Ht S : Type} (continuation : Hs → Ht)
    (statusSource : Hs → S) (statusTarget : Ht → S) (Le : S → S → Prop) :
    Prop :=
  ObstructionEmpty (ArrowMonotonicityObstruction continuation statusSource
    statusTarget Le)

/-- Record-level monotonicity for a descended record transport. -/
def RecordLevelArrow {Rs Rt S : Type} (recordTransport : Rs → Rt)
    (statusSource : Rs → S) (statusTarget : Rt → S) (Le : S → S → Prop) :
    Prop :=
  ∀ r, Le (statusSource r) (statusTarget (recordTransport r))

/-- Strict arrow witness. -/
def StrictArrowWitness {Hs Ht S : Type} (continuation : Hs → Ht)
    (statusSource : Hs → S) (statusTarget : Ht → S) (Lt : S → S → Prop) :
    Prop :=
  ∃ h, Lt (statusSource h) (statusTarget (continuation h))

/-- Strict record arrow: monotone everywhere and strictly increasing somewhere. -/
def StrictRecordArrow {Hs Ht S : Type} (continuation : Hs → Ht)
    (statusSource : Hs → S) (statusTarget : Ht → S)
    (Le Lt : S → S → Prop) : Prop :=
  ArrowMonotone continuation statusSource statusTarget Le ∧
    StrictArrowWitness continuation statusSource statusTarget Lt

/-- Layer arrow gates: record transport descends, statuses are record-defined
at both stages, and status transport is monotone. -/
def LayerArrow {Hs Rs Ht Rt S : Type} (recordSource : Hs → Rs)
    (continuation : Hs → Ht) (recordTarget : Ht → Rt)
    (statusSource : Hs → S) (statusTarget : Ht → S) (Le : S → S → Prop) :
    Prop :=
  RecordTransportDescends recordSource continuation recordTarget ∧
    StatusReadoutDescends recordSource statusSource ∧
      StatusReadoutDescends recordTarget statusTarget ∧
        ArrowMonotone continuation statusSource statusTarget Le

/-- Reversible record transport at status level: forward and backward
record-level maps are both monotone. -/
def ReversibleRecordStatusTransport {Rs Rt S : Type} (forward : Rs → Rt)
    (backward : Rt → Rs) (statusSource : Rs → S) (statusTarget : Rt → S)
    (Le : S → S → Prop) : Prop :=
  RecordLevelArrow forward statusSource statusTarget Le ∧
    RecordLevelArrow backward statusTarget statusSource Le

/-- Budgeted arrow status: monotonicity defects are explicitly within budget. -/
def BudgetedArrow {Index Residual Budget : Type} (defect : Index → Residual)
    (budget : Budget) (WithinBudget : Residual → Budget → Prop) : Prop :=
  ∀ i, WithinBudget (defect i) budget

/-- Probabilistic arrow status with an explicitly declared stochastic order. -/
def ProbabilisticRecordArrow {Rs Law : Type} (kernelLaw : Rs → Law)
    (StochasticMonotone : (Rs → Law) → Prop) : Prop :=
  StochasticMonotone kernelLaw

/-- Erasure is arrow-compatible only when the erasure status is itself ordered
above the source status by the declared order. -/
def ErasureWithRecord {S : Type} (sourceStatus erasedStatus : S)
    (Le : S → S → Prop) : Prop :=
  Le sourceStatus erasedStatus

/-- Source status vocabulary for arrow claims. -/
inductive ArrowStatus where
  | strictRecordArrow
  | weakRecordArrow
  | recordStatusPreserving
  | recordReversible
  | recordTransportFailure
  | statusOverread
  | arrowMonotonicityFailure
  | erasedWithRecord
  | unrecordedErasure
  | informationLoss
  | localArrow
  | globalArrowObstructed
  | probabilisticRecordArrow
  | budgetedArrow
  | protocolArrowArtifact
  | presentationArrowArtifact
  | arrowOverread
deriving DecidableEq

/-- Meaning assignment for the F38 status vocabulary. -/
def ArrowStatusHolds (strict weak preserving reversible transportFailure
    statusOverread monotonicityFailure erased unrecorded infoLoss localOnly
    globalObstructed probabilistic budgeted protocol presentation overread : Prop) :
    ArrowStatus → Prop
  | ArrowStatus.strictRecordArrow => strict
  | ArrowStatus.weakRecordArrow => weak
  | ArrowStatus.recordStatusPreserving => preserving
  | ArrowStatus.recordReversible => reversible
  | ArrowStatus.recordTransportFailure => transportFailure
  | ArrowStatus.statusOverread => statusOverread
  | ArrowStatus.arrowMonotonicityFailure => monotonicityFailure
  | ArrowStatus.erasedWithRecord => erased
  | ArrowStatus.unrecordedErasure => unrecorded
  | ArrowStatus.informationLoss => infoLoss
  | ArrowStatus.localArrow => localOnly
  | ArrowStatus.globalArrowObstructed => globalObstructed
  | ArrowStatus.probabilisticRecordArrow => probabilistic
  | ArrowStatus.budgetedArrow => budgeted
  | ArrowStatus.protocolArrowArtifact => protocol
  | ArrowStatus.presentationArrowArtifact => presentation
  | ArrowStatus.arrowOverread => overread

/-- Record transport descent iff no record-transport obstruction is present. -/
theorem record_transport_descends_iff_no_obstruction {Hs Rs Ht Rt : Type}
    (recordSource : Hs → Rs) (continuation : Hs → Ht)
    (recordTarget : Ht → Rt) (hrecordSource : Function.Surjective recordSource) :
    RecordTransportDescends recordSource continuation recordTarget ↔
      RecordTransportObstructionEmpty recordSource continuation recordTarget :=
  descent_repair_normal_form recordSource continuation recordTarget hrecordSource

/-- Status readout descent iff no status-overread obstruction is present. -/
theorem status_readout_descends_iff_no_obstruction {H R S : Type}
    (record : H → R) (status : H → S) (hrecord : Function.Surjective record) :
    StatusReadoutDescends record status ↔
      StatusReadoutObstructionEmpty record status :=
  descent_repair_normal_form record (fun h : H => h) status hrecord

/-- A record-level status map always gives a record-defined raw status. -/
theorem record_status_signature_descends {H R S : Type} (record : H → R)
    (statusOfRecord : R → S) :
    StatusReadoutDescends record (recordStatusSignature record statusOfRecord) := by
  refine ⟨statusOfRecord, ?_⟩
  funext h
  rfl

/-- Arrow monotonicity iff no monotonicity obstruction is present. -/
theorem arrow_monotone_iff_no_obstruction {Hs Ht S : Type}
    (continuation : Hs → Ht) (statusSource : Hs → S) (statusTarget : Ht → S)
    (Le : S → S → Prop) :
    ArrowMonotone continuation statusSource statusTarget Le ↔
      ArrowMonotonicityObstructionEmpty continuation statusSource statusTarget Le := by
  constructor
  · intro hmono h hobstruction
    exact hobstruction (hmono h)
  · intro hempty h
    exact Classical.byContradiction (fun hnot => hempty h hnot)

/-- Strict arrow is monotonicity plus an explicit strict witness. -/
theorem strict_arrow_iff_monotone_and_witness {Hs Ht S : Type}
    (continuation : Hs → Ht) (statusSource : Hs → S) (statusTarget : Ht → S)
    (Le Lt : S → S → Prop) :
    StrictRecordArrow continuation statusSource statusTarget Le Lt ↔
      ArrowMonotone continuation statusSource statusTarget Le ∧
        StrictArrowWitness continuation statusSource statusTarget Lt := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Layer arrow is exactly the four declared gates. -/
theorem layer_arrow_iff_gates {Hs Rs Ht Rt S : Type} (recordSource : Hs → Rs)
    (continuation : Hs → Ht) (recordTarget : Ht → Rt)
    (statusSource : Hs → S) (statusTarget : Ht → S) (Le : S → S → Prop) :
    LayerArrow recordSource continuation recordTarget statusSource statusTarget Le ↔
      RecordTransportDescends recordSource continuation recordTarget ∧
        StatusReadoutDescends recordSource statusSource ∧
          StatusReadoutDescends recordTarget statusTarget ∧
            ArrowMonotone continuation statusSource statusTarget Le := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Record-level monotonicity plus descended record transport gives raw
monotonicity of the induced status signatures. -/
theorem record_level_arrow_to_raw {Hs Rs Ht Rt S : Type}
    (recordSource : Hs → Rs) (continuation : Hs → Ht)
    (recordTarget : Ht → Rt) (recordTransport : Rs → Rt)
    (statusSource : Rs → S) (statusTarget : Rt → S) (Le : S → S → Prop) :
    recordTransport ∘ recordSource = recordTarget ∘ continuation →
      RecordLevelArrow recordTransport statusSource statusTarget Le →
        ArrowMonotone continuation
          (recordStatusSignature recordSource statusSource)
          (recordStatusSignature recordTarget statusTarget) Le := by
  intro htransport hrecordArrow h
  have htransportAt : recordTransport (recordSource h) = recordTarget (continuation h) :=
    congrFun htransport h
  have hmono := hrecordArrow (recordSource h)
  simpa [recordStatusSignature, Function.comp, htransportAt] using hmono

/--
Arrow From Record Monotonicity Normal Form. A layer arrow is record transport
descent, record-defined status at both stages, and monotone status transport;
strictness is monotonicity plus a strict witness.
-/
theorem arrow_from_record_monotonicity {Hs Rs Ht Rt S : Type}
    (recordSource : Hs → Rs) (continuation : Hs → Ht)
    (recordTarget : Ht → Rt) (statusSourceRaw : Hs → S)
    (statusTargetRaw : Ht → S) (statusSource : Rs → S) (statusTarget : Rt → S)
    (recordTransport : Rs → Rt) (Le Lt : S → S → Prop)
    (hrecordSource : Function.Surjective recordSource)
    (hrecordTarget : Function.Surjective recordTarget) :
    (RecordTransportDescends recordSource continuation recordTarget ↔
      RecordTransportObstructionEmpty recordSource continuation recordTarget) ∧
      (StatusReadoutDescends recordSource statusSourceRaw ↔
        StatusReadoutObstructionEmpty recordSource statusSourceRaw) ∧
        (StatusReadoutDescends recordTarget statusTargetRaw ↔
          StatusReadoutObstructionEmpty recordTarget statusTargetRaw) ∧
          (ArrowMonotone continuation statusSourceRaw statusTargetRaw Le ↔
            ArrowMonotonicityObstructionEmpty continuation statusSourceRaw
              statusTargetRaw Le) ∧
            (StrictRecordArrow continuation statusSourceRaw statusTargetRaw Le Lt ↔
              ArrowMonotone continuation statusSourceRaw statusTargetRaw Le ∧
                StrictArrowWitness continuation statusSourceRaw statusTargetRaw Lt) ∧
              (LayerArrow recordSource continuation recordTarget statusSourceRaw
                  statusTargetRaw Le ↔
                RecordTransportDescends recordSource continuation recordTarget ∧
                  StatusReadoutDescends recordSource statusSourceRaw ∧
                    StatusReadoutDescends recordTarget statusTargetRaw ∧
                      ArrowMonotone continuation statusSourceRaw statusTargetRaw Le) ∧
                (recordTransport ∘ recordSource = recordTarget ∘ continuation →
                  RecordLevelArrow recordTransport statusSource statusTarget Le →
                    ArrowMonotone continuation
                      (recordStatusSignature recordSource statusSource)
                      (recordStatusSignature recordTarget statusTarget) Le) := by
  exact ⟨record_transport_descends_iff_no_obstruction recordSource continuation
      recordTarget hrecordSource,
    status_readout_descends_iff_no_obstruction recordSource statusSourceRaw
      hrecordSource,
    status_readout_descends_iff_no_obstruction recordTarget statusTargetRaw
      hrecordTarget,
    arrow_monotone_iff_no_obstruction continuation statusSourceRaw statusTargetRaw Le,
    strict_arrow_iff_monotone_and_witness continuation statusSourceRaw statusTargetRaw
      Le Lt,
    layer_arrow_iff_gates recordSource continuation recordTarget statusSourceRaw
      statusTargetRaw Le,
    record_level_arrow_to_raw recordSource continuation recordTarget recordTransport
      statusSource statusTarget Le⟩


/-- The paper's arrow is a descended record map monotone on all record classes. -/
def PaperArrow {Hs Rs Ht Rt S : Type}
    (rs : Hs → Rs) (κ : Hs → Ht) (rt : Ht → Rt)
    (ss : Rs → S) (st : Rt → S) (Le : S → S → Prop) : Prop :=
  RecordTransportDescends rs κ rt ∧
    ∀ h, Le (ss (rs h)) (st (rt (κ h)))

/-- Record descent and record-level monotonicity characterize the arrow. -/
theorem paper_arrow_from_record_monotonicity {Hs Rs Ht Rt S : Type}
    (rs : Hs → Rs) (κ : Hs → Ht) (rt : Ht → Rt)
    (ss : Rs → S) (st : Rt → S) (Le : S → S → Prop) (hrs : Function.Surjective rs)
    (_hrt : Function.Surjective rt) :
    (RecordTransportDescends rs κ rt ↔
      ∃ κbar : Rs → Rt, κbar ∘ rs = rt ∘ κ) ∧
    (PaperArrow rs κ rt ss st Le ↔
      ∃ κbar : Rs → Rt, κbar ∘ rs = rt ∘ κ ∧
        ∀ x : Rs, Le (ss x) (st (κbar x))) := by
  constructor
  · rfl
  constructor
  · rintro ⟨⟨κbar, hκ⟩, hmono⟩
    refine ⟨κbar, hκ, ?_⟩
    rintro x
    obtain ⟨h, rfl⟩ := hrs x
    change Le (ss (rs h)) (st (κbar (rs h)))
    have hx : κbar (rs h) = rt (κ h) := congrFun hκ h
    rw [hx]
    exact hmono h
  · rintro ⟨κbar, hκ, hmono⟩
    refine ⟨⟨κbar, hκ⟩, ?_⟩
    intro h
    change Le (ss (rs h)) (st (rt (κ h)))
    have hx : κbar (rs h) = rt (κ h) := congrFun hκ h
    rw [← hx]
    exact hmono (rs h)

/-- F38: fiber constancy constructs the descended record map; target-record
surjectivity is not needed for either direction. -/
theorem paper_arrow_from_record_monotonicity_fiber
    {Hs Rs Ht Rt S : Type}
    (rs : Hs → Rs) (κ : Hs → Ht) (rt : Ht → Rt)
    (ss : Rs → S) (st : Rt → S) (Le : S → S → Prop)
    (hrs : Function.Surjective rs) :
    ((∀ h h', rs h = rs h' → rt (κ h) = rt (κ h')) ↔
      ∃ κbar : Rs → Rt, κbar ∘ rs = rt ∘ κ) ∧
    (PaperArrow rs κ rt ss st Le ↔
      ∃ κbar : Rs → Rt, κbar ∘ rs = rt ∘ κ ∧
        ∀ x : Rs, Le (ss x) (st (κbar x))) := by
  classical
  constructor
  · constructor
    · intro hconst
      let rep : Rs → Hs := fun x => Classical.choose (hrs x)
      refine ⟨fun x => rt (κ (rep x)), ?_⟩
      funext h
      exact hconst (rep (rs h)) h (Classical.choose_spec (hrs (rs h)))
    · rintro ⟨κbar, hκ⟩ h h' hsame
      have hh := congrFun hκ h
      have hh' := congrFun hκ h'
      exact hh.symm.trans ((congrArg κbar hsame).trans hh')
  · constructor
    · rintro ⟨⟨κbar, hκ⟩, hmono⟩
      refine ⟨κbar, hκ, ?_⟩
      intro x
      obtain ⟨h, rfl⟩ := hrs x
      have hx : κbar (rs h) = rt (κ h) := congrFun hκ h
      rw [hx]
      exact hmono h
    · rintro ⟨κbar, hκ, hmono⟩
      refine ⟨⟨κbar, hκ⟩, ?_⟩
      intro h
      have hx : κbar (rs h) = rt (κ h) := congrFun hκ h
      rw [← hx]
      exact hmono (rs h)


end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.ArrowFromRecordMonotonicity
