import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F20 Fact / Record Formation.

A fact is an event-value decoded from a stable record quotient: the event
descends to the record, the record quotient transports, and decoded fact-values
commute with declared updates.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.FactRecordFormation

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- Record signature produced at the event stage by formation route and record
quotient. -/
def recordSignature {H0 H1 R1 : Type} (γ : H0 → H1) (ρ1 : H1 → R1) :
    H0 → R1 :=
  fun h => ρ1 (γ h)

/-- The event value is recorded when it factors through the formed record
signature. -/
def EventRecorded {H0 E H1 R1 : Type} (ε : H0 → E) (γ : H0 → H1)
    (ρ1 : H1 → R1) : Prop :=
  Descends (recordSignature γ ρ1) (fun h : H0 => h) ε

/-- Event-to-record split pair: same record, different event value. -/
def EventRecordObstruction {H0 E H1 R1 : Type} (ε : H0 → E) (γ : H0 → H1)
    (ρ1 : H1 → R1) : (H0 × H0) → Prop :=
  splitPairObstruction (recordSignature γ ρ1) (fun h : H0 => h) ε

/-- No event-to-record obstruction is present. -/
def EventRecordObstructionEmpty {H0 E H1 R1 : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) : Prop :=
  ObstructionEmpty (EventRecordObstruction ε γ ρ1)

/-- Redundant-record obstruction: same event value, different formed record. -/
def RedundantRecordObstruction {H0 E H1 R1 : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) : (H0 × H0) → Prop :=
  fun pair =>
    ε pair.1 = ε pair.2 ∧
      recordSignature γ ρ1 pair.1 ≠ recordSignature γ ρ1 pair.2

/-- No redundant-record obstruction is present. -/
def RedundantRecordObstructionEmpty {H0 E H1 R1 : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) : Prop :=
  ObstructionEmpty (RedundantRecordObstruction ε γ ρ1)

/-- A coarse fact records a coarsening of the event value. -/
def CoarseFact {H0 E Ec H1 R1 : Type} (ε : H0 → E) (coarsen : E → Ec)
    (γ : H0 → H1) (ρ1 : H1 → R1) : Prop :=
  EventRecorded (coarsen ∘ ε) γ ρ1

/-- Record quotient stability along a declared continuation. -/
def RecordStable {Hs Rs Ht Rt : Type} (ρs : Hs → Rs) (θ : Hs → Ht)
    (ρt : Ht → Rt) : Prop :=
  Descends ρs θ ρt

/-- Record-stability obstruction. -/
def RecordStabilityObstruction {Hs Rs Ht Rt : Type} (ρs : Hs → Rs)
    (θ : Hs → Ht) (ρt : Ht → Rt) : (Hs × Hs) → Prop :=
  splitPairObstruction ρs θ ρt

/-- No record-stability obstruction is present. -/
def RecordStabilityObstructionEmpty {Hs Rs Ht Rt : Type} (ρs : Hs → Rs)
    (θ : Hs → Ht) (ρt : Ht → Rt) : Prop :=
  ObstructionEmpty (RecordStabilityObstruction ρs θ ρt)

/-- Decoded fact-values commute with declared fact-value update. -/
def FactValueStable {Rs Rt Es Et : Type} (θbar : Rs → Rt) (ds : Rs → Es)
    (dt : Rt → Et) (update : Es → Et) : Prop :=
  ∀ r : Rs, dt (θbar r) = update (ds r)

/-- Fact-value stability defect. -/
def FactValueStabilityDefect {Rs Rt Es Et : Type} (θbar : Rs → Rt)
    (ds : Rs → Es) (dt : Rt → Et) (update : Es → Et) : Rs → Prop :=
  fun r => dt (θbar r) ≠ update (ds r)

/-- No fact-value stability defect is present. -/
def FactValueStabilityDefectEmpty {Rs Rt Es Et : Type} (θbar : Rs → Rt)
    (ds : Rs → Es) (dt : Rt → Et) (update : Es → Et) : Prop :=
  ObstructionEmpty (FactValueStabilityDefect θbar ds dt update)

/-- Stable fact: event records, record transports, and decoded value commutes
with the declared update. -/
def StableFact {H0 E H1 R1 Hs Rs Ht Rt Es Et : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) (ρs : Hs → Rs) (θ : Hs → Ht)
    (ρt : Ht → Rt) (θbar : Rs → Rt) (ds : Rs → Es) (dt : Rt → Et)
    (update : Es → Et) : Prop :=
  EventRecorded ε γ ρ1 ∧ RecordStable ρs θ ρt ∧
    FactValueStable θbar ds dt update

/-- Canonical record refinement carrying both old record and event value. -/
def recordEventExtension {H0 E H1 R1 : Type} (ε : H0 → E) (γ : H0 → H1)
    (ρ1 : H1 → R1) : H0 → R1 × E :=
  fun h => (recordSignature γ ρ1 h, ε h)

/-- The record/event extension retains the old record signature. -/
def RetainsRecord {H0 R1 Ext : Type} (record : H0 → R1) (extension : H0 → Ext) :
    Prop :=
  Descends extension (fun h : H0 => h) record

/-- The record/event extension carries the event value. -/
def CarriesEvent {H0 E Ext : Type} (extension : H0 → Ext) (ε : H0 → E) :
    Prop :=
  Descends extension (fun h : H0 => h) ε

/-- Idempotent record packaging. -/
def IdempotentPackaging {H : Type} (C : H → H) : Prop :=
  ∀ h : H, C (C h) = C h

/-- Fixed point of a record packaging map. -/
def FixedByPackaging {H : Type} (C : H → H) (h : H) : Prop :=
  C h = h

/-- Four exact record comparison statuses. -/
inductive RecordComparisonStatus where
  | exactRecord
  | redundantRecord
  | ambiguousRecord
  | incomparableRecord
deriving DecidableEq

/-- Meaning of each exact record comparison status. -/
def RecordComparisonStatusHolds {H0 E H1 R1 : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) : RecordComparisonStatus → Prop
  | RecordComparisonStatus.exactRecord =>
      EventRecordObstructionEmpty ε γ ρ1 ∧ RedundantRecordObstructionEmpty ε γ ρ1
  | RecordComparisonStatus.redundantRecord =>
      EventRecordObstructionEmpty ε γ ρ1 ∧ ¬ RedundantRecordObstructionEmpty ε γ ρ1
  | RecordComparisonStatus.ambiguousRecord =>
      ¬ EventRecordObstructionEmpty ε γ ρ1 ∧ RedundantRecordObstructionEmpty ε γ ρ1
  | RecordComparisonStatus.incomparableRecord =>
      ¬ EventRecordObstructionEmpty ε γ ρ1 ∧
        ¬ RedundantRecordObstructionEmpty ε γ ρ1

/-- Exactly one exact record-comparison status applies. -/
def ExactlyOneRecordComparisonStatus {H0 E H1 R1 : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) : Prop :=
  ∃ status : RecordComparisonStatus,
    RecordComparisonStatusHolds ε γ ρ1 status ∧
      ∀ other : RecordComparisonStatus,
        RecordComparisonStatusHolds ε γ ρ1 other → other = status

/-- Broader F20 status vocabulary. -/
inductive FactRecordStatus where
  | rawEvent
  | recordedEvent
  | stableFact
  | unstableRecord
  | factValueInstability
  | ambiguousRecord
  | redundantRecord
  | coarseFact
  | evidenceRecord
  | probabilisticRecord
  | erasedWithRecord
  | tombstoneRecord
  | recordHolonomy
  | factOverread
  | unsupportedFact
deriving DecidableEq

/-- Meaning assignment for the F20 status vocabulary. -/
def FactRecordStatusHolds (raw recorded stable unstable valueInstability ambiguous
    redundant coarse evidence probabilistic erased tombstone holonomy overread
    unsupported : Prop) : FactRecordStatus → Prop
  | FactRecordStatus.rawEvent => raw
  | FactRecordStatus.recordedEvent => recorded
  | FactRecordStatus.stableFact => stable
  | FactRecordStatus.unstableRecord => unstable
  | FactRecordStatus.factValueInstability => valueInstability
  | FactRecordStatus.ambiguousRecord => ambiguous
  | FactRecordStatus.redundantRecord => redundant
  | FactRecordStatus.coarseFact => coarse
  | FactRecordStatus.evidenceRecord => evidence
  | FactRecordStatus.probabilisticRecord => probabilistic
  | FactRecordStatus.erasedWithRecord => erased
  | FactRecordStatus.tombstoneRecord => tombstone
  | FactRecordStatus.recordHolonomy => holonomy
  | FactRecordStatus.factOverread => overread
  | FactRecordStatus.unsupportedFact => unsupported

/-- Event-to-record descent is exactly absence of the event-record obstruction. -/
theorem event_recorded_iff_no_obstruction {H0 E H1 R1 : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1)
    (hrecord : Function.Surjective (recordSignature γ ρ1)) :
    EventRecorded ε γ ρ1 ↔ EventRecordObstructionEmpty ε γ ρ1 :=
  descent_repair_normal_form (recordSignature γ ρ1) (fun h : H0 => h) ε hrecord

/-- Record transport stability is exactly absence of the record-stability
obstruction. -/
theorem record_stable_iff_no_obstruction {Hs Rs Ht Rt : Type} (ρs : Hs → Rs)
    (θ : Hs → Ht) (ρt : Ht → Rt) (hρs : Function.Surjective ρs) :
    RecordStable ρs θ ρt ↔ RecordStabilityObstructionEmpty ρs θ ρt :=
  descent_repair_normal_form ρs θ ρt hρs

/-- Fact-value stability is exactly absence of fact-value stability defects. -/
theorem fact_value_stable_iff_no_defect {Rs Rt Es Et : Type} (θbar : Rs → Rt)
    (ds : Rs → Es) (dt : Rt → Et) (update : Es → Et) :
    FactValueStable θbar ds dt update ↔
      FactValueStabilityDefectEmpty θbar ds dt update := by
  constructor
  · intro hstable r hdefect
    exact hdefect (hstable r)
  · intro hempty r
    exact Classical.byContradiction (fun hneq => hempty r hneq)

/-- Stable fact formation is exactly the three empty-obstruction gates. -/
theorem stable_fact_iff_no_obstructions
    {H0 E H1 R1 Hs Rs Ht Rt Es Et : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) (ρs : Hs → Rs) (θ : Hs → Ht)
    (ρt : Ht → Rt) (θbar : Rs → Rt) (ds : Rs → Es) (dt : Rt → Et)
    (update : Es → Et)
    (hrecord : Function.Surjective (recordSignature γ ρ1))
    (hρs : Function.Surjective ρs) :
    StableFact ε γ ρ1 ρs θ ρt θbar ds dt update ↔
      EventRecordObstructionEmpty ε γ ρ1 ∧
        RecordStabilityObstructionEmpty ρs θ ρt ∧
          FactValueStabilityDefectEmpty θbar ds dt update := by
  constructor
  · intro hfact
    exact ⟨(event_recorded_iff_no_obstruction ε γ ρ1 hrecord).1 hfact.1,
      (record_stable_iff_no_obstruction ρs θ ρt hρs).1 hfact.2.1,
      (fact_value_stable_iff_no_defect θbar ds dt update).1 hfact.2.2⟩
  · intro h
    exact ⟨(event_recorded_iff_no_obstruction ε γ ρ1 hrecord).2 h.1,
      (record_stable_iff_no_obstruction ρs θ ρt hρs).2 h.2.1,
      (fact_value_stable_iff_no_defect θbar ds dt update).2 h.2.2⟩

/-- The canonical record/event extension retains the old record. -/
theorem record_extension_retains_record {H0 E H1 R1 : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) :
    RetainsRecord (recordSignature γ ρ1) (recordEventExtension ε γ ρ1) := by
  refine ⟨Prod.fst, ?_⟩
  funext h
  rfl

/-- The canonical record/event extension carries the event value. -/
theorem record_extension_carries_event {H0 E H1 R1 : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) :
    CarriesEvent (recordEventExtension ε γ ρ1) ε := by
  refine ⟨Prod.snd, ?_⟩
  funext h
  rfl

/-- Idempotent packaging sends every state to a fixed record-stable state. -/
theorem idempotent_packaging_fixed {H : Type} (C : H → H) :
    IdempotentPackaging C → ∀ h : H, FixedByPackaging C (C h) := by
  intro hidem h
  exact hidem h

/-- The exact record comparison has one status. -/
theorem record_comparison_status_partition {H0 E H1 R1 : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) :
    ExactlyOneRecordComparisonStatus ε γ ρ1 := by
  classical
  by_cases hrec : EventRecordObstructionEmpty ε γ ρ1
  · by_cases hred : RedundantRecordObstructionEmpty ε γ ρ1
    · refine ⟨RecordComparisonStatus.exactRecord, ⟨hrec, hred⟩, ?_⟩
      intro other hother
      cases other with
      | exactRecord => rfl
      | redundantRecord => exact False.elim (hother.2 hred)
      | ambiguousRecord => exact False.elim (hother.1 hrec)
      | incomparableRecord => exact False.elim (hother.1 hrec)
    · refine ⟨RecordComparisonStatus.redundantRecord, ⟨hrec, hred⟩, ?_⟩
      intro other hother
      cases other with
      | exactRecord => exact False.elim (hred hother.2)
      | redundantRecord => rfl
      | ambiguousRecord => exact False.elim (hother.1 hrec)
      | incomparableRecord => exact False.elim (hother.1 hrec)
  · by_cases hred : RedundantRecordObstructionEmpty ε γ ρ1
    · refine ⟨RecordComparisonStatus.ambiguousRecord, ⟨hrec, hred⟩, ?_⟩
      intro other hother
      cases other with
      | exactRecord => exact False.elim (hrec hother.1)
      | redundantRecord => exact False.elim (hrec hother.1)
      | ambiguousRecord => rfl
      | incomparableRecord => exact False.elim (hother.2 hred)
    · refine ⟨RecordComparisonStatus.incomparableRecord, ⟨hrec, hred⟩, ?_⟩
      intro other hother
      cases other with
      | exactRecord => exact False.elim (hrec hother.1)
      | redundantRecord => exact False.elim (hrec hother.1)
      | ambiguousRecord => exact False.elim (hred hother.2)
      | incomparableRecord => rfl

/--
Fact / Record Formation Normal Form. An event becomes a stable fact exactly
when its event value descends to the formed record, record transport descends
along the declared continuation, and decoded fact-values commute with the
declared update. The canonical repair extends the record by the event value,
and idempotent packaging lands in fixed record states.
-/
theorem fact_record_formation
    {H0 E H1 R1 Hs Rs Ht Rt Es Et H : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) (ρs : Hs → Rs) (θ : Hs → Ht)
    (ρt : Ht → Rt) (θbar : Rs → Rt) (ds : Rs → Es) (dt : Rt → Et)
    (update : Es → Et) (C : H → H)
    (hrecord : Function.Surjective (recordSignature γ ρ1))
    (hρs : Function.Surjective ρs) :
    (EventRecorded ε γ ρ1 ↔ EventRecordObstructionEmpty ε γ ρ1) ∧
      (RecordStable ρs θ ρt ↔ RecordStabilityObstructionEmpty ρs θ ρt) ∧
        (FactValueStable θbar ds dt update ↔
          FactValueStabilityDefectEmpty θbar ds dt update) ∧
          (StableFact ε γ ρ1 ρs θ ρt θbar ds dt update ↔
            EventRecordObstructionEmpty ε γ ρ1 ∧
              RecordStabilityObstructionEmpty ρs θ ρt ∧
                FactValueStabilityDefectEmpty θbar ds dt update) ∧
            ExactlyOneRecordComparisonStatus ε γ ρ1 ∧
              RetainsRecord (recordSignature γ ρ1) (recordEventExtension ε γ ρ1) ∧
                CarriesEvent (recordEventExtension ε γ ρ1) ε ∧
                  (IdempotentPackaging C → ∀ h : H, FixedByPackaging C (C h)) := by
  exact ⟨event_recorded_iff_no_obstruction ε γ ρ1 hrecord,
    record_stable_iff_no_obstruction ρs θ ρt hρs,
    fact_value_stable_iff_no_defect θbar ds dt update,
    stable_fact_iff_no_obstructions ε γ ρ1 ρs θ ρt θbar ds dt update hrecord hρs,
    record_comparison_status_partition ε γ ρ1,
    record_extension_retains_record ε γ ρ1,
    record_extension_carries_event ε γ ρ1,
    idempotent_packaging_fixed C⟩

/-- When the declared record transport is the descended raw transport,
fact-value stability is exactly the raw-history fact-value equation. -/
theorem fact_value_stable_iff_raw_transport
    {Hs Rs Ht Rt Es Et : Type}
    (ρs : Hs → Rs) (θ : Hs → Ht) (ρt : Ht → Rt)
    (θbar : Rs → Rt) (ds : Rs → Es) (dt : Rt → Et)
    (update : Es → Et) (hρs : Function.Surjective ρs)
    (hdesc : θbar ∘ ρs = ρt ∘ θ) :
    FactValueStable θbar ds dt update ↔
      ∀ h, dt (ρt (θ h)) = update (ds (ρs h)) := by
  constructor
  · intro hstable h
    have hh := congrFun hdesc h
    dsimp [Function.comp] at hh
    exact hh.symm ▸ hstable (ρs h)
  · intro hraw rs
    obtain ⟨h, rfl⟩ := hρs rs
    have hh := congrFun hdesc h
    dsimp [Function.comp] at hh
    exact hh ▸ hraw h

/-- F20 with the raw-history fact-value clause for a descended record transport. -/
theorem paper_fact_record_formation_with_raw_transport
    {H0 E H1 R1 Hs Rs Ht Rt Es Et H : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) (ρs : Hs → Rs) (θ : Hs → Ht)
    (ρt : Ht → Rt) (θbar : Rs → Rt) (ds : Rs → Es) (dt : Rt → Et)
    (update : Es → Et) (C : H → H)
    (hrecord : Function.Surjective (recordSignature γ ρ1))
    (hρs : Function.Surjective ρs) (hdesc : θbar ∘ ρs = ρt ∘ θ) :
    ((EventRecorded ε γ ρ1 ↔ EventRecordObstructionEmpty ε γ ρ1) ∧
      (RecordStable ρs θ ρt ↔ RecordStabilityObstructionEmpty ρs θ ρt) ∧
        (FactValueStable θbar ds dt update ↔
          FactValueStabilityDefectEmpty θbar ds dt update) ∧
          (StableFact ε γ ρ1 ρs θ ρt θbar ds dt update ↔
            EventRecordObstructionEmpty ε γ ρ1 ∧
              RecordStabilityObstructionEmpty ρs θ ρt ∧
                FactValueStabilityDefectEmpty θbar ds dt update) ∧
            ExactlyOneRecordComparisonStatus ε γ ρ1 ∧
              RetainsRecord (recordSignature γ ρ1) (recordEventExtension ε γ ρ1) ∧
                CarriesEvent (recordEventExtension ε γ ρ1) ε ∧
                  (IdempotentPackaging C → ∀ h : H, FixedByPackaging C (C h))) ∧
    (FactValueStable θbar ds dt update ↔
      ∀ h, dt (ρt (θ h)) = update (ds (ρs h))) := by
  exact ⟨fact_record_formation ε γ ρ1 ρs θ ρt θbar ds dt update C hrecord hρs,
    fact_value_stable_iff_raw_transport ρs θ ρt θbar ds dt update hρs hdesc⟩

/-- The image of a packaging map, as a predicate on records. -/
def PackagingRange {H : Type} (C : H → H) : H → Prop :=
  fun h => ∃ x, C x = h

/-- A packaging map is idempotent exactly when its image is its fixed locus. -/
theorem idempotent_packaging_iff_range_fixed {H : Type} (C : H → H) :
    IdempotentPackaging C ↔ PackagingRange C = (fun h : H => C h = h) := by
  constructor
  · intro hidem
    funext h
    apply propext
    constructor
    · rintro ⟨x, rfl⟩
      exact hidem x
    · intro hfixed
      exact ⟨h, hfixed⟩
  · intro hrange h
    have hh : PackagingRange C (C h) := ⟨h, rfl⟩
    rw [hrange] at hh
    exact hh

/-- F20 with the exact idempotent-image law and the raw fact-value clause. -/
theorem paper_fact_record_formation_idempotent_range
    {H0 E H1 R1 Hs Rs Ht Rt Es Et H : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) (ρs : Hs → Rs) (θ : Hs → Ht)
    (ρt : Ht → Rt) (θbar : Rs → Rt) (ds : Rs → Es) (dt : Rt → Et)
    (update : Es → Et) (C : H → H)
    (hrecord : Function.Surjective (recordSignature γ ρ1))
    (hρs : Function.Surjective ρs) (hdesc : θbar ∘ ρs = ρt ∘ θ) :
    ((EventRecorded ε γ ρ1 ↔ EventRecordObstructionEmpty ε γ ρ1) ∧
      (RecordStable ρs θ ρt ↔ RecordStabilityObstructionEmpty ρs θ ρt) ∧
        (FactValueStable θbar ds dt update ↔
          FactValueStabilityDefectEmpty θbar ds dt update) ∧
          (StableFact ε γ ρ1 ρs θ ρt θbar ds dt update ↔
            EventRecordObstructionEmpty ε γ ρ1 ∧
              RecordStabilityObstructionEmpty ρs θ ρt ∧
                FactValueStabilityDefectEmpty θbar ds dt update) ∧
            ExactlyOneRecordComparisonStatus ε γ ρ1 ∧
              RetainsRecord (recordSignature γ ρ1) (recordEventExtension ε γ ρ1) ∧
                CarriesEvent (recordEventExtension ε γ ρ1) ε ∧
                  (IdempotentPackaging C ↔
                    PackagingRange C = (fun h : H => C h = h))) ∧
    (FactValueStable θbar ds dt update ↔
      ∀ h, dt (ρt (θ h)) = update (ds (ρs h))) := by
  rcases paper_fact_record_formation_with_raw_transport ε γ ρ1 ρs θ ρt θbar
    ds dt update C hrecord hρs hdesc with
    ⟨⟨h1, h2, h3, h4, h5, h6, h7, _⟩, hraw⟩
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7,
    idempotent_packaging_iff_range_fixed C⟩, hraw⟩

/-- F20 with the transport equation confined to its final moreover clause. -/
theorem paper_fact_record_formation_conditional_raw_transport
    {H0 E H1 R1 Hs Rs Ht Rt Es Et H : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) (ρs : Hs → Rs) (θ : Hs → Ht)
    (ρt : Ht → Rt) (θbar : Rs → Rt) (ds : Rs → Es) (dt : Rt → Et)
    (update : Es → Et) (C : H → H)
    (hrecord : Function.Surjective (recordSignature γ ρ1))
    (hρs : Function.Surjective ρs) :
    (EventRecorded ε γ ρ1 ↔ EventRecordObstructionEmpty ε γ ρ1) ∧
    (RecordStable ρs θ ρt ↔ RecordStabilityObstructionEmpty ρs θ ρt) ∧
    (FactValueStable θbar ds dt update ↔
      FactValueStabilityDefectEmpty θbar ds dt update) ∧
    (StableFact ε γ ρ1 ρs θ ρt θbar ds dt update ↔
      EventRecordObstructionEmpty ε γ ρ1 ∧
        RecordStabilityObstructionEmpty ρs θ ρt ∧
          FactValueStabilityDefectEmpty θbar ds dt update) ∧
    ExactlyOneRecordComparisonStatus ε γ ρ1 ∧
    RetainsRecord (recordSignature γ ρ1) (recordEventExtension ε γ ρ1) ∧
    CarriesEvent (recordEventExtension ε γ ρ1) ε ∧
    (IdempotentPackaging C ↔
      PackagingRange C = (fun h : H => C h = h)) ∧
    (θbar ∘ ρs = ρt ∘ θ →
      (FactValueStable θbar ds dt update ↔
        ∀ h, dt (ρt (θ h)) = update (ds (ρs h)))) := by
  rcases fact_record_formation ε γ ρ1 ρs θ ρt θbar ds dt update C
    hrecord hρs with ⟨h1, h2, h3, h4, h5, h6, h7, _⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7,
    idempotent_packaging_iff_range_fixed C,
    fun hdesc => fact_value_stable_iff_raw_transport ρs θ ρt θbar ds dt
      update hρs hdesc⟩

/-- When the event decoder and record transport commute with their raw maps,
fact-value stability transports the original event along the continuation. -/
theorem fact_value_stable_transports_event {H0 E H1 R1 Ht Rt Et : Type}
    (ε : H0 → E) (γ : H0 → H1) (ρ1 : H1 → R1)
    (θ : H1 → Ht) (ρt : Ht → Rt) (θbar : R1 → Rt)
    (ds : R1 → E) (dt : Rt → Et) (update : E → Et)
    (hdecode : ds ∘ ρ1 ∘ γ = ε)
    (hdesc : θbar ∘ ρ1 = ρt ∘ θ)
    (hstable : FactValueStable θbar ds dt update) :
    dt ∘ ρt ∘ θ ∘ γ = update ∘ ε := by
  funext h
  calc
    dt (ρt (θ (γ h))) = dt (θbar (ρ1 (γ h))) :=
      congrArg dt (congrFun hdesc (γ h)).symm
    _ = update (ds (ρ1 (γ h))) := hstable (ρ1 (γ h))
    _ = update (ε h) := congrArg update (congrFun hdecode h)

/-- F20 retains its general formation clauses and adds the event-to-fact link
for the specialized source stage and event decoder, guarded by their two
commuting equations. -/
theorem paper_fact_record_formation_conditional_raw_transport_with_event
    {H0 E H1 R1 Hs Rs Ht Rt Es Et H : Type} (ε : H0 → E)
    (γ : H0 → H1) (ρ1 : H1 → R1) (ρs : Hs → Rs) (θ : Hs → Ht)
    (ρt : Ht → Rt) (θbar : Rs → Rt) (ds : Rs → Es) (dt : Rt → Et)
    (update : Es → Et) (C : H → H)
    (hrecord : Function.Surjective (recordSignature γ ρ1))
    (hρs : Function.Surjective ρs) :
    ((EventRecorded ε γ ρ1 ↔ EventRecordObstructionEmpty ε γ ρ1) ∧
    (RecordStable ρs θ ρt ↔ RecordStabilityObstructionEmpty ρs θ ρt) ∧
    (FactValueStable θbar ds dt update ↔
      FactValueStabilityDefectEmpty θbar ds dt update) ∧
    (StableFact ε γ ρ1 ρs θ ρt θbar ds dt update ↔
      EventRecordObstructionEmpty ε γ ρ1 ∧
        RecordStabilityObstructionEmpty ρs θ ρt ∧
          FactValueStabilityDefectEmpty θbar ds dt update) ∧
    ExactlyOneRecordComparisonStatus ε γ ρ1 ∧
    RetainsRecord (recordSignature γ ρ1) (recordEventExtension ε γ ρ1) ∧
    CarriesEvent (recordEventExtension ε γ ρ1) ε ∧
    (IdempotentPackaging C ↔
      PackagingRange C = (fun h : H => C h = h)) ∧
    (θbar ∘ ρs = ρt ∘ θ →
      (FactValueStable θbar ds dt update ↔
        ∀ h, dt (ρt (θ h)) = update (ds (ρs h))))) ∧
    (∀ {Ht' Rt' Et' : Type} (θevent : H1 → Ht') (ρtevent : Ht' → Rt')
      (θbarevent : R1 → Rt') (dsevent : R1 → E) (dtevent : Rt' → Et')
      (updateEvent : E → Et'),
      dsevent ∘ ρ1 ∘ γ = ε →
      θbarevent ∘ ρ1 = ρtevent ∘ θevent →
      FactValueStable θbarevent dsevent dtevent updateEvent →
      dtevent ∘ ρtevent ∘ θevent ∘ γ = updateEvent ∘ ε) := by
  refine ⟨paper_fact_record_formation_conditional_raw_transport ε γ ρ1 ρs θ ρt
    θbar ds dt update C hrecord hρs, ?_⟩
  intro Ht' Rt' Et' θevent ρtevent θbarevent dsevent dtevent updateEvent
    hdecode hdesc hstable
  exact fact_value_stable_transports_event ε γ ρ1 θevent ρtevent θbarevent
    dsevent dtevent updateEvent hdecode hdesc hstable

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.FactRecordFormation
