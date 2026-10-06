/-!
F9 No Unstatused Residual.

A formed stability package may have residuals, obstructions, priced gaps, or
recorded absences. What it may not have is a native residual with no typed
status in its own residual registry.
-/

namespace SixBirdsMetaMath.FoundationsIV.Stability.NoUnstatusedResidual

/-- The judgment family whose classifier assigns a residual status. -/
inductive JudgmentFamily where
  | claim
  | promotion
  | gate
  | square
  | stability
  | visibility
  | residual
deriving DecidableEq

/--
The projected Foundations IV residual-status vocabulary. The concrete
Foundations III status families remain separated by the `JudgmentFamily` tag.
-/
inductive ResidualStatus where
  | outsideScope
  | absentWithRecord
  | blocked
  | undefinedCircular
  | activeObstruction
  | priced
  | accepted
deriving DecidableEq

/-- A status value tagged by the judgment family that produced it. -/
structure TypedStatus where
  family : JudgmentFamily
  status : ResidualStatus

/-- A residual record has a native locus and the data needed by a total
classifier. The fields stand for the typed residual kind, threshold/audit data,
visibility record, and classifier output described in the source. -/
structure ResidualRecord (Residual : Type) where
  locus : Residual
  residualKindDeclared : Prop
  thresholdDeclared : Prop
  auditDeclared : Prop
  visibilityRecorded : Prop
  classifierFamily : JudgmentFamily
  classifierStatus : ResidualStatus

/-- The family-tagged status extracted from a residual record. -/
def ResidualRecord.typedStatus {Residual : Type} (record : ResidualRecord Residual) :
    TypedStatus :=
  { family := record.classifierFamily, status := record.classifierStatus }

/--
A formed stability package has a covering residual record for every native
residual, the covering record is unique at that locus, and the record is
well-formed enough for its classifier to return a typed status.
-/
structure FormedStabilityPackage (Residual : Type) where
  Record : Type
  toResidualRecord : Record → ResidualRecord Residual
  recordOf : Residual → Record
  record_covers : ∀ r : Residual, (toResidualRecord (recordOf r)).locus = r
  record_unique :
    ∀ (r : Residual) (record : Record),
      (toResidualRecord record).locus = r → record = recordOf r
  record_well_formed :
    ∀ record : Record,
      (toResidualRecord record).residualKindDeclared ∧
        (toResidualRecord record).thresholdDeclared ∧
          (toResidualRecord record).auditDeclared ∧
            (toResidualRecord record).visibilityRecorded

/-- The package's total status assignment for native residuals. -/
def statusAssignment {Residual : Type} (pkg : FormedStabilityPackage Residual)
    (r : Residual) : TypedStatus :=
  (pkg.toResidualRecord (pkg.recordOf r)).typedStatus

/-- A native residual has some typed status record. -/
def HasTypedStatus {Residual : Type} (pkg : FormedStabilityPackage Residual)
    (r : Residual) : Prop :=
  ∃ record : pkg.Record,
    (pkg.toResidualRecord record).locus = r ∧
      ∃ status : TypedStatus, (pkg.toResidualRecord record).typedStatus = status

/-- The typed status is unique across all records covering the same residual
locus. -/
def HasUniqueTypedStatus {Residual : Type} (pkg : FormedStabilityPackage Residual)
    (r : Residual) : Prop :=
  ∃ record : pkg.Record,
    (pkg.toResidualRecord record).locus = r ∧
      ∀ other : pkg.Record,
        (pkg.toResidualRecord other).locus = r →
          (pkg.toResidualRecord other).typedStatus =
            (pkg.toResidualRecord record).typedStatus

/-- An unstatused native residual is a residual with no typed status record. -/
def UnstatusedResidual {Residual : Type} (pkg : FormedStabilityPackage Residual)
    (r : Residual) : Prop :=
  ¬ HasTypedStatus pkg r

/-- Every covering record in a formed package has the declared well-formedness
fields needed by its classifier. -/
theorem covering_record_well_formed {Residual : Type}
    (pkg : FormedStabilityPackage Residual) (r : Residual) :
    (pkg.toResidualRecord (pkg.recordOf r)).residualKindDeclared ∧
      (pkg.toResidualRecord (pkg.recordOf r)).thresholdDeclared ∧
        (pkg.toResidualRecord (pkg.recordOf r)).auditDeclared ∧
          (pkg.toResidualRecord (pkg.recordOf r)).visibilityRecorded :=
  pkg.record_well_formed (pkg.recordOf r)

/--
No Unstatused Residual Normal Form. In a formed stability package, every
native residual has a typed status, that status is unique at its residual
locus, and therefore no native residual is unstatused.
-/
theorem no_unstatused_residual {Residual : Type}
    (pkg : FormedStabilityPackage Residual) :
    (∀ r : Residual, HasTypedStatus pkg r) ∧
      (∀ r : Residual, HasUniqueTypedStatus pkg r) ∧
        ∀ r : Residual, ¬ UnstatusedResidual pkg r := by
  constructor
  · intro r
    refine ⟨pkg.recordOf r, pkg.record_covers r, ?_⟩
    exact ⟨statusAssignment pkg r, rfl⟩
  · constructor
    · intro r
      refine ⟨pkg.recordOf r, pkg.record_covers r, ?_⟩
      intro other hother
      have hrecord : other = pkg.recordOf r := pkg.record_unique r other hother
      rw [hrecord]
    · intro r hunstatused
      exact hunstatused ⟨pkg.recordOf r, pkg.record_covers r,
        ⟨statusAssignment pkg r, rfl⟩⟩

/-- Record coverage, without uniqueness of records at a locus. -/
def RecordCoverage {Residual Record : Type}
    (locus : Record → Residual) : Prop :=
  ∀ r, ∃ rec, locus rec = r

/-- Agreement of typed statuses at a common residual locus. -/
def StatusCoherent {Residual Record : Type}
    (locus : Record → Residual) (status : Record → TypedStatus) : Prop :=
  ∀ rec rec', locus rec = locus rec' → status rec = status rec'

/-- A status assignment on loci represents every record exactly when
common-locus records agree, assuming record coverage. -/
theorem status_assignment_exists_iff_coherent
    {Residual Record : Type} (locus : Record → Residual)
    (status : Record → TypedStatus) (hcover : RecordCoverage locus) :
    (∃ st : Residual → TypedStatus, ∀ rec, st (locus rec) = status rec) ↔
      StatusCoherent locus status := by
  classical
  constructor
  · rintro ⟨st, hst⟩ rec rec' heq
    calc
      status rec = st (locus rec) := (hst rec).symm
      _ = st (locus rec') := congrArg st heq
      _ = status rec' := hst rec'
  · intro hcoherent
    let chosen : Residual → Record := fun r => Classical.choose (hcover r)
    refine ⟨fun r => status (chosen r), ?_⟩
    intro rec
    exact hcoherent (chosen (locus rec)) rec
      (Classical.choose_spec (hcover (locus rec)))

/-- With typed statuses on records, coverage is equivalent to absence of an
unstatused locus. -/
theorem record_coverage_iff_no_unstatused
    {Residual Record : Type} (locus : Record → Residual)
    (status : Record → TypedStatus) :
    RecordCoverage locus ↔
      ∀ r, ¬ (¬ ∃ rec, locus rec = r ∧
        ∃ s : TypedStatus, status rec = s) := by
  constructor
  · intro hc r hnone
    obtain ⟨rec, hrec⟩ := hc r
    exact hnone ⟨rec, hrec, status rec, rfl⟩
  · intro h r
    have hex : ∃ rec, locus rec = r ∧
        ∃ s : TypedStatus, status rec = s := Classical.byContradiction (h r)
    obtain ⟨rec, hrec, _⟩ := hex
    exact ⟨rec, hrec⟩

/-- F9 under coverage and common-locus status agreement, with both converses. -/
theorem no_unstatused_residual_coherent
    {Residual Record : Type} (locus : Record → Residual)
    (status : Record → TypedStatus) (hcover : RecordCoverage locus)
    (hcoherent : StatusCoherent locus status) :
    (∀ r, ∃ rec, locus rec = r ∧ ∃ s : TypedStatus, status rec = s) ∧
    (∀ r, ∃ s : TypedStatus, ∀ rec, locus rec = r → status rec = s) ∧
    (∀ r, ¬ (¬ ∃ rec, locus rec = r ∧
      ∃ s : TypedStatus, status rec = s)) ∧
    ((∃ st : Residual → TypedStatus,
      ∀ rec, st (locus rec) = status rec) ↔ StatusCoherent locus status) ∧
    (RecordCoverage locus ↔
      ∀ r, ¬ (¬ ∃ rec, locus rec = r ∧
        ∃ s : TypedStatus, status rec = s)) := by
  refine ⟨?_, ?_, ?_, status_assignment_exists_iff_coherent locus status hcover,
    record_coverage_iff_no_unstatused locus status⟩
  · intro r
    obtain ⟨rec, hrec⟩ := hcover r
    exact ⟨rec, hrec, status rec, rfl⟩
  · intro r
    obtain ⟨rec, hrec⟩ := hcover r
    refine ⟨status rec, ?_⟩
    intro other hother
    exact (hcoherent rec other (hrec.trans hother.symm)).symm
  · exact (record_coverage_iff_no_unstatused locus status).mp hcover

/-- F9 for any declared typed-status carrier. The classifier's codomain is
`Status`, so no particular list of status families is assumed. -/
theorem no_unstatused_residual_arbitrary_status
    {Residual Record Status : Type} (locus : Record → Residual)
    (status : Record → Status) (hcover : RecordCoverage locus)
    (hcoherent : ∀ rec rec', locus rec = locus rec' → status rec = status rec') :
    (∀ r, ∃ rec, locus rec = r ∧ ∃ s : Status, status rec = s) ∧
    (∀ r, ∃ s : Status, ∀ rec, locus rec = r → status rec = s) ∧
    (∀ r, ¬ (¬ ∃ rec, locus rec = r ∧
      ∃ s : Status, status rec = s)) ∧
    ((∃ st : Residual → Status,
      ∀ rec, st (locus rec) = status rec) ↔
      ∀ rec rec', locus rec = locus rec' → status rec = status rec') ∧
    (RecordCoverage locus ↔
      ∀ r, ¬ (¬ ∃ rec, locus rec = r ∧
        ∃ s : Status, status rec = s)) := by
  classical
  have hassign :
      (∃ st : Residual → Status,
        ∀ rec, st (locus rec) = status rec) ↔
        ∀ rec rec', locus rec = locus rec' → status rec = status rec' := by
    constructor
    · rintro ⟨st, hst⟩ rec rec' heq
      calc
        status rec = st (locus rec) := (hst rec).symm
        _ = st (locus rec') := congrArg st heq
        _ = status rec' := hst rec'
    · intro hsame
      let chosen : Residual → Record := fun r => Classical.choose (hcover r)
      refine ⟨fun r => status (chosen r), ?_⟩
      intro rec
      exact hsame (chosen (locus rec)) rec
        (Classical.choose_spec (hcover (locus rec)))
  have hcoverage : RecordCoverage locus ↔
      ∀ r, ¬ (¬ ∃ rec, locus rec = r ∧
        ∃ s : Status, status rec = s) := by
    constructor
    · intro hc r hnone
      obtain ⟨rec, hrec⟩ := hc r
      exact hnone ⟨rec, hrec, status rec, Eq.refl _⟩
    · intro h r
      have hex : ∃ rec, locus rec = r ∧
          ∃ s : Status, status rec = s := Classical.byContradiction (h r)
      obtain ⟨rec, hrec, _⟩ := hex
      exact ⟨rec, hrec⟩
  refine ⟨?_, ?_, hcoverage.mp hcover, hassign, hcoverage⟩
  · intro r
    obtain ⟨rec, hrec⟩ := hcover r
    exact ⟨rec, hrec, status rec, Eq.refl _⟩
  · intro r
    obtain ⟨rec, hrec⟩ := hcover r
    refine ⟨status rec, ?_⟩
    intro other hother
    exact (hcoherent rec other (hrec.trans hother.symm)).symm

/-- A locus assignment exists exactly when statuses agree at each covered locus. -/
theorem status_assignment_exists_iff_coherent_any_status
    {Residual Record Status : Type} (locus : Record → Residual)
    (status : Record → Status) (hcover : RecordCoverage locus) :
    (∃ st : Residual → Status, ∀ rec, st (locus rec) = status rec) ↔
      ∀ rec rec', locus rec = locus rec' → status rec = status rec' := by
  classical
  constructor
  · rintro ⟨st, hst⟩ rec rec' heq
    calc
      status rec = st (locus rec) := (hst rec).symm
      _ = st (locus rec') := congrArg st heq
      _ = status rec' := hst rec'
  · intro hsame
    let chosen : Residual → Record := fun r => Classical.choose (hcover r)
    refine ⟨fun r => status (chosen r), ?_⟩
    intro rec
    exact hsame (chosen (locus rec)) rec
      (Classical.choose_spec (hcover (locus rec)))

/-- Coverage is equivalent to absence of an unstatused locus, for any status carrier. -/
theorem record_coverage_iff_no_unstatused_any_status
    {Residual Record Status : Type} (locus : Record → Residual)
    (status : Record → Status) :
    RecordCoverage locus ↔
      ∀ r, ¬ (¬ ∃ rec, locus rec = r ∧ ∃ s : Status, status rec = s) := by
  classical
  constructor
  · intro hc r hnone
    obtain ⟨rec, hrec⟩ := hc r
    exact hnone ⟨rec, hrec, status rec, rfl⟩
  · intro h r
    have hex : ∃ rec, locus rec = r ∧ ∃ s : Status, status rec = s :=
      Classical.byContradiction (h r)
    obtain ⟨rec, hrec, _⟩ := hex
    exact ⟨rec, hrec⟩

/-- F9 with coverage and coherence scoped to the clauses that use them. -/
theorem no_unstatused_residual_paper_scoped
    {Residual Record Status : Type} (locus : Record → Residual)
    (status : Record → Status) :
    ((RecordCoverage locus ∧
      (∀ rec rec', locus rec = locus rec' → status rec = status rec')) →
      (∀ r, ∃ rec, locus rec = r ∧ ∃ s : Status, status rec = s) ∧
      (∀ r, ∃ s : Status, ∀ rec, locus rec = r → status rec = s) ∧
      (∀ r, ¬ (¬ ∃ rec, locus rec = r ∧ ∃ s : Status, status rec = s))) ∧
    (RecordCoverage locus →
      ((∃ st : Residual → Status, ∀ rec, st (locus rec) = status rec) ↔
        ∀ rec rec', locus rec = locus rec' → status rec = status rec')) ∧
    (RecordCoverage locus ↔
      ∀ r, ¬ (¬ ∃ rec, locus rec = r ∧ ∃ s : Status, status rec = s)) := by
  refine ⟨?_, status_assignment_exists_iff_coherent_any_status locus status,
    record_coverage_iff_no_unstatused_any_status locus status⟩
  rintro ⟨hcover, hcoherent⟩
  refine ⟨?_, ?_, (record_coverage_iff_no_unstatused_any_status locus status).mp hcover⟩
  · intro r
    obtain ⟨rec, hrec⟩ := hcover r
    exact ⟨rec, hrec, status rec, rfl⟩
  · intro r
    obtain ⟨rec, hrec⟩ := hcover r
    refine ⟨status rec, ?_⟩
    intro other hother
    exact (hcoherent rec other (hrec.trans hother.symm)).symm

end SixBirdsMetaMath.FoundationsIV.Stability.NoUnstatusedResidual
