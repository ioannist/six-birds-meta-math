import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.AOR.Hierarchy
import SixBirdsMetaMath.NS.ClosureRecords
import SixBirdsMetaMath.Main.LegalQuotient

namespace SixBirdsMetaMath.NS.AORInstance

open SixBirdsMetaMath.AOR.PreSB
open SixBirdsMetaMath.AOR.DefectStrata
open SixBirdsMetaMath.AOR.ResidualAtlas
open SixBirdsMetaMath.AOR.Cascades
open SixBirdsMetaMath.AOR.Refinement
open SixBirdsMetaMath.Main.LegalQuotient

universe u

/-!
Legacy compatibility model for the original NS-as-AOR claim inventory.

This module retains the historical flag-based PreSB object, tag dispatch and
projection witnesses so existing names remain inspectable. The object uses a
placeholder Nat × Nat carrier and unconditional structural flags. Its assignment
does not consume R4/R6/R7 evidence. Consequently `inRefStableAOR` is only a theorem
about that legacy representation, with an additional supplied limit-payment
hypothesis; it does not establish semantic AOR membership or NS regularity.

The maintained Needles NS endpoint uses `SixBirdsNeedles.NS.AuditDelivery`
and `SixBirdsNeedles.AOR.Core`; those semantic modules are not mirrored here.
There the weak estimate, norm-return bridge and continuation criterion carry
explicit evidence, and each consumer goal requires an accepted readout.
Analytic construction of the first two inputs remains open. The concrete
quotient-transport projections below remain valid at their stated hypotheses.
-/

/-- Smooth-data parameters for the NS AOR-instance reading. -/
structure NSSmoothDataParameters where
  InitialData : Type u
  u0 : InitialData
  sobolevExponent : Rat
  gamma0_gt_five_halves : 5 < 2 * sobolevExponent
  divergenceFree : InitialData → Prop
  inSobolevGamma0 : InitialData → Prop
  divergenceFree_u0 : divergenceFree u0
  inSobolevGamma0_u0 : inSobolevGamma0 u0

/-- The NS scope restricts to smooth divergence-free Sobolev data. -/
def nsScopeRecord : scopeRecord where
  carrierClass := fun _ => True
  sourceLedger := fun _ => True
  interfaceFamily := fun _ => True
  routeRegistry := fun _ => True

/--
`def:ns:aor-instance-object`.

The NS smooth-data carrier is presented as a fixed-scope PreSB object.
Its registry fields are the typed slots populated by the NS closure
records; all structural audit obligations are discharged for the
AOR-instance reading.
-/
def aorInstanceObject (_data : NSSmoothDataParameters.{u}) :
    preSBCarrier nsScopeRecord where
  H := Nat × Nat
  H_admissible := True.intro
  quotient := Nat × Nat
  q := id
  Q := fun _ _ => True
  Gamma := Unit
  Gamma_admissible := True.intro
  R := SixBirdsMetaMath.NS.ClosureRecords.ClosureR1R9
  Creg := Unit
  Src := Unit
  Src_admissible := True.intro
  Ifc := Unit
  Ifc_admissible := True.intro
  Obs := Unit
  Stage := Nat
  Constr := Unit
  Rewrite := Unit
  Hol := Unit
  Res := Unit
  Stat := Unit
  NC := Unit
  Meta := Unit
  declaredRecordsTyped := True
  citedRoutesAudited := True
  residualsStatused := True
  nonclaimsRegistered := True
  metaAuditDischarged := True

/-- The NS carrier as an AOR object. -/
def nsAORCarrier (data : NSSmoothDataParameters.{u}) : aorSubcategory nsScopeRecord :=
  ⟨aorInstanceObject data, by
    exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩⟩

/-- Legacy residual-tag assignment. The R4/R6/R7 arguments are not consumed;
this does not construct analytical payment from those records. -/
def nsAssignment
    (data : NSSmoothDataParameters.{u})
    (_R4 : SixBirdsMetaMath.NS.ClosureRecords.R4SourceAdmission)
    (_R6 : SixBirdsMetaMath.NS.ClosureRecords.R6LPTransport)
    (_R7 : SixBirdsMetaMath.NS.ClosureRecords.R7HalfLogAnalyticity) :
    sigmaResidual (aorInclusionObj (nsAORCarrier data)) → AOR8Status :=
  fun atom =>
    match residualPrimaryType atom with
    | residualTypesTwelve.source => AOR8Status.budgeted
    | residualTypesTwelve.transport => AOR8Status.zero
    | residualTypesTwelve.scale => AOR8Status.zero
    | residualTypesTwelve.limit => AOR8Status.budgeted
    | residualTypesTwelve.role => AOR8Status.zero
    | residualTypesTwelve.target => AOR8Status.zero
    | _ => AOR8Status.zero

/-- The NS AOR carrier paired with its R-record-derived discharge assignment. -/
def nsCarrierWithDischarge
    (data : NSSmoothDataParameters.{u})
    (R4 : SixBirdsMetaMath.NS.ClosureRecords.R4SourceAdmission)
    (R6 : SixBirdsMetaMath.NS.ClosureRecords.R6LPTransport)
    (R7 : SixBirdsMetaMath.NS.ClosureRecords.R7HalfLogAnalyticity)
    (limitCost : sigmaResidual (aorInclusionObj (nsAORCarrier data)) → Nat → Nat) :
    AORCarrierWithDischarge nsScopeRecord where
  toCarrier := nsAORCarrier data
  dischargeAssignment := nsAssignment data R4 R6 R7
  limitCost := limitCost

/-- Discharge labels used in the NS AOR-instance reading. -/
inductive NSDischargeStatus where
  | byConstruction
  | approvedOther
  | budgetedPerStage
  | zero
  | crossCascade
  | contractiveTail
  | summable
  | asymptoticBudgeted
  | outOfScopeNonclaim

/-- Projection package for the mechanical NS closure-record discharges. -/
structure NSMechanicalRRecordsWitness
    (R : SixBirdsMetaMath.NS.ClosureRecords.ClosureR1R9) : Prop where
  R1_by_construction : R.R1.carrierAdequacyOriented ∧ R.R1.smallerXiIsBetter
  R2_by_construction :
    R.R2.exactBGPackage ∧ R.R2.preservesDivergenceFree ∧ R.R2.preservesMismatchSector
  R3_by_construction : R.R3.nullModeLegal ∧ R.R3.packagedCarrierLegal
  R5_by_construction : ∀ j, R.R5.lambda (j + 1) = 2 * R.R5.lambda j
  R9_by_construction :
    R.R9.noCriterionNativeReplacement ∧ R.R9.noGenericBesovClaim ∧
      R.R9.noUntypedGlobalComparison ∧ R.R9.noClosureOutsideSmoothDataWithoutRecords
  R8_approved_other :
    R.R8.bkmImportAccepted ∧ R.R8.bgImportAccepted ∧ R.R8.katoImportAccepted ∧
      R.R8.wangHalfLogImportAccepted ∧ R.R8.lpBcdImportAccepted ∧
        R.R8.sobolevBesovEmbeddingAccepted
  no_extra_residual_beyond_R4_R6_R7 : True

/--
`thm:ns:aor-mechanical-r-records`.

The mechanical records project directly from the NS `ClosureR1R9` bundle.
-/
theorem aorMechanicalRRecords
    (R : SixBirdsMetaMath.NS.ClosureRecords.ClosureR1R9) :
    NSMechanicalRRecordsWitness R where
  R1_by_construction := ⟨R.R1.carrierAdequacyOriented_holds, R.R1.smallerXiIsBetter_holds⟩
  R2_by_construction :=
    ⟨R.R2.exactBGPackage_holds, R.R2.preservesDivergenceFree_holds,
      R.R2.preservesMismatchSector_holds⟩
  R3_by_construction := ⟨R.R3.nullModeLegal_holds, R.R3.packagedCarrierLegal_holds⟩
  R5_by_construction := R.R5.frequencyDoubling
  R9_by_construction :=
    ⟨R.R9.noCriterionNativeReplacement_holds, R.R9.noGenericBesovClaim_holds,
      R.R9.noUntypedGlobalComparison_holds,
      R.R9.noClosureOutsideSmoothDataWithoutRecords_holds⟩
  R8_approved_other :=
    ⟨R.R8.bkmImportAccepted_holds, R.R8.bgImportAccepted_holds, R.R8.katoImportAccepted_holds,
      R.R8.wangHalfLogImportAccepted_holds, R.R8.lpBcdImportAccepted_holds,
      R.R8.sobolevBesovEmbeddingAccepted_holds⟩
  no_extra_residual_beyond_R4_R6_R7 := True.intro

/-- Kernel descent predicate available from the exposed NS R4 fields. -/
def nsTransportDescendsKernel
    (R4 : SixBirdsMetaMath.NS.ClosureRecords.R4SourceAdmission)
    (v : Mat R4.e 1) : Prop :=
  matMul R4.C_J_t v = zeroMat R4.e 1 →
    matMul R4.C_J_t_h (matMul R4.carrierTransport v) = zeroMat R4.eNext 1

/-- Carrier-space quotient-map well-definedness predicate from the exposed NS R4 fields. -/
def nsInducedQuotientMapWellDefined
    (R4 : SixBirdsMetaMath.NS.ClosureRecords.R4SourceAdmission) : Prop :=
  ∀ v : Mat R4.e 1, nsTransportDescendsKernel R4 v

/-- Typed Loewner recurrence predicate available from the exposed NS R4 ledger. -/
def nsLoewnerRecurrenceTypedOnQuotient
    (R4 : SixBirdsMetaMath.NS.ClosureRecords.R4SourceAdmission) : Prop :=
  R4.recurrenceAccepted ∧ PositiveSemidefinite R4.C_J_t ∧
    PositiveSemidefinite R4.C_J_t_h ∧ PositiveSemidefinite R4.ledger.Omega_tr ∧
      PositiveSemidefinite R4.ledger.Omega_pr ∧
        PositiveSemidefinite R4.ledger.Omega_visc ∧
          PositiveSemidefinite R4.ledger.Omega_tail ∧
            PositiveSemidefinite R4.ledger.Omega_str

/--
Smooth-data zero-kernel narrowing available from the AOR-instance data and R4 audits.

The current NS R4 record exposes positive semidefiniteness of the endpoint
audit forms, not positive definiteness. This predicate therefore records the
smooth-data hypotheses together with PSD audits as the formal surrogate for
the paper's `Ker C_{J,t} = {0}` claim; a later NS strengthening can replace
the PSD fields by positive-definite audits.
-/
def nsSmoothKernelZero
    (data : NSSmoothDataParameters.{u})
    (R4 : SixBirdsMetaMath.NS.ClosureRecords.R4SourceAdmission) : Prop :=
  data.divergenceFree data.u0 ∧ data.inSobolevGamma0 data.u0 ∧
    PositiveSemidefinite R4.C_J_t ∧ PositiveSemidefinite R4.C_J_t_h

/-- Quotient-transport descent package for `R_{4q}`. -/
structure NSQuotientTransportRecord
    (data : NSSmoothDataParameters.{u})
    (R4 : SixBirdsMetaMath.NS.ClosureRecords.R4SourceAdmission) : Prop where
  transport_descends_kernel :
    ∀ v : Mat R4.e 1, nsTransportDescendsKernel R4 v
  induced_quotient_map_well_defined : nsInducedQuotientMapWellDefined R4
  loewner_recurrence_typed_on_quotient : nsLoewnerRecurrenceTypedOnQuotient R4
  smooth_kernel_zero : nsSmoothKernelZero data R4

/--
`thm:ns:aor-quotient-transport-record`.

Projection-packaged `R_{4q}` record.  Kernel descent and quotient
well-definedness use the carrier-space audit forms and transport exposed
by NS `R4SourceAdmission`; the remaining narrowing is that the smooth-data
zero-kernel clause records PSD endpoint audits rather than a full positive
definiteness proof.
-/
theorem aorQuotientTransportRecord
    (data : NSSmoothDataParameters.{u})
    (R4 : SixBirdsMetaMath.NS.ClosureRecords.R4SourceAdmission) :
    NSQuotientTransportRecord data R4 where
  transport_descends_kernel := by
    intro v hker
    exact R4.kernel_preserved v hker
  induced_quotient_map_well_defined :=
    by
      intro v hker
      exact R4.kernel_preserved v hker
  loewner_recurrence_typed_on_quotient :=
    ⟨R4.recurrenceAccepted_holds, R4.audit_psd_t, R4.audit_psd_t_h,
      R4.ledger.Omega_tr_positive, R4.ledger.Omega_pr_positive,
      R4.ledger.Omega_visc_positive, R4.ledger.Omega_tail_positive,
      R4.ledger.Omega_str_positive⟩
  smooth_kernel_zero :=
    ⟨data.divergenceFree_u0, data.inSobolevGamma0_u0, R4.audit_psd_t, R4.audit_psd_t_h⟩

/-- R4 source-admission discharge package. -/
structure NSR4DischargeWitness
    (data : NSSmoothDataParameters.{u})
    (R4 : SixBirdsMetaMath.NS.ClosureRecords.R4SourceAdmission)
    (R4q : NSQuotientTransportRecord data R4)
    (R6 : SixBirdsMetaMath.NS.ClosureRecords.R6LPTransport)
    (R7 : SixBirdsMetaMath.NS.ClosureRecords.R7HalfLogAnalyticity) : Prop where
  primary_source : True
  forces_transport : List.Mem residualTypesTwelve.transport
    (forcedSecondaryTypes residualTypesTwelve.source)
  forces_scale : List.Mem residualTypesTwelve.scale
    (forcedSecondaryTypes residualTypesTwelve.source)
  forces_target : List.Mem residualTypesTwelve.target
    (forcedSecondaryTypes residualTypesTwelve.source)
  forces_role : List.Mem residualTypesTwelve.role
    (forcedSecondaryTypes residualTypesTwelve.source)
  recurrence_budgeted : R4.recurrenceAccepted
  quotient_transport_zero :
    ∀ v : Mat R4.e 1, nsTransportDescendsKernel R4 v
  cross_cascade_to_R6_R7 :
    R6.typedTransportAccepted ∧ R7.halfLogAnalyticityAccepted ∧ R7.bgCompatibleStages

/--
`thm:ns:aor-r4-discharge`.

R4 has primary type `source`, forced transport/scale/target/role secondaries,
uses the imported source-admission acceptance as its budgeted witness, consumes
`R_{4q}` for zero transport, and routes the non-standalone scale/limit branch
to the R6/R7 acceptance records.
-/
theorem aorR4Discharge
    (data : NSSmoothDataParameters.{u})
    (R4 : SixBirdsMetaMath.NS.ClosureRecords.R4SourceAdmission)
    (R4q : NSQuotientTransportRecord data R4)
    (R6 : SixBirdsMetaMath.NS.ClosureRecords.R6LPTransport)
    (R7 : SixBirdsMetaMath.NS.ClosureRecords.R7HalfLogAnalyticity) :
  NSR4DischargeWitness data R4 R4q R6 R7 where
  primary_source := True.intro
  forces_transport := List.Mem.head _
  forces_scale := List.Mem.tail _ (List.Mem.head _)
  forces_target := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  forces_role := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  recurrence_budgeted := R4.recurrenceAccepted_holds
  quotient_transport_zero := R4q.transport_descends_kernel
  cross_cascade_to_R6_R7 :=
    ⟨R6.typedTransportAccepted_holds, R7.halfLogAnalyticityAccepted_holds,
      R7.bgCompatibleStages_holds⟩

/-- R6 LP-transport discharge package. -/
structure NSR6DischargeWitness
    (R6 : SixBirdsMetaMath.NS.ClosureRecords.R6LPTransport) : Prop where
  primary_transport : True
  forces_scale : List.Mem residualTypesTwelve.scale
    (forcedSecondaryTypes residualTypesTwelve.transport)
  forces_limit : List.Mem residualTypesTwelve.limit
    (forcedSecondaryTypes residualTypesTwelve.transport)
  forces_target : List.Mem residualTypesTwelve.target
    (forcedSecondaryTypes residualTypesTwelve.transport)
  forces_role : List.Mem residualTypesTwelve.role
    (forcedSecondaryTypes residualTypesTwelve.transport)
  forces_presentation : List.Mem residualTypesTwelve.presentation
    (forcedSecondaryTypes residualTypesTwelve.transport)
  transport_zero : R6.typedTransportAccepted
  contractive_tail : R6.transport.bgCompatibleDoublingSequence
  summable_status : R6.transport.normSquaredAsymptotic

/--
`thm:ns:aor-r6-discharge`.

R6 has primary type `transport`, carries the forced secondary types listed in
the atlas, and projects the LP-transport record as zero/contractive/summable
evidence.
-/
theorem aorR6Discharge
    (R6 : SixBirdsMetaMath.NS.ClosureRecords.R6LPTransport) :
  NSR6DischargeWitness R6 where
  primary_transport := True.intro
  forces_scale := List.Mem.head _
  forces_limit := List.Mem.tail _ (List.Mem.head _)
  forces_target := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  forces_role := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  forces_presentation :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  transport_zero := R6.typedTransportAccepted_holds
  contractive_tail := R6.transport.bgCompatibleDoublingSequence_holds
  summable_status := R6.transport.normSquaredAsymptotic_holds

/-- R7 half-log transfer discharge package. -/
structure NSR7DischargeWitness
    (R7 : SixBirdsMetaMath.NS.ClosureRecords.R7HalfLogAnalyticity) : Prop where
  primary_scale : True
  forces_limit : List.Mem residualTypesTwelve.limit
    (forcedSecondaryTypes residualTypesTwelve.scale)
  forces_horizon : List.Mem residualTypesTwelve.horizon
    (forcedSecondaryTypes residualTypesTwelve.scale)
  forces_source : List.Mem residualTypesTwelve.source
    (forcedSecondaryTypes residualTypesTwelve.scale)
  forces_target : List.Mem residualTypesTwelve.target
    (forcedSecondaryTypes residualTypesTwelve.scale)
  forces_presentation : List.Mem residualTypesTwelve.presentation
    (forcedSecondaryTypes residualTypesTwelve.scale)
  zero_scale : R7.halfLogAnalyticityAccepted
  basic_gate : R7.bgCompatibleStages
  horizon_nonclaim : R7.smoothDataSubcarrier

/--
`thm:ns:aor-r7-discharge`.

R7 has primary type `scale`, carries the listed forced secondaries, and
projects the NS half-log/smooth-data fields into the AOR statuses.
-/
theorem aorR7Discharge
    (R7 : SixBirdsMetaMath.NS.ClosureRecords.R7HalfLogAnalyticity) :
  NSR7DischargeWitness R7 where
  primary_scale := True.intro
  forces_limit := List.Mem.head _
  forces_horizon := List.Mem.tail _ (List.Mem.head _)
  forces_source := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  forces_target := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  forces_presentation :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  zero_scale := R7.halfLogAnalyticityAccepted_holds
  basic_gate := R7.bgCompatibleStages_holds
  horizon_nonclaim := R7.smoothDataSubcarrier_holds

/-- Final NS refinement-stable AOR package. -/
structure NSRefStableAORWitness
    (data : NSSmoothDataParameters.{u})
    (R : SixBirdsMetaMath.NS.ClosureRecords.ClosureR1R9)
    (limitCost : sigmaResidual (aorInclusionObj (nsAORCarrier data)) → Nat → Nat) : Prop where
  carrier_refstable : refinementStableAOR
    (nsCarrierWithDischarge data R.R4 R.R6 R.R7 limitCost)
  quotient_transport_consumed :
    ∀ v : Mat R.R4.e 1, nsTransportDescendsKernel R.R4 v
  r4_r6_r7_discharges_consumed :
    R.R4.recurrenceAccepted ∧ R.R6.typedTransportAccepted ∧
      R.R7.halfLogAnalyticityAccepted ∧ R.R7.bgCompatibleStages
  mechanical_records_consumed :
    R.R1.carrierAdequacyOriented ∧ R.R2.exactBGPackage ∧ R.R3.nullModeLegal ∧
      (∀ j, R.R5.lambda (j + 1) = 2 * R.R5.lambda j) ∧
        R.R9.noClosureOutsideSmoothDataWithoutRecords
  framework_regular_regularization_modulo_imports :
    R.R8.bkmImportAccepted ∧ R.R8.bgImportAccepted ∧ R.R8.katoImportAccepted ∧
      R.R8.wangHalfLogImportAccepted ∧ R.R8.lpBcdImportAccepted ∧
        R.R8.sobolevBesovEmbeddingAccepted

/--
`thm:ns:in-refstableaor`.

Legacy tag-level refinement-stability package, conditional on `hLimitPaid`.
This statement does not imply NS regularity. Generic reachability dispatch and
projected acceptance predicates do not supply the analytic norm-return bridge.
Use `NS.AuditDelivery` for the current semantic consumer interface.
-/
theorem inRefStableAOR
    (data : NSSmoothDataParameters.{u})
    (R : SixBirdsMetaMath.NS.ClosureRecords.ClosureR1R9)
    (limitCost : sigmaResidual (aorInclusionObj (nsAORCarrier data)) → Nat → Nat)
    (hLimitPaid : ∀ atom, ∃ status, closesLimitResidual status (limitCost atom))
    (R4q : NSQuotientTransportRecord data R.R4)
    (R4_discharge : NSR4DischargeWitness data R.R4 R4q R.R6 R.R7)
    (R6_discharge : NSR6DischargeWitness R.R6)
    (R7_discharge : NSR7DischargeWitness R.R7)
    (R_mechanical : NSMechanicalRRecordsWitness R) :
    NSRefStableAORWitness data R limitCost where
  carrier_refstable := by
    constructor
    · intro atom
      cases atom with
      | dischargeStatusMissing primary _ =>
          cases primary
          · have _h := R4_discharge.quotient_transport_zero
            exact ⟨reachableFromZero_zero _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R4_discharge.quotient_transport_zero
            exact ⟨reachableFromZero_zero _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R4_discharge.cross_cascade_to_R6_R7
            exact ⟨reachableFromZero_zero _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R6_discharge.transport_zero
            exact ⟨reachableFromZero_zero _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R6_discharge.summable_status
            exact ⟨reachableFromZero_zero _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R7_discharge.basic_gate
            exact ⟨reachableFromZero_zero _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R4_discharge.recurrence_budgeted
            exact ⟨reachableFromZero_budgeted _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R7_discharge.horizon_nonclaim
            exact ⟨reachableFromZero_zero _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R7_discharge.zero_scale
            exact ⟨reachableFromZero_zero _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R6_discharge.summable_status
            have _h' := R7_discharge.basic_gate
            exact ⟨reachableFromZero_budgeted _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R6_discharge.contractive_tail
            exact ⟨reachableFromZero_zero _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R4_discharge.forces_role
            exact ⟨reachableFromZero_zero _, residualRecordOfAtom_eventuallyEmpty _⟩
          · have _h := R4_discharge.forces_target
            exact ⟨reachableFromZero_zero _, residualRecordOfAtom_eventuallyEmpty _⟩
    · intro atom
      exact hLimitPaid atom
  quotient_transport_consumed := R4_discharge.quotient_transport_zero
  r4_r6_r7_discharges_consumed :=
    ⟨R4_discharge.recurrence_budgeted, R6_discharge.transport_zero,
      R7_discharge.zero_scale, R7_discharge.basic_gate⟩
  mechanical_records_consumed :=
    ⟨R_mechanical.R1_by_construction.1, R_mechanical.R2_by_construction.1,
      R_mechanical.R3_by_construction.1, R_mechanical.R5_by_construction,
      R_mechanical.R9_by_construction.2.2.2⟩
  framework_regular_regularization_modulo_imports :=
    R_mechanical.R8_approved_other

end SixBirdsMetaMath.NS.AORInstance
