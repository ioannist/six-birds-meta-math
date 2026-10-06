import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.NS.Carrier
import SixBirdsMetaMath.NS.PDEImports
import SixBirdsMetaMath.NS.Cascade
import SixBirdsMetaMath.NS.GevreyLP

namespace SixBirdsMetaMath.NS.ClosureRecords

open SixBirdsMetaMath.Main.LegalQuotient

/-!
NS paper §7 "Six Birds closure records R1--R9".

- `def:ns:closure-r1-r9` — the bundle `R = (R₁, …, R₉)` of standing
  closure hypotheses on the NS carrier.

Per `paper/notation_and_terminology.md` §4.4, the Lean realization
declares **nine separate top-level proof-carrying structures**
(`R1AdequacyOrientation`, `R2ExactBGPackage`, `R3NullModeLegality`,
`R4SourceAdmission`, `R5BGFrequencyDoubling`, `R6LPTransport`,
`R7HalfLogAnalyticity`, `R8PaperGroundedImports`, `R9NonclaimBoundary`)
plus a `ClosureR1R9` bundle structure that holds the nine record
values as fields. The bundle does **not** carry the conclusion
`T_max = ∞`; that is a downstream consequence (T10), not a bundle
field.
-/

/-- R1: adequacy orientation, with smaller residuals treated as better. -/
structure R1AdequacyOrientation where
  carrierAdequacyOriented : Prop
  smallerXiIsBetter : Prop
  carrierAdequacyOriented_holds : carrierAdequacyOriented
  smallerXiIsBetter_holds : smallerXiIsBetter

/--
R2: exact BG-windowed package preserving divergence-free structure and
the mismatch sector.
-/
structure R2ExactBGPackage where
  exactBGPackage : Prop
  preservesDivergenceFree : Prop
  preservesMismatchSector : Prop
  exactBGPackage_holds : exactBGPackage
  preservesDivergenceFree_holds : preservesDivergenceFree
  preservesMismatchSector_holds : preservesMismatchSector

/-- R3: null-mode legality of `L^{phys}` and `D^{BG}` for `C_{J,t}`. -/
structure R3NullModeLegality where
  nullModeLegal : Prop
  packagedCarrierLegal : Prop
  nullModeLegal_holds : nullModeLegal
  packagedCarrierLegal_holds : packagedCarrierLegal

/--
R4: source-admission recurrence accepted on the cascade, with a concrete
source-admission ledger.
-/
structure R4SourceAdmission where
  e : Nat
  eNext : Nat
  z : Nat
  C_J_t : Mat e e
  C_J_t_h : Mat eNext eNext
  audit_psd_t : PositiveSemidefinite C_J_t
  audit_psd_t_h : PositiveSemidefinite C_J_t_h
  carrierTransport : Mat eNext e
  kernel_preserved :
    ∀ v : Mat e 1,
      matMul C_J_t v = zeroMat e 1 →
      matMul C_J_t_h (matMul carrierTransport v) = zeroMat eNext 1
  ledger : SixBirdsMetaMath.NS.Cascade.sourceAdmissionLedger z
  recurrenceAccepted : Prop
  recurrenceAccepted_holds : recurrenceAccepted

/-- R5: BG frequency-doubling staging `lambda_{j+1} = 2 lambda_j`. -/
structure R5BGFrequencyDoubling where
  lambda : Nat → Rat
  frequencyDoubling : ∀ j, lambda (j + 1) = 2 * lambda j

/--
R6: dissolving-side LP transport accepted as the typed transport with
`s >= q - eps`.
-/
structure R6LPTransport where
  domainDim : Nat
  responseDim : Nat
  transport : SixBirdsMetaMath.NS.GevreyLP.lpTransport domainDim responseDim
  typedTransportAccepted : Prop
  typedTransportAccepted_holds : typedTransportAccepted

/--
R7: half-log analyticity on the smooth-data subcarrier at BG-compatible
stages.
-/
structure R7HalfLogAnalyticity where
  halfLogAnalyticityAccepted : Prop
  smoothDataSubcarrier : Prop
  bgCompatibleStages : Prop
  halfLogAnalyticityAccepted_holds : halfLogAnalyticityAccepted
  smoothDataSubcarrier_holds : smoothDataSubcarrier
  bgCompatibleStages_holds : bgCompatibleStages

/--
R8: paper-grounded PDE imports accepted at declared status.
-/
structure R8PaperGroundedImports where
  bkmImportAccepted : Prop
  bgImportAccepted : Prop
  katoImportAccepted : Prop
  wangHalfLogImportAccepted : Prop
  lpBcdImportAccepted : Prop
  sobolevBesovEmbeddingAccepted : Prop
  bkmImportAccepted_holds : bkmImportAccepted
  bgImportAccepted_holds : bgImportAccepted
  katoImportAccepted_holds : katoImportAccepted
  wangHalfLogImportAccepted_holds : wangHalfLogImportAccepted
  lpBcdImportAccepted_holds : lpBcdImportAccepted
  sobolevBesovEmbeddingAccepted_holds : sobolevBesovEmbeddingAccepted

/--
R9: nonclaim boundary excluding criterion-native replacement, generic
Besov claims, untyped global comparison, and closure outside the
smooth-data subcarrier without additional records.
-/
structure R9NonclaimBoundary where
  noCriterionNativeReplacement : Prop
  noGenericBesovClaim : Prop
  noUntypedGlobalComparison : Prop
  noClosureOutsideSmoothDataWithoutRecords : Prop
  noCriterionNativeReplacement_holds : noCriterionNativeReplacement
  noGenericBesovClaim_holds : noGenericBesovClaim
  noUntypedGlobalComparison_holds : noUntypedGlobalComparison
  noClosureOutsideSmoothDataWithoutRecords_holds :
    noClosureOutsideSmoothDataWithoutRecords

/--
Six Birds closure bundle `R = (R1, ..., R9)`.

This bundle contains only the nine standing proof-carrying records.  It
does not contain a `Tmax = infinity` conclusion; that is the downstream
deliverable theorem.
-/
structure ClosureR1R9 where
  R1 : R1AdequacyOrientation
  R2 : R2ExactBGPackage
  R3 : R3NullModeLegality
  R4 : R4SourceAdmission
  R5 : R5BGFrequencyDoubling
  R6 : R6LPTransport
  R7 : R7HalfLogAnalyticity
  R8 : R8PaperGroundedImports
  R9 : R9NonclaimBoundary

end SixBirdsMetaMath.NS.ClosureRecords
