import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.NS.Carrier
import SixBirdsMetaMath.NS.PDEImports
import SixBirdsMetaMath.NS.ClosureRecords
import SixBirdsMetaMath.NS.Cascade
import SixBirdsMetaMath.NS.NoGo
import SixBirdsMetaMath.NS.GevreyLP
import SixBirdsMetaMath.NS.CriterionNativeGap

namespace SixBirdsMetaMath.NS.MainTheorem

/-!
NS paper §8 "Main theorem under Six Birds closure".

- `thm:ns:framework-deliverable-regularity` (T10) — under the closure
  record bundle `R = (R₁,…,R₉)` and the typed-context discipline, for
  every divergence-free `u₀ ∈ H^{γ₀}` with `γ₀ > 5/2`,
  `T_max(u₀) = ∞`. Status: `partial` / `projection_packaged`. The
  retained Lean realization applies the explicitly supplied
  `closureDeliverable` implication, whose consequent is the full
  regularity conclusion. It does not derive a T4/T6/T8/T9/BKM
  implication chain from analytical estimates. The maintained Needles
  endpoint separates the weak estimate, criterion return and continuation
  inputs; both endpoints remain conditional on their stated bridges.
-/

/--
Framework-deliverable NS regularity.

The closure bundle itself contains only the nine standing records.  The
regularity conclusion is obtained by applying the typed-context
deliverability bridge to those records and to the smooth-data
hypotheses on `u0`.
-/
theorem frameworkDeliverableRegularity {InitialData Lifespan : Type}
    (R : SixBirdsMetaMath.NS.ClosureRecords.ClosureR1R9)
    (typedContextDiscipline : Prop)
    (sobolevExponent : Rat)
    (divergenceFree inSobolevGamma0 acceptedSmoothDataChannel :
      InitialData → Prop)
    (Tmax : InitialData → Lifespan) (infinity : Lifespan)
    (u0 : InitialData)
    (hTypedContext : typedContextDiscipline)
    (hSobolevExponent : 5 < 2 * sobolevExponent)
    (hDivergenceFree : divergenceFree u0)
    (hSobolev : inSobolevGamma0 u0)
    (hAcceptedSmooth : acceptedSmoothDataChannel u0)
    (closureDeliverable :
      R.R1.carrierAdequacyOriented →
        R.R2.exactBGPackage →
          R.R3.nullModeLegal →
            R.R4.recurrenceAccepted →
              (∀ j, R.R5.lambda (j + 1) = 2 * R.R5.lambda j) →
                R.R6.typedTransportAccepted →
                  R.R7.halfLogAnalyticityAccepted →
                    R.R8.bkmImportAccepted →
                      R.R8.bgImportAccepted →
                        R.R8.katoImportAccepted →
                          R.R8.wangHalfLogImportAccepted →
                            R.R8.lpBcdImportAccepted →
                              R.R8.sobolevBesovEmbeddingAccepted →
                                R.R9.noCriterionNativeReplacement →
                                  R.R9.noGenericBesovClaim →
                                    R.R9.noUntypedGlobalComparison →
                                      R.R9.noClosureOutsideSmoothDataWithoutRecords →
                                        typedContextDiscipline →
                                          5 < 2 * sobolevExponent →
                                            divergenceFree u0 →
                                              inSobolevGamma0 u0 →
                                                acceptedSmoothDataChannel u0 →
                                                  Tmax u0 = infinity) :
    Tmax u0 = infinity := by
  exact closureDeliverable
    R.R1.carrierAdequacyOriented_holds
    R.R2.exactBGPackage_holds
    R.R3.nullModeLegal_holds
    R.R4.recurrenceAccepted_holds
    R.R5.frequencyDoubling
    R.R6.typedTransportAccepted_holds
    R.R7.halfLogAnalyticityAccepted_holds
    R.R8.bkmImportAccepted_holds
    R.R8.bgImportAccepted_holds
    R.R8.katoImportAccepted_holds
    R.R8.wangHalfLogImportAccepted_holds
    R.R8.lpBcdImportAccepted_holds
    R.R8.sobolevBesovEmbeddingAccepted_holds
    R.R9.noCriterionNativeReplacement_holds
    R.R9.noGenericBesovClaim_holds
    R.R9.noUntypedGlobalComparison_holds
    R.R9.noClosureOutsideSmoothDataWithoutRecords_holds
    hTypedContext
    hSobolevExponent
    hDivergenceFree
    hSobolev
    hAcceptedSmooth

end SixBirdsMetaMath.NS.MainTheorem
