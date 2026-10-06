import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.NS.Carrier
import SixBirdsMetaMath.NS.PDEImports

namespace SixBirdsMetaMath.NS.NoGo

/-!
NS paper §5 "Framework-derived no-go theorems (NG2--NG10)".

Theorem-grade no-gos that constrain lawful refinements of the residual
cascade, numbered to match `ns_no_go_theorem_ledger.csv`:
- `thm:ns:no-go-scalar-energy` (NG2) — scalar energy/enstrophy is not a linear native family
- `thm:ns:no-go-packing-amplitude` (NG3) — packing alone does not control `D^{BG}` amplitude
- `thm:ns:no-go-sparse-shadow` (NG4) — sparseness needs sector containment
- `thm:ns:no-go-marker-only` (NG5) — markers need quantitative bridge
- `thm:ns:no-go-metric-shadow` (NG6) — weighted metrics need explicit dominance
- `thm:ns:no-go-moving-window` (NG7) — moving windows need fixed/exhaustive ledger
- `thm:ns:no-go-half-log-endpoint` (NG8) — half-log Gevrey fails summable propagation
- `thm:ns:no-go-published-analyticity` (NG9) — available analyticity short by `√(log λ_J)`
- `thm:ns:no-go-raw-nonlinearity` (NG10) — raw nonlinear observables illegal as Schur probes

The exports are conditional logical necessity templates. Each accepts
its essential necessity implication as a hypothesis; the listed PDE
obstructions and nonlinear-to-linear failures are not derived here.
NG2 likewise assumes both the linear-family necessity implication and
the absence of a lawful linear family.
-/

/--
NG2: quadratic energy/enstrophy scalars are not lawful linear native
probe families for the Schur-complement residual.
-/
theorem noGoScalarEnergy
    (quadraticScalarDeclared lawfulLinearNativeFamily wellFormedSchurResidual : Prop)
    (requiresLinearFamily :
      quadraticScalarDeclared → wellFormedSchurResidual → lawfulLinearNativeFamily)
    (hQuadratic : quadraticScalarDeclared)
    (hNoLinearFamily : ¬ lawfulLinearNativeFamily) :
    ¬ wellFormedSchurResidual := by
  intro hResidual
  exact hNoLinearFamily (requiresLinearFamily hQuadratic hResidual)

/--
NG3: packing alone controls BG amplitude only below the stated
amplitude threshold, or after a sector-matched bridge / paid tail record.
-/
theorem noGoPackingAmplitude
    (d alpha : Rat)
    (packingAloneControlsDBG sectorMatchedAmplitudeBridge paidTailSmallness : Prop)
    (controlRequires :
      packingAloneControlsDBG →
        alpha < (3 - d) / 2 ∨ sectorMatchedAmplitudeBridge ∨ paidTailSmallness)
    (hNoThreshold : ¬ alpha < (3 - d) / 2)
    (hNoBridge : ¬ sectorMatchedAmplitudeBridge)
    (hNoTail : ¬ paidTailSmallness) :
    ¬ packingAloneControlsDBG := by
  intro hControl
  cases controlRequires hControl with
  | inl hThreshold => exact hNoThreshold hThreshold
  | inr hRest =>
      cases hRest with
      | inl hBridge => exact hNoBridge hBridge
      | inr hTail => exact hNoTail hTail

/--
NG4: sparse-shadow imports pay the bad-bad overlap only with sector
containment or a paid mismatch record.
-/
theorem noGoSparseShadow
    (sparseFieldPaysOmegaBB sectorContained paidMismatchRecord : Prop)
    (payRequires :
      sparseFieldPaysOmegaBB → sectorContained ∨ paidMismatchRecord)
    (hNoSectorContainment : ¬ sectorContained)
    (hNoPaidMismatch : ¬ paidMismatchRecord) :
    ¬ sparseFieldPaysOmegaBB := by
  intro hPays
  cases payRequires hPays with
  | inl hSector => exact hNoSectorContainment hSector
  | inr hMismatch => exact hNoPaidMismatch hMismatch

/--
NG5: marker payloads do not dominate BG amplitude without a quantitative
amplitude bridge supplied by a lawful native family or record-grade
bad-bad bound.
-/
theorem noGoMarkerOnly
    (markerOnlyField dominatesDBGAmplitude newNativeProbeFamily recordGradeMbbBound : Prop)
    (dominanceRequires :
      markerOnlyField → dominatesDBGAmplitude →
        newNativeProbeFamily ∨ recordGradeMbbBound)
    (hMarkerOnly : markerOnlyField)
    (hNoNativeProbe : ¬ newNativeProbeFamily)
    (hNoMbbBound : ¬ recordGradeMbbBound) :
    ¬ dominatesDBGAmplitude := by
  intro hDominates
  cases dominanceRequires hMarkerOnly hDominates with
  | inl hNative => exact hNoNativeProbe hNative
  | inr hMbb => exact hNoMbbBound hMbb

/--
NG6: metric shadows need normalized BG/BKM dominance together with the
sector bridge, dominance constant, and time gate.
-/
theorem noGoMetricShadow
    (metricShrinksResidual controlsFixedDBGReadout normalizedDominance
      sectorMatchedAmplitudeBridge dominanceConstantSupplied timeGateSupplied : Prop)
    (controlRequires :
      metricShrinksResidual → controlsFixedDBGReadout →
        normalizedDominance ∧ sectorMatchedAmplitudeBridge ∧
          dominanceConstantSupplied ∧ timeGateSupplied)
    (hMetricShadow : metricShrinksResidual)
    (hNoNormalizedDominance : ¬ normalizedDominance) :
    ¬ controlsFixedDBGReadout := by
  intro hControls
  exact hNoNormalizedDominance (controlRequires hMetricShadow hControls).left

/--
NG7: moving-window and derivative-stack support-only data promote only
with finite termination, a fixed-ledger squeeze, or an exhaustive-ledger
squeeze.
-/
theorem noGoMovingWindow
    (movingWindowData completedCarrierClosure finiteTermination fixedLedgerSqueeze
      exhaustiveLedgerSqueeze : Prop)
    (promotionRequires :
      movingWindowData → completedCarrierClosure →
        finiteTermination ∨ fixedLedgerSqueeze ∨ exhaustiveLedgerSqueeze)
    (hMovingWindowData : movingWindowData)
    (hNoFiniteTermination : ¬ finiteTermination)
    (hNoFixedLedger : ¬ fixedLedgerSqueeze)
    (hNoExhaustiveLedger : ¬ exhaustiveLedgerSqueeze) :
    ¬ completedCarrierClosure := by
  intro hClosure
  cases promotionRequires hMovingWindowData hClosure with
  | inl hFinite => exact hNoFiniteTermination hFinite
  | inr hRest =>
      cases hRest with
      | inl hFixed => exact hNoFixedLedger hFixed
      | inr hExhaustive => exact hNoExhaustiveLedger hExhaustive

/--
NG8: the half-log lane alone cannot satisfy summable predictive
propagation when the stage ratio is eventually above one, unless an
additional decay record is supplied.
-/
theorem noGoHalfLogEndpoint
    (stageRatioLimit : Rat)
    (halfLogLaneOnly summablePredictivePropagation additionalDecayRecord : Prop)
    (hStageRatioAboveOne : 1 < stageRatioLimit)
    (summabilityRequires :
      1 < stageRatioLimit →
        halfLogLaneOnly → summablePredictivePropagation → additionalDecayRecord)
    (hHalfLogLane : halfLogLaneOnly)
    (hNoAdditionalDecay : ¬ additionalDecayRecord) :
    ¬ summablePredictivePropagation := by
  intro hSummable
  exact hNoAdditionalDecay
    (summabilityRequires hStageRatioAboveOne hHalfLogLane hSummable)

/--
NG9: the available half-log analyticity lane is insufficient for the
direct radius-window route without LP transport rescue, a full-log
radius, or an alternative new-radius theorem.
-/
theorem noGoPublishedAnalyticity
    (availableHalfLogLane directRadiusWindowGate lpTransportRescue fullLogRadius
      alternativeNewRadiusTheorem : Prop)
    (directRouteRequires :
      availableHalfLogLane → directRadiusWindowGate →
        lpTransportRescue ∨ fullLogRadius ∨ alternativeNewRadiusTheorem)
    (hAvailableLane : availableHalfLogLane)
    (hNoLPTransport : ¬ lpTransportRescue)
    (hNoFullLog : ¬ fullLogRadius)
    (hNoAlternativeRadius : ¬ alternativeNewRadiusTheorem) :
    ¬ directRadiusWindowGate := by
  intro hGate
  cases directRouteRequires hAvailableLane hGate with
  | inl hLP => exact hNoLPTransport hLP
  | inr hRest =>
      cases hRest with
      | inl hFullLog => exact hNoFullLog hFullLog
      | inr hAlternative => exact hNoAlternativeRadius hAlternative

/--
NG10: raw nonlinear observables cannot enter `L^{phys}` as Schur probes;
lawful entry requires tangent linearization, interaction lifting, or
recording the contribution in the source-admission ledger.
-/
theorem noGoRawNonlinearity
    (rawNonlinearObservable entersNativeSchurProbe tangentLinearization
      interactionLifting sourceAdmissionEntry : Prop)
    (entryRequires :
      rawNonlinearObservable → entersNativeSchurProbe →
        tangentLinearization ∨ interactionLifting ∨ sourceAdmissionEntry)
    (hRawNonlinear : rawNonlinearObservable)
    (hNoTangentLinearization : ¬ tangentLinearization)
    (hNoInteractionLifting : ¬ interactionLifting)
    (hNoSourceAdmissionEntry : ¬ sourceAdmissionEntry) :
    ¬ entersNativeSchurProbe := by
  intro hEntry
  cases entryRequires hRawNonlinear hEntry with
  | inl hTangent => exact hNoTangentLinearization hTangent
  | inr hRest =>
      cases hRest with
      | inl hLift => exact hNoInteractionLifting hLift
      | inr hSource => exact hNoSourceAdmissionEntry hSource

end SixBirdsMetaMath.NS.NoGo
