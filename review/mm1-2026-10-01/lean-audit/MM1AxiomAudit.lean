import SixBirdsMetaMath.MetaMath
import SixBirdsMetaMath.RHNavier
import SixBirdsMetaMath.RHNavierPvNP

/-!
MM-1 proof self-review and axiom audit. Run from lean/:
  lake env lean ../review/mm1-2026-10-01/lean-audit/MM1AxiomAudit.lean

Claim codes are distinct independently of their interpretations. The selective
base is sound, accepts the false code and rejects the true code, although both
interpret True. The actual 1x1 finite-matrix carrier has zero audit/readouts and
zero residual. Its classification instance is proved, rather than assumed.

Classification is supplied per instance. The dichotomy's native branch uses
only soundness of the accepted code base; its X branch uses the classification
hypothesis. Aim/discipline/coverage guards are omitted because they are unused.

Coverage from classification requires explicit residual-code representability.
Without it an arbitrary claim language need not encode residual closure.
The proof does not identify code non-equivalence with negated X-equivalence.

Bridge satisfiability records EVERY retained paper hypothesis, as well as the
classification and obligation schema instances. These instances are explicitly
proved in the model. The bridge theorem uses only composition, composite
X-equivalence and the two schema instances; its docstring lists unused inputs.

All nine previous axioms are now Prop-valued schema definitions. Conditional
applications do not prove the schemas. Part-II and calibration opaque interfaces
are retained as permitted, and no axiom asserts a proposition about them.
V5's derivation conjunct follows independently from V4; no recognition or
closure hypothesis is used for that conjunct. CTMT's constructor proof remains
unchanged except for forced claim-code and carrier-language typing.

FoundationsIV, RHNavier, RHNavierPvNP and the Lake setup are untouched. Metadata
paper-file changes are restricted to Lean names/statuses and Lean status counts.
-/

set_option pp.universes true

-- lean/SixBirdsMetaMath/MetaMath/RecognitionMode/ClosureContentThesis.lean:46
#check SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.ClosureContentThesisSchema

-- lean/SixBirdsMetaMath/MetaMath/RecognitionMode/ClosureContentThesis.lean:55
#check SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.closure_content_thesis
#print axioms SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.closure_content_thesis

-- lean/SixBirdsMetaMath/MetaMath/RecognitionMode/AttackForeclosureV5.lean:47
#check SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.AttackForeclosureV5Schema

-- lean/SixBirdsMetaMath/MetaMath/RecognitionMode/AttackForeclosureV5.lean:59
#check SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.attack_v5_derivation_conjunct_of_v4
#print axioms SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.attack_v5_derivation_conjunct_of_v4

-- lean/SixBirdsMetaMath/MetaMath/RecognitionMode/AttackForeclosureV5.lean:69
#check SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.attack_foreclosure_v5
#print axioms SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.attack_foreclosure_v5

-- lean/SixBirdsMetaMath/MetaMath/RecognitionMode/Template.lean:56
#check SixBirdsMetaMath.MetaMath.RecognitionMode.Template.TemplateApplicabilitySchema

-- lean/SixBirdsMetaMath/MetaMath/RecognitionMode/Template.lean:66
#check SixBirdsMetaMath.MetaMath.RecognitionMode.Template.recognition_template_applicability
#print axioms SixBirdsMetaMath.MetaMath.RecognitionMode.Template.recognition_template_applicability

-- lean/SixBirdsMetaMath/MetaMath/RecognitionMode/VerdictSignature.lean:41
#check SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature.VerdictSignatureSchema

-- lean/SixBirdsMetaMath/MetaMath/RecognitionMode/VerdictSignature.lean:52
#check SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature.verdict_signature
#print axioms SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature.verdict_signature

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:15
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.InternalMoveSignature

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:21
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.internalMoveSemantics

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:24
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.advancesXWithoutExternal

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:28
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.InFrameworkScope

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:32
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.AttackForeclosureV4Schema

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:37
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.attack_foreclosure_v4
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.attack_foreclosure_v4

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/Coverage.lean:10
#check SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.CoverageSchema

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/Coverage.lean:16
#check SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.coverage_of_classification
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.coverage_of_classification

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/Coverage.lean:34
#check SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.coverage_theorem
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.coverage_theorem

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/TypeFiniteForeclosure.lean:27
#check SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.classifyAs

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/TypeFiniteForeclosure.lean:42
#check SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.type_finite_foreclosure
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.type_finite_foreclosure

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/TypeFiniteForeclosure.lean:54
#check SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.classify

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/TypeFiniteForeclosure.lean:60
#check SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.classify_spec
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.classify_spec

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:8
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.BridgeSignature

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:17
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.TypedBridge

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:19
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.XStrengthObligation

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:22
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.BridgeComposition

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:27
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.BridgeObligationSchema

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:39
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:58
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.twoClaimBridgeSignature

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:68
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility_hypotheses_satisfiable
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility_hypotheses_satisfiable

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CTMTRecursion.lean:24
#check SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.cascadeReducesToDeeperFamily

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CTMTRecursion.lean:36
#check SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.CTMTTower

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CTMTRecursion.lean:50
#check SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.ctmt_recursion
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.ctmt_recursion

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:19
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.ClaimLanguage

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:31
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.TypedPrimaryCarrier

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:51
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.carrierResidual

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:55
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.residualClosureZero

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:59
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.residualClosureEquivalent

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:63
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.xEquivalent

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:72
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.nonXEquivalent

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:76
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.openPending

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:83
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.NativeClosureOutcome

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:89
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.sameLevelSelfAuditFailure

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:97
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.creTE

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:104
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.creBF

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:112
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.creCTMT

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:122
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.CoverageContext

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:128
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.CarrierClassificationSchema

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:135
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.carrier_dichotomy
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.carrier_dichotomy

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:156
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.twoTrueClaims

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:159
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.selectiveTrueBase

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:162
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.sound_base_noncollapse
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.sound_base_noncollapse

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:171
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.closedTwoClaimCarrier

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:189
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.closedTwoClaimCarrier_zero
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.closedTwoClaimCarrier_zero

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:195
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.closedTwoClaimCarrier_classification
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.closedTwoClaimCarrier_classification

-- lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:207
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.nonXEquivalent_and_xEquivalent
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.nonXEquivalent_and_xEquivalent

-- lean/SixBirdsMetaMath/MetaMath/CalibrationFamily/FrameworkTypeSelfChar.lean:72
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.FrameworkTypeGeneralSchema

/- Complete signature catalogue. Implicit language parameters are shown
by the corresponding #check output above. For schema definitions and structures,
the entire source declaration is copied so the proposition/fields are explicit.

SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.ClosureContentThesisSchema
lean/SixBirdsMetaMath/MetaMath/RecognitionMode/ClosureContentThesis.lean:46
def ClosureContentThesisSchema : Prop :=
  ∀
    (c : FormedClosure) (X : Prop)
    (_hcolumn : VDifferentialTSOColumn c),
    IsFormedLayerClosureContent (loadBearingFor c X) c ∧
    ¬ IsDerivableFromFrameworkPrimitives (loadBearingFor c X) ∧
    NamedAsAcceptedSource (loadBearingFor c X) c

SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.closure_content_thesis
lean/SixBirdsMetaMath/MetaMath/RecognitionMode/ClosureContentThesis.lean:55
theorem closure_content_thesis
    (hschema : ClosureContentThesisSchema)
    (c : FormedClosure) (X : Prop)
    (hcolumn : VDifferentialTSOColumn c) :
    IsFormedLayerClosureContent (loadBearingFor c X) c ∧
    ¬ IsDerivableFromFrameworkPrimitives (loadBearingFor c X) ∧
    NamedAsAcceptedSource (loadBearingFor c X) c

SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.AttackForeclosureV5Schema
lean/SixBirdsMetaMath/MetaMath/RecognitionMode/AttackForeclosureV5.lean:47
def AttackForeclosureV5Schema (signature : InternalMoveSignature language) : Prop :=
  ∀ (c : FormedClosure) (X : language.Claim),
    VDifferentialTSOColumn c → SBClosureAssumption c → InFrameworkScope signature X →
      (∀ move : FrameworkInternalMove, IsDerivationRoute move →
        ¬ advancesXWithoutExternal signature move X) ∧
      (∀ l : RecognitionModeLanding c (language.interp X),
        ImportsAsNamedRecognition l (loadBearingFor c (language.interp X))) ∧
      (∀ _l : RecognitionModeLanding c (language.interp X),
        LandsAtTheoremGrade c (language.interp X))

SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.attack_v5_derivation_conjunct_of_v4
lean/SixBirdsMetaMath/MetaMath/RecognitionMode/AttackForeclosureV5.lean:59
theorem attack_v5_derivation_conjunct_of_v4
    (signature : InternalMoveSignature language)
    (hv4 : AttackForeclosureV4Schema signature)
    (X : language.Claim) (hscope : InFrameworkScope signature X) :
    ∀ move : FrameworkInternalMove, IsDerivationRoute move →
      ¬ advancesXWithoutExternal signature move X

SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.attack_foreclosure_v5
lean/SixBirdsMetaMath/MetaMath/RecognitionMode/AttackForeclosureV5.lean:69
theorem attack_foreclosure_v5
    (signature : InternalMoveSignature language)
    (hschema : AttackForeclosureV5Schema signature)
    (c : FormedClosure) (X : language.Claim)
    (hcolumn : VDifferentialTSOColumn c)
    (hclosure : SBClosureAssumption c)
    (hscope : InFrameworkScope signature X) :
    (∀ move : FrameworkInternalMove, IsDerivationRoute move →
      ¬ advancesXWithoutExternal signature move X) ∧
    (∀ l : RecognitionModeLanding c (language.interp X),
      ImportsAsNamedRecognition l (loadBearingFor c (language.interp X))) ∧
    (∀ _l : RecognitionModeLanding c (language.interp X),
      LandsAtTheoremGrade c (language.interp X))

SixBirdsMetaMath.MetaMath.RecognitionMode.Template.TemplateApplicabilitySchema
lean/SixBirdsMetaMath/MetaMath/RecognitionMode/Template.lean:56
def TemplateApplicabilitySchema : Prop :=
  ∀
    (c : FormedClosure) (X : Prop)
    (_hcolumn : VDifferentialTSOColumn c)
    (_hclosure : SBClosureAssumption c)
    (htemplate : SevenStageTemplate c X)
    (_happlies : TemplateApplies c X htemplate),
    LandsAtTheoremGrade c X

SixBirdsMetaMath.MetaMath.RecognitionMode.Template.recognition_template_applicability
lean/SixBirdsMetaMath/MetaMath/RecognitionMode/Template.lean:66
theorem recognition_template_applicability
    (hschema : TemplateApplicabilitySchema)
    (c : FormedClosure) (X : Prop)
    (hcolumn : VDifferentialTSOColumn c)
    (hclosure : SBClosureAssumption c)
    (htemplate : SevenStageTemplate c X)
    (happlies : TemplateApplies c X htemplate) :
    LandsAtTheoremGrade c X

SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature.VerdictSignatureSchema
lean/SixBirdsMetaMath/MetaMath/RecognitionMode/VerdictSignature.lean:41
def VerdictSignatureSchema : Prop :=
  ∀
    (c : FormedClosure) (X : Prop)
    (_hcolumn : VDifferentialTSOColumn c)
    (htemplate : SevenStageTemplate c X)
    (_happlies : TemplateApplies c X htemplate),
    sweepVerdict htemplate SweepOption.frameworkPrimitive = Verdict.ii ∧
    sweepVerdict htemplate SweepOption.sauNonDescent = Verdict.iii ∧
    sweepVerdict htemplate SweepOption.vDifferentialElevation = Verdict.ii

SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature.verdict_signature
lean/SixBirdsMetaMath/MetaMath/RecognitionMode/VerdictSignature.lean:52
theorem verdict_signature
    (hschema : VerdictSignatureSchema)
    (c : FormedClosure) (X : Prop)
    (hcolumn : VDifferentialTSOColumn c)
    (htemplate : SevenStageTemplate c X)
    (happlies : TemplateApplies c X htemplate) :
    sweepVerdict htemplate SweepOption.frameworkPrimitive = Verdict.ii ∧
    sweepVerdict htemplate SweepOption.sauNonDescent = Verdict.iii ∧
    sweepVerdict htemplate SweepOption.vDifferentialElevation = Verdict.ii

SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.InternalMoveSignature
lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:15
structure InternalMoveSignature (language : ClaimLanguage.{u}) where
  semantics : FrameworkInternalMove → language.Claim → Prop
  scope : language.Claim → Prop

variable {language : ClaimLanguage.{u}}

SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.internalMoveSemantics
lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:21
def internalMoveSemantics (signature : InternalMoveSignature language)
    (move : FrameworkInternalMove) (X : language.Claim) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.advancesXWithoutExternal
lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:24
def advancesXWithoutExternal (signature : InternalMoveSignature language)
    (move : FrameworkInternalMove) (X : language.Claim) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.InFrameworkScope
lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:28
def InFrameworkScope (signature : InternalMoveSignature language)
    (X : language.Claim) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.AttackForeclosureV4Schema
lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:32
def AttackForeclosureV4Schema (signature : InternalMoveSignature language) : Prop :=
  ∀ (X : language.Claim) (move : FrameworkInternalMove),
    InFrameworkScope signature X → ¬ advancesXWithoutExternal signature move X

SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.attack_foreclosure_v4
lean/SixBirdsMetaMath/MetaMath/Foreclosure/AttackForeclosure.lean:37
theorem attack_foreclosure_v4 (signature : InternalMoveSignature language)
    (hschema : AttackForeclosureV4Schema signature)
    (X : language.Claim) (move : FrameworkInternalMove)
    (hscope : InFrameworkScope signature X) :
    ¬ advancesXWithoutExternal signature move X

SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.CoverageSchema
lean/SixBirdsMetaMath/MetaMath/Foreclosure/Coverage.lean:10
def CoverageSchema (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop :=
  nonXEquivalent X C ∨ creTE X C ∨ creBF X C ∨ creCTMT X C

SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.coverage_of_classification
lean/SixBirdsMetaMath/MetaMath/Foreclosure/Coverage.lean:16
theorem coverage_of_classification
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hresidual : ∃ c : language.Claim, residualClosureEquivalent C c)
    (hclassification : CarrierClassificationSchema X C) :
    nonXEquivalent X C ∨ creTE X C ∨ creBF X C ∨ creCTMT X C

SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.coverage_theorem
lean/SixBirdsMetaMath/MetaMath/Foreclosure/Coverage.lean:34
theorem coverage_theorem
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hcoverage : CoverageSchema X C) :
    nonXEquivalent X C ∨ creTE X C ∨ creBF X C ∨ creCTMT X C

SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.classifyAs
lean/SixBirdsMetaMath/MetaMath/Foreclosure/TypeFiniteForeclosure.lean:27
def classifyAs (s : CarrierState) (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.type_finite_foreclosure
lean/SixBirdsMetaMath/MetaMath/Foreclosure/TypeFiniteForeclosure.lean:42
theorem type_finite_foreclosure
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hcoverage : CoverageSchema X C) :
    ∃ s : CarrierState, classifyAs s X C

SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.classify
lean/SixBirdsMetaMath/MetaMath/Foreclosure/TypeFiniteForeclosure.lean:54
noncomputable def classify
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hcoverage : CoverageSchema X C) : CarrierState

SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.classify_spec
lean/SixBirdsMetaMath/MetaMath/Foreclosure/TypeFiniteForeclosure.lean:60
theorem classify_spec
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hcoverage : CoverageSchema X C) :
    classifyAs (classify X C hcoverage) X C

SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.BridgeSignature
lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:8
structure BridgeSignature (language : ClaimLanguage.{u}) where
  Bridge : Type v
  obligation : Bridge → language.Claim → Prop
  composition : Bridge → TypedPrimaryCarrier language → TypedPrimaryCarrier language →
    language.Claim → Prop
  coverage : language.Claim → TypedPrimaryCarrier language → Prop

variable {language : ClaimLanguage.{u}}

SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.TypedBridge
lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:17
abbrev TypedBridge (signature : BridgeSignature.{u, v} language) : Type v

SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.XStrengthObligation
lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:19
def XStrengthObligation (signature : BridgeSignature language)
    (B : TypedBridge signature) (X : language.Claim) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.BridgeComposition
lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:22
def BridgeComposition (signature : BridgeSignature language)
    (B : TypedBridge signature) (C composite : TypedPrimaryCarrier language)
    (X : language.Claim) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.BridgeObligationSchema
lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:27
def BridgeObligationSchema (signature : BridgeSignature language)
    (B : TypedBridge signature) (C composite : TypedPrimaryCarrier language)
    (X : language.Claim) : Prop :=
  BridgeComposition signature B C composite X →
    ExactlyOneOfThree (creTE X composite) (creBF X composite) (creCTMT X composite) →
      XStrengthObligation signature B X

SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility
lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:39
theorem bridge_impossibility
    (signature : BridgeSignature language)
    (_acceptedImportsBase : language.Claim → Prop)
    (_h_imports_sound : ∀ c, _acceptedImportsBase c → language.interp c)
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (B : TypedBridge signature) (composite : TypedPrimaryCarrier language)
    (_hCNonX : nonXEquivalent X C)
    (_hCNative : residualClosureZero C)
    (hcomp : BridgeComposition signature B C composite X)
    (hcompositeProduces : residualClosureZero composite ∧ residualClosureEquivalent composite X)
    (_hcompositeDiscipline : composite.typedContextDiscipline)
    (_hcompositeAimed : composite.aimedAt X)
    (_hcompositeCtx : CoverageContext signature.coverage X composite)
    (hclassification : CarrierClassificationSchema X composite)
    (hbridge : BridgeObligationSchema signature B C composite X) :
    XStrengthObligation signature B X

SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.twoClaimBridgeSignature
lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:58
def twoClaimBridgeSignature : BridgeSignature.{0, 0} twoTrueClaims where
  Bridge

SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility_hypotheses_satisfiable
lean/SixBirdsMetaMath/MetaMath/Foreclosure/BridgeImpossibility.lean:68
theorem bridge_impossibility_hypotheses_satisfiable :
    ∃ (language : ClaimLanguage.{0})
      (signature : BridgeSignature.{0, 0} language)
      (acceptedImportsBase : language.Claim → Prop)
      (X : language.Claim) (C composite : TypedPrimaryCarrier language)
      (B : TypedBridge signature),
      (∀ c, acceptedImportsBase c → language.interp c) ∧
      nonXEquivalent X C ∧ residualClosureZero C ∧
      BridgeComposition signature B C composite X ∧
      (residualClosureZero composite ∧ residualClosureEquivalent composite X) ∧
      composite.typedContextDiscipline ∧ composite.aimedAt X ∧
      CoverageContext signature.coverage X composite ∧
      CarrierClassificationSchema X composite ∧
      BridgeObligationSchema signature B C composite X

SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.cascadeReducesToDeeperFamily
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CTMTRecursion.lean:24
def cascadeReducesToDeeperFamily
    (semantics : language.Claim → TypedPrimaryCarrier language → TypedPrimaryCarrier language → Prop)
    (X : language.Claim) (C Cdeeper : TypedPrimaryCarrier language) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.CTMTTower
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CTMTRecursion.lean:36
inductive CTMTTower
    (semantics : language.Claim → TypedPrimaryCarrier language → TypedPrimaryCarrier language → Prop)
    (X : language.Claim) : TypedPrimaryCarrier language → Nat → Prop where
  | base {C : TypedPrimaryCarrier language} (h : creCTMT X C) :
      CTMTTower semantics X C 1
  | step {C Cdeeper : TypedPrimaryCarrier language} (n : Nat)
      (htower : CTMTTower semantics X Cdeeper (n + 1))
      (hreduces : cascadeReducesToDeeperFamily semantics X C Cdeeper) :
      CTMTTower semantics X C (n + 2)

SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.ctmt_recursion
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CTMTRecursion.lean:50
theorem ctmt_recursion :
    (∀ (semantics : language.Claim → TypedPrimaryCarrier language → TypedPrimaryCarrier language → Prop)
        (X : language.Claim) (C : TypedPrimaryCarrier language),
        CTMTTower semantics X C 1 ↔ creCTMT X C) ∧
    (∀ (semantics : language.Claim → TypedPrimaryCarrier language → TypedPrimaryCarrier language → Prop)
        (X : language.Claim) (C Cdeeper : TypedPrimaryCarrier language) (n : Nat),
        CTMTTower semantics X Cdeeper (n + 1) →
          cascadeReducesToDeeperFamily semantics X C Cdeeper →
            CTMTTower semantics X C (n + 2))

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.ClaimLanguage
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:19
structure ClaimLanguage where
  Claim : Type u
  interp : Claim → Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.TypedPrimaryCarrier
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:31
structure TypedPrimaryCarrier (language : ClaimLanguage.{u}) where
  e : Nat
  y : Nat
  z : Nat
  audit : Mat e e
  nativeProbes : Mat y e
  dissolvingReadout : Mat z e
  KLLdagger : Mat y y
  aimedAt : language.Claim → Prop
  typedContextDiscipline : Prop
  sameLevelAuditStatus : SixBirdsMetaMath.F3ClaimStatus
  noAcceptedBridgeToTarget : language.Claim → Prop
  structurallyBridgeIncompatible : language.Claim → Prop
  cascadeReducesToMatrixFamily : Prop
  inheritedRecordsDecideMatrixFamily : Prop
  matrixFamilyDecisionEquivalentToTarget : language.Claim → Prop

variable {language : ClaimLanguage.{u}}

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.carrierResidual
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:51
def carrierResidual (C : TypedPrimaryCarrier language) : Mat C.z C.z

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.residualClosureZero
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:55
def residualClosureZero (C : TypedPrimaryCarrier language) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.residualClosureEquivalent
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:59
def residualClosureEquivalent (C : TypedPrimaryCarrier language) (X : language.Claim) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.xEquivalent
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:63
def xEquivalent (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.nonXEquivalent
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:72
def nonXEquivalent (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.openPending
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:76
def openPending (acceptedImportsBase : language.Claim → Prop) (X' : language.Claim) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.NativeClosureOutcome
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:83
def NativeClosureOutcome
    (acceptedImportsBase : language.Claim → Prop) (C : TypedPrimaryCarrier language) (X' : language.Claim) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.sameLevelSelfAuditFailure
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:89
def sameLevelSelfAuditFailure (C : TypedPrimaryCarrier language) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.creTE
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:97
def creTE (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.creBF
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:104
def creBF (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.creCTMT
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:112
def creCTMT (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.CoverageContext
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:122
def CoverageContext
    (guard : language.Claim → TypedPrimaryCarrier language → Prop)
    (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.CarrierClassificationSchema
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:128
def CarrierClassificationSchema
    (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop :=
  xEquivalent X C →
    ExactlyOneOfThree (creTE X C) (creBF X C) (creCTMT X C)

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.carrier_dichotomy
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:135
theorem carrier_dichotomy
    (acceptedImportsBase : language.Claim → Prop)
    (h_imports_sound : ∀ c, acceptedImportsBase c → language.interp c)
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hclassification : CarrierClassificationSchema X C) :
    (nonXEquivalent X C →
      ∃ X' : language.Claim,
        residualClosureEquivalent C X' ∧ X' ≠ X ∧
          NativeClosureOutcome acceptedImportsBase C X') ∧
    (xEquivalent X C →
      ExactlyOneOfThree (creTE X C) (creBF X C) (creCTMT X C))

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.twoTrueClaims
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:156
def twoTrueClaims : ClaimLanguage.{0}

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.selectiveTrueBase
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:159
def selectiveTrueBase : twoTrueClaims.Claim → Prop

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.sound_base_noncollapse
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:162
theorem sound_base_noncollapse :
    (∀ c, selectiveTrueBase c → twoTrueClaims.interp c) ∧
    twoTrueClaims.interp false ∧ twoTrueClaims.interp true ∧
    selectiveTrueBase false ∧ ¬ selectiveTrueBase true

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.closedTwoClaimCarrier
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:171
def closedTwoClaimCarrier : TypedPrimaryCarrier twoTrueClaims where
  e

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.closedTwoClaimCarrier_zero
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:189
theorem closedTwoClaimCarrier_zero : residualClosureZero closedTwoClaimCarrier

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.closedTwoClaimCarrier_classification
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:195
theorem closedTwoClaimCarrier_classification (X : twoTrueClaims.Claim) :
    CarrierClassificationSchema X closedTwoClaimCarrier

SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.nonXEquivalent_and_xEquivalent
lean/SixBirdsMetaMath/MetaMath/Foreclosure/CarrierDichotomy.lean:207
theorem nonXEquivalent_and_xEquivalent :
    nonXEquivalent true closedTwoClaimCarrier ∧
      xEquivalent true closedTwoClaimCarrier

SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.FrameworkTypeGeneralSchema
lean/SixBirdsMetaMath/MetaMath/CalibrationFamily/FrameworkTypeSelfChar.lean:72
def FrameworkTypeGeneralSchema : Prop :=
    ∀ c : FormedClosure,
      VDifferentialTSOColumn c →
        ¬ typesMatch (cascadeFrameworkType c) (standardClayTargetType c)
-/

-- Complete manifest name/type and theorem dependency audit.
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.TypedPrimaryCarrier
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.carrierResidual
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.residualClosureZero
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.residualClosureEquivalent
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.xEquivalent
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.nonXEquivalent
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.openPending
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.NativeClosureOutcome
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.sameLevelSelfAuditFailure
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.creTE
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.creBF
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.creCTMT
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.ExactlyOneOfThree
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.CoverageContext
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.CarrierClassificationSchema
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.carrier_dichotomy
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.carrier_dichotomy
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.TypedBridge
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.XStrengthObligation
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.BridgeComposition
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.BridgeObligationSchema
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility
#check SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.CoverageSchema
#check SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.CarrierState
#check SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.classifyAs
#check SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.type_finite_foreclosure
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.type_finite_foreclosure
#check SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.classify
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.FrameworkInternalMove
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.internalMoveSemantics
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.advancesXWithoutExternal
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.InFrameworkScope
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.AttackForeclosureV4Schema
#check SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.cascadeReducesToDeeperFamily
#check SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.CTMTTower
#check SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.ctmt_recursion
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.ctmt_recursion
#check SixBirdsMetaMath.MetaMath.RecognitionMode.Template.FormedClosure
#check SixBirdsMetaMath.MetaMath.RecognitionMode.Template.VDifferentialTSOColumn
#check SixBirdsMetaMath.MetaMath.RecognitionMode.Template.SBClosureAssumption
#check SixBirdsMetaMath.MetaMath.RecognitionMode.Template.SevenStageTemplate
#check SixBirdsMetaMath.MetaMath.RecognitionMode.Template.TemplateApplies
#check SixBirdsMetaMath.MetaMath.RecognitionMode.Template.LandsAtTheoremGrade
#check SixBirdsMetaMath.MetaMath.RecognitionMode.Template.TemplateApplicabilitySchema
#check SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature.SweepOption
#check SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature.Verdict
#check SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature.sweepVerdict
#check SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature.VerdictSignatureSchema
#check SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.StructuralContent
#check SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.loadBearingFor
#check SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.IsFormedLayerClosureContent
#check SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.IsDerivableFromFrameworkPrimitives
#check SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.NamedAsAcceptedSource
#check SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.ClosureContentThesisSchema
#check SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.IsDerivationRoute
#check SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.RecognitionModeLanding
#check SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.ImportsAsNamedRecognition
#check SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.AttackForeclosureV5Schema
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.Structure.Calibration
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.Structure.calibrationFamily
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.Structure.calibration_family_structure
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.Structure.calibration_family_structure
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.RebadgeDiscipline.CalibrationProfile
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.RebadgeDiscipline.isRebadgeOf
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.RebadgeDiscipline.genuinelyNew
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.RebadgeDiscipline.rebadge_discipline
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.RebadgeDiscipline.rebadge_discipline
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgesAsTheorems.BridgeKind
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgesAsTheorems.TypedBridge
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgesAsTheorems.bridges_as_theorems
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgesAsTheorems.bridges_as_theorems
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgeTypeDirection.TypedBridge.reverse
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgeTypeDirection.bridge_type_direction
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.BridgeTypeDirection.bridge_type_direction
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.CarrierRegion
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.boundedDepthRegion
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.lowDegreeRegion
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.stableLocalRegion
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.queryRegion
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.topologicalRegion
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.lowNSDegreeRegion
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.nc1Region
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.nc2Region
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.pPolyRegion
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.adaptivePolyTimeRegion
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.calibrationCoverage
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.familyCoverage
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.TypedHole
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.xiNC1Coverage
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.xiAdaptiveTrace
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.isGenuineHole
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.all_covered_regions_in_family
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.all_covered_regions_in_family
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.all_uncovered_regions_not_in_family
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.all_uncovered_regions_not_in_family
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.bounded_depth_overlap
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.bounded_depth_overlap
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.empty_coverage_adds_nothing
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.empty_coverage_adds_nothing
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.coverage_family_geometry
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry.coverage_family_geometry
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FunctorialGates.FunctorialGate
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FunctorialGates.namedFunctorialGates
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FunctorialGates.named_functorial_gates
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.FunctorialGates.named_functorial_gates
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.FrameworkType
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.pvnpFrameworkType
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.standardClayPvNPType
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.typesMatch
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.pvnp_framework_type_mismatch
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.pvnp_framework_type_mismatch
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.cascadeFrameworkType
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.standardClayTargetType
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.FrameworkTypeGeneralSchema
#check SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.framework_type_self_characterization
#print axioms SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar.framework_type_self_characterization
#check SixBirdsMetaMath.RHNavier.JointSixBirdsObservationReturn.joint_actual_zero_xi_and_navier_source_return
#print axioms SixBirdsMetaMath.RHNavier.JointSixBirdsObservationReturn.joint_actual_zero_xi_and_navier_source_return
#check SixBirdsMetaMath.RHNavierPvNP.TriadObservationReturn.concrete_triad_gaussian_xi_span
#print axioms SixBirdsMetaMath.RHNavierPvNP.TriadObservationReturn.concrete_triad_gaussian_xi_span
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.ClaimLanguage
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.sound_base_noncollapse
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.sound_base_noncollapse
#check SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.nonXEquivalent_and_xEquivalent
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.nonXEquivalent_and_xEquivalent
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.BridgeSignature
#check SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility_hypotheses_satisfiable
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility_hypotheses_satisfiable
#check SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.coverage_of_classification
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.coverage_of_classification
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.InternalMoveSignature
#check SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.attack_v5_derivation_conjunct_of_v4
#print axioms SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.attack_v5_derivation_conjunct_of_v4
#check SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.coverage_theorem
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.coverage_theorem
#check SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.attack_foreclosure_v4
#print axioms SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure.attack_foreclosure_v4
#check SixBirdsMetaMath.MetaMath.RecognitionMode.Template.recognition_template_applicability
#print axioms SixBirdsMetaMath.MetaMath.RecognitionMode.Template.recognition_template_applicability
#check SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature.verdict_signature
#print axioms SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature.verdict_signature
#check SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.closure_content_thesis
#print axioms SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis.closure_content_thesis
#check SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.attack_foreclosure_v5
#print axioms SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.attack_foreclosure_v5

/- Final verification receipts, 2026-10-01; all commands exit 0.
From lean/:
  lake build
  Build completed successfully (3846 jobs).
  lake build SixBirdsMetaMath.RHNavier SixBirdsMetaMath.RHNavierPvNP
  Build completed successfully (3848 jobs).
From repository root:
  python3 scripts/check_manifests.py --check
  manifest check passed: main=22 entries, xi=13 entries, ns=37 entries,
  aor=47 entries, trust_base=6 axioms, section_module_map covers every queued section
  python3 scripts/check_statements_of_record_meta_math.py
  ok: 68 rows; 117 manifest decls cross-checked; 19 inventory labels matched.
  python3 scripts/check_needles_lean.py --skip-build
  SixBirdsMetaMath Lean prechecks passed
  make paper-preflight-meta_math
  paper lint passed for paper/meta_math
  ok: 68 rows; 117 manifest decls cross-checked; 19 inventory labels matched.

Preflight side effect: the existing latexmk success_cmd ran
scripts/sync_meta_math_paper.py and regenerated the standalone source/PDF.
No modular paper .tex or .bib source was edited. The generated standalone
source was not included in the initial preservation snapshot, so its prior
contents are not established by that snapshot.

All 117 MetaMath manifest names typecheck; all theorem rows have only permitted
axiom dependencies. Project axiom declarations under MetaMath/: 0.
FoundationsIV.hiddenness_pending is retained unchanged and is outside MetaMath.

Required headline axiom output:
'SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy.carrier_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixBirdsMetaMath.MetaMath.Foreclosure.Coverage.coverage_of_classification' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure.type_finite_foreclosure' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility.bridge_impossibility_hypotheses_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixBirdsMetaMath.MetaMath.Foreclosure.CTMTRecursion.ctmt_recursion' depends on axioms: [propext]
'SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5.attack_v5_derivation_conjunct_of_v4' does not depend on any axioms
-/
