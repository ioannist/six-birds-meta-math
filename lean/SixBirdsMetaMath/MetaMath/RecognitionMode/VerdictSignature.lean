import SixBirdsMetaMath.MetaMath.RecognitionMode.Template

namespace SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature

open SixBirdsMetaMath.MetaMath.RecognitionMode.Template

/-!
T8 Cross-Track Verdict Signature.

This module records the Stage-6 option taxonomy and the M5 verdict labels
used by the recognition-mode landing template.  The cross-track signature is
paper-proposal-grade, so it is registered as an explicit conditional schema.
-/

/-- The three independent derivation routes attempted in Stage 6. -/
inductive SweepOption where
  | frameworkPrimitive
  | sauNonDescent
  | vDifferentialElevation
  deriving DecidableEq, Repr

/-- The three verdict outcomes used in M5's three-option sweep. -/
inductive Verdict where
  | i
  | ii
  | iii
  deriving DecidableEq, Repr, Inhabited

/--
Verdict reader for the Stage-6 sweep data in a seven-stage template.
Opaque so the conditional schema genuinely asserts the M5 `(ii)/(iii)/(ii)`
signature rather than reducing by definition.
-/
opaque sweepVerdict {c : FormedClosure} {X : Prop}
    (_htemplate : SevenStageTemplate c X) (opt : SweepOption) : Verdict

/--
T8 obligation: TSO-column closures attempted via the recognition-mode
template exhibit the `(ii)/(iii)/(ii)` Stage-6 verdict signature.
-/
def VerdictSignatureSchema : Prop :=
  ∀
    (c : FormedClosure) (X : Prop)
    (_hcolumn : VDifferentialTSOColumn c)
    (htemplate : SevenStageTemplate c X)
    (_happlies : TemplateApplies c X htemplate),
    sweepVerdict htemplate SweepOption.frameworkPrimitive = Verdict.ii ∧
    sweepVerdict htemplate SweepOption.sauNonDescent = Verdict.iii ∧
    sweepVerdict htemplate SweepOption.vDifferentialElevation = Verdict.ii

/-- Conditional application of the explicit schema hypothesis. -/
theorem verdict_signature
    (hschema : VerdictSignatureSchema)
    (c : FormedClosure) (X : Prop)
    (hcolumn : VDifferentialTSOColumn c)
    (htemplate : SevenStageTemplate c X)
    (happlies : TemplateApplies c X htemplate) :
    sweepVerdict htemplate SweepOption.frameworkPrimitive = Verdict.ii ∧
    sweepVerdict htemplate SweepOption.sauNonDescent = Verdict.iii ∧
    sweepVerdict htemplate SweepOption.vDifferentialElevation = Verdict.ii :=
  hschema c X hcolumn htemplate happlies

end SixBirdsMetaMath.MetaMath.RecognitionMode.VerdictSignature
