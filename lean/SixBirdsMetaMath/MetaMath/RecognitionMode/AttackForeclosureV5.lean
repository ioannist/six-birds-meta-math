import SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure
import SixBirdsMetaMath.MetaMath.RecognitionMode.Template
import SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis

namespace SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5

open SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy
open SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure
open SixBirdsMetaMath.MetaMath.RecognitionMode.Template
open SixBirdsMetaMath.MetaMath.RecognitionMode.ClosureContentThesis

variable {language : ClaimLanguage.{u}}

/-!
T10 Attack Foreclosure v5 refinement.

The v5 claim refines, rather than replaces, v4: derivation routes remain
foreclosed, while recognition-mode landings import a named structural source
as recognition and reach theorem-grade under the standard SB closure
assumption.
-/

/--
Identify which framework-internal moves are derivation routes, the v4
foreclosure target.  Opaque so v5 clause 1 is genuine about which moves are
derivation routes, not vacuously all moves.
-/
opaque IsDerivationRoute : FrameworkInternalMove → Prop

/--
A recognition-mode landing for closure `c` targeting `X`.  Opaque so the
recognition-import clauses cannot be trivialized by choosing structure fields.
-/
opaque RecognitionModeLanding (c : FormedClosure) (X : Prop) : Type

/-- Landing `l` imports structural content `s` as named recognition. -/
opaque ImportsAsNamedRecognition {c : FormedClosure} {X : Prop}
    (l : RecognitionModeLanding c X) (s : StructuralContent) : Prop

/-
T10 conditional schema: v4 remains valid for derivation routes, while recognition
landings are structurally distinct named-source imports and achieve
theorem-grade under the SB closure assumption.
-/
/-- The v5 schema is an explicit premise for a supplied move interpretation.
Recognition predicates remain uninterpreted and are not asserted by any axiom. -/
def AttackForeclosureV5Schema (signature : InternalMoveSignature language) : Prop :=
  ∀ (c : FormedClosure) (X : language.Claim),
    VDifferentialTSOColumn c → SBClosureAssumption c → InFrameworkScope signature X →
      (∀ move : FrameworkInternalMove, IsDerivationRoute move →
        ¬ advancesXWithoutExternal signature move X) ∧
      (∀ l : RecognitionModeLanding c (language.interp X),
        ImportsAsNamedRecognition l (loadBearingFor c (language.interp X))) ∧
      (∀ _l : RecognitionModeLanding c (language.interp X),
        LandsAtTheoremGrade c (language.interp X))

/-- The derivation-route conjunct needs only v4 and scope, not recognition
content, a formed closure, column membership or a closure assumption. -/
theorem attack_v5_derivation_conjunct_of_v4
    (signature : InternalMoveSignature language)
    (hv4 : AttackForeclosureV4Schema signature)
    (X : language.Claim) (hscope : InFrameworkScope signature X) :
    ∀ move : FrameworkInternalMove, IsDerivationRoute move →
      ¬ advancesXWithoutExternal signature move X := by
  intro move _
  exact hv4 X move hscope

/-- Conditional application of the explicit v5 schema. -/
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
      LandsAtTheoremGrade c (language.interp X)) :=
  hschema c X hcolumn hclosure hscope

end SixBirdsMetaMath.MetaMath.RecognitionMode.AttackForeclosureV5
