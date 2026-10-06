import SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy

namespace SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility

open SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy

/-- Arbitrary interpretations of bridge types, guards and obligations. -/
structure BridgeSignature (language : ClaimLanguage.{u}) where
  Bridge : Type v
  obligation : Bridge → language.Claim → Prop
  composition : Bridge → TypedPrimaryCarrier language → TypedPrimaryCarrier language →
    language.Claim → Prop
  coverage : language.Claim → TypedPrimaryCarrier language → Prop

variable {language : ClaimLanguage.{u}}

abbrev TypedBridge (signature : BridgeSignature.{u, v} language) : Type v := signature.Bridge

def XStrengthObligation (signature : BridgeSignature language)
    (B : TypedBridge signature) (X : language.Claim) : Prop := signature.obligation B X

def BridgeComposition (signature : BridgeSignature language)
    (B : TypedBridge signature) (C composite : TypedPrimaryCarrier language)
    (X : language.Claim) : Prop := signature.composition B C composite X

/-- Per-instance bridge-obligation schema; this implication is a hypothesis. -/
def BridgeObligationSchema (signature : BridgeSignature language)
    (B : TypedBridge signature) (C composite : TypedPrimaryCarrier language)
    (X : language.Claim) : Prop :=
  BridgeComposition signature B C composite X →
    ExactlyOneOfThree (creTE X composite) (creBF X composite) (creCTMT X composite) →
      XStrengthObligation signature B X

/-- Conditional bridge conclusion. The source's non-X/native hypotheses,
the composite's zero-residual hypothesis, aim, discipline and coverage guards,
and the accepted-imports base and its soundness are retained from the paper
but unused in this proof. Only composition, composite X-equivalence,
classification and the bridge-obligation instance are used. -/
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
    XStrengthObligation signature B X := by
  exact hbridge hcomp (hclassification hcompositeProduces.2)

/-- An explicit bridge interpretation for the satisfiability control. -/
def twoClaimBridgeSignature : BridgeSignature.{0, 0} twoTrueClaims where
  Bridge := Unit
  obligation := fun _ c => twoTrueClaims.interp c
  composition := fun _ C composite c =>
    C = closedTwoClaimCarrier ∧ composite = closedTwoClaimCarrier ∧ c = true
  coverage := fun _ _ => True

/-- All hypotheses of the repaired bridge theorem hold together in a concrete
one-dimensional zero-matrix model. Distinct true codes remove the former
propositional-equality contradiction. Every schema instance is proved here. -/
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
      BridgeObligationSchema signature B C composite X := by
  refine ⟨twoTrueClaims, twoClaimBridgeSignature, selectiveTrueBase, true,
    closedTwoClaimCarrier, closedTwoClaimCarrier, (),
    sound_base_noncollapse.1, nonXEquivalent_and_xEquivalent.1,
    closedTwoClaimCarrier_zero, ⟨rfl, rfl, rfl⟩,
    ⟨closedTwoClaimCarrier_zero, nonXEquivalent_and_xEquivalent.2⟩,
    True.intro, True.intro, True.intro,
    closedTwoClaimCarrier_classification true, ?_⟩
  intro _ _
  exact True.intro

end SixBirdsMetaMath.MetaMath.Foreclosure.BridgeImpossibility
