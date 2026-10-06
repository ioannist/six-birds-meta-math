import SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy

namespace SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure

open SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy

/-- The three classes of framework-internal moves allowed by the audit discipline. -/
inductive FrameworkInternalMove where
  | pivot
  | bridgeImport
  | cascadeReduction
  deriving DecidableEq, Repr

/-- Both move semantics and the scope predicate are freely supplied interpretations. -/
structure InternalMoveSignature (language : ClaimLanguage.{u}) where
  semantics : FrameworkInternalMove → language.Claim → Prop
  scope : language.Claim → Prop

variable {language : ClaimLanguage.{u}}

def internalMoveSemantics (signature : InternalMoveSignature language)
    (move : FrameworkInternalMove) (X : language.Claim) : Prop := signature.semantics move X

def advancesXWithoutExternal (signature : InternalMoveSignature language)
    (move : FrameworkInternalMove) (X : language.Claim) : Prop :=
  internalMoveSemantics signature move X

def InFrameworkScope (signature : InternalMoveSignature language)
    (X : language.Claim) : Prop := signature.scope X

/-- Conditional v4 schema, not an assertion about an uninterpreted semantics. -/
def AttackForeclosureV4Schema (signature : InternalMoveSignature language) : Prop :=
  ∀ (X : language.Claim) (move : FrameworkInternalMove),
    InFrameworkScope signature X → ¬ advancesXWithoutExternal signature move X

/-- Apply an explicitly supplied v4 schema. -/
theorem attack_foreclosure_v4 (signature : InternalMoveSignature language)
    (hschema : AttackForeclosureV4Schema signature)
    (X : language.Claim) (move : FrameworkInternalMove)
    (hscope : InFrameworkScope signature X) :
    ¬ advancesXWithoutExternal signature move X := hschema X move hscope

end SixBirdsMetaMath.MetaMath.Foreclosure.AttackForeclosure
