import SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy

namespace SixBirdsMetaMath.MetaMath.Foreclosure.Coverage

open SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy

variable {language : ClaimLanguage.{u}}

/-- Per-instance four-way coverage schema, without any assertion of its truth. -/
def CoverageSchema (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop :=
  nonXEquivalent X C ∨ creTE X C ∨ creBF X C ∨ creCTMT X C

/-- Coverage follows from classification when some claim code represents the
residual-closure proposition. No assumption that non-X and X are complementary
is made, and no aim/discipline/coverage guard is used. -/
theorem coverage_of_classification
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hresidual : ∃ c : language.Claim, residualClosureEquivalent C c)
    (hclassification : CarrierClassificationSchema X C) :
    nonXEquivalent X C ∨ creTE X C ∨ creBF X C ∨ creCTMT X C := by
  classical
  by_cases hx : xEquivalent X C
  · rcases hclassification hx with hte | hbf | hctmt
    · exact Or.inr (Or.inl hte.1)
    · exact Or.inr (Or.inr (Or.inl hbf.1))
    · exact Or.inr (Or.inr (Or.inr hctmt.1))
  · rcases hresidual with ⟨c, hc⟩
    refine Or.inl ⟨c, hc, ?_⟩
    intro h
    subst c
    exact hx hc

/-- Conditional application of the explicitly supplied coverage instance. -/
theorem coverage_theorem
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hcoverage : CoverageSchema X C) :
    nonXEquivalent X C ∨ creTE X C ∨ creBF X C ∨ creCTMT X C :=
  hcoverage

end SixBirdsMetaMath.MetaMath.Foreclosure.Coverage
