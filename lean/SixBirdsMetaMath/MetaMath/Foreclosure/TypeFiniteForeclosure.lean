import SixBirdsMetaMath.MetaMath.Foreclosure.Coverage

/-!
T4 Type-Finite Foreclosure.

The four-way T3 coverage result induces a uniform finite type of carrier
states.  The carrier space itself may have arbitrary cardinality; the typed
classification space has exactly these four constructors.
-/

namespace SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure

open SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy
open SixBirdsMetaMath.MetaMath.Foreclosure.Coverage

variable {language : ClaimLanguage.{u}}

/-- The four T4 typed states for an `X`-aimed carrier. -/
inductive CarrierState : Type where
  | nonXEquivalent
  | creTE
  | creBF
  | creCTMT
  deriving DecidableEq, Repr

/-- A carrier is classified as one of the four T4 states. -/
def classifyAs (s : CarrierState) (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop :=
  match s with
  | .nonXEquivalent => nonXEquivalent X C
  | .creTE => creTE X C
  | .creBF => creBF X C
  | .creCTMT => creCTMT X C

/--
T4 Type-Finite Foreclosure.

Under T3 coverage, every disciplined framework-internal carrier aimed at an
open conjecture `X` lands in one of the four typed carrier states.  Thus the
door-space is uniformly type-finite, independently of the carrier-space
cardinality.
-/
theorem type_finite_foreclosure
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hcoverage : CoverageSchema X C) :
    ∃ s : CarrierState, classifyAs s X C := by
  rcases coverage_theorem X C hcoverage with
    hnon | hte | hbf | hctmt
  · exact ⟨CarrierState.nonXEquivalent, hnon⟩
  · exact ⟨CarrierState.creTE, hte⟩
  · exact ⟨CarrierState.creBF, hbf⟩
  · exact ⟨CarrierState.creCTMT, hctmt⟩

/-- A selected T4 state for a disciplined `X`-aimed carrier. -/
noncomputable def classify
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hcoverage : CoverageSchema X C) : CarrierState :=
  Classical.choose (type_finite_foreclosure X C hcoverage)

/-- The selected T4 classifier is sound for its carrier. -/
theorem classify_spec
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hcoverage : CoverageSchema X C) :
    classifyAs (classify X C hcoverage) X C :=
  Classical.choose_spec (type_finite_foreclosure X C hcoverage)

end SixBirdsMetaMath.MetaMath.Foreclosure.TypeFiniteForeclosure
