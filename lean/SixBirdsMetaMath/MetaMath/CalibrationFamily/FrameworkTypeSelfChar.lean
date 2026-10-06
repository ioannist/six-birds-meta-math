import SixBirdsMetaMath.MetaMath.CalibrationFamily.FunctorialGates
import SixBirdsMetaMath.MetaMath.RecognitionMode.Template

namespace SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar

open SixBirdsMetaMath.MetaMath.CalibrationFamily.FunctorialGates
open SixBirdsMetaMath.MetaMath.RecognitionMode.Template

/-!
T16 Framework-Type Self-Characterization.

The PvNP calibration-family framework type is compared against the standard
Clay-grade PvNP target type.  The candidate framework-general mismatch claim
is kept as a narrow same-paper obligation; the three named gates are supplied
by T17.
-/

/-- Four-axis type descriptor for framework reach or target obligation shape. -/
structure FrameworkType where
  uniformity : String
  worstCaseness : String
  scoping : String
  packaging : String
  deriving Repr, Inhabited

/-- PvNP framework-native type: nonuniform / average-case / scoped / package-based. -/
def pvnpFrameworkType : FrameworkType where
  uniformity := "nonuniform"
  worstCaseness := "average-case"
  scoping := "scoped"
  packaging := "package-based"

/-- Standard Clay-grade PvNP target type: uniform / worst-case / unconditional / language-based. -/
def standardClayPvNPType : FrameworkType where
  uniformity := "uniform"
  worstCaseness := "worst-case"
  scoping := "unconditional"
  packaging := "language-based"

/-- Two framework types match only when all four axes agree. -/
def typesMatch (a b : FrameworkType) : Prop :=
  a.uniformity = b.uniformity ∧
    a.worstCaseness = b.worstCaseness ∧
      a.scoping = b.scoping ∧
        a.packaging = b.packaging

/--
The PvNP framework-type mismatch with the standard Clay target type is
directly decidable from the concrete four-axis records.
-/
theorem pvnp_framework_type_mismatch :
    ¬ typesMatch pvnpFrameworkType standardClayPvNPType := by
  intro hmatch
  exact (by decide : "nonuniform" ≠ "uniform") hmatch.1

/--
The framework type a Clay-class track in V-Differential's trace-state-only
column exhibits via its calibration family.
-/
opaque cascadeFrameworkType : FormedClosure → FrameworkType

/--
The standard Clay-target framework type for a Clay-class problem instance.
-/
opaque standardClayTargetType : FormedClosure → FrameworkType

/--
Same-paper candidate framework-general obligation: every Clay-class track in
V-Differential's trace-state-only column has a cascade-native framework type
that differs from its standard Clay target type.
-/
def FrameworkTypeGeneralSchema : Prop :=
    ∀ c : FormedClosure,
      VDifferentialTSOColumn c →
        ¬ typesMatch (cascadeFrameworkType c) (standardClayTargetType c)

/--
Framework-type self-characterization: the PvNP framework-native type differs
from the Clay-grade target type, and T17 supplies exactly three named
functorial gates separating the two.
-/
theorem framework_type_self_characterization :
    ¬ typesMatch pvnpFrameworkType standardClayPvNPType ∧
      namedFunctorialGates.length = 3 := by
  refine ⟨pvnp_framework_type_mismatch, ?_⟩
  exact named_functorial_gates.1

end SixBirdsMetaMath.MetaMath.CalibrationFamily.FrameworkTypeSelfChar
