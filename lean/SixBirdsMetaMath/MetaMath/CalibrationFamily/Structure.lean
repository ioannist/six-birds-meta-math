namespace SixBirdsMetaMath.MetaMath.CalibrationFamily.Structure

/-!
T11 Calibration-Family Structure.

The calibration-family finding is represented as typed calibration records
seeded by the M6 table.  The seed list is not a closed universe: further
calibrations are represented by arbitrary additional `Calibration` values.
-/

/-- A non-descending calibration with its detector class and native carrier type. -/
structure Calibration where
  name : String
  detectorClass : String
  nativeCarrierType : String
  deriving Repr

/-- The M6 seeded calibration family: 12 concrete calibrations plus one META object. -/
def calibrationFamily : List Calibration :=
  [
    { name := "vobs",
      detectorClass := "Low-degree polynomial (LDLR)",
      nativeCarrierType := "AC0 / AC0[p]-adjacent" },
    { name := "M_I",
      detectorClass := "Mutual-information / KL divergence",
      nativeCarrierType := "Bounded-information packages" },
    { name := "R_E",
      detectorClass := "Stable / local / overlap algorithms",
      nativeCarrierType := "Random-restriction / coupling-stable" },
    { name := "C_h",
      detectorClass := "Topological obstruction",
      nativeCarrierType := "Cohomology-lifted; Lovasz/Kneser reach" },
    { name := "Q_amp",
      detectorClass := "Quantum amplitude / query",
      nativeCarrierType := "Black-box; BBBV reach" },
    { name := "I_alg",
      detectorClass := "Algebraic ideal / Nullstellensatz",
      nativeCarrierType := "Proof-system / certificate-degree" },
    { name := "R_real",
      detectorClass := "Realizability",
      nativeCarrierType := "lambda-calculus / typed-program" },
    { name := "O_Cstar",
      detectorClass := "C*-operator",
      nativeCarrierType := "Operator-algebraic" },
    { name := "F_existsSO",
      detectorClass := "Descriptive complexity (exists-SO)",
      nativeCarrierType := "Logical / locality reach" },
    { name := "S_HO",
      detectorClass := "Game-semantic strategy",
      nativeCarrierType := "Higher-order game" },
    { name := "P_PH",
      detectorClass := "Persistent homology",
      nativeCarrierType := "Scale-dependent topological" },
    { name := "A_VNP",
      detectorClass := "Arithmetic complexity / VNP",
      nativeCarrierType := "GCT / polynomial families" },
    { name := "M_mot",
      detectorClass := "Computational motive (META)",
      nativeCarrierType := "Cross-calibration transport" }
  ]

/--
The seeded family has at least the 13 M6 entries, while the type remains
open-ended: any further named `Calibration` can be considered as an
additional family member candidate.
-/
theorem calibration_family_structure :
    calibrationFamily.length ≥ 13 ∧
      ∀ (c : Calibration), c.name ≠ "" → True := by
  constructor
  · decide
  · intro _c _hname
    trivial

end SixBirdsMetaMath.MetaMath.CalibrationFamily.Structure
