import SixBirdsMetaMath.MetaMath.CalibrationFamily.Structure

namespace SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry

open SixBirdsMetaMath.MetaMath.CalibrationFamily.Structure

/-!
T15 Coverage-Family Geometry.

Calibration coverage is represented as typed carrier regions reached by
calibrations.  Named typed holes are regions not currently reached by the
family coverage union.
-/

/-- A native carrier-region or complexity-class sub-region. -/
structure CarrierRegion where
  name : String
  deriving DecidableEq, Repr

/--
Carrier regions named in M6 section 11 (np207 verified): the union covers
bounded-depth, low-degree, stable-local, query, topological, and
low-NS-degree regions; other named regions remain uncovered holes.
-/
def boundedDepthRegion : CarrierRegion := ⟨"bounded-depth"⟩
def lowDegreeRegion : CarrierRegion := ⟨"low-degree"⟩
def stableLocalRegion : CarrierRegion := ⟨"stable-local"⟩
def queryRegion : CarrierRegion := ⟨"query"⟩
def topologicalRegion : CarrierRegion := ⟨"topological"⟩
def lowNSDegreeRegion : CarrierRegion := ⟨"low-NS-degree"⟩

def nc1Region : CarrierRegion := ⟨"NC1"⟩
def nc2Region : CarrierRegion := ⟨"NC2"⟩
def pPolyRegion : CarrierRegion := ⟨"P/poly"⟩
def adaptivePolyTimeRegion : CarrierRegion := ⟨"general-adaptive-poly-time"⟩

/--
Each seeded calibration contributes the named carrier regions verified in
M6 section 11.  The map is keyed by the ASCII calibration names used in T11.
-/
def calibrationCoverage (c : Calibration) : List CarrierRegion :=
  match c.name with
  | "vobs" => [boundedDepthRegion, lowDegreeRegion]
  | "M_I" => [boundedDepthRegion]
  | "R_E" => [stableLocalRegion]
  | "C_h" => [topologicalRegion]
  | "Q_amp" => [queryRegion]
  | "I_alg" => [lowNSDegreeRegion]
  | _ => []

/-- Family coverage is the union, represented as list concatenation, of member coverages. -/
def familyCoverage (family : List Calibration) : List CarrierRegion :=
  family.flatMap calibrationCoverage

/-- A named typed hole: an uncovered carrier region recorded as its own object. -/
structure TypedHole where
  name : String
  region : CarrierRegion
  deriving Repr

/-- Named NC1 coverage hole from M6 section 11. -/
def xiNC1Coverage : TypedHole :=
  { name := "Xi_NC1_coverage", region := nc1Region }

/-- Named adaptive trace-invariant hole from M6 section 11. -/
def xiAdaptiveTrace : TypedHole :=
  { name := "Xi_adaptive_trace_invariant_for_NC1", region := adaptivePolyTimeRegion }

/-- A hole is genuine relative to a family when its region is absent from family coverage. -/
def isGenuineHole (h : TypedHole) (family : List Calibration) : Prop :=
  h.region ∉ familyCoverage family

/-- All six M6 section 11 covered regions occur in the seeded family coverage. -/
theorem all_covered_regions_in_family :
    boundedDepthRegion ∈ familyCoverage calibrationFamily ∧
      lowDegreeRegion ∈ familyCoverage calibrationFamily ∧
        stableLocalRegion ∈ familyCoverage calibrationFamily ∧
          queryRegion ∈ familyCoverage calibrationFamily ∧
            topologicalRegion ∈ familyCoverage calibrationFamily ∧
              lowNSDegreeRegion ∈ familyCoverage calibrationFamily := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- All four M6 section 11 uncovered regions are absent from the seeded family coverage. -/
theorem all_uncovered_regions_not_in_family :
    nc1Region ∉ familyCoverage calibrationFamily ∧
      nc2Region ∉ familyCoverage calibrationFamily ∧
        pPolyRegion ∉ familyCoverage calibrationFamily ∧
          adaptivePolyTimeRegion ∉ familyCoverage calibrationFamily := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/--
Shared-region overlap: `boundedDepthRegion` is in the native coverage of
both the `vobs` and `M_I` calibrations from the T11 seed.
-/
theorem bounded_depth_overlap :
    ∃ c1 c2 : Calibration,
      c1 ∈ calibrationFamily ∧ c2 ∈ calibrationFamily ∧
        c1 ≠ c2 ∧
          boundedDepthRegion ∈ calibrationCoverage c1 ∧
            boundedDepthRegion ∈ calibrationCoverage c2 := by
  let cVobs : Calibration :=
    { name := "vobs",
      detectorClass := "Low-degree polynomial (LDLR)",
      nativeCarrierType := "AC0 / AC0[p]-adjacent" }
  let cMI : Calibration :=
    { name := "M_I",
      detectorClass := "Mutual-information / KL divergence",
      nativeCarrierType := "Bounded-information packages" }
  refine ⟨cVobs, cMI, ?_, ?_, ?_, ?_, ?_⟩
  · simp [calibrationFamily, cVobs]
  · simp [calibrationFamily, cMI]
  · intro hsame
    exact (by decide : "vobs" ≠ "M_I") (congrArg Calibration.name hsame)
  · decide
  · decide

/--
A calibration with empty native coverage adds nothing to family coverage.
This captures the M6 point that more calibrations are not monotonically more
closure power; only native carrier coverage changes the union.
-/
theorem empty_coverage_adds_nothing
    (c : Calibration) (h : calibrationCoverage c = [])
    (family : List Calibration) :
    familyCoverage (family ++ [c]) = familyCoverage family := by
  simp [familyCoverage, h]

/--
The seeded T11 family covers the six verified regions, excludes all four
named uncovered regions, and the two named typed holes are genuine.
-/
theorem coverage_family_geometry :
    boundedDepthRegion ∈ familyCoverage calibrationFamily ∧
      lowDegreeRegion ∈ familyCoverage calibrationFamily ∧
        stableLocalRegion ∈ familyCoverage calibrationFamily ∧
          queryRegion ∈ familyCoverage calibrationFamily ∧
            topologicalRegion ∈ familyCoverage calibrationFamily ∧
              lowNSDegreeRegion ∈ familyCoverage calibrationFamily ∧
                nc1Region ∉ familyCoverage calibrationFamily ∧
                  nc2Region ∉ familyCoverage calibrationFamily ∧
                    pPolyRegion ∉ familyCoverage calibrationFamily ∧
                      adaptivePolyTimeRegion ∉ familyCoverage calibrationFamily ∧
                        isGenuineHole xiNC1Coverage calibrationFamily ∧
                          isGenuineHole xiAdaptiveTrace calibrationFamily := by
  rcases all_covered_regions_in_family with
    ⟨hbounded, hlow, hstable, hquery, htop, hlowNS⟩
  rcases all_uncovered_regions_not_in_family with
    ⟨hnc1, hnc2, hpPoly, hadaptive⟩
  refine ⟨hbounded, hlow, hstable, hquery, htop, hlowNS, hnc1, hnc2, hpPoly, hadaptive, ?_, ?_⟩
  · change nc1Region ∉ familyCoverage calibrationFamily
    exact hnc1
  · change adaptivePolyTimeRegion ∉ familyCoverage calibrationFamily
    exact hadaptive

end SixBirdsMetaMath.MetaMath.CalibrationFamily.CoverageFamilyGeometry
