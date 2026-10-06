import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
F47 Fine-Tuning as Small Selector Region.

Fine-tuning is modeled as smallness of a target-compatible region inside a
declared moduli space under a declared measure/size ledger. Realized
fine-tuning additionally requires a selected modulus in that region; smallness
alone does not supply the selector.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.FineTuning

/-- The target-compatible moduli region `F ⁻¹' A`. -/
def CompatibleRegion {Moduli Value : Type} (readout : Moduli → Value)
    (targetRegion : Value → Prop) : Moduli → Prop :=
  fun modulus => targetRegion (readout modulus)

/-- The target is impossible when the compatible region is empty. -/
def TargetImpossible {Moduli : Type} (compatible : Moduli → Prop) : Prop :=
  ∀ modulus, ¬ compatible modulus

/-- The target is lawlike when every lawful modulus is compatible. -/
def TargetLawlike {Moduli : Type} (compatible : Moduli → Prop) : Prop :=
  ∀ modulus, compatible modulus

/-- A small selector region requires a nonzero compatible region whose measured
size is bounded by the declared threshold-scaled total measure. -/
def SmallSelectorRegion {Moduli Measure Threshold : Type}
    (measureRegion : (Moduli → Prop) → Measure) (totalMeasure : Measure)
    (threshold : Threshold) (scaleThreshold : Threshold → Measure → Measure)
    (Positive : Measure → Prop) (Le : Measure → Measure → Prop)
    (compatible : Moduli → Prop) : Prop :=
  Positive (measureRegion compatible) ∧
    Le (measureRegion compatible) (scaleThreshold threshold totalMeasure)

/-- Measure-zero tuning is a nonempty compatible region with zero declared
measure. -/
def MeasureZeroTuning {Moduli Measure : Type}
    (measureRegion : (Moduli → Prop) → Measure) (Zero : Measure)
    (compatible : Moduli → Prop) : Prop :=
  (∃ modulus, compatible modulus) ∧ measureRegion compatible = Zero

/-- Target-compatible but not fine-tuned: a nonempty compatible region whose
measure is not small under the declared threshold. -/
def CompatibleNotFineTuned {Moduli Measure Threshold : Type}
    (measureRegion : (Moduli → Prop) → Measure) (totalMeasure : Measure)
    (threshold : Threshold) (scaleThreshold : Threshold → Measure → Measure)
    (Positive : Measure → Prop) (Le : Measure → Measure → Prop)
    (compatible : Moduli → Prop) : Prop :=
  Positive (measureRegion compatible) ∧
    ¬ Le (measureRegion compatible) (scaleThreshold threshold totalMeasure)

/-- Realized fine-tuning requires a declared selector, selected membership in
the compatible region, and the small-region condition. -/
def RealizedFineTuning {Moduli Measure Threshold : Type}
    (measureRegion : (Moduli → Prop) → Measure) (totalMeasure : Measure)
    (threshold : Threshold) (scaleThreshold : Threshold → Measure → Measure)
    (Positive : Measure → Prop) (Le : Measure → Measure → Prop)
    (compatible : Moduli → Prop) (selected : Moduli)
    (selectorDeclared : Prop) : Prop :=
  selectorDeclared ∧
    compatible selected ∧
      SmallSelectorRegion measureRegion totalMeasure threshold scaleThreshold
        Positive Le compatible

/-- A small compatible region without a selected modulus is not yet realized
fine-tuning. -/
def SmallCompatibleRegionOnly {Moduli Measure Threshold : Type}
    (measureRegion : (Moduli → Prop) → Measure) (totalMeasure : Measure)
    (threshold : Threshold) (scaleThreshold : Threshold → Measure → Measure)
    (Positive : Measure → Prop) (Le : Measure → Measure → Prop)
    (compatible : Moduli → Prop) (selectorDeclared : Prop) : Prop :=
  SmallSelectorRegion measureRegion totalMeasure threshold scaleThreshold
      Positive Le compatible ∧
    ¬ selectorDeclared

/-- Fine-tuning claims are well-typed only when all structural declarations are
present. -/
def FineTuningWellTyped (moduliDeclared targetDeclared measureDeclared
    thresholdDeclared presentationStatused : Prop) : Prop :=
  moduliDeclared ∧ targetDeclared ∧ measureDeclared ∧ thresholdDeclared ∧
    presentationStatused

/-- Fine-tuning overread: a tuning claim is made while required declarations are
missing. -/
def FineTuningOverread (moduliDeclared targetDeclared measureDeclared
    thresholdDeclared presentationStatused : Prop) : Prop :=
  ¬ FineTuningWellTyped moduliDeclared targetDeclared measureDeclared
    thresholdDeclared presentationStatused

/-- A measure/ledger is stable when the package supplies a stability predicate
for it. -/
def StableMeasureLedger {Moduli Measure : Type}
    (measureRegion : (Moduli → Prop) → Measure)
    (Stable : ((Moduli → Prop) → Measure) → Prop) : Prop :=
  Stable measureRegion

/-- A conditioned tuning claim changes the measure/ledger by declaring a
conditioning event. -/
def ConditionedFineTuning {Condition Moduli Measure Threshold : Type}
    (condition : Condition) (conditionedMeasure : Condition → (Moduli → Prop) → Measure)
    (totalMeasure : Condition → Measure) (threshold : Threshold)
    (scaleThreshold : Threshold → Measure → Measure) (Positive : Measure → Prop)
    (Le : Measure → Measure → Prop) (compatible : Moduli → Prop) : Prop :=
  SmallSelectorRegion (conditionedMeasure condition) (totalMeasure condition)
    threshold scaleThreshold Positive Le compatible

/-- Law-strengthening explanation: under a strengthened base all moduli become
target-compatible. -/
def LawStrengthenedTarget {Moduli : Type} (compatibleAfterStrengthening : Moduli → Prop) :
    Prop :=
  TargetLawlike compatibleAfterStrengthening

/-- Selector explanation: a declared selector source lands in the compatible
region. -/
def SelectorExplanation {Source Moduli : Type} (selector : Source → Moduli)
    (source : Source) (compatible : Moduli → Prop) : Prop :=
  compatible (selector source)

/-- Source status vocabulary for fine-tuning claims. -/
inductive FineTuningStatus where
  | uniqueClosure
  | targetImpossible
  | targetLawlike
  | contingentNotFineTuned
  | smallSelectorRegion
  | realizedFineTuning
  | measureZeroTuning
  | singularSelectorRegion
  | probabilisticFineTuning
  | conditionedFineTuning
  | measureAbsent
  | unstableMeasure
  | infiniteMeasureAmbiguity
  | cutoffDependentTuning
  | targetOverSpecified
  | posthocTarget
  | presentationTuningArtifact
  | hiddenFineTuningSelector
  | boundarySelectedFineTuning
  | lawStrengthened
  | nativeTarget
  | recordedTarget
  | observedTarget
  | naturalLawlike
  | naturalLargeRegion
  | explainedFineTuning
  | unexplainedFineTuning
  | fineTuningOverread
deriving DecidableEq

/-- Meaning assignment for the F47 fine-tuning status vocabulary. -/
def FineTuningStatusHolds (unique impossible lawlike contingentNotSmall small realized
    measureZero singular probabilistic conditioned measureAbsent unstable infiniteAmbiguous
    cutoffDependent targetOverSpecified posthoc presentationArtifact hiddenSelector
    boundarySelected lawStrengthened native recorded observed naturalLaw naturalLarge
    explained unexplained overread : Prop) : FineTuningStatus → Prop
  | FineTuningStatus.uniqueClosure => unique
  | FineTuningStatus.targetImpossible => impossible
  | FineTuningStatus.targetLawlike => lawlike
  | FineTuningStatus.contingentNotFineTuned => contingentNotSmall
  | FineTuningStatus.smallSelectorRegion => small
  | FineTuningStatus.realizedFineTuning => realized
  | FineTuningStatus.measureZeroTuning => measureZero
  | FineTuningStatus.singularSelectorRegion => singular
  | FineTuningStatus.probabilisticFineTuning => probabilistic
  | FineTuningStatus.conditionedFineTuning => conditioned
  | FineTuningStatus.measureAbsent => measureAbsent
  | FineTuningStatus.unstableMeasure => unstable
  | FineTuningStatus.infiniteMeasureAmbiguity => infiniteAmbiguous
  | FineTuningStatus.cutoffDependentTuning => cutoffDependent
  | FineTuningStatus.targetOverSpecified => targetOverSpecified
  | FineTuningStatus.posthocTarget => posthoc
  | FineTuningStatus.presentationTuningArtifact => presentationArtifact
  | FineTuningStatus.hiddenFineTuningSelector => hiddenSelector
  | FineTuningStatus.boundarySelectedFineTuning => boundarySelected
  | FineTuningStatus.lawStrengthened => lawStrengthened
  | FineTuningStatus.nativeTarget => native
  | FineTuningStatus.recordedTarget => recorded
  | FineTuningStatus.observedTarget => observed
  | FineTuningStatus.naturalLawlike => naturalLaw
  | FineTuningStatus.naturalLargeRegion => naturalLarge
  | FineTuningStatus.explainedFineTuning => explained
  | FineTuningStatus.unexplainedFineTuning => unexplained
  | FineTuningStatus.fineTuningOverread => overread

/-- Compatible region is exactly the target preimage under the moduli readout. -/
theorem compatible_region_iff_preimage {Moduli Value : Type}
    (readout : Moduli → Value) (targetRegion : Value → Prop) (modulus : Moduli) :
    CompatibleRegion readout targetRegion modulus ↔ targetRegion (readout modulus) := by
  rfl

/-- Extensionally equal target regions give extensionally equal compatible
regions. -/
theorem compatible_region_ext {Moduli Value : Type} (readout : Moduli → Value)
    (targetRegion₁ targetRegion₂ : Value → Prop)
    (htarget : ∀ value, targetRegion₁ value ↔ targetRegion₂ value) :
    CompatibleRegion readout targetRegion₁ =
      CompatibleRegion readout targetRegion₂ := by
  funext modulus
  exact propext (htarget (readout modulus))

/-- Small selector region is exactly the positive-and-threshold measure gate. -/
theorem small_selector_region_iff_threshold {Moduli Measure Threshold : Type}
    (measureRegion : (Moduli → Prop) → Measure) (totalMeasure : Measure)
    (threshold : Threshold) (scaleThreshold : Threshold → Measure → Measure)
    (Positive : Measure → Prop) (Le : Measure → Measure → Prop)
    (compatible : Moduli → Prop) :
    SmallSelectorRegion measureRegion totalMeasure threshold scaleThreshold
        Positive Le compatible ↔
      Positive (measureRegion compatible) ∧
        Le (measureRegion compatible) (scaleThreshold threshold totalMeasure) := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Realized fine-tuning is selected membership plus small compatible region,
with selector declaration carried explicitly. -/
theorem realized_fine_tuning_iff_selected_small {Moduli Measure Threshold : Type}
    (measureRegion : (Moduli → Prop) → Measure) (totalMeasure : Measure)
    (threshold : Threshold) (scaleThreshold : Threshold → Measure → Measure)
    (Positive : Measure → Prop) (Le : Measure → Measure → Prop)
    (compatible : Moduli → Prop) (selected : Moduli)
    (selectorDeclared : Prop) :
    RealizedFineTuning measureRegion totalMeasure threshold scaleThreshold
        Positive Le compatible selected selectorDeclared ↔
      selectorDeclared ∧ compatible selected ∧
        SmallSelectorRegion measureRegion totalMeasure threshold scaleThreshold
          Positive Le compatible := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Empty compatible region is impossibility, not realized fine-tuning. -/
theorem target_impossible_not_realized {Moduli Measure Threshold : Type}
    (measureRegion : (Moduli → Prop) → Measure) (totalMeasure : Measure)
    (threshold : Threshold) (scaleThreshold : Threshold → Measure → Measure)
    (Positive : Measure → Prop) (Le : Measure → Measure → Prop)
    (compatible : Moduli → Prop) (selected : Moduli)
    (selectorDeclared : Prop) :
    TargetImpossible compatible →
      ¬ RealizedFineTuning measureRegion totalMeasure threshold scaleThreshold
        Positive Le compatible selected selectorDeclared := by
  intro himpossible hrealized
  exact himpossible selected hrealized.2.1

/-- Fine-tuning well-typedness is exactly the required declaration tuple. -/
theorem fine_tuning_well_typed_iff (moduliDeclared targetDeclared measureDeclared
    thresholdDeclared presentationStatused : Prop) :
    FineTuningWellTyped moduliDeclared targetDeclared measureDeclared
        thresholdDeclared presentationStatused ↔
      moduliDeclared ∧ targetDeclared ∧ measureDeclared ∧ thresholdDeclared ∧
        presentationStatused := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
Fine-Tuning as Small Selector Region Normal Form. The target-compatible region
is the preimage of the target condition on moduli; smallness is meaningful only
through a declared positive threshold measure gate; and realized fine-tuning
requires a declared selected modulus lying in that small region. Empty regions
are impossible targets, not realized tuning.
-/
theorem fine_tuning_small_selector_region {Moduli Value Measure Threshold : Type}
    (readout : Moduli → Value) (targetRegion : Value → Prop)
    (measureRegion : (Moduli → Prop) → Measure) (totalMeasure : Measure)
    (threshold : Threshold) (scaleThreshold : Threshold → Measure → Measure)
    (Positive : Measure → Prop) (Le : Measure → Measure → Prop)
    (selected : Moduli) (selectorDeclared : Prop)
    (moduliDeclared targetDeclared measureDeclared thresholdDeclared
      presentationStatused : Prop) :
    (∀ modulus,
      CompatibleRegion readout targetRegion modulus ↔
        targetRegion (readout modulus)) ∧
      (SmallSelectorRegion measureRegion totalMeasure threshold scaleThreshold
          Positive Le (CompatibleRegion readout targetRegion) ↔
        Positive (measureRegion (CompatibleRegion readout targetRegion)) ∧
          Le (measureRegion (CompatibleRegion readout targetRegion))
            (scaleThreshold threshold totalMeasure)) ∧
        (RealizedFineTuning measureRegion totalMeasure threshold scaleThreshold
            Positive Le (CompatibleRegion readout targetRegion) selected
            selectorDeclared ↔
          selectorDeclared ∧ CompatibleRegion readout targetRegion selected ∧
            SmallSelectorRegion measureRegion totalMeasure threshold scaleThreshold
              Positive Le (CompatibleRegion readout targetRegion)) ∧
          (TargetImpossible (CompatibleRegion readout targetRegion) →
            ¬ RealizedFineTuning measureRegion totalMeasure threshold scaleThreshold
              Positive Le (CompatibleRegion readout targetRegion) selected
              selectorDeclared) ∧
            (FineTuningWellTyped moduliDeclared targetDeclared measureDeclared
                thresholdDeclared presentationStatused ↔
              moduliDeclared ∧ targetDeclared ∧ measureDeclared ∧
                thresholdDeclared ∧ presentationStatused) := by
  exact ⟨fun modulus => compatible_region_iff_preimage readout targetRegion modulus,
    small_selector_region_iff_threshold measureRegion totalMeasure threshold
      scaleThreshold Positive Le (CompatibleRegion readout targetRegion),
    realized_fine_tuning_iff_selected_small measureRegion totalMeasure threshold
      scaleThreshold Positive Le (CompatibleRegion readout targetRegion) selected
      selectorDeclared,
    target_impossible_not_realized measureRegion totalMeasure threshold scaleThreshold
      Positive Le (CompatibleRegion readout targetRegion) selected selectorDeclared,
    fine_tuning_well_typed_iff moduliDeclared targetDeclared measureDeclared
      thresholdDeclared presentationStatused⟩

/-- Paper F47, including realized-region positivity/nonemptiness and
monotonicity under target strengthening. -/
theorem fine_tuning_small_selector_region_paper
    {Moduli Value Measure Threshold : Type}
    (readout : Moduli → Value) (targetRegion : Value → Prop)
    (measureRegion : (Moduli → Prop) → Measure) (totalMeasure : Measure)
    (threshold : Threshold) (scaleThreshold : Threshold → Measure → Measure)
    (Positive : Measure → Prop) (Le : Measure → Measure → Prop)
    (selected : Moduli) (selectorDeclared : Prop)
    (moduliDeclared targetDeclared measureDeclared thresholdDeclared
      presentationStatused : Prop) :
    (∀ modulus,
      CompatibleRegion readout targetRegion modulus ↔
        targetRegion (readout modulus)) ∧
    (SmallSelectorRegion measureRegion totalMeasure threshold scaleThreshold
        Positive Le (CompatibleRegion readout targetRegion) ↔
      Positive (measureRegion (CompatibleRegion readout targetRegion)) ∧
        Le (measureRegion (CompatibleRegion readout targetRegion))
          (scaleThreshold threshold totalMeasure)) ∧
    (RealizedFineTuning measureRegion totalMeasure threshold scaleThreshold
        Positive Le (CompatibleRegion readout targetRegion) selected
        selectorDeclared ↔
      selectorDeclared ∧ CompatibleRegion readout targetRegion selected ∧
        SmallSelectorRegion measureRegion totalMeasure threshold scaleThreshold
          Positive Le (CompatibleRegion readout targetRegion)) ∧
    (TargetImpossible (CompatibleRegion readout targetRegion) →
      ¬ RealizedFineTuning measureRegion totalMeasure threshold scaleThreshold
        Positive Le (CompatibleRegion readout targetRegion) selected
        selectorDeclared) ∧
    (FineTuningWellTyped moduliDeclared targetDeclared measureDeclared
        thresholdDeclared presentationStatused ↔
      moduliDeclared ∧ targetDeclared ∧ measureDeclared ∧
        thresholdDeclared ∧ presentationStatused) ∧
    (RealizedFineTuning measureRegion totalMeasure threshold scaleThreshold
        Positive Le (CompatibleRegion readout targetRegion) selected
        selectorDeclared →
      Positive (measureRegion (CompatibleRegion readout targetRegion)) ∧
        ∃ m, CompatibleRegion readout targetRegion m) ∧
    (∀ targetRegion' : Value → Prop,
      (∀ A B : Moduli → Prop,
        (∀ m, A m → B m) → Le (measureRegion A) (measureRegion B)) →
      (∀ x y z, Le x y → Le y z → Le x z) →
      (∀ v, targetRegion v → targetRegion' v) →
      Positive (measureRegion (CompatibleRegion readout targetRegion)) →
      SmallSelectorRegion measureRegion totalMeasure threshold scaleThreshold
        Positive Le (CompatibleRegion readout targetRegion') →
      SmallSelectorRegion measureRegion totalMeasure threshold scaleThreshold
        Positive Le (CompatibleRegion readout targetRegion)) := by
  rcases fine_tuning_small_selector_region readout targetRegion measureRegion
    totalMeasure threshold scaleThreshold Positive Le selected selectorDeclared
    moduliDeclared targetDeclared measureDeclared thresholdDeclared
    presentationStatused with ⟨hmem, hsmall, hrealized, himpossible, htyped⟩
  refine ⟨hmem, hsmall, hrealized, himpossible, htyped, ?_, ?_⟩
  · intro hreal
    exact ⟨hreal.2.2.1, selected, hreal.2.1⟩
  · intro targetRegion' hmono htrans htarget hpositive hsmall'
    refine ⟨hpositive, ?_⟩
    exact htrans _ _ _
      (hmono _ _ (fun m hm => htarget (readout m) hm)) hsmall'.2

/-- With real measure records, complementary regions cannot both be smaller
than half the positive total. Only their complementary-region additivity is
needed, rather than additivity on all events. -/
theorem complementary_selector_regions_not_both_small_real
    {Moduli Value : Type} (readout : Moduli → Value) (targetRegion : Value → Prop)
    (measureRegion : (Moduli → Prop) → ℝ) (totalMeasure threshold : ℝ)
    (hadd : measureRegion (fun _ => True) =
      measureRegion (CompatibleRegion readout targetRegion) +
        measureRegion (CompatibleRegion readout (fun v => ¬ targetRegion v)))
    (htotal : measureRegion (fun _ => True) = totalMeasure)
    (hpositive : 0 < totalMeasure) (hthreshold : threshold < 1 / 2) :
    ¬ (SmallSelectorRegion measureRegion totalMeasure threshold (· * ·)
        (fun x => 0 < x) (· ≤ ·) (CompatibleRegion readout targetRegion) ∧
      SmallSelectorRegion measureRegion totalMeasure threshold (· * ·)
        (fun x => 0 < x) (· ≤ ·)
        (CompatibleRegion readout (fun v => ¬ targetRegion v))) := by
  rintro ⟨⟨_, hsmall⟩, ⟨_, hcomplement⟩⟩
  have hscaled := mul_lt_mul_of_pos_right hthreshold hpositive
  rw [htotal] at hadd
  change measureRegion (CompatibleRegion readout targetRegion) ≤
    threshold * totalMeasure at hsmall
  change measureRegion (CompatibleRegion readout (fun v => ¬ targetRegion v)) ≤
    threshold * totalMeasure at hcomplement
  nlinarith

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.FineTuning
