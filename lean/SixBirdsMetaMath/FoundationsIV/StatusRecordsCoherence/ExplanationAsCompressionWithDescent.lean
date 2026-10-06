import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F30 Explanation as Compression With Descent.

An explanation is modeled as an explanatory quotient that is available from the
declared base quotient, preserves the target readout by descent, and is
nontrivially compressed only when it forgets some base distinction. Residual,
probabilistic, scoped, hidden-source, local, and narrative cases are typed as
statuses rather than silently promoted to exact explanation.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ExplanationAsCompressionWithDescent

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- The explanatory quotient uses only distinctions available in the base. -/
def SourceAdmissible {H B E : Type} (base : H → B) (explanation : H → E) :
    Prop :=
  Descends base (fun h : H => h) explanation

/-- The target readout is recoverable from the explanatory quotient. -/
def TargetPreserving {H E T : Type} (explanation : H → E) (target : H → T) :
    Prop :=
  Descends explanation (fun h : H => h) target

/-- Exact explanation is source admissibility plus exact target preservation. -/
def ExactExplanation {H B E T : Type} (base : H → B) (explanation : H → E)
    (target : H → T) : Prop :=
  SourceAdmissible base explanation ∧ TargetPreserving explanation target

/-- Source-overread obstruction: same base value but different explanation. -/
def SourceOverreadObstruction {H B E : Type} (base : H → B)
    (explanation : H → E) : (H × H) → Prop :=
  splitPairObstruction base (fun h : H => h) explanation

/-- No source-overread obstruction is present. -/
def SourceOverreadObstructionEmpty {H B E : Type} (base : H → B)
    (explanation : H → E) : Prop :=
  ObstructionEmpty (SourceOverreadObstruction base explanation)

/-- Target-loss obstruction: same explanation value but different target. -/
def TargetLossObstruction {H E T : Type} (explanation : H → E)
    (target : H → T) : (H × H) → Prop :=
  splitPairObstruction explanation (fun h : H => h) target

/-- No target-loss obstruction is present. -/
def TargetLossObstructionEmpty {H E T : Type} (explanation : H → E)
    (target : H → T) : Prop :=
  ObstructionEmpty (TargetLossObstruction explanation target)

/-- Compression witness: the explanation identifies states separated by the
base quotient. -/
def CompressionWitness {H B E : Type} (explanation : H → E) (base : H → B) :
    (H × H) → Prop :=
  splitPairObstruction explanation (fun h : H => h) base

/-- The compression witness set is empty. -/
def CompressionWitnessEmpty {H B E : Type} (explanation : H → E)
    (base : H → B) : Prop :=
  ObstructionEmpty (CompressionWitness explanation base)

/-- The compression witness set is nonempty, so the explanation is genuinely
coarser than the base on reachable states. -/
def CompressionWitnessNonempty {H B E : Type} (explanation : H → E)
    (base : H → B) : Prop :=
  ∃ pair, CompressionWitness explanation base pair

/-- Strict compression means source admissibility plus failure of the base to
descend back through the explanation. -/
def StrictCompression {H B E : Type} (base : H → B) (explanation : H → E) :
    Prop :=
  SourceAdmissible base explanation ∧
    ¬ Descends explanation (fun h : H => h) base

/-- Exact compressed explanation adds nontrivial compression to the exact
descent diagram. -/
def ExactCompressedExplanation {H B E T : Type} (base : H → B)
    (explanation : H → E) (target : H → T) : Prop :=
  ExactExplanation base explanation target ∧ CompressionWitnessNonempty explanation base

/-- A target quotient is minimal sufficient for a target when it preserves the
target and every exact target-preserving explanation descends to it. -/
def MinimalTargetSufficient {H QT T : Type} (targetQuotient : H → QT)
    (target : H → T) : Prop :=
  TargetPreserving targetQuotient target ∧
    ∀ {E : Type} (explanation : H → E),
      TargetPreserving explanation target →
        Descends explanation (fun h : H => h) targetQuotient

/-- Dynamic explanation requires the later explanatory quotient to descend
along the continuation and then preserve the later target. -/
def DynamicExplanation {H E H' E' T' : Type} (explanation : H → E)
    (continuation : H → H') (laterExplanation : H' → E')
    (laterTarget : H' → T') : Prop :=
  Descends explanation continuation laterExplanation ∧
    TargetPreserving laterExplanation laterTarget

/-- Residual-budgeted explanation is typed separately from exact target
preservation. -/
def BudgetedExplanation {H B E Residual Budget : Type} (base : H → B)
    (explanation : H → E) (residual : H → Residual)
    (budget : Budget) (WithinBudget : Residual → Budget → Prop) : Prop :=
  SourceAdmissible base explanation ∧ ∀ h, WithinBudget (residual h) budget

/-- Source status vocabulary for explanation claims. -/
inductive ExplanationStatus where
  | exactCompressedExplanation
  | exactRestatement
  | targetRestatement
  | redundantExplanation
  | overcompressed
  | sourceOverread
  | budgetedExplanation
  | probabilisticExplanation
  | mechanisticExplanation
  | causalExplanation
  | scopedExplanation
  | localExplanation
  | globalExplanationObstructed
  | circularExplanation
  | narrativeAssociation
  | explanationOverread
deriving DecidableEq

/-- Meaning assignment for the F30 status vocabulary. -/
def ExplanationStatusHolds (exactCompressed exactRestatement targetRestatement
    redundant overcompressed sourceOverread budgeted probabilistic mechanistic causal
    scopedStatus localOnly globalObstructed circular narrative overread : Prop) :
    ExplanationStatus → Prop
  | ExplanationStatus.exactCompressedExplanation => exactCompressed
  | ExplanationStatus.exactRestatement => exactRestatement
  | ExplanationStatus.targetRestatement => targetRestatement
  | ExplanationStatus.redundantExplanation => redundant
  | ExplanationStatus.overcompressed => overcompressed
  | ExplanationStatus.sourceOverread => sourceOverread
  | ExplanationStatus.budgetedExplanation => budgeted
  | ExplanationStatus.probabilisticExplanation => probabilistic
  | ExplanationStatus.mechanisticExplanation => mechanistic
  | ExplanationStatus.causalExplanation => causal
  | ExplanationStatus.scopedExplanation => scopedStatus
  | ExplanationStatus.localExplanation => localOnly
  | ExplanationStatus.globalExplanationObstructed => globalObstructed
  | ExplanationStatus.circularExplanation => circular
  | ExplanationStatus.narrativeAssociation => narrative
  | ExplanationStatus.explanationOverread => overread

/-- Source admissibility is exactly absence of the source-overread split pair. -/
theorem source_admissible_iff_no_overread {H B E : Type} (base : H → B)
    (explanation : H → E) (hbase : Function.Surjective base) :
    SourceAdmissible base explanation ↔
      SourceOverreadObstructionEmpty base explanation :=
  descent_repair_normal_form base (fun h : H => h) explanation hbase

/-- Target preservation is exactly absence of target loss. -/
theorem target_preserving_iff_no_loss {H E T : Type} (explanation : H → E)
    (target : H → T) (hexplanation : Function.Surjective explanation) :
    TargetPreserving explanation target ↔
      TargetLossObstructionEmpty explanation target :=
  descent_repair_normal_form explanation (fun h : H => h) target hexplanation

/-- The base descends back through the explanation exactly when there is no
compression witness. -/
theorem base_descends_back_iff_no_compression_witness {H B E : Type}
    (base : H → B) (explanation : H → E)
    (hexplanation : Function.Surjective explanation) :
    Descends explanation (fun h : H => h) base ↔
      CompressionWitnessEmpty explanation base :=
  descent_repair_normal_form explanation (fun h : H => h) base hexplanation

/-- Exact explanation is equivalent to the two empty obstruction conditions. -/
theorem exact_explanation_iff_empty_obstructions {H B E T : Type}
    (base : H → B) (explanation : H → E) (target : H → T)
    (hbase : Function.Surjective base)
    (hexplanation : Function.Surjective explanation) :
    ExactExplanation base explanation target ↔
      SourceOverreadObstructionEmpty base explanation ∧
        TargetLossObstructionEmpty explanation target := by
  constructor
  · intro hexact
    exact ⟨(source_admissible_iff_no_overread base explanation hbase).1 hexact.1,
      (target_preserving_iff_no_loss explanation target hexplanation).1 hexact.2⟩
  · intro hclear
    exact ⟨(source_admissible_iff_no_overread base explanation hbase).2 hclear.1,
      (target_preserving_iff_no_loss explanation target hexplanation).2 hclear.2⟩

/-- Exact explanation is equivalently the factorization
`H -> B -> E -> T`. -/
theorem exact_explanation_iff_factorization {H B E T : Type}
    (base : H → B) (explanation : H → E) (target : H → T) :
    ExactExplanation base explanation target ↔
      ∃ alpha : B → E, ∃ beta : E → T,
        alpha ∘ base = explanation ∧ beta ∘ explanation = target := by
  constructor
  · intro hexact
    rcases hexact with ⟨hsource, htarget⟩
    rcases hsource with ⟨alpha, halpha⟩
    rcases htarget with ⟨beta, hbeta⟩
    refine ⟨alpha, beta, ?_, ?_⟩
    · simpa [Function.comp] using halpha
    · simpa [Function.comp] using hbeta
  · intro hfactor
    rcases hfactor with ⟨alpha, beta, halpha, hbeta⟩
    constructor
    · refine ⟨alpha, ?_⟩
      simpa [Function.comp] using halpha
    · refine ⟨beta, ?_⟩
      simpa [Function.comp] using hbeta

/-- Strict compression is source admissibility plus a nonempty compression
witness set. -/
theorem strict_compression_iff_source_and_witness {H B E : Type}
    (base : H → B) (explanation : H → E)
    (hbase : Function.Surjective base)
    (hexplanation : Function.Surjective explanation) :
    StrictCompression base explanation ↔
      SourceOverreadObstructionEmpty base explanation ∧
        CompressionWitnessNonempty explanation base := by
  constructor
  · intro hstrict
    have hsourceEmpty :
        SourceOverreadObstructionEmpty base explanation :=
      (source_admissible_iff_no_overread base explanation hbase).1 hstrict.1
    have hnotEmpty : ¬ CompressionWitnessEmpty explanation base := by
      intro hempty
      exact hstrict.2
        ((base_descends_back_iff_no_compression_witness base explanation
          hexplanation).2 hempty)
    have hwitness : CompressionWitnessNonempty explanation base := by
      classical
      exact Classical.byContradiction (fun hnoWitness =>
        hnotEmpty (fun pair hpair => hnoWitness ⟨pair, hpair⟩))
    exact ⟨hsourceEmpty, hwitness⟩
  · intro hclear
    constructor
    · exact (source_admissible_iff_no_overread base explanation hbase).2 hclear.1
    · intro hback
      have hempty : CompressionWitnessEmpty explanation base :=
        (base_descends_back_iff_no_compression_witness base explanation
          hexplanation).1 hback
      rcases hclear.2 with ⟨pair, hpair⟩
      exact hempty pair hpair

/-- Exact compressed explanation is exactly the source-clear, target-clear,
compression-witness normal form. -/
theorem exact_compressed_iff_obstruction_normal_form {H B E T : Type}
    (base : H → B) (explanation : H → E) (target : H → T)
    (hbase : Function.Surjective base)
    (hexplanation : Function.Surjective explanation) :
    ExactCompressedExplanation base explanation target ↔
      SourceOverreadObstructionEmpty base explanation ∧
        TargetLossObstructionEmpty explanation target ∧
          CompressionWitnessNonempty explanation base := by
  constructor
  · intro hcompressed
    have hclear :=
      (exact_explanation_iff_empty_obstructions base explanation target hbase
        hexplanation).1 hcompressed.1
    exact ⟨hclear.1, hclear.2, hcompressed.2⟩
  · intro hnf
    exact ⟨(exact_explanation_iff_empty_obstructions base explanation target hbase
      hexplanation).2 ⟨hnf.1, hnf.2.1⟩, hnf.2.2⟩

/-- Dynamic explanation composes the transport descent and later target descent,
so the continued target descends through the earlier explanatory quotient. -/
theorem dynamic_explanation_target_descends {H E H' E' T' : Type}
    (explanation : H → E) (continuation : H → H')
    (laterExplanation : H' → E') (laterTarget : H' → T') :
    DynamicExplanation explanation continuation laterExplanation laterTarget →
      Descends explanation continuation laterTarget := by
  intro hdynamic
  rcases hdynamic.1 with ⟨transport, htransport⟩
  rcases hdynamic.2 with ⟨decode, hdecode⟩
  refine ⟨decode ∘ transport, ?_⟩
  funext h
  have htransportAt : transport (explanation h) = laterExplanation (continuation h) :=
    congrFun htransport h
  have hdecodeAt : decode (laterExplanation (continuation h)) =
      laterTarget (continuation h) :=
    congrFun hdecode (continuation h)
  calc
    (decode ∘ transport) (explanation h) =
        decode (laterExplanation (continuation h)) := by
          simpa [Function.comp] using congrArg decode htransportAt
    _ = laterTarget (continuation h) := hdecodeAt

/-- Budgeted residual explanations remain budgeted records; this theorem only
packages the residual status and does not promote it to exact explanation. -/
theorem budgeted_explanation_has_budgeted_status {H B E Residual Budget : Type}
    (base : H → B) (explanation : H → E) (residual : H → Residual)
    (budget : Budget) (WithinBudget : Residual → Budget → Prop) :
    BudgetedExplanation base explanation residual budget WithinBudget →
      ExplanationStatusHolds False False False False False False True False False False
        False False False False False False ExplanationStatus.budgetedExplanation := by
  intro _
  trivial

/--
Explanation as Compression With Descent Normal Form. Exact explanation is the
two-descent diagram `H -> B -> E -> T`, equivalently no source-overread and no
target-loss split pairs. Nontrivial compressed explanation adds a same-
explanation/different-base witness, and dynamic explanation composes by
descent.
-/
theorem explanation_as_compression_with_descent {H B E T H' E' T' : Type}
    (base : H → B) (explanation : H → E) (target : H → T)
    (continuation : H → H') (laterExplanation : H' → E')
    (laterTarget : H' → T')
    (hbase : Function.Surjective base)
    (hexplanation : Function.Surjective explanation) :
    (ExactExplanation base explanation target ↔
      SourceOverreadObstructionEmpty base explanation ∧
        TargetLossObstructionEmpty explanation target) ∧
      (ExactExplanation base explanation target ↔
        ∃ alpha : B → E, ∃ beta : E → T,
          alpha ∘ base = explanation ∧ beta ∘ explanation = target) ∧
        (StrictCompression base explanation ↔
          SourceOverreadObstructionEmpty base explanation ∧
            CompressionWitnessNonempty explanation base) ∧
          (ExactCompressedExplanation base explanation target ↔
            SourceOverreadObstructionEmpty base explanation ∧
              TargetLossObstructionEmpty explanation target ∧
                CompressionWitnessNonempty explanation base) ∧
            (DynamicExplanation explanation continuation laterExplanation laterTarget →
              Descends explanation continuation laterTarget) := by
  exact ⟨exact_explanation_iff_empty_obstructions base explanation target hbase
      hexplanation,
    exact_explanation_iff_factorization base explanation target,
    strict_compression_iff_source_and_witness base explanation hbase hexplanation,
    exact_compressed_iff_obstruction_normal_form base explanation target hbase
      hexplanation,
    dynamic_explanation_target_descends explanation continuation laterExplanation
      laterTarget⟩

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ExplanationAsCompressionWithDescent
