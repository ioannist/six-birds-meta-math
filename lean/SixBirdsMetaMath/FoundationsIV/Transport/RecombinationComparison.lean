import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F5 Recombination Comparison / Branch-Merge Transport.

Branchwise bookkeeping and recombination behavior are modeled as two quotient
maps out of the same fixed-support branch assemblage surface:
`K : Branch -> QK` and `R : Branch -> QR`. Recombination is
branchwise-determined exactly when `R` factors through `K`; the obstruction is
a same-support split pair equal in `K` and separated in `R`.
-/

namespace SixBirdsMetaMath.FoundationsIV.Transport.RecombinationComparison

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- Recombination factors through the branchwise quotient. -/
def BranchwiseDetermined {Branch QK QR : Type} (K : Branch → QK)
    (R : Branch → QR) : Prop :=
  Descends K (fun b : Branch => b) R

/-- The recombination quotient retains enough information to recover the
branchwise quotient. -/
def BranchwiseDetectable {Branch QK QR : Type} (K : Branch → QK)
    (R : Branch → QR) : Prop :=
  Descends R (fun b : Branch => b) K

/-- Same branchwise summary, different recombination behavior. -/
def BranchMergeSplitPair {Branch QK QR : Type} (K : Branch → QK)
    (R : Branch → QR) : (Branch × Branch) → Prop :=
  splitPairObstruction K (fun b : Branch => b) R

/-- Same recombination behavior, different branchwise summary. -/
def RecombinationToBranchSplitPair {Branch QK QR : Type} (K : Branch → QK)
    (R : Branch → QR) : (Branch × Branch) → Prop :=
  splitPairObstruction R (fun b : Branch => b) K

/-- A predicate-level obstruction exists. -/
def HasObstruction {A : Type} (obstruction : A → Prop) : Prop :=
  ¬ ObstructionEmpty obstruction

/-- The four two-sided quotient-comparison statuses. -/
inductive RecombinationStatus where
  | collapse
  | recombinationSensitiveRefinement
  | recombinationWashout
  | incomparable
deriving DecidableEq

/-- Meaning of each recombination-comparison status. -/
def RecombinationStatusHolds {Branch QK QR : Type} (K : Branch → QK)
    (R : Branch → QR) : RecombinationStatus → Prop
  | RecombinationStatus.collapse =>
      ObstructionEmpty (BranchMergeSplitPair K R) ∧
        ObstructionEmpty (RecombinationToBranchSplitPair K R)
  | RecombinationStatus.recombinationSensitiveRefinement =>
      HasObstruction (BranchMergeSplitPair K R) ∧
        ObstructionEmpty (RecombinationToBranchSplitPair K R)
  | RecombinationStatus.recombinationWashout =>
      ObstructionEmpty (BranchMergeSplitPair K R) ∧
        HasObstruction (RecombinationToBranchSplitPair K R)
  | RecombinationStatus.incomparable =>
      HasObstruction (BranchMergeSplitPair K R) ∧
        HasObstruction (RecombinationToBranchSplitPair K R)

/-- Exactly one recombination-comparison status applies. -/
def ExactlyOneRecombinationStatus {Branch QK QR : Type} (K : Branch → QK)
    (R : Branch → QR) : Prop :=
  ∃ status : RecombinationStatus,
    RecombinationStatusHolds K R status ∧
      ∀ other : RecombinationStatus,
        RecombinationStatusHolds K R other → other = status

/-- The two-sided obstruction bits classify the quotient comparison. -/
theorem recombination_status_partition {Branch QK QR : Type} (K : Branch → QK)
    (R : Branch → QR) :
    ExactlyOneRecombinationStatus K R := by
  classical
  by_cases hKR : ObstructionEmpty (BranchMergeSplitPair K R)
  · by_cases hRK : ObstructionEmpty (RecombinationToBranchSplitPair K R)
    · refine ⟨RecombinationStatus.collapse, ⟨hKR, hRK⟩, ?_⟩
      intro other hother
      cases other with
      | collapse => rfl
      | recombinationSensitiveRefinement =>
          exact False.elim (hother.1 hKR)
      | recombinationWashout =>
          exact False.elim (hother.2 hRK)
      | incomparable =>
          exact False.elim (hother.1 hKR)
    · refine ⟨RecombinationStatus.recombinationWashout, ⟨hKR, hRK⟩, ?_⟩
      intro other hother
      cases other with
      | collapse =>
          exact False.elim (hRK hother.2)
      | recombinationSensitiveRefinement =>
          exact False.elim (hother.1 hKR)
      | recombinationWashout => rfl
      | incomparable =>
          exact False.elim (hother.1 hKR)
  · by_cases hRK : ObstructionEmpty (RecombinationToBranchSplitPair K R)
    · refine ⟨RecombinationStatus.recombinationSensitiveRefinement, ⟨hKR, hRK⟩, ?_⟩
      intro other hother
      cases other with
      | collapse =>
          exact False.elim (hKR hother.1)
      | recombinationSensitiveRefinement => rfl
      | recombinationWashout =>
          exact False.elim (hother.2 hRK)
      | incomparable =>
          exact False.elim (hother.2 hRK)
    · refine ⟨RecombinationStatus.incomparable, ⟨hKR, hRK⟩, ?_⟩
      intro other hother
      cases other with
      | collapse =>
          exact False.elim (hKR hother.1)
      | recombinationSensitiveRefinement =>
          exact False.elim (hRK hother.2)
      | recombinationWashout =>
          exact False.elim (hKR hother.1)
      | incomparable => rfl

/--
Recombination Comparison Normal Form. For quotient maps `K` and `R` on the
same fixed-support branch assemblage surface, recombination is
branchwise-determined iff there is no K-to-R branch-merge split pair. The
reverse detectability direction is the separate R-to-K criterion, and the two
obstruction bits give exactly one of the four comparison statuses.

The surjectivity hypotheses record that `K` and `R` are quotient maps onto
their declared quotient carriers.
-/
theorem recombination_comparison {Branch QK QR : Type} (K : Branch → QK)
    (R : Branch → QR) (hK : Function.Surjective K)
    (hR : Function.Surjective R) :
    (BranchwiseDetermined K R ↔ ObstructionEmpty (BranchMergeSplitPair K R)) ∧
      (BranchwiseDetectable K R ↔
        ObstructionEmpty (RecombinationToBranchSplitPair K R)) ∧
        ExactlyOneRecombinationStatus K R := by
  constructor
  · exact descent_repair_normal_form K (fun b : Branch => b) R hK
  · constructor
    · exact descent_repair_normal_form R (fun b : Branch => b) K hR
    · exact recombination_status_partition K R

end SixBirdsMetaMath.FoundationsIV.Transport.RecombinationComparison
