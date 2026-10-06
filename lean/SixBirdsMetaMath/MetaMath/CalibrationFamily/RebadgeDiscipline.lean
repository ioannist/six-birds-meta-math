namespace SixBirdsMetaMath.MetaMath.CalibrationFamily.RebadgeDiscipline

/-!
T12 Rebadge Discipline.

This module isolates the four discriminating axes used to decide whether a
candidate calibration is genuinely new or merely a relabeled clone of an
existing family member.
-/

/-- The four-axis profile used by the rebadge discipline. -/
structure CalibrationProfile where
  algebraicIdentities : String
  detectorClass : String
  descentInvariants : String
  carrierOrientation : String
  deriving Repr

/-- A candidate is a rebadge of an existing profile when all four axes match. -/
def isRebadgeOf (candidate existing : CalibrationProfile) : Prop :=
  candidate.algebraicIdentities = existing.algebraicIdentities ∧
    candidate.detectorClass = existing.detectorClass ∧
      candidate.descentInvariants = existing.descentInvariants ∧
        candidate.carrierOrientation = existing.carrierOrientation

/-- A candidate is genuinely new when it is not a rebadge of any family member. -/
def genuinelyNew (candidate : CalibrationProfile) (family : List CalibrationProfile) : Prop :=
  ∀ existing ∈ family, ¬ isRebadgeOf candidate existing

/--
Rebadge discipline: "not matching all four axes anywhere" is equivalent to
"for every existing member, at least one discriminating axis differs."
-/
theorem rebadge_discipline
    (candidate : CalibrationProfile) (family : List CalibrationProfile) :
    genuinelyNew candidate family ↔
      ∀ existing ∈ family,
        candidate.algebraicIdentities ≠ existing.algebraicIdentities ∨
          candidate.detectorClass ≠ existing.detectorClass ∨
            candidate.descentInvariants ≠ existing.descentInvariants ∨
              candidate.carrierOrientation ≠ existing.carrierOrientation := by
  constructor
  · intro hnew existing hmem
    have hnotRebadge := hnew existing hmem
    by_cases halg : candidate.algebraicIdentities = existing.algebraicIdentities
    · by_cases hdet : candidate.detectorClass = existing.detectorClass
      · by_cases hdesc : candidate.descentInvariants = existing.descentInvariants
        · by_cases horient : candidate.carrierOrientation = existing.carrierOrientation
          · exact False.elim (hnotRebadge ⟨halg, hdet, hdesc, horient⟩)
          · exact Or.inr (Or.inr (Or.inr horient))
        · exact Or.inr (Or.inr (Or.inl hdesc))
      · exact Or.inr (Or.inl hdet)
    · exact Or.inl halg
  · intro hdiff existing hmem hrebadge
    rcases hdiff existing hmem with halg | hdet | hdesc | horient
    · exact halg hrebadge.1
    · exact hdet hrebadge.2.1
    · exact hdesc hrebadge.2.2.1
    · exact horient hrebadge.2.2.2

end SixBirdsMetaMath.MetaMath.CalibrationFamily.RebadgeDiscipline
