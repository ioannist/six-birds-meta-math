namespace SixBirdsMetaMath.MetaMath.CalibrationFamily.FunctorialGates

/-!
T17 Named Functorial Gates.

Named functorial gates are the third typed-deposit species: specified
typed transports with a source, target, direction, and theorem obligation.
-/

/-- A typed functorial gate with a stated theorem obligation. -/
structure FunctorialGate where
  name : String
  source : String
  target : String
  direction : String
  theoremObligation : String
  deriving Repr

/-- The three named functorial gates from the PvNP np193-np221 sprint. -/
def namedFunctorialGates : List FunctorialGate :=
  [
    { name := "Xi_function_degree_to_NS_certificate_degree",
      source := "vobs (low-degree detector)",
      target := "I_alg (Nullstellensatz certificate-degree)",
      direction := "vobs -> I_alg",
      theoremObligation :=
        "detector-shadow degree iff ideal-membership certificate degree" },
    { name := "Xi_planted_statistical_to_NP_hard_language_lift",
      source := "average-case statistical detection",
      target := "worst-case NP-hard language hardness",
      direction := "average -> worst",
      theoremObligation :=
        "lift average-case detection to NP-hard language hardness" },
    { name := "Xi_uniform_time_hierarchy_realization_functor",
      source := "nonuniform-family",
      target := "uniform-time-hierarchy host layer",
      direction := "nonuniform -> uniform",
      theoremObligation :=
        "match Williams-style uniform time-hierarchy arguments" }
  ]

/-- The named functorial-gates species is seeded by three nonempty specifications. -/
theorem named_functorial_gates :
    namedFunctorialGates.length = 3 ∧
      ∀ g ∈ namedFunctorialGates, g.name ≠ "" ∧ g.theoremObligation ≠ "" := by
  constructor
  · decide
  · intro g hg
    simp [namedFunctorialGates] at hg
    rcases hg with hg | hg | hg
    · subst g
      decide
    · subst g
      decide
    · subst g
      decide

end SixBirdsMetaMath.MetaMath.CalibrationFamily.FunctorialGates
