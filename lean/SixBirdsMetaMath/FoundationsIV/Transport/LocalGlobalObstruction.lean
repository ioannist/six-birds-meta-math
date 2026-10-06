/-!
F4 Local-Global Obstruction Normal Form.

The local data of a finite patch system are represented abstractly as a
`LocalFamily`; the declared global objects are represented as `Global`, with
restriction map `R : Global -> LocalFamily`. Overlap compatibility is a
predicate on local families. The normal form separates overlap failure,
compatible non-global data, ambiguous global fillers, and exact global fillers.
-/

namespace SixBirdsMetaMath.FoundationsIV.Transport.LocalGlobalObstruction

/-- A local family lies in the declared image of the global restriction map. -/
def InDeclaredImage {Global LocalFamily : Type} (R : Global → LocalFamily)
    (a : LocalFamily) : Prop :=
  ∃ g : Global, R g = a

/-- A local family globalizes when it has a declared global filler. -/
def Globalizes {Global LocalFamily : Type} (R : Global → LocalFamily)
    (a : LocalFamily) : Prop :=
  ∃ g : Global, R g = a

/-- The genuine local-global obstruction: compatible local data outside the
declared global image. -/
def LocalGlobalObstruction {Global LocalFamily : Type}
    (compatible : LocalFamily → Prop) (R : Global → LocalFamily)
    (a : LocalFamily) : Prop :=
  compatible a ∧ ¬ InDeclaredImage R a

/-- A unique declared global filler for a local family. -/
def UniquePreimage {Global LocalFamily : Type} (R : Global → LocalFamily)
    (a : LocalFamily) : Prop :=
  ∃ g : Global, R g = a ∧ ∀ g' : Global, R g' = a → g' = g

/-- At least two distinct declared global fillers for a local family. -/
def MultiplePreimages {Global LocalFamily : Type} (R : Global → LocalFamily)
    (a : LocalFamily) : Prop :=
  ∃ g₁ g₂ : Global, R g₁ = a ∧ R g₂ = a ∧ g₁ ≠ g₂

/-- The four typed local-global statuses from the source normal form. -/
inductive LocalGlobalStatus where
  | overlapInconsistent
  | compatibleNonGlobal
  | globalAmbiguous
  | globalExact
deriving DecidableEq

/-- Meaning of each local-global status for a fixed local family. -/
def StatusHolds {Global LocalFamily : Type} (compatible : LocalFamily → Prop)
    (R : Global → LocalFamily) (a : LocalFamily) : LocalGlobalStatus → Prop
  | LocalGlobalStatus.overlapInconsistent => ¬ compatible a
  | LocalGlobalStatus.compatibleNonGlobal => LocalGlobalObstruction compatible R a
  | LocalGlobalStatus.globalAmbiguous => MultiplePreimages R a
  | LocalGlobalStatus.globalExact => UniquePreimage R a

/-- Exactly one local-global status applies. -/
def ExactlyOneStatus {Global LocalFamily : Type} (compatible : LocalFamily → Prop)
    (R : Global → LocalFamily) (a : LocalFamily) : Prop :=
  ∃ status : LocalGlobalStatus,
    StatusHolds compatible R a status ∧
      ∀ other : LocalGlobalStatus,
        StatusHolds compatible R a other → other = status

/-- Ambiguous global filling implies image membership. -/
theorem multiple_preimages_in_image {Global LocalFamily : Type}
    {R : Global → LocalFamily} {a : LocalFamily} :
    MultiplePreimages R a → InDeclaredImage R a := by
  intro h
  rcases h with ⟨g₁, _g₂, hg₁, _hg₂, _hne⟩
  exact ⟨g₁, hg₁⟩

/-- Exact global filling implies image membership. -/
theorem unique_preimage_in_image {Global LocalFamily : Type}
    {R : Global → LocalFamily} {a : LocalFamily} :
    UniquePreimage R a → InDeclaredImage R a := by
  intro h
  rcases h with ⟨g, hg, _huniq⟩
  exact ⟨g, hg⟩

/-- A local family cannot have both multiple and unique declared fillers. -/
theorem multiple_preimages_not_unique {Global LocalFamily : Type}
    {R : Global → LocalFamily} {a : LocalFamily} :
    MultiplePreimages R a → UniquePreimage R a → False := by
  intro hmultiple hunique
  rcases hmultiple with ⟨g₁, g₂, hg₁, hg₂, hne⟩
  rcases hunique with ⟨g, _hg, huniq⟩
  have h₁ : g₁ = g := huniq g₁ hg₁
  have h₂ : g₂ = g := huniq g₂ hg₂
  exact hne (h₁.trans h₂.symm)

/--
Local-Global Obstruction Normal Form. If the declared restriction map sends
global objects to compatible local families, then every local family has
exactly one of the four source statuses. Moreover, for compatible local data,
globalization is exactly membership in the declared image of `R`.
-/
theorem local_global_obstruction_normal_form {Global LocalFamily : Type}
    (compatible : LocalFamily → Prop) (R : Global → LocalFamily)
    (hR_compatible : ∀ g : Global, compatible (R g)) (a : LocalFamily) :
    (compatible a → (Globalizes R a ↔ InDeclaredImage R a)) ∧
      ExactlyOneStatus compatible R a := by
  constructor
  · intro _ha
    constructor
    · intro h
      exact h
    · intro h
      exact h
  · classical
    by_cases hcompat : compatible a
    · by_cases himage : InDeclaredImage R a
      · rcases himage with ⟨g, hg⟩
        cases Classical.em (∃ g₂ : Global, R g₂ = a ∧ g ≠ g₂) with
        | inl hother =>
            rcases hother with ⟨g₂, hg₂, hne⟩
            refine ⟨LocalGlobalStatus.globalAmbiguous, ?_, ?_⟩
            · exact ⟨g, g₂, hg, hg₂, hne⟩
            · intro other hotherStatus
              cases other with
              | overlapInconsistent =>
                  exact False.elim (hotherStatus hcompat)
              | compatibleNonGlobal =>
                  exact False.elim (hotherStatus.2 ⟨g, hg⟩)
              | globalAmbiguous =>
                  rfl
              | globalExact =>
                  exact False.elim
                    (multiple_preimages_not_unique
                      ⟨g, g₂, hg, hg₂, hne⟩ hotherStatus)
        | inr hnoOther =>
            have hunique : UniquePreimage R a := by
              refine ⟨g, hg, ?_⟩
              intro g' hg'
              cases Classical.em (g = g') with
              | inl heq => exact heq.symm
              | inr hne =>
                  exact False.elim (hnoOther ⟨g', hg', hne⟩)
            refine ⟨LocalGlobalStatus.globalExact, hunique, ?_⟩
            intro other hotherStatus
            cases other with
            | overlapInconsistent =>
                exact False.elim (hotherStatus hcompat)
            | compatibleNonGlobal =>
                exact False.elim (hotherStatus.2 ⟨g, hg⟩)
            | globalAmbiguous =>
                exact False.elim (multiple_preimages_not_unique hotherStatus hunique)
            | globalExact =>
                rfl
      · refine ⟨LocalGlobalStatus.compatibleNonGlobal, ⟨hcompat, himage⟩, ?_⟩
        intro other hotherStatus
        cases other with
        | overlapInconsistent =>
            exact False.elim (hotherStatus hcompat)
        | compatibleNonGlobal =>
            rfl
        | globalAmbiguous =>
            exact False.elim (himage (multiple_preimages_in_image hotherStatus))
        | globalExact =>
            exact False.elim (himage (unique_preimage_in_image hotherStatus))
    · refine ⟨LocalGlobalStatus.overlapInconsistent, hcompat, ?_⟩
      intro other hotherStatus
      cases other with
      | overlapInconsistent =>
          rfl
      | compatibleNonGlobal =>
          exact False.elim (hcompat hotherStatus.1)
      | globalAmbiguous =>
          rcases hotherStatus with ⟨g₁, _g₂, hg₁, _hg₂, _hne⟩
          exact False.elim (hcompat (hg₁ ▸ hR_compatible g₁))
      | globalExact =>
          rcases hotherStatus with ⟨g, hg, _huniq⟩
          exact False.elim (hcompat (hg ▸ hR_compatible g))

/-- Paper F4: global fillers are compatible, globalization is precisely
compatible membership in the declared image, and the four local-global
statuses partition every local family. -/
theorem local_global_obstruction_paper {F G : Type}
    (Comp : F → Prop) (R : G → F) (hR : ∀ g, Comp (R g)) :
    (∀ a, Globalizes R a → Comp a) ∧
    (∀ a, Globalizes R a ↔ (Comp a ∧ InDeclaredImage R a)) ∧
    (∀ a, ExactlyOneStatus Comp R a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ⟨g, hg⟩
    exact hg ▸ hR g
  · intro a
    constructor
    · intro hglobal
      exact ⟨(show Comp a from by
        rcases hglobal with ⟨g, hg⟩
        exact hg ▸ hR g), hglobal⟩
    · intro h
      exact h.2
  · intro a
    exact (local_global_obstruction_normal_form Comp R hR a).2

/-- Every compatible family has exactly one global filler iff the restriction
map is injective and its image is exactly the compatible families. -/
theorem compatible_unique_preimages_iff {F G : Type}
    (Comp : F → Prop) (R : G → F) (hR : ∀ g, Comp (R g)) :
    (∀ a, Comp a → UniquePreimage R a) ↔
      (Function.Injective R ∧ ∀ a, (∃ g, R g = a) ↔ Comp a) := by
  constructor
  · intro hexact
    constructor
    · intro g g' heq
      obtain ⟨filler, _, hunique⟩ := hexact (R g) (hR g)
      exact (hunique g rfl).trans (hunique g' heq.symm).symm
    · intro a
      constructor
      · rintro ⟨g, hg⟩
        exact hg ▸ hR g
      · intro hcomp
        obtain ⟨g, hg, _⟩ := hexact a hcomp
        exact ⟨g, hg⟩
  · rintro ⟨hinjective, himage⟩ a hcomp
    obtain ⟨g, hg⟩ := (himage a).mpr hcomp
    exact ⟨g, hg, fun g' hg' => hinjective (hg'.trans hg.symm)⟩

/-- Full F4 with the exact-globalization criterion for every compatible family. -/
theorem local_global_obstruction_paper_full {F G : Type}
    (Comp : F → Prop) (R : G → F) (hR : ∀ g, Comp (R g)) :
    ((∀ a, Globalizes R a → Comp a) ∧
      (∀ a, Globalizes R a ↔ (Comp a ∧ InDeclaredImage R a)) ∧
      (∀ a, ExactlyOneStatus Comp R a)) ∧
    ((∀ a, Comp a → UniquePreimage R a) ↔
      (Function.Injective R ∧ ∀ a, (∃ g, R g = a) ↔ Comp a)) := by
  exact ⟨local_global_obstruction_paper Comp R hR,
    compatible_unique_preimages_iff Comp R hR⟩

end SixBirdsMetaMath.FoundationsIV.Transport.LocalGlobalObstruction
