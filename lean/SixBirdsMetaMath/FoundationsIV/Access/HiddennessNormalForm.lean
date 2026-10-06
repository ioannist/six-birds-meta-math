import SixBirdsMetaMath.FoundationsIV.Access.NoFreeDistinction

/-!
F13a Hiddenness theorem-grade quotient/currentizer normal form.

This file records the theorem-grade layer only. The CSL formed-closure law is
F13b. The saturated-SAT source is represented by the explicit hypothesis
`HiddennessSourceObligation`: current surjectivity and normal-form clauses
1--4. The fifth clause and the exposure/collapse/surplus equivalences are
derived from that hypothesis, without a project axiom.
-/

namespace SixBirdsMetaMath.FoundationsIV.Access.HiddennessNormalForm

open SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure

/-- Layer-agnostic quotient/currentizer data for the theorem-grade hiddenness
normal form. -/
structure HiddennessInterface where
  Hist : Type
  Current : Type
  Predictive : Type
  Upstream : Type
  current : Hist → Current
  predictive : Hist → Predictive
  upstream : Hist → Upstream
  forgetPredictive : Predictive → Current
  predictive_refines_current : forgetPredictive ∘ predictive = current
  determiningStateTyped : Prop
  minimalRelevantUpstream : Prop
  lawfulCurrentExposure : Prop

/-- The upstream determining signature descends to current access. -/
def QuotientExposed (I : HiddennessInterface) : Prop :=
  FactorsThroughQ I.current I.upstream

/-- The determining state is hidden from current observation. -/
def HiddenFromCurrent (I : HiddennessInterface) : Prop :=
  ¬ I.lawfulCurrentExposure

/-- The predictive quotient collapses to the current quotient: since `current`
already factors through `predictive`, this is the missing reverse descent. -/
def PredictiveCollapse (I : HiddennessInterface) : Prop :=
  FactorsThroughQ I.current I.predictive

/-- A surviving predictive surplus is a same-current / different-predictive
split pair. -/
def PredictiveSurplus (I : HiddennessInterface) : Prop :=
  ∃ x y : I.Hist, I.current x = I.current y ∧ I.predictive x ≠ I.predictive y

/-- The theorem-grade hiddenness normal-form content, separated from the later
CSL formed-closure law. -/
def HiddennessNormalForm (I : HiddennessInterface) : Prop :=
  I.determiningStateTyped ∧ I.minimalRelevantUpstream ∧
    (I.lawfulCurrentExposure ↔ QuotientExposed I) ∧
      (PredictiveCollapse I ↔ I.lawfulCurrentExposure) ∧
        (PredictiveSurplus I ↔ HiddenFromCurrent I)

/-- The source-specific input now records surjectivity and the first four
normal-form clauses. The final clause follows from quotient descent. -/
def HiddennessSourceObligation (I : HiddennessInterface) : Prop :=
  Function.Surjective I.current ∧ I.determiningStateTyped ∧
    I.minimalRelevantUpstream ∧
      (I.lawfulCurrentExposure ↔ QuotientExposed I) ∧
        (PredictiveCollapse I ↔ I.lawfulCurrentExposure)

/-- The fifth normal-form clause is a consequence of the fourth once the
current quotient is surjective. -/
theorem predictive_surplus_iff_hidden_of_collapse
    (I : HiddennessInterface) (hsurj : Function.Surjective I.current)
    (hcollapse : PredictiveCollapse I ↔ I.lawfulCurrentExposure) :
    PredictiveSurplus I ↔ HiddenFromCurrent I := by
  have hsplit : PredictiveSurplus I ↔ ¬ PredictiveCollapse I := by
    constructor
    · rintro ⟨x,y,hxy,hne⟩ ⟨bar,hcomm⟩
      have hx := congrFun hcomm x
      have hy := congrFun hcomm y
      exact hne (hx.symm.trans ((congrArg bar hxy).trans hy))
    · intro hnot
      classical
      exact Classical.byContradiction (fun hnosplit =>
        have hclosed : SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure.PackageClosed
            I.current I.predictive := by
          intro x y hxy
          exact Classical.byContradiction (fun hne =>
            hnosplit ⟨x,y,hxy,hne⟩)
        hnot ((SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure.sufficiency_closure
          I.current I.predictive hsurj).1.1 hclosed))
  constructor
  · intro h hvisible
    exact (hsplit.1 h) (hcollapse.2 hvisible)
  · intro hhidden
    exact hsplit.2 (fun hcollapsed => hhidden (hcollapse.1 hcollapsed))

/-- The split-pair surplus is exactly failure of predictive descent through
surjective current access; no exposure assumption is needed. -/
theorem predictive_surplus_iff_not_collapse
    (I : HiddennessInterface) (hsurj : Function.Surjective I.current) :
    PredictiveSurplus I ↔ ¬ PredictiveCollapse I := by
  constructor
  · rintro ⟨x,y,hxy,hne⟩ ⟨bar,hcomm⟩
    have hx := congrFun hcomm x
    have hy := congrFun hcomm y
    exact hne (hx.symm.trans ((congrArg bar hxy).trans hy))
  · intro hnot
    classical
    exact Classical.byContradiction (fun hnosplit =>
      have hclosed : SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure.PackageClosed
          I.current I.predictive := by
        intro x y hxy
        exact Classical.byContradiction (fun hne =>
          hnosplit ⟨x,y,hxy,hne⟩)
      hnot ((SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure.sufficiency_closure
        I.current I.predictive hsurj).1.1 hclosed))

/-- F13a normal form conditional on the explicit source obligation. -/
theorem hiddenness_normal_form (I : HiddennessInterface)
    (hsrc : HiddennessSourceObligation I) :
    HiddennessNormalForm I := by
  rcases hsrc with ⟨hsurj, htyped, hminimal,
    hexposed, hcollapse⟩
  exact ⟨htyped, hminimal, hexposed, hcollapse,
    predictive_surplus_iff_hidden_of_collapse I hsurj hcollapse⟩

/-- The conditional F13a normal form identifies quotient exposure with
predictive collapse, and collapse with absence of a predictive split pair. -/
theorem hiddenness_exposure_collapse_surplus
    (I : HiddennessInterface) (hsrc : HiddennessSourceObligation I) :
    (QuotientExposed I ↔ PredictiveCollapse I) ∧
    (PredictiveCollapse I ↔ ¬ PredictiveSurplus I) := by
  have hcore := hsrc
  have hnormal := hiddenness_normal_form I hsrc
  have hsplit := predictive_surplus_iff_not_collapse I hcore.1
  constructor
  · exact hnormal.2.2.1.symm.trans hnormal.2.2.2.1.symm
  · constructor
    · intro hc hs
      exact (hsplit.mp hs) hc
    · intro hno
      classical
      exact Classical.byContradiction (fun hnot =>
        hno (hsplit.mpr hnot))

/-- F13a's conditional paper-facing theorem with the derived exposure,
collapse, and no-surplus equivalences stated alongside the normal form. -/
theorem hiddenness_normal_form_with_exposure_collapse_surplus
    (I : HiddennessInterface) (hsrc : HiddennessSourceObligation I) :
    HiddennessNormalForm I ∧
    (QuotientExposed I ↔ PredictiveCollapse I) ∧
    (PredictiveCollapse I ↔ ¬ PredictiveSurplus I) := by
  exact ⟨hiddenness_normal_form I hsrc,
    hiddenness_exposure_collapse_surplus I hsrc⟩

/-- For surjective current access, the collapse/exposure equivalence and the
surplus/hiddenness equivalence are equivalent, without a source certificate. -/
theorem hidden_iff_collapse_iff_of_surjective
    (I : HiddennessInterface) (hsurj : Function.Surjective I.current) :
    (PredictiveCollapse I ↔ I.lawfulCurrentExposure) ↔
      (PredictiveSurplus I ↔ HiddenFromCurrent I) := by
  constructor
  · exact predictive_surplus_iff_hidden_of_collapse I hsurj
  · intro hhidden
    classical
    have hsplit := predictive_surplus_iff_not_collapse I hsurj
    constructor
    · intro hc
      exact Classical.byContradiction (fun hnotExposure =>
        (hsplit.mp (hhidden.mpr hnotExposure)) hc)
    · intro hexposure
      exact Classical.byContradiction (fun hnotCollapse =>
        (hhidden.mp (hsplit.mpr hnotCollapse)) hexposure)

/-- Clauses four and five are equivalent whenever predictive surplus is
equivalent to non-collapse; current surjectivity is not required. -/
theorem hidden_iff_collapse_iff_of_surplus_iff_not_collapse
    (I : HiddennessInterface)
    (h : PredictiveSurplus I ↔ ¬ PredictiveCollapse I) :
    (PredictiveCollapse I ↔ I.lawfulCurrentExposure) ↔
      (PredictiveSurplus I ↔ HiddenFromCurrent I) := by
  constructor
  · intro hcollapse
    constructor
    · intro hsurplus hexposure
      exact (h.mp hsurplus) (hcollapse.mpr hexposure)
    · intro hhidden
      exact h.mpr (fun hcollapsed => hhidden (hcollapse.mp hcollapsed))
  · intro hhidden
    constructor
    · intro hcollapsed
      exact Classical.byContradiction (fun hnotExposure =>
        (h.mp (hhidden.mpr hnotExposure)) hcollapsed)
    · intro hexposure
      exact Classical.byContradiction (fun hnotCollapse =>
        (hhidden.mp (h.mpr hnotCollapse)) hexposure)

/-- F13a for an arbitrary source predicate and its explicitly supplied source
obligation: current surjectivity and clauses 1--4 imply the full normal form
and its exposure/collapse/no-surplus consequences. -/
theorem hiddenness_normal_form_of_source_obligation
    (Src : HiddennessInterface → Prop)
    (hS : ∀ J, Src J → HiddennessSourceObligation J)
    (I : HiddennessInterface) (src : Src I) :
    Function.Surjective I.current ∧ HiddennessNormalForm I ∧
      (QuotientExposed I ↔ PredictiveCollapse I) ∧
      (PredictiveCollapse I ↔ ¬ PredictiveSurplus I) := by
  rcases hS I src with ⟨hsurj, htyped, hminimal, hexposed, hcollapse⟩
  have hsplit := predictive_surplus_iff_not_collapse I hsurj
  refine ⟨hsurj, ⟨htyped, hminimal, hexposed, hcollapse,
    predictive_surplus_iff_hidden_of_collapse I hsurj hcollapse⟩,
    hexposed.symm.trans hcollapse.symm, ?_⟩
  constructor
  · intro hc hs
    exact (hsplit.mp hs) hc
  · intro hno
    classical
    exact Classical.byContradiction (fun hnot => hno (hsplit.mpr hnot))

/-- The surplus/no-collapse equivalence holds exactly when current access is
surjective or the predictive codomain is nonempty, supplying a default value
for current classes outside the current image. -/
theorem predictive_surplus_iff_not_collapse_iff (I : HiddennessInterface) :
    (PredictiveSurplus I ↔ ¬ PredictiveCollapse I) ↔
      (Function.Surjective I.current ∨ Nonempty I.Predictive) := by
  classical
  constructor
  · intro hsplit
    by_cases hpred : Nonempty I.Predictive
    · exact Or.inr hpred
    · left
      have hcollapse : PredictiveCollapse I :=
        Classical.byContradiction (fun hnot =>
          let ⟨x, _, _, _⟩ := hsplit.mpr hnot
          hpred ⟨I.predictive x⟩)
      obtain ⟨bar, _⟩ := hcollapse
      intro a
      exact False.elim (hpred ⟨bar a⟩)
  · rintro (hsurj | hpred)
    · exact predictive_surplus_iff_not_collapse I hsurj
    · constructor
      · rintro ⟨x, y, hxy, hne⟩ ⟨bar, hcomm⟩
        exact hne ((congrFun hcomm x).symm.trans
          ((congrArg bar hxy).trans (congrFun hcomm y)))
      · intro hnot
        apply Classical.byContradiction
        intro hnosplit
        let bar : I.Current → I.Predictive := fun a =>
          if h : ∃ x, I.current x = a then I.predictive (Classical.choose h)
          else Classical.choice hpred
        apply hnot
        refine ⟨bar, ?_⟩
        funext x
        have himage : ∃ y, I.current y = I.current x := ⟨x, rfl⟩
        change (if h : ∃ y, I.current y = I.current x then
          I.predictive (Classical.choose h) else Classical.choice hpred) = I.predictive x
        rw [dif_pos himage]
        exact Classical.byContradiction (fun hne =>
          hnosplit ⟨Classical.choose himage, x, Classical.choose_spec himage, hne⟩)


/-- An exposed one-point interface with identity quotient maps. -/
def exposedUnitInterface : HiddennessInterface where
  Hist := Unit
  Current := Unit
  Predictive := Unit
  Upstream := Unit
  current := id
  predictive := id
  upstream := id
  forgetPredictive := id
  predictive_refines_current := rfl
  determiningStateTyped := True
  minimalRelevantUpstream := True
  lawfulCurrentExposure := True

/-- The explicit source hypothesis is inhabited by an exposed Unit model. -/
theorem hiddenness_source_obligation_satisfiable :
    ∃ I : HiddennessInterface, HiddennessSourceObligation I := by
  refine ⟨exposedUnitInterface, ?_⟩
  refine ⟨fun x => ⟨x, rfl⟩, True.intro, True.intro, ?_, ?_⟩
  · exact ⟨fun _ => ⟨id, rfl⟩, fun _ => True.intro⟩
  · exact ⟨fun _ => True.intro, fun _ => ⟨id, rfl⟩⟩

/-- Two histories have the same current class but distinct predictive and
upstream states. Current exposure is false. -/
def hiddenBoolInterface : HiddennessInterface where
  Hist := Bool
  Current := Unit
  Predictive := Bool
  Upstream := Bool
  current := fun _ => ()
  predictive := id
  upstream := id
  forgetPredictive := fun _ => ()
  predictive_refines_current := rfl
  determiningStateTyped := True
  minimalRelevantUpstream := True
  lawfulCurrentExposure := False

/-- The explicit source obligation also has an instance with predictive
surplus: the histories `false` and `true` share their current class. -/
theorem hiddenness_source_obligation_with_surplus_satisfiable :
    ∃ I : HiddennessInterface,
      HiddennessSourceObligation I ∧ PredictiveSurplus I := by
  have hsplit : PredictiveSurplus hiddenBoolInterface :=
    ⟨false, true, rfl, Bool.false_ne_true⟩
  have hnot : ¬ PredictiveCollapse hiddenBoolInterface := by
    rintro ⟨bar, hcomm⟩
    have hf := congrFun hcomm false
    have ht := congrFun hcomm true
    exact Bool.false_ne_true (hf.symm.trans ht)
  refine ⟨hiddenBoolInterface, ?_, hsplit⟩
  refine ⟨?_, True.intro, True.intro, ?_, ?_⟩
  · intro x
    cases x
    exact ⟨false, rfl⟩
  · exact ⟨False.elim, hnot⟩
  · exact ⟨hnot, False.elim⟩

end SixBirdsMetaMath.FoundationsIV.Access.HiddennessNormalForm
