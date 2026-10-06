/-!
F15b Spontaneous SSB / Branch-Selection Formation.

The orbit map identifies precisely the configurations related by the declared
action. A formation record chooses within orbit classes and exhibits a moved
formed configuration. A fixed-valued selector cannot select that configuration.
-/

namespace SixBirdsMetaMath.FoundationsIV.Symmetry.SpontaneousSSB

/-- A formed selector preserves orbit classes and selects a configuration
moved by the action at one formed input. -/
def FormationRecord {C G Q : Type} (q : C → Q) (Ω : C → Prop)
    (act : G → C → C) (F : C → C) (c : C) (g : G) : Prop :=
  (∀ x, q (F x) = q x) ∧ Ω c ∧ act g (F c) ≠ F c

/-- Paper F15b: a formation record exists exactly when some formed
configuration is moved; every formation record preserves orbit classes and
selects a moved configuration; a pointwise fixed selector cannot select it. -/
theorem spontaneous_ssb_characterization {C G Q : Type}
    (q : C → Q) (Ω : C → Prop) (act : G → C → C)
    (hq_orbit : ∀ c c', q c = q c' ↔ ∃ g, act g c = c') :
    ((∃ F : C → C, ∃ c : C, ∃ g : G, FormationRecord q Ω act F c g) ↔
      ∃ c : C, ∃ g : G, Ω c ∧ act g c ≠ c) ∧
    (∀ (F : C → C) (c : C) (g : G),
      FormationRecord q Ω act F c g →
        (∀ x, q (F x) = q x) ∧ act g (F c) ≠ F c) ∧
    (∀ (F : C → C) (c : C) (g : G),
      FormationRecord q Ω act F c g →
        ∀ σ : Q → C, (∀ h o, σ o = act h (σ o)) → σ (q c) ≠ F c) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨F, c, g, hsame, hΩ, hmoved⟩
      obtain ⟨k, hk⟩ := (hq_orbit c (F c)).mp (hsame c).symm
      by_cases hkc : act k c = c
      · have hFc : F c = c := hk.symm.trans hkc
        exact ⟨c, g, hΩ, by simpa [hFc] using hmoved⟩
      · exact ⟨c, k, hΩ, hkc⟩
    · rintro ⟨c, g, hΩ, hmoved⟩
      exact ⟨id, c, g, (by intro x; rfl), hΩ, hmoved⟩
  · intro F c g hrecord
    exact ⟨hrecord.1, hrecord.2.2⟩
  · intro F c g hrecord σ hfixed heq
    apply hrecord.2.2
    calc
      act g (F c) = act g (σ (q c)) := congrArg (act g) heq.symm
      _ = σ (q c) := (hfixed g (q c)).symm
      _ = F c := heq

/-- The two-element group acts on itself by xor. -/
def boolAction (g c : Bool) : Bool := Bool.xor g c

/-- Its orbit quotient has one class. -/
def boolOrbit : Bool → Unit := fun _ => ()

/-- The Bool action realizes the orbit-map equivalence, and both sides of the
existence clause in F15b hold for the everywhere-formed predicate. -/
theorem bool_spontaneous_ssb_instance :
    (∀ c : Bool, boolAction false c = c) ∧
    (∀ g h c : Bool,
      boolAction (Bool.xor g h) c = boolAction g (boolAction h c)) ∧
    (∀ c c' : Bool, boolOrbit c = boolOrbit c' ↔
      ∃ g : Bool, boolAction g c = c') ∧
    (∃ F : Bool → Bool, ∃ c : Bool, ∃ g : Bool,
      FormationRecord boolOrbit (fun _ => True) boolAction F c g) ∧
    (∃ c : Bool, ∃ g : Bool, True ∧ boolAction g c ≠ c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c
    cases c <;> decide
  · intro g h c
    cases g <;> cases h <;> cases c <;> decide
  · intro c c'
    cases c <;> cases c' <;> decide
  · exact ⟨id, false, true, (by intro x; rfl), trivial, by decide⟩
  · exact ⟨false, true, trivial, by decide⟩

/-- A branch-selection record whose selector is constant on every orbit. -/
def OrbitConstantFormationRecord {C G Q : Type} (q : C → Q) (Ω : C → Prop)
    (act : G → C → C) (F : C → C) (c : C) (g : G) : Prop :=
  FormationRecord q Ω act F c g ∧ ∀ h x, F (act h x) = F x

/-- Paper F15b with an orbit-constant selector and an explicit orbit witness
for the selected ground-state branch. -/
theorem spontaneous_ssb_orbit_constant_characterization {C G Q : Type}
    (q : C → Q) (Ω : C → Prop) (act : G → C → C)
    (hq_orbit : ∀ c c', q c = q c' ↔ ∃ g, act g c = c') :
    ((∃ F : C → C, ∃ c : C, ∃ g : G,
        OrbitConstantFormationRecord q Ω act F c g) ↔
      ∃ c : C, ∃ g : G, Ω c ∧ act g c ≠ c) ∧
    (∀ (F : C → C) (c : C) (g : G),
      OrbitConstantFormationRecord q Ω act F c g →
        (∀ x, q (F x) = q x) ∧
        (∃ h : G, act h c = F c) ∧ act g (F c) ≠ F c) ∧
    (∀ (F : C → C) (c : C) (g : G),
      OrbitConstantFormationRecord q Ω act F c g →
        ∀ σ : Q → C, (∀ h o, σ o = act h (σ o)) → σ (q c) ≠ F c) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨F, c, g, hrecord⟩
      exact (spontaneous_ssb_characterization q Ω act hq_orbit).1.1
        ⟨F, c, g, hrecord.1⟩
    · rintro ⟨c, g, hΩ, hmoved⟩
      let rep : Q → C := fun o =>
        if ho : o = q c then c
        else if hx : ∃ x : C, q x = o then Classical.choose hx else c
      let F : C → C := fun x => rep (q x)
      have hrep : ∀ x, q (rep (q x)) = q x := by
        intro x
        change q (if ho : q x = q c then c
          else if hx : ∃ y : C, q y = q x then Classical.choose hx else c) = q x
        by_cases hc : q x = q c
        · simp only [dif_pos hc]
          exact hc.symm
        · have hx : ∃ y : C, q y = q x := ⟨x, rfl⟩
          simp only [dif_neg hc, dif_pos hx]
          exact Classical.choose_spec hx
      have hFc : F c = c := by simp [F, rep]
      have hconstant : ∀ h x, F (act h x) = F x := by
        intro h x
        exact congrArg rep (((hq_orbit x (act h x)).2 ⟨h, rfl⟩).symm)
      refine ⟨F, c, g, ⟨?_, hΩ, ?_⟩, hconstant⟩
      · exact hrep
      · simpa [hFc] using hmoved
  · intro F c g hrecord
    have hsame := hrecord.1.1
    exact ⟨hsame, (hq_orbit c (F c)).1 (hsame c).symm,
      hrecord.1.2.2⟩
  · intro F c g hrecord
    exact (spontaneous_ssb_characterization q Ω act hq_orbit).2.2
      F c g hrecord.1

/-- The Bool orbit admits an orbit-constant breaker record. -/
theorem bool_orbit_constant_ssb_instance :
    ∃ F : Bool → Bool, ∃ c : Bool, ∃ g : Bool,
      OrbitConstantFormationRecord boolOrbit (fun _ => True)
        boolAction F c g := by
  exact ⟨fun _ => false, false, true,
    ⟨(by intro x; rfl), trivial, (by decide)⟩,
    (by intros; rfl)⟩

/-- Invariant formation makes both separated branches formed ground states. -/
theorem orbit_constant_formation_distinct_ground_states {C G Q : Type}
    (q : C → Q) (Ω : C → Prop) (act : G → C → C)
    (hq_orbit : ∀ c c', q c = q c' ↔ ∃ g, act g c = c')
    (hΩ : ∀ g c, Ω (act g c) ↔ Ω c)
    (F : C → C) (c : C) (g : G)
    (hrecord : OrbitConstantFormationRecord q Ω act F c g) :
    Ω (F c) ∧ Ω (act g (F c)) ∧
      q (F c) = q c ∧ q (act g (F c)) = q c ∧
        F c ≠ act g (F c) := by
  have hFc : q (F c) = q c := hrecord.1.1 c
  obtain ⟨k, hk⟩ := (hq_orbit c (F c)).mp hFc.symm
  have hformed : Ω (F c) := hk ▸ (hΩ k c).mpr hrecord.1.2.1
  have hmove : q (act g (F c)) = q (F c) :=
    ((hq_orbit (F c) (act g (F c))).mpr ⟨g, rfl⟩).symm
  exact ⟨hformed, (hΩ g (F c)).mpr hformed, hFc,
    hmove.trans hFc, Ne.symm hrecord.1.2.2⟩

/-- F15b, with the two distinct formed branches under invariant formation. -/
theorem spontaneous_ssb_orbit_constant_paper {C G Q : Type}
    (q : C → Q) (Ω : C → Prop) (act : G → C → C)
    (hq_orbit : ∀ c c', q c = q c' ↔ ∃ g, act g c = c') :
    (((∃ F : C → C, ∃ c : C, ∃ g : G,
        OrbitConstantFormationRecord q Ω act F c g) ↔
      ∃ c : C, ∃ g : G, Ω c ∧ act g c ≠ c) ∧
    (∀ (F : C → C) (c : C) (g : G),
      OrbitConstantFormationRecord q Ω act F c g →
        (∀ x, q (F x) = q x) ∧
        (∃ h : G, act h c = F c) ∧ act g (F c) ≠ F c) ∧
    (∀ (F : C → C) (c : C) (g : G),
      OrbitConstantFormationRecord q Ω act F c g →
        ∀ σ : Q → C, (∀ h o, σ o = act h (σ o)) → σ (q c) ≠ F c)) ∧
    (∀ _hΩ : ∀ g c, Ω (act g c) ↔ Ω c,
      ∀ (F : C → C) (c : C) (g : G),
        OrbitConstantFormationRecord q Ω act F c g →
          Ω (F c) ∧ Ω (act g (F c)) ∧
            q (F c) = q c ∧ q (act g (F c)) = q c ∧
              F c ≠ act g (F c)) := by
  exact ⟨spontaneous_ssb_orbit_constant_characterization q Ω act hq_orbit,
    fun hΩ F c g hrecord =>
      orbit_constant_formation_distinct_ground_states q Ω act hq_orbit hΩ
        F c g hrecord⟩

end SixBirdsMetaMath.FoundationsIV.Symmetry.SpontaneousSSB
