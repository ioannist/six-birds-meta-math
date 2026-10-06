/-!
F8 Strict Extension.

Genuine layer growth is not mere difference. A candidate new quotient is a
strict extension of an old quotient exactly when it retains the old quotient
and splits at least one old fiber.
-/

namespace SixBirdsMetaMath.FoundationsIV.Stability.StrictExtension

/-- The new quotient is definable from the old quotient. -/
def DefinableFromOld {X QOld QNew : Type} (πOld : X → QOld)
    (πNew : X → QNew) : Prop :=
  ∃ lift : QOld → QNew, lift ∘ πOld = πNew

/-- The old quotient is retained by the new quotient. -/
def RetainsOld {X QOld QNew : Type} (πOld : X → QOld)
    (πNew : X → QNew) : Prop :=
  ∃ collapse : QNew → QOld, collapse ∘ πNew = πOld

/-- The new quotient splits an old quotient fiber. -/
def SplitFiberExists {X QOld QNew : Type} (πOld : X → QOld)
    (πNew : X → QNew) : Prop :=
  ∃ x y : X, πOld x = πOld y ∧ πNew x ≠ πNew y

/-- Same old object, different new object. -/
def ExtensionSplitPair {X QOld QNew : Type} (πOld : X → QOld)
    (πNew : X → QNew) : (X × X) → Prop :=
  fun pair => πOld pair.1 = πOld pair.2 ∧ πNew pair.1 ≠ πNew pair.2

/-- Same new object, different old object: a lost old distinction. -/
def LossSplitPair {X QOld QNew : Type} (πOld : X → QOld)
    (πNew : X → QNew) : (X × X) → Prop :=
  fun pair => πNew pair.1 = πNew pair.2 ∧ πOld pair.1 ≠ πOld pair.2

/-- Retentive non-definability: old structure retained, new quotient not
definable from the old one. -/
def StrictExtension {X QOld QNew : Type} (πOld : X → QOld)
    (πNew : X → QNew) : Prop :=
  RetainsOld πOld πNew ∧ ¬ DefinableFromOld πOld πNew

/-- The canonical retentive repair of an arbitrary proposed new quotient. -/
def commonRefinement {X QOld QNew : Type} (πOld : X → QOld)
    (πNew : X → QNew) : X → QOld × QNew :=
  fun x => (πOld x, πNew x)

/-- Four statuses for comparing an old and candidate new quotient. -/
inductive StrictExtensionStatus where
  | equivalent
  | strict
  | coarsening
  | incomparable
deriving DecidableEq

/-- Meaning of each strict-extension comparison status. -/
def StrictExtensionStatusHolds {X QOld QNew : Type} (πOld : X → QOld)
    (πNew : X → QNew) : StrictExtensionStatus → Prop
  | StrictExtensionStatus.equivalent =>
      DefinableFromOld πOld πNew ∧ RetainsOld πOld πNew
  | StrictExtensionStatus.strict =>
      ¬ DefinableFromOld πOld πNew ∧ RetainsOld πOld πNew
  | StrictExtensionStatus.coarsening =>
      DefinableFromOld πOld πNew ∧ ¬ RetainsOld πOld πNew
  | StrictExtensionStatus.incomparable =>
      ¬ DefinableFromOld πOld πNew ∧ ¬ RetainsOld πOld πNew

/-- Exactly one strict-extension status applies. -/
def ExactlyOneStrictExtensionStatus {X QOld QNew : Type} (πOld : X → QOld)
    (πNew : X → QNew) : Prop :=
  ∃ status : StrictExtensionStatus,
    StrictExtensionStatusHolds πOld πNew status ∧
      ∀ other : StrictExtensionStatus,
        StrictExtensionStatusHolds πOld πNew other → other = status

/-- No old-fiber split lets the new quotient factor through the old quotient. -/
theorem definable_from_old_of_no_split {X QOld QNew : Type}
    (πOld : X → QOld) (πNew : X → QNew)
    (hπOld : Function.Surjective πOld) :
    ¬ SplitFiberExists πOld πNew → DefinableFromOld πOld πNew := by
  intro hnoSplit
  classical
  let lift : QOld → QNew := fun q => πNew (Classical.choose (hπOld q))
  refine ⟨lift, ?_⟩
  funext x
  unfold lift
  let x0 : X := Classical.choose (hπOld (πOld x))
  have hx0 : πOld x0 = πOld x := Classical.choose_spec (hπOld (πOld x))
  change πNew x0 = πNew x
  exact Classical.byContradiction (fun hneq =>
    False.elim (hnoSplit ⟨x0, x, hx0, hneq⟩))

/-- A non-definable new quotient must split some old fiber. -/
theorem split_of_not_definable {X QOld QNew : Type}
    (πOld : X → QOld) (πNew : X → QNew)
    (hπOld : Function.Surjective πOld) :
    ¬ DefinableFromOld πOld πNew → SplitFiberExists πOld πNew := by
  intro hnotDef
  exact Classical.byContradiction (fun hnoSplit =>
    hnotDef (definable_from_old_of_no_split πOld πNew hπOld hnoSplit))

/-- The common refinement always retains the old quotient. -/
theorem common_refinement_retains_old {X QOld QNew : Type} (πOld : X → QOld)
    (πNew : X → QNew) :
    RetainsOld πOld (commonRefinement πOld πNew) := by
  refine ⟨Prod.fst, ?_⟩
  funext x
  rfl

/-- If the proposed new quotient splits an old fiber, the common refinement is
a strict retentive repair over the old quotient. -/
theorem common_refinement_strict_of_split {X QOld QNew : Type}
    (πOld : X → QOld) (πNew : X → QNew) :
    SplitFiberExists πOld πNew →
      StrictExtension πOld (commonRefinement πOld πNew) := by
  intro hsplit
  constructor
  · exact common_refinement_retains_old πOld πNew
  · intro hdef
    rcases hdef with ⟨lift, hcomm⟩
    rcases hsplit with ⟨x, y, hOld, hNewNe⟩
    have hx : lift (πOld x) = (πOld x, πNew x) := congrFun hcomm x
    have hy : lift (πOld y) = (πOld y, πNew y) := congrFun hcomm y
    have hpair : (πOld x, πNew x) = (πOld y, πNew y) := by
      calc
        (πOld x, πNew x) = lift (πOld x) := hx.symm
        _ = lift (πOld y) := by rw [hOld]
        _ = (πOld y, πNew y) := hy
    exact hNewNe (congrArg Prod.snd hpair)

/-- The two factorization bits classify the old/new quotient relation. -/
theorem strict_extension_status_partition {X QOld QNew : Type}
    (πOld : X → QOld) (πNew : X → QNew) :
    ExactlyOneStrictExtensionStatus πOld πNew := by
  classical
  by_cases hdef : DefinableFromOld πOld πNew
  · by_cases hret : RetainsOld πOld πNew
    · refine ⟨StrictExtensionStatus.equivalent, ⟨hdef, hret⟩, ?_⟩
      intro other hother
      cases other with
      | equivalent => rfl
      | strict =>
          exact False.elim (hother.1 hdef)
      | coarsening =>
          exact False.elim (hother.2 hret)
      | incomparable =>
          exact False.elim (hother.1 hdef)
    · refine ⟨StrictExtensionStatus.coarsening, ⟨hdef, hret⟩, ?_⟩
      intro other hother
      cases other with
      | equivalent =>
          exact False.elim (hret hother.2)
      | strict =>
          exact False.elim (hother.1 hdef)
      | coarsening => rfl
      | incomparable =>
          exact False.elim (hother.1 hdef)
  · by_cases hret : RetainsOld πOld πNew
    · refine ⟨StrictExtensionStatus.strict, ⟨hdef, hret⟩, ?_⟩
      intro other hother
      cases other with
      | equivalent =>
          exact False.elim (hdef hother.1)
      | strict => rfl
      | coarsening =>
          exact False.elim (hdef hother.1)
      | incomparable =>
          exact False.elim (hother.2 hret)
    · refine ⟨StrictExtensionStatus.incomparable, ⟨hdef, hret⟩, ?_⟩
      intro other hother
      cases other with
      | equivalent =>
          exact False.elim (hdef hother.1)
      | strict =>
          exact False.elim (hret hother.2)
      | coarsening =>
          exact False.elim (hdef hother.1)
      | incomparable => rfl

/--
Strict Extension Normal Form. For a quotient map `πOld`, retentive
non-definability of `πNew` is equivalent to retaining the old quotient and
splitting at least one old fiber. The second conjunct records the four-way
normal-form classification: equivalence, strict extension, coarsening, or
incomparable rewrite.
-/
theorem strict_extension {X QOld QNew : Type} (πOld : X → QOld)
    (πNew : X → QNew) (hπOld : Function.Surjective πOld) :
    (StrictExtension πOld πNew ↔
      RetainsOld πOld πNew ∧ SplitFiberExists πOld πNew) ∧
        ExactlyOneStrictExtensionStatus πOld πNew := by
  constructor
  · constructor
    · intro hstrict
      exact ⟨hstrict.1, split_of_not_definable πOld πNew hπOld hstrict.2⟩
    · intro h
      rcases h with ⟨hret, hsplit⟩
      constructor
      · exact hret
      · intro hdef
        rcases hdef with ⟨lift, hcomm⟩
        rcases hsplit with ⟨x, y, hOld, hNewNe⟩
        have hx : lift (πOld x) = πNew x := congrFun hcomm x
        have hy : lift (πOld y) = πNew y := congrFun hcomm y
        have hNew : πNew x = πNew y := by
          calc
            πNew x = lift (πOld x) := hx.symm
            _ = lift (πOld y) := by rw [hOld]
            _ = πNew y := hy
        exact hNewNe hNew
  · exact strict_extension_status_partition πOld πNew

end SixBirdsMetaMath.FoundationsIV.Stability.StrictExtension
