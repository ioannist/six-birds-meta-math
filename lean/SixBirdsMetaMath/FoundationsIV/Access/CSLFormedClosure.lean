/-!
F13b CSL formed-closure law: direct finite-interface form.

Determination by current access together with the upstream state makes every
predictive split pair reveal a difference in the upstream state.
-/

namespace SixBirdsMetaMath.FoundationsIV.Access.CSLFormedClosure

/-- A predictive distinction inside one current-access fiber. -/
def PredictiveSurplus {H Q M : Type} (currQ : H → Q) (predM : H → M) : Prop :=
  ∃ h h', currQ h = currQ h' ∧ predM h ≠ predM h'

/-- A predictive distinction inside one current-access fiber that also
distinguishes the upstream determining state. -/
def HiddenFromCurrent {H Q M S : Type} (currQ : H → Q)
    (predM : H → M) (d : H → S) : Prop :=
  ∃ h h', currQ h = currQ h' ∧ d h ≠ d h' ∧ predM h ≠ predM h'

/-- Paper F13b: determination by current access and upstream state forces
upstream separation of predictive split pairs, so predictive surplus is
equivalent to a hidden upstream distinction. -/
theorem csl_formed_closure_direct {H Q M S : Type}
    (currQ : H → Q) (predM : H → M) (d : H → S)
    (hdet : ∀ h h', currQ h = currQ h' → d h = d h' →
      predM h = predM h') :
    (∀ h h', currQ h = currQ h' → predM h ≠ predM h' → d h ≠ d h') ∧
      (PredictiveSurplus currQ predM ↔ HiddenFromCurrent currQ predM d) := by
  have hsplit : ∀ h h', currQ h = currQ h' →
      predM h ≠ predM h' → d h ≠ d h' := by
    intro h h' hq hm hd
    exact hm (hdet h h' hq hd)
  refine ⟨hsplit, ?_⟩
  constructor
  · rintro ⟨h, h', hq, hm⟩
    exact ⟨h, h', hq, hsplit h h' hq hm, hm⟩
  · rintro ⟨h, h', hq, _, hm⟩
    exact ⟨h, h', hq, hm⟩

/-- An arbitrary state readout determines the predictive readout jointly with
current access when the predictive readout is constant on the joint fibers. -/
def ReadoutDetermining {H Q M S : Type} (currQ : H → Q)
    (predM : H → M) (d : H → S) : Prop :=
  ∀ h h', currQ h = currQ h' → d h = d h' → predM h = predM h'

/-- The paper's hidden-state surplus, with no determining assumption. -/
abbrev HiddenStateSurplus {H Q M S : Type} (currQ : H → Q)
    (predM : H → M) (d : H → S) : Prop :=
  HiddenFromCurrent currQ predM d

/-- The image of the joint current/state readout, retaining empty carriers. -/
def JointReadoutImage {H Q S : Type} (currQ : H → Q) (d : H → S) : Type :=
  {qs : Q × S // ∃ h : H, (currQ h, d h) = qs}

/-- The joint readout corestricted to its image. -/
def jointReadoutToImage {H Q S : Type} (currQ : H → Q) (d : H → S)
    (h : H) : JointReadoutImage currQ d :=
  ⟨(currQ h, d h), h, rfl⟩

/-- Determination is exactly factorization through the image of the joint
readout, without inhabitedness or surjectivity assumptions. -/
theorem readout_determining_iff_image_factorization {H Q M S : Type}
    (currQ : H → Q) (predM : H → M) (d : H → S) :
    ReadoutDetermining currQ predM d ↔
      ∃ g : JointReadoutImage currQ d → M,
        ∀ h, predM h = g (jointReadoutToImage currQ d h) := by
  classical
  constructor
  · intro hdet
    let rep : JointReadoutImage currQ d → H :=
      fun qs => Classical.choose qs.property
    refine ⟨fun qs => predM (rep qs), ?_⟩
    intro h
    have heq : (currQ (rep (jointReadoutToImage currQ d h)),
        d (rep (jointReadoutToImage currQ d h))) = (currQ h, d h) :=
      Classical.choose_spec (jointReadoutToImage currQ d h).property
    exact (hdet _ h (congrArg Prod.fst heq) (congrArg Prod.snd heq)).symm
  · rintro ⟨g, hg⟩ h h' hq hd
    have heq : jointReadoutToImage currQ d h = jointReadoutToImage currQ d h' :=
      Subtype.ext (Prod.ext hq hd)
    exact (hg h).trans ((congrArg g heq).trans (hg h').symm)

/-- With a nonempty predictive carrier, the factor map extends to the full
product, including joint values not realized by any history. -/
theorem readout_determining_iff_product_factorization {H Q M S : Type}
    (currQ : H → Q) (predM : H → M) (d : H → S) (hM : Nonempty M) :
    ReadoutDetermining currQ predM d ↔
      ∃ g : Q × S → M, ∀ h, predM h = g (currQ h, d h) := by
  classical
  constructor
  · intro hdet
    let g : Q × S → M := fun qs =>
      if hqs : ∃ h : H, (currQ h, d h) = qs then
        predM (Classical.choose hqs) else Classical.choice hM
    refine ⟨g, ?_⟩
    intro h
    have hqs : ∃ h' : H, (currQ h', d h') = (currQ h, d h) := ⟨h, rfl⟩
    simp only [g, dif_pos hqs]
    have heq := Classical.choose_spec hqs
    exact (hdet _ h (congrArg Prod.fst heq) (congrArg Prod.snd heq)).symm
  · rintro ⟨g, hg⟩ h h' hq hd
    exact (hg h).trans ((congrArg g (Prod.ext hq hd)).trans (hg h').symm)

/-- Empty histories and predictions show why full-product factorization cannot
be claimed without an extension hypothesis. -/
theorem empty_readout_determining_not_product_factorization :
    ReadoutDetermining (Empty.elim : Empty → Unit)
      (id : Empty → Empty) (Empty.elim : Empty → Unit) ∧
    ¬ ∃ g : Unit × Unit → Empty,
      ∀ h : Empty, h = g (Empty.elim h, Empty.elim h) := by
  constructor
  · intro h
    exact Empty.elim h
  · rintro ⟨g, _⟩
    exact Empty.elim (g ((), ()))

/-- Every predictive split either separates the declared state or remains a
predictive split inside one joint current/state fiber. -/
theorem predictive_surplus_iff_hidden_or_joint_split {H Q M S : Type}
    (currQ : H → Q) (predM : H → M) (d : H → S) :
    PredictiveSurplus currQ predM ↔ HiddenStateSurplus currQ predM d ∨
      ∃ h h', currQ h = currQ h' ∧ d h = d h' ∧ predM h ≠ predM h' := by
  classical
  constructor
  · rintro ⟨h, h', hq, hm⟩
    by_cases hd : d h = d h'
    · exact Or.inr ⟨h, h', hq, hd, hm⟩
    · exact Or.inl ⟨h, h', hq, hd, hm⟩
  · intro hsplit
    cases hsplit with
    | inl hhidden =>
        obtain ⟨h, h', hq, _, hm⟩ := hhidden
        exact ⟨h, h', hq, hm⟩
    | inr hjoint =>
        obtain ⟨h, h', hq, _, hm⟩ := hjoint
        exact ⟨h, h', hq, hm⟩

/-- F13b extended to arbitrary state readouts: the original formed-closure law
is conditional on determination, while factorization and the split diagnosis
require no determining hypothesis. Full-product extension requires nonempty M. -/
theorem csl_formed_closure_direct_strengthened {H Q M S : Type}
    (currQ : H → Q) (predM : H → M) (d : H → S) :
    (ReadoutDetermining currQ predM d →
      (∀ h h', currQ h = currQ h' → predM h ≠ predM h' → d h ≠ d h') ∧
        (PredictiveSurplus currQ predM ↔ HiddenFromCurrent currQ predM d)) ∧
    (ReadoutDetermining currQ predM d ↔
      ∃ g : JointReadoutImage currQ d → M,
        ∀ h, predM h = g (jointReadoutToImage currQ d h)) ∧
    (Nonempty M → (ReadoutDetermining currQ predM d ↔
      ∃ g : Q × S → M, ∀ h, predM h = g (currQ h, d h))) ∧
    (PredictiveSurplus currQ predM ↔ HiddenStateSurplus currQ predM d ∨
      ∃ h h', currQ h = currQ h' ∧ d h = d h' ∧ predM h ≠ predM h') := by
  exact ⟨fun hdet => csl_formed_closure_direct currQ predM d hdet,
    readout_determining_iff_image_factorization currQ predM d,
    fun hM => readout_determining_iff_product_factorization currQ predM d hM,
    predictive_surplus_iff_hidden_or_joint_split currQ predM d⟩

/-- The predictive readout is itself determining. -/
theorem predictive_readout_determining {H Q M : Type}
    (currQ : H → Q) (predM : H → M) :
    ReadoutDetermining currQ predM predM := by
  intro _ _ _ hm
  exact hm

/-- Determination is precisely containment of the joint-state kernel in the
canonical joint-predictive kernel. -/
theorem readout_determining_iff_joint_kernel {H Q M S : Type}
    (currQ : H → Q) (predM : H → M) (d : H → S) :
    ReadoutDetermining currQ predM d ↔
      ∀ h h', (currQ h, d h) = (currQ h', d h') →
        (currQ h, predM h) = (currQ h', predM h') := by
  constructor
  · intro hdet h h' heq
    exact Prod.ext (congrArg (fun p : Q × S => p.1) heq)
      (hdet h h' (congrArg Prod.fst heq) (congrArg Prod.snd heq))
  · intro hkernel h h' hq hd
    exact congrArg Prod.snd (hkernel h h' (Prod.ext hq hd))

/-- The coverage statement extended by the new canonicality clauses. -/
theorem csl_formed_closure_direct_kernel_strengthened {H Q M S : Type}
    (currQ : H → Q) (predM : H → M) (d : H → S) :
    ((ReadoutDetermining currQ predM d →
      (∀ h h', currQ h = currQ h' → predM h ≠ predM h' → d h ≠ d h') ∧
        (PredictiveSurplus currQ predM ↔ HiddenFromCurrent currQ predM d)) ∧
    (ReadoutDetermining currQ predM d ↔
      ∃ g : JointReadoutImage currQ d → M,
        ∀ h, predM h = g (jointReadoutToImage currQ d h)) ∧
    (Nonempty M → (ReadoutDetermining currQ predM d ↔
      ∃ g : Q × S → M, ∀ h, predM h = g (currQ h, d h))) ∧
    (PredictiveSurplus currQ predM ↔ HiddenStateSurplus currQ predM d ∨
      ∃ h h', currQ h = currQ h' ∧ d h = d h' ∧ predM h ≠ predM h')) ∧
    ReadoutDetermining currQ predM predM ∧
    (∀ (S' : Type) (d' : H → S'),
      ReadoutDetermining currQ predM d' ↔
        ∀ h h', (currQ h, d' h) = (currQ h', d' h') →
          (currQ h, predM h) = (currQ h', predM h')) := by
  exact ⟨csl_formed_closure_direct_strengthened currQ predM d,
    predictive_readout_determining currQ predM,
    fun _ d' => readout_determining_iff_joint_kernel currQ predM d'⟩

/-- A determining pairing maps its image to the canonical predictive pairing's
image, with no inhabitedness or surjectivity assumptions. -/
theorem determining_pairing_factors_through_image {H Q M S : Type}
    (currQ : H → Q) (predM : H → M) (d : H → S)
    (hdet : ReadoutDetermining currQ predM d) :
    ∃ G : JointReadoutImage currQ d → JointReadoutImage currQ predM,
      jointReadoutToImage currQ predM = G ∘ jointReadoutToImage currQ d := by
  classical
  let G : JointReadoutImage currQ d → JointReadoutImage currQ predM :=
    fun qs => jointReadoutToImage currQ predM (Classical.choose qs.property)
  refine ⟨G, ?_⟩
  funext h
  apply Subtype.ext
  have heq := Classical.choose_spec (jointReadoutToImage currQ d h).property
  exact ((readout_determining_iff_joint_kernel currQ predM d).mp hdet
    _ h heq).symm

/-- The canonical pairing is determining and factors through the image of
every determining pairing, expressing coarseness as a map statement. -/
theorem canonical_pairing_coarsest_on_images {H Q M : Type}
    (currQ : H → Q) (predM : H → M) :
    ReadoutDetermining currQ predM predM ∧
    (∀ (S' : Type) (d' : H → S'), ReadoutDetermining currQ predM d' →
      ∃ G : JointReadoutImage currQ d' → JointReadoutImage currQ predM,
        jointReadoutToImage currQ predM = G ∘ jointReadoutToImage currQ d') := by
  exact ⟨predictive_readout_determining currQ predM,
    fun _ d' hdet => determining_pairing_factors_through_image currQ predM d' hdet⟩

/-- Nonempty predictions allow the canonical pairing's factor map to extend
to the whole product codomain of every determining pairing. -/
theorem determining_pairing_factors_through_product {H Q M S : Type}
    (currQ : H → Q) (predM : H → M) (d : H → S)
    (hM : Nonempty M) (hdet : ReadoutDetermining currQ predM d) :
    ∃ G : Q × S → Q × M,
      (fun h => (currQ h, predM h)) = G ∘ (fun h => (currQ h, d h)) := by
  obtain ⟨g, hg⟩ :=
    (readout_determining_iff_product_factorization currQ predM d hM).mp hdet
  refine ⟨fun qs => (qs.1, g qs), ?_⟩
  funext h
  exact Prod.ext rfl (hg h)

/-- The full F13b conclusion includes the canonical pairing's coarseness
on images and, conditionally on nonempty predictions, full-product factorization. -/
theorem csl_formed_closure_direct_full {H Q M S : Type}
    (currQ : H → Q) (predM : H → M) (d : H → S) :
    (((ReadoutDetermining currQ predM d →
      (∀ h h', currQ h = currQ h' → predM h ≠ predM h' → d h ≠ d h') ∧
        (PredictiveSurplus currQ predM ↔ HiddenFromCurrent currQ predM d)) ∧
    (ReadoutDetermining currQ predM d ↔
      ∃ g : JointReadoutImage currQ d → M,
        ∀ h, predM h = g (jointReadoutToImage currQ d h)) ∧
    (Nonempty M → (ReadoutDetermining currQ predM d ↔
      ∃ g : Q × S → M, ∀ h, predM h = g (currQ h, d h))) ∧
    (PredictiveSurplus currQ predM ↔ HiddenStateSurplus currQ predM d ∨
      ∃ h h', currQ h = currQ h' ∧ d h = d h' ∧ predM h ≠ predM h')) ∧
    ReadoutDetermining currQ predM predM ∧
    (∀ (S' : Type) (d' : H → S'),
      ReadoutDetermining currQ predM d' ↔
        ∀ h h', (currQ h, d' h) = (currQ h', d' h') →
          (currQ h, predM h) = (currQ h', predM h'))) ∧
    (ReadoutDetermining currQ predM predM ∧
      (∀ (S' : Type) (d' : H → S'), ReadoutDetermining currQ predM d' →
        ∃ G : JointReadoutImage currQ d' → JointReadoutImage currQ predM,
          jointReadoutToImage currQ predM = G ∘ jointReadoutToImage currQ d')) ∧
    (Nonempty M → ∀ (S' : Type) (d' : H → S'),
      ReadoutDetermining currQ predM d' →
        ∃ G : Q × S' → Q × M,
          (fun h => (currQ h, predM h)) = G ∘ (fun h => (currQ h, d' h))) := by
  exact ⟨csl_formed_closure_direct_kernel_strengthened currQ predM d,
    canonical_pairing_coarsest_on_images currQ predM,
    fun hM _ d' hdet => determining_pairing_factors_through_product
      currQ predM d' hM hdet⟩

end SixBirdsMetaMath.FoundationsIV.Access.CSLFormedClosure
