import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F37 Complementarity as Non-Joint Access.

The product signature of two quotients exists as a function, but that is not
the same as a formed admissible joint access package. Complementarity is valid
separate access together with obstruction to every declared admissible joint
carrier at the stated scope.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Complementarity

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- The set-theoretic product signature carrying two access quotients. -/
def jointSignature {H QA QB : Type} (qA : H → QA) (qB : H → QB) :
    H → QA × QB :=
  fun h => (qA h, qB h)

/-- A target family/signature is valid for an access quotient when it descends
through that quotient. -/
def AccessTargetValid {H Q Target : Type} (access : H → Q)
    (target : H → Target) : Prop :=
  Descends access (fun h : H => h) target

/-- Individual access package: a formedness gate plus target validity. -/
def IndividuallyFormedAccess {H Q Target : Type} (formed : Prop)
    (access : H → Q) (target : H → Target) : Prop :=
  formed ∧ AccessTargetValid access target

/-- Split-pair obstruction for target validity of one access quotient. -/
def AccessTargetObstruction {H Q Target : Type} (access : H → Q)
    (target : H → Target) : (H × H) → Prop :=
  splitPairObstruction access (fun h : H => h) target

/-- No target-validity obstruction is present. -/
def AccessTargetObstructionEmpty {H Q Target : Type} (access : H → Q)
    (target : H → Target) : Prop :=
  ObstructionEmpty (AccessTargetObstruction access target)

/-- A carrier carries both access quotients when each quotient descends through
that carrier. -/
def CarriesBothAccesses {H K QA QB : Type} (carrier : H → K)
    (qA : H → QA) (qB : H → QB) : Prop :=
  Descends carrier (fun h : H => h) qA ∧
    Descends carrier (fun h : H => h) qB

/-- A declared joint-carrier class has a formed joint access when some carrier
in the class is admissible and carries both access quotients. The codomain `K`
is part of the declared scope, preserving that complementarity is scoped. -/
def JointAccessExists {H K QA QB : Type} (qA : H → QA) (qB : H → QB)
    (AdmissibleJoint : (H → K) → Prop) : Prop :=
  ∃ carrier : H → K, AdmissibleJoint carrier ∧ CarriesBothAccesses carrier qA qB

/-- The product signature is admissible only if the declared admissibility
predicate says it is; product existence alone is not enough. -/
def ProductJointAdmissible {H QA QB : Type} (qA : H → QA) (qB : H → QB)
    (AdmissibleProduct : (H → QA × QB) → Prop) : Prop :=
  AdmissibleProduct (jointSignature qA qB)

/-- Complementarity at a declared joint-carrier scope: both separate accesses
are individually formed and valid, but no admissible joint carrier exists. -/
def ComplementaryAtScope {H QA QB TargetA TargetB K : Type}
    (formedA formedB : Prop) (qA : H → QA) (qB : H → QB)
    (targetA : H → TargetA) (targetB : H → TargetB)
    (AdmissibleJoint : (H → K) → Prop) : Prop :=
  IndividuallyFormedAccess formedA qA targetA ∧
    IndividuallyFormedAccess formedB qB targetB ∧
      ¬ JointAccessExists qA qB AdmissibleJoint

/-- Common quotient shared by two views, distinct from joint refinement. -/
def CommonQuotientOnly {H Public QA QB : Type} (publicQ : H → Public)
    (qA : H → QA) (qB : H → QB) : Prop :=
  Descends qA (fun h : H => h) publicQ ∧
    Descends qB (fun h : H => h) publicQ

/-- Sequential access order residue: the two access orders produce different
target values for some state. -/
def AccessOrderHolonomy {H HAB HBA R : Type} (accessAB : H → HAB)
    (accessBA : H → HBA) (resultAB : HAB → R) (resultBA : HBA → R) : Prop :=
  ∃ h, resultAB (accessAB h) ≠ resultBA (accessBA h)

/-- Strict joint extension by memory/protocol/boundary state. -/
def jointStrictExtension {H QA QB M : Type} (qA : H → QA) (qB : H → QB)
    (memory : H → M) : H → (QA × QB) × M :=
  fun h => (jointSignature qA qB h, memory h)

/-- The added memory is not already carried by the product signature. -/
def MemoryNotInProduct {H QA QB M : Type} (qA : H → QA) (qB : H → QB)
    (memory : H → M) : Prop :=
  ¬ Descends (jointSignature qA qB) (fun h : H => h) memory

/-- Strict joint extension records the product signature and an additional
memory/protocol component that was not free at the original product scope. -/
def StrictJointExtension {H QA QB M : Type} (qA : H → QA) (qB : H → QB)
    (memory : H → M) : Prop :=
  MemoryNotInProduct qA qB memory ∧
    CarriesBothAccesses (jointStrictExtension qA qB memory) qA qB ∧
      Descends (jointStrictExtension qA qB memory) (fun h : H => h) memory

/-- Source status vocabulary for complementarity claims. -/
inductive ComplementarityStatus where
  | exactJointAccess
  | productJointAccess
  | jointAccessByStrictExtension
  | sequentialAccess
  | orderDependentAccess
  | complementary
  | coarsenedJointAccess
  | probabilisticJointCoupling
  | commonObjectOnly
  | localJointAccess
  | globalJointObstructed
  | protocolSupportedJointAccess
  | presentationArtifact
  | hiddenJointRefinement
  | budgetedJointAccess
  | invalidSeparateAccess
  | complementarityOverread
deriving DecidableEq

/-- Meaning assignment for the F37 status vocabulary. -/
def ComplementarityStatusHolds (exact product strict sequential orderDependent
    complementary coarsened probabilistic commonOnly localOnly globalObstructed
    protocol presentation hidden budgeted invalidSeparate overread : Prop) :
    ComplementarityStatus → Prop
  | ComplementarityStatus.exactJointAccess => exact
  | ComplementarityStatus.productJointAccess => product
  | ComplementarityStatus.jointAccessByStrictExtension => strict
  | ComplementarityStatus.sequentialAccess => sequential
  | ComplementarityStatus.orderDependentAccess => orderDependent
  | ComplementarityStatus.complementary => complementary
  | ComplementarityStatus.coarsenedJointAccess => coarsened
  | ComplementarityStatus.probabilisticJointCoupling => probabilistic
  | ComplementarityStatus.commonObjectOnly => commonOnly
  | ComplementarityStatus.localJointAccess => localOnly
  | ComplementarityStatus.globalJointObstructed => globalObstructed
  | ComplementarityStatus.protocolSupportedJointAccess => protocol
  | ComplementarityStatus.presentationArtifact => presentation
  | ComplementarityStatus.hiddenJointRefinement => hidden
  | ComplementarityStatus.budgetedJointAccess => budgeted
  | ComplementarityStatus.invalidSeparateAccess => invalidSeparate
  | ComplementarityStatus.complementarityOverread => overread

/-- Individual target validity is exactly absence of its split-pair
obstruction. -/
theorem access_target_valid_iff_no_obstruction {H Q Target : Type}
    (access : H → Q) (target : H → Target)
    (haccess : Function.Surjective access) :
    AccessTargetValid access target ↔ AccessTargetObstructionEmpty access target :=
  descent_repair_normal_form access (fun h : H => h) target haccess

/-- The product signature carries the first access quotient. -/
theorem joint_signature_carries_left {H QA QB : Type} (qA : H → QA)
    (qB : H → QB) :
    Descends (jointSignature qA qB) (fun h : H => h) qA := by
  refine ⟨Prod.fst, ?_⟩
  funext h
  rfl

/-- The product signature carries the second access quotient. -/
theorem joint_signature_carries_right {H QA QB : Type} (qA : H → QA)
    (qB : H → QB) :
    Descends (jointSignature qA qB) (fun h : H => h) qB := by
  refine ⟨Prod.snd, ?_⟩
  funext h
  rfl

/-- The product signature always carries both views. This is only a carrying
fact, not a joint-admissibility fact. -/
theorem joint_signature_carries_both {H QA QB : Type} (qA : H → QA)
    (qB : H → QB) :
    CarriesBothAccesses (jointSignature qA qB) qA qB :=
  ⟨joint_signature_carries_left qA qB, joint_signature_carries_right qA qB⟩

/-- Universal property: any carrier carrying both access quotients refines the
product signature. -/
theorem carrier_refines_joint_signature {H K QA QB : Type} (carrier : H → K)
    (qA : H → QA) (qB : H → QB) :
    CarriesBothAccesses carrier qA qB →
      Descends carrier (fun h : H => h) (jointSignature qA qB) := by
  intro hboth
  rcases hboth.1 with ⟨rhoA, hrhoA⟩
  rcases hboth.2 with ⟨rhoB, hrhoB⟩
  refine ⟨fun k => (rhoA k, rhoB k), ?_⟩
  funext h
  have hA : rhoA (carrier h) = qA h := congrFun hrhoA h
  have hB : rhoB (carrier h) = qB h := congrFun hrhoB h
  exact Prod.ext hA hB

/-- Complementarity is exactly valid separate access plus no declared
admissible joint carrier. -/
theorem complementary_iff_valid_separate_and_no_joint
    {H QA QB TargetA TargetB K : Type} (formedA formedB : Prop)
    (qA : H → QA) (qB : H → QB) (targetA : H → TargetA)
    (targetB : H → TargetB) (AdmissibleJoint : (H → K) → Prop) :
    ComplementaryAtScope formedA formedB qA qB targetA targetB AdmissibleJoint ↔
      IndividuallyFormedAccess formedA qA targetA ∧
        IndividuallyFormedAccess formedB qB targetB ∧
          ¬ JointAccessExists qA qB AdmissibleJoint := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Product existence is distinct from product admissibility. -/
theorem product_signature_precision {H QA QB : Type} (qA : H → QA) (qB : H → QB)
    (AdmissibleProduct : (H → QA × QB) → Prop) :
    CarriesBothAccesses (jointSignature qA qB) qA qB ∧
      (ProductJointAdmissible qA qB AdmissibleProduct ↔
        AdmissibleProduct (jointSignature qA qB)) := by
  exact ⟨joint_signature_carries_both qA qB, Iff.rfl⟩

/-- The strict joint extension carries both access quotients. -/
theorem joint_strict_extension_carries_both {H QA QB M : Type}
    (qA : H → QA) (qB : H → QB) (memory : H → M) :
    CarriesBothAccesses (jointStrictExtension qA qB memory) qA qB := by
  constructor
  · refine ⟨fun z => z.1.1, ?_⟩
    funext h
    rfl
  · refine ⟨fun z => z.1.2, ?_⟩
    funext h
    rfl

/-- The strict joint extension carries the added memory. -/
theorem joint_strict_extension_carries_memory {H QA QB M : Type}
    (qA : H → QA) (qB : H → QB) (memory : H → M) :
    Descends (jointStrictExtension qA qB memory) (fun h : H => h) memory := by
  refine ⟨Prod.snd, ?_⟩
  funext h
  rfl

/-- Strict joint extension is exactly adding non-product memory while carrying
the old product views and the new memory. -/
theorem strict_joint_extension_iff_memory_not_product {H QA QB M : Type}
    (qA : H → QA) (qB : H → QB) (memory : H → M) :
    StrictJointExtension qA qB memory ↔ MemoryNotInProduct qA qB memory := by
  constructor
  · intro hstrict
    exact hstrict.1
  · intro hmemory
    exact ⟨hmemory, joint_strict_extension_carries_both qA qB memory,
      joint_strict_extension_carries_memory qA qB memory⟩

/--
Complementarity as Non-Joint Access Normal Form. The product signature exists
and is the minimal carrier of both views, but complementarity is valid separate
access plus absence of a declared admissible joint carrier at the scoped class.
-/
theorem complementarity_as_non_joint_access
    {H QA QB TargetA TargetB K M : Type} (formedA formedB : Prop)
    (qA : H → QA) (qB : H → QB) (targetA : H → TargetA)
    (targetB : H → TargetB) (AdmissibleJoint : (H → K) → Prop)
    (AdmissibleProduct : (H → QA × QB) → Prop) (memory : H → M)
    (hA : Function.Surjective qA) (hB : Function.Surjective qB) :
    (AccessTargetValid qA targetA ↔ AccessTargetObstructionEmpty qA targetA) ∧
      (AccessTargetValid qB targetB ↔ AccessTargetObstructionEmpty qB targetB) ∧
        CarriesBothAccesses (jointSignature qA qB) qA qB ∧
          (∀ carrier : H → K,
            CarriesBothAccesses carrier qA qB →
              Descends carrier (fun h : H => h) (jointSignature qA qB)) ∧
          (ComplementaryAtScope formedA formedB qA qB targetA targetB
              AdmissibleJoint ↔
            IndividuallyFormedAccess formedA qA targetA ∧
              IndividuallyFormedAccess formedB qB targetB ∧
                ¬ JointAccessExists qA qB AdmissibleJoint) ∧
          (ProductJointAdmissible qA qB AdmissibleProduct ↔
            AdmissibleProduct (jointSignature qA qB)) ∧
          (StrictJointExtension qA qB memory ↔ MemoryNotInProduct qA qB memory) := by
  exact ⟨access_target_valid_iff_no_obstruction qA targetA hA,
    access_target_valid_iff_no_obstruction qB targetB hB,
    joint_signature_carries_both qA qB,
    fun carrier => carrier_refines_joint_signature carrier qA qB,
    complementary_iff_valid_separate_and_no_joint formedA formedB qA qB targetA
      targetB AdmissibleJoint,
    (product_signature_precision qA qB AdmissibleProduct).2,
    strict_joint_extension_iff_memory_not_product qA qB memory⟩

/-- A readout constant on the fibers of a carrier factors through that
carrier when the source is nonempty. The value off the carrier image uses a
fixed source point. -/
theorem factor_through_carrier_of_fiber_constant {H K Q : Type}
    (hH : Nonempty H) (j : H → K) (q : H → Q)
    (hconstant : ∀ h h', j h = j h' → q h = q h') :
    ∃ a : K → Q, a ∘ j = q := by
  classical
  let h₀ : H := Classical.choice hH
  let a : K → Q := fun k =>
    if h : ∃ x : H, j x = k then q (Classical.choose h) else q h₀
  refine ⟨a, ?_⟩
  funext x
  have himage : ∃ y : H, j y = j x := ⟨x, rfl⟩
  change (if h : ∃ y : H, j y = j x then q (Classical.choose h) else q h₀) = q x
  rw [dif_pos himage]
  exact hconstant _ x (Classical.choose_spec himage)

/-- Paper F37: with separately admissible accesses, complementarity means
that every admissible joint carrier identifies a pair separated by at least
one of the two access quotients. -/
theorem complementarity_split_criterion
    {H QA QB TargetA TargetB K : Type} (hH : Nonempty H)
    (formedA formedB : Prop) (qA : H → QA) (qB : H → QB)
    (targetA : H → TargetA) (targetB : H → TargetB)
    (J : (H → K) → Prop)
    (hqA : Function.Surjective qA) (hqB : Function.Surjective qB)
    (hseparateA : IndividuallyFormedAccess formedA qA targetA)
    (hseparateB : IndividuallyFormedAccess formedB qB targetB) :
    ComplementaryAtScope formedA formedB qA qB targetA targetB J ↔
      ∀ j : H → K, J j →
        ∃ h h', j h = j h' ∧ (qA h ≠ qA h' ∨ qB h ≠ qB h') := by
  let _ := hqA
  let _ := hqB
  constructor
  · intro hcomp j hj
    classical
    apply Classical.byContradiction
    intro hnoSplit
    have hconstantA : ∀ h h', j h = j h' → qA h = qA h' := by
      intro h h' heq
      exact Classical.byContradiction (fun hne =>
        hnoSplit ⟨h, h', heq, Or.inl hne⟩)
    have hconstantB : ∀ h h', j h = j h' → qB h = qB h' := by
      intro h h' heq
      exact Classical.byContradiction (fun hne =>
        hnoSplit ⟨h, h', heq, Or.inr hne⟩)
    obtain ⟨a, ha⟩ := factor_through_carrier_of_fiber_constant hH j qA hconstantA
    obtain ⟨b, hb⟩ := factor_through_carrier_of_fiber_constant hH j qB hconstantB
    exact hcomp.2.2 ⟨j, hj, ⟨a, ha⟩, ⟨b, hb⟩⟩
  · intro hsplit
    refine ⟨hseparateA, hseparateB, ?_⟩
    intro hjoint
    obtain ⟨j, hj, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hjoint
    obtain ⟨h, h', heq, hdiff⟩ := hsplit j hj
    have heqA : qA h = qA h' := by
      calc
        qA h = a (j h) := (congrFun ha h).symm
        _ = a (j h') := congrArg a heq
        _ = qA h' := congrFun ha h'
    have heqB : qB h = qB h' := by
      calc
        qB h = b (j h) := (congrFun hb h).symm
        _ = b (j h') := congrArg b heq
        _ = qB h' := congrFun hb h'
    cases hdiff with
    | inl hne => exact hne heqA
    | inr hne => exact hne heqB

/-- Carrying the two accesses separately is equivalent to factoring their
pairing through the declared carrier. -/
theorem carries_both_iff_joint_signature_factorization {H K QA QB : Type}
    (j : H → K) (qA : H → QA) (qB : H → QB) :
    CarriesBothAccesses j qA qB ↔
      ∃ g : K → QA × QB, (fun h => (qA h, qB h)) = g ∘ j := by
  constructor
  · intro hboth
    obtain ⟨g, hg⟩ := carrier_refines_joint_signature j qA qB hboth
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, hg⟩
    constructor
    · refine ⟨fun k => (g k).1, ?_⟩
      funext h
      exact (congrArg Prod.fst (congrFun hg h)).symm
    · refine ⟨fun k => (g k).2, ?_⟩
      funext h
      exact (congrArg Prod.snd (congrFun hg h)).symm

/-- Under separate admissibility, complementarity is the absence of an
admissible carrier through which the product signature factors. -/
theorem complementary_iff_no_joint_signature_factorization
    {H QA QB TargetA TargetB K : Type}
    (formedA formedB : Prop) (qA : H → QA) (qB : H → QB)
    (targetA : H → TargetA) (targetB : H → TargetB) (J : (H → K) → Prop)
    (hseparateA : IndividuallyFormedAccess formedA qA targetA)
    (hseparateB : IndividuallyFormedAccess formedB qB targetB) :
    ComplementaryAtScope formedA formedB qA qB targetA targetB J ↔
      ¬ ∃ j : H → K, J j ∧
        ∃ g : K → QA × QB, (fun h => (qA h, qB h)) = g ∘ j := by
  constructor
  · rintro hcomp ⟨j, hj, hg⟩
    exact hcomp.2.2 ⟨j, hj,
      (carries_both_iff_joint_signature_factorization j qA qB).mpr hg⟩
  · intro hno
    refine ⟨hseparateA, hseparateB, ?_⟩
    rintro ⟨j, hj, hboth⟩
    exact hno ⟨j, hj,
      (carries_both_iff_joint_signature_factorization j qA qB).mp hboth⟩

/-- If the product signature is itself declared admissible, complementary
access is impossible at that product-carrier scope. -/
theorem admissible_joint_signature_not_complementary
    {H QA QB TargetA TargetB : Type}
    (formedA formedB : Prop) (qA : H → QA) (qB : H → QB)
    (targetA : H → TargetA) (targetB : H → TargetB)
    (J : (H → QA × QB) → Prop) (hpair : J (jointSignature qA qB)) :
    ¬ ComplementaryAtScope formedA formedB qA qB targetA targetB J := by
  intro hcomp
  exact hcomp.2.2 ⟨jointSignature qA qB, hpair, joint_signature_carries_both qA qB⟩

/-- F37 retains its split criterion and adds the product-factorization
criterion and the corollary for admissible product signatures. -/
theorem complementarity_split_criterion_full
    {H QA QB TargetA TargetB K : Type} (hH : Nonempty H)
    (formedA formedB : Prop) (qA : H → QA) (qB : H → QB)
    (targetA : H → TargetA) (targetB : H → TargetB)
    (J : (H → K) → Prop)
    (hqA : Function.Surjective qA) (hqB : Function.Surjective qB)
    (hseparateA : IndividuallyFormedAccess formedA qA targetA)
    (hseparateB : IndividuallyFormedAccess formedB qB targetB) :
    (ComplementaryAtScope formedA formedB qA qB targetA targetB J ↔
      ∀ j : H → K, J j →
        ∃ h h', j h = j h' ∧ (qA h ≠ qA h' ∨ qB h ≠ qB h')) ∧
    (ComplementaryAtScope formedA formedB qA qB targetA targetB J ↔
      ¬ ∃ j : H → K, J j ∧
        ∃ g : K → QA × QB, (fun h => (qA h, qB h)) = g ∘ j) ∧
    (∀ Jprod : (H → QA × QB) → Prop, Jprod (jointSignature qA qB) →
      ¬ ComplementaryAtScope formedA formedB qA qB targetA targetB Jprod) := by
  exact ⟨complementarity_split_criterion hH formedA formedB qA qB targetA targetB
    J hqA hqB hseparateA hseparateB,
    complementary_iff_no_joint_signature_factorization formedA formedB qA qB
      targetA targetB J hseparateA hseparateB,
    fun Jprod hpair => admissible_joint_signature_not_complementary
      formedA formedB qA qB targetA targetB Jprod hpair⟩

/-- The split-pair criterion needs no surjectivity of either access map;
nonempty source supplies default quotient values off each carrier image. -/
theorem complementarity_split_criterion_without_surjectivity
    {H QA QB TargetA TargetB K : Type} (hH : Nonempty H)
    (formedA formedB : Prop) (qA : H → QA) (qB : H → QB)
    (targetA : H → TargetA) (targetB : H → TargetB)
    (J : (H → K) → Prop)
    (hseparateA : IndividuallyFormedAccess formedA qA targetA)
    (hseparateB : IndividuallyFormedAccess formedB qB targetB) :
    ComplementaryAtScope formedA formedB qA qB targetA targetB J ↔
      ∀ j : H → K, J j →
        ∃ h h', j h = j h' ∧ (qA h ≠ qA h' ∨ qB h ≠ qB h') := by
  constructor
  · intro hcomp j hj
    classical
    apply Classical.byContradiction
    intro hnoSplit
    have hconstantA : ∀ h h', j h = j h' → qA h = qA h' := by
      intro h h' heq
      exact Classical.byContradiction (fun hne =>
        hnoSplit ⟨h, h', heq, Or.inl hne⟩)
    have hconstantB : ∀ h h', j h = j h' → qB h = qB h' := by
      intro h h' heq
      exact Classical.byContradiction (fun hne =>
        hnoSplit ⟨h, h', heq, Or.inr hne⟩)
    obtain ⟨a, ha⟩ := factor_through_carrier_of_fiber_constant hH j qA hconstantA
    obtain ⟨b, hb⟩ := factor_through_carrier_of_fiber_constant hH j qB hconstantB
    exact hcomp.2.2 ⟨j, hj, ⟨a, ha⟩, ⟨b, hb⟩⟩
  · intro hsplit
    refine ⟨hseparateA, hseparateB, ?_⟩
    intro hjoint
    obtain ⟨j, hj, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hjoint
    obtain ⟨h, h', heq, hdiff⟩ := hsplit j hj
    have heqA : qA h = qA h' := by
      calc
        qA h = a (j h) := (congrFun ha h).symm
        _ = a (j h') := congrArg a heq
        _ = qA h' := congrFun ha h'
    have heqB : qB h = qB h' := by
      calc
        qB h = b (j h) := (congrFun hb h).symm
        _ = b (j h') := congrArg b heq
        _ = qB h' := congrFun hb h'
    cases hdiff with
    | inl hne => exact hne heqA
    | inr hne => exact hne heqB

/-- Full F37 split and product-factorization criteria without access-map
surjectivity, retaining the nonempty source and separate admissibility. -/
theorem complementarity_split_criterion_general
    {H QA QB TargetA TargetB K : Type} (hH : Nonempty H)
    (formedA formedB : Prop) (qA : H → QA) (qB : H → QB)
    (targetA : H → TargetA) (targetB : H → TargetB)
    (J : (H → K) → Prop)
    (hseparateA : IndividuallyFormedAccess formedA qA targetA)
    (hseparateB : IndividuallyFormedAccess formedB qB targetB) :
    (ComplementaryAtScope formedA formedB qA qB targetA targetB J ↔
      ∀ j : H → K, J j →
        ∃ h h', j h = j h' ∧ (qA h ≠ qA h' ∨ qB h ≠ qB h')) ∧
    (ComplementaryAtScope formedA formedB qA qB targetA targetB J ↔
      ¬ ∃ j : H → K, J j ∧
        ∃ g : K → QA × QB, (fun h => (qA h, qB h)) = g ∘ j) ∧
    (∀ Jprod : (H → QA × QB) → Prop, Jprod (jointSignature qA qB) →
      ¬ ComplementaryAtScope formedA formedB qA qB targetA targetB Jprod) := by
  exact ⟨complementarity_split_criterion_without_surjectivity hH formedA formedB qA qB targetA targetB
    J hseparateA hseparateB,
    complementary_iff_no_joint_signature_factorization formedA formedB qA qB
      targetA targetB J hseparateA hseparateB,
    fun Jprod hpair => admissible_joint_signature_not_complementary
      formedA formedB qA qB targetA targetB Jprod hpair⟩

/-- Without separate-access hypotheses, the split and factorization criteria
include individual formedness and validity as conjuncts. -/
theorem complementarity_split_criterion_general_unconditional
    {H QA QB TargetA TargetB K : Type} (hH : Nonempty H)
    (formedA formedB : Prop) (qA : H → QA) (qB : H → QB)
    (targetA : H → TargetA) (targetB : H → TargetB)
    (J : (H → K) → Prop) :
    (ComplementaryAtScope formedA formedB qA qB targetA targetB J ↔
      IndividuallyFormedAccess formedA qA targetA ∧
      IndividuallyFormedAccess formedB qB targetB ∧
      ∀ j : H → K, J j →
        ∃ h h', j h = j h' ∧ (qA h ≠ qA h' ∨ qB h ≠ qB h')) ∧
    (ComplementaryAtScope formedA formedB qA qB targetA targetB J ↔
      IndividuallyFormedAccess formedA qA targetA ∧
      IndividuallyFormedAccess formedB qB targetB ∧
      ¬ ∃ j : H → K, J j ∧
        ∃ g : K → QA × QB, (fun h => (qA h, qB h)) = g ∘ j) ∧
    (∀ Jprod : (H → QA × QB) → Prop, Jprod (jointSignature qA qB) →
      ¬ ComplementaryAtScope formedA formedB qA qB targetA targetB Jprod) := by
  refine ⟨?_, ?_, fun Jprod hpair =>
    admissible_joint_signature_not_complementary
      formedA formedB qA qB targetA targetB Jprod hpair⟩
  · constructor
    · intro hcomp
      exact ⟨hcomp.1, hcomp.2.1,
        (complementarity_split_criterion_without_surjectivity hH formedA
          formedB qA qB targetA targetB J hcomp.1 hcomp.2.1).mp hcomp⟩
    · rintro ⟨hA, hB, hsplit⟩
      exact (complementarity_split_criterion_without_surjectivity hH formedA
        formedB qA qB targetA targetB J hA hB).mpr hsplit
  · constructor
    · intro hcomp
      exact ⟨hcomp.1, hcomp.2.1,
        (complementary_iff_no_joint_signature_factorization formedA formedB
          qA qB targetA targetB J hcomp.1 hcomp.2.1).mp hcomp⟩
    · rintro ⟨hA, hB, hno⟩
      exact (complementary_iff_no_joint_signature_factorization formedA formedB
        qA qB targetA targetB J hA hB).mpr hno

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Complementarity
