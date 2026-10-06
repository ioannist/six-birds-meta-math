import SixBirdsMetaMath.FoundationsIV.Access.NoFreeDistinction

/-!
F24 Layer Multiplicity.

Nontrivial limited access generically creates non-descending role signatures.
The important discipline from the source is represented in
`LayerFormationDiscipline`: generic pressure toward layers is theorem-grade,
but a specific formed layer still requires admissibility, closure, and status.
-/

namespace SixBirdsMetaMath.FoundationsIV.Access.LayerMultiplicity

open SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure
open SixBirdsMetaMath.FoundationsIV.Access.NoFreeDistinction

/-- Same current object, different role signature. -/
def RoleSignatureSplitPair {H Q S : Type} (q : H → Q) (role : H → S) :
    (H × H) → Prop :=
  DistinctionSplitPair q role

/-- The role signature descends through the current layer. -/
def RoleDescends {H Q S : Type} (q : H → Q) (role : H → S) : Prop :=
  DefinableFromAccess q role

/-- The layer-multiplicity split obstruction is empty. -/
def RoleObstructionEmpty {H Q S : Type} (q : H → Q) (role : H → S) : Prop :=
  DistinctionObstructionEmpty q role

/-- The role signature splits at least one current fiber. -/
def HasRoleSplit {H Q S : Type} (q : H → Q) (role : H → S) : Prop :=
  HasDistinctionSplit q role

/-- Canonical retentive layer extension carrying the role signature. -/
def roleLayerExtension {H Q S : Type} (q : H → Q) (role : H → S) :
    H → Q × S :=
  financedRefinement q role

/-- Source discipline: generic layer pressure is not yet a specific formed
layer. Specific layer formation requires role-nativity, exact carriage need,
admissibility, closure, and residual/status coverage. -/
structure LayerFormationDiscipline where
  nativeToDeclaredRole : Prop
  mustCarryExactly : Prop
  admissibility : Prop
  closure : Prop
  residualStatus : Prop

/-- The conditions under which a detected split may be promoted from layer
pressure to a specific formed layer. -/
def SpecificLayerFormationAllowed (discipline : LayerFormationDiscipline) :
    Prop :=
  discipline.nativeToDeclaredRole ∧ discipline.mustCarryExactly ∧
    discipline.admissibility ∧ discipline.closure ∧ discipline.residualStatus

/-- The source's discipline note as a reusable API predicate. -/
def ImportantDisciplinePreserved (discipline : LayerFormationDiscipline) :
    Prop :=
  SpecificLayerFormationAllowed discipline →
    discipline.admissibility ∧ discipline.closure ∧ discipline.residualStatus

/-- Count of all signatures `H → S` when `|H| = historyCount` and
`|S| = codomainCount`. -/
def AllSignatureCount (historyCount codomainCount : Nat) : Nat :=
  codomainCount ^ historyCount

/-- Count of signatures descending through a quotient image of size
`imageCount`. -/
def DescendingSignatureCount (imageCount codomainCount : Nat) : Nat :=
  codomainCount ^ imageCount

/-- Count of non-descending signatures, expressed as the complement of the
descending count inside all signatures. -/
def NonDescendingSignatureCount (historyCount imageCount codomainCount : Nat) :
    Nat :=
  AllSignatureCount historyCount codomainCount -
    DescendingSignatureCount imageCount codomainCount

/-- Finite counting hypotheses for generic pressure: nontrivial unresolved
fiber mass and at least two role values. -/
def CountingPressure (historyCount imageCount codomainCount unresolvedMass : Nat) :
    Prop :=
  1 < codomainCount ∧ imageCount < historyCount ∧
    historyCount = imageCount + unresolvedMass

/-- Paid/statused decisions available when a native role signature does not
descend through the old layer. -/
def LayerDecisionCosted (strictLayerExtension memoryLayer hiddenUpstreamRole
    bridgeMediatedRole budgetedRole scopedRole coarsenedRole outsideRoleScope
    blockedNonClosure : Prop) : Prop :=
  strictLayerExtension ∨ memoryLayer ∨ hiddenUpstreamRole ∨
    bridgeMediatedRole ∨ budgetedRole ∨ scopedRole ∨ coarsenedRole ∨
      outsideRoleScope ∨ blockedNonClosure

/-- A native exact role split requires a layer decision. -/
def LayerDecisionRequired (discipline : LayerFormationDiscipline)
    (hasSplit costed : Prop) : Prop :=
  discipline.nativeToDeclaredRole → discipline.mustCarryExactly →
    hasSplit → costed

/-- F24 status vocabulary. -/
inductive LayerMultiplicityStatus where
  | inheritedRole
  | strictLayerExtension
  | memoryOrPredictiveLayer
  | hiddenUpstreamRole
  | bridgeMediatedRole
  | budgetedRole
  | scopedRole
  | coarsenedRole
  | outsideRoleScope
  | layerFormationFailure
deriving DecidableEq

/-- Meaning of each layer-multiplicity status. -/
def LayerMultiplicityStatusHolds (inherited strict memory hidden bridge budget
    scopedRole coarsened outside blocked : Prop) :
    LayerMultiplicityStatus → Prop
  | LayerMultiplicityStatus.inheritedRole => inherited
  | LayerMultiplicityStatus.strictLayerExtension => strict
  | LayerMultiplicityStatus.memoryOrPredictiveLayer => memory
  | LayerMultiplicityStatus.hiddenUpstreamRole => hidden
  | LayerMultiplicityStatus.bridgeMediatedRole => bridge
  | LayerMultiplicityStatus.budgetedRole => budget
  | LayerMultiplicityStatus.scopedRole => scopedRole
  | LayerMultiplicityStatus.coarsenedRole => coarsened
  | LayerMultiplicityStatus.outsideRoleScope => outside
  | LayerMultiplicityStatus.layerFormationFailure => blocked

/-- Descent of a role signature is exactly absence of the multiplicity split
obstruction. -/
theorem role_descends_iff_no_split {H Q S : Type} (q : H → Q) (role : H → S)
    (hq : Function.Surjective q) :
    RoleDescends q role ↔ RoleObstructionEmpty q role :=
  distinction_definable_iff_no_split q role hq

/-- A role split is equivalent to non-emptiness of the obstruction. -/
theorem has_role_split_iff_not_empty {H Q S : Type} (q : H → Q)
    (role : H → S) :
    HasRoleSplit q role ↔ ¬ RoleObstructionEmpty q role :=
  has_distinction_split_iff_not_empty q role

/-- The canonical role extension retains the old layer. -/
theorem role_extension_retains_access {H Q S : Type} (q : H → Q)
    (role : H → S) :
    RetainsAccess q (roleLayerExtension q role) :=
  financed_refinement_retains_access q role

/-- The canonical role extension carries the role signature. -/
theorem role_extension_carries_role {H Q S : Type} (q : H → Q)
    (role : H → S) :
    CarriesDistinction (roleLayerExtension q role) role :=
  financed_refinement_carries_distinction q role

/-- A non-descending role signature makes the canonical role extension strict. -/
theorem role_extension_strict_of_split {H Q S : Type} (q : H → Q)
    (role : H → S) :
    HasRoleSplit q role →
      StrictAccessExtension q (roleLayerExtension q role) :=
  financed_refinement_strict_of_split q role

/-- The canonical role extension factors through every package retaining
the old layer and carrying the role signature. -/
theorem role_extension_minimal {H Q S T : Type} (q : H → Q) (role : H → S)
    (package : H → T) (hretains : RetainsAccess q package)
    (hcarries : CarriesDistinction package role) :
    FactorsThroughQ package (roleLayerExtension q role) :=
  financed_refinement_minimal q role package hretains hcarries

/-- The finite counting pressure formula: descending signatures have numerator
`m^K` against `m^N`; if `K < N` and `m ≥ 2`, the non-descending complement is
positive. -/
theorem generic_counting_pressure (historyCount imageCount codomainCount
    unresolvedMass : Nat) :
    CountingPressure historyCount imageCount codomainCount unresolvedMass →
      DescendingSignatureCount imageCount codomainCount *
          codomainCount ^ unresolvedMass =
        AllSignatureCount historyCount codomainCount ∧
        0 <
          NonDescendingSignatureCount historyCount imageCount codomainCount := by
  intro hpressure
  rcases hpressure with ⟨hcodomain, hproper, hcount⟩
  constructor
  · unfold DescendingSignatureCount AllSignatureCount
    rw [hcount, Nat.pow_add]
  · unfold NonDescendingSignatureCount AllSignatureCount DescendingSignatureCount
    exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hcodomain hproper)

/-- Specific layer formation exposes the discipline requirements from the
source note. -/
theorem layer_formation_requires_discipline
    (discipline : LayerFormationDiscipline) :
    ImportantDisciplinePreserved discipline := by
  intro hformed
  exact ⟨hformed.2.2.1, hformed.2.2.2.1, hformed.2.2.2.2⟩

/--
Layer Multiplicity Normal Form. Role signatures descend exactly when the
layer-multiplicity obstruction is empty. A split role signature yields the
canonical strict retentive extension `(q, role)`, with the same universal
property as no-free-distinction. Finite counting records the generic pressure:
when `K < N` and `|S| ≥ 2`, non-descending signatures form a positive
complement. The theorem also keeps the source discipline explicit: generic
pressure does not by itself assert a formed layer without admissibility,
closure, and residual/status coverage.
-/
theorem layer_multiplicity {H Q S : Type} (q : H → Q) (role : H → S)
    (hq : Function.Surjective q) (discipline : LayerFormationDiscipline)
    (historyCount imageCount codomainCount unresolvedMass : Nat)
    (memoryLayer hiddenUpstreamRole bridgeMediatedRole budgetedRole scopedRole
      coarsenedRole outsideRoleScope blockedNonClosure : Prop) :
    (RoleDescends q role ↔ RoleObstructionEmpty q role) ∧
      (HasRoleSplit q role ↔ ¬ RoleObstructionEmpty q role) ∧
        RetainsAccess q (roleLayerExtension q role) ∧
          CarriesDistinction (roleLayerExtension q role) role ∧
            (HasRoleSplit q role →
              StrictAccessExtension q (roleLayerExtension q role)) ∧
              (∀ {T : Type} (package : H → T),
                RetainsAccess q package →
                  CarriesDistinction package role →
                    FactorsThroughQ package (roleLayerExtension q role)) ∧
                (CountingPressure historyCount imageCount codomainCount
                    unresolvedMass →
                  DescendingSignatureCount imageCount codomainCount *
                      codomainCount ^ unresolvedMass =
                    AllSignatureCount historyCount codomainCount ∧
                    0 <
                      NonDescendingSignatureCount historyCount imageCount
                        codomainCount) ∧
                  LayerDecisionRequired discipline (HasRoleSplit q role)
                    (LayerDecisionCosted
                      (StrictAccessExtension q (roleLayerExtension q role))
                      memoryLayer hiddenUpstreamRole bridgeMediatedRole
                      budgetedRole scopedRole coarsenedRole outsideRoleScope
                      blockedNonClosure) ∧
                    ImportantDisciplinePreserved discipline := by
  refine ⟨role_descends_iff_no_split q role hq,
    has_role_split_iff_not_empty q role,
    role_extension_retains_access q role,
    role_extension_carries_role q role,
    role_extension_strict_of_split q role,
    ?_, generic_counting_pressure historyCount imageCount codomainCount
      unresolvedMass, ?_, layer_formation_requires_discipline discipline⟩
  · intro T package hretains hcarries
    exact role_extension_minimal q role package hretains hcarries
  · intro _hnative _hmust hsplit
    exact Or.inl (role_extension_strict_of_split q role hsplit)


/-- A strict canonical role extension splits an old quotient fiber by its role. -/
theorem role_split_of_strict_extension {H Q S : Type} (q : H → Q)
    (role : H → S) :
    StrictAccessExtension q (roleLayerExtension q role) → HasRoleSplit q role := by
  rintro ⟨_, x, y, hq, hstrict⟩
  refine ⟨x, y, hq, ?_⟩
  intro hrole
  apply hstrict
  exact Prod.ext hq hrole

/-- The paper's role descent, strict-refinement, and inclusive resolution laws. -/
theorem paper_layer_multiplicity {H Q S : Type} (q : H → Q)
    (role : H → S) (hq : Function.Surjective q)
    (memoryLayer hiddenUpstreamRole bridgeMediatedRole budgetedRole scopedRole
      coarsenedRole outsideRoleScope blockedNonClosure : Prop) :
    (RoleDescends q role ↔ RoleObstructionEmpty q role) ∧
    (HasRoleSplit q role ↔ ¬ RoleObstructionEmpty q role) ∧
    (HasRoleSplit q role ↔
      StrictAccessExtension q (roleLayerExtension q role)) ∧
    (HasRoleSplit q role →
      LayerDecisionCosted
        (StrictAccessExtension q (roleLayerExtension q role))
        memoryLayer hiddenUpstreamRole bridgeMediatedRole budgetedRole
        scopedRole coarsenedRole outsideRoleScope blockedNonClosure) := by
  refine ⟨role_descends_iff_no_split q role hq,
    has_role_split_iff_not_empty q role, ?_, ?_⟩
  · exact ⟨role_extension_strict_of_split q role,
      role_split_of_strict_extension q role⟩
  · intro hsplit
    exact Or.inl (role_extension_strict_of_split q role hsplit)


/-- The joint role layer is the coarsest map carrying both access and role. -/
theorem role_layer_extension_coarsest {H Q S T : Type}
    (q : H → Q) (role : H → S) (p : H → T)
    (a : T → Q) (b : T → S)
    (hq : q = a ∘ p) (hrole : role = b ∘ p) :
    roleLayerExtension q role = (fun t => (a t, b t)) ∘ p := by
  funext h
  exact Prod.ext (congrFun hq h) (congrFun hrole h)

/-- F24 including the joint role layer's coarsest-refinement equation. -/
theorem paper_layer_multiplicity_with_minimality {H Q S : Type}
    (q : H → Q) (role : H → S) (hq : Function.Surjective q)
    (memoryLayer hiddenUpstreamRole bridgeMediatedRole budgetedRole scopedRole
      coarsenedRole outsideRoleScope blockedNonClosure : Prop) :
    ((RoleDescends q role ↔ RoleObstructionEmpty q role) ∧
    (HasRoleSplit q role ↔ ¬ RoleObstructionEmpty q role) ∧
    (HasRoleSplit q role ↔
      StrictAccessExtension q (roleLayerExtension q role)) ∧
    (HasRoleSplit q role →
      LayerDecisionCosted
        (StrictAccessExtension q (roleLayerExtension q role))
        memoryLayer hiddenUpstreamRole bridgeMediatedRole budgetedRole
        scopedRole coarsenedRole outsideRoleScope blockedNonClosure)) ∧
    (∀ {T : Type} (p : H → T) (a : T → Q) (b : T → S),
      q = a ∘ p → role = b ∘ p →
        roleLayerExtension q role = (fun t => (a t, b t)) ∘ p) := by
  exact ⟨paper_layer_multiplicity q role hq memoryLayer hiddenUpstreamRole
      bridgeMediatedRole budgetedRole scopedRole coarsenedRole outsideRoleScope
      blockedNonClosure,
    fun p a b hqa hrb => role_layer_extension_coarsest q role p a b hqa hrb⟩

/-- The image predicate of the paired role layer. -/
def RoleLayerRange {H Q S : Type} (q : H → Q) (role : H → S) :
    Q × S → Prop :=
  fun z => ∃ h, roleLayerExtension q role h = z

/-- The paired role layer viewed as a surjection onto its actual image. -/
def roleLayerCorestriction {H Q S : Type} (q : H → Q) (role : H → S) :
    H → {z : Q × S // RoleLayerRange q role z} :=
  fun h => ⟨roleLayerExtension q role h, ⟨h, rfl⟩⟩

/-- The corestricted role layer factors through any surjective package
carrying both the old quotient and the role. -/
theorem role_layer_corestriction_coarsest {H Q S T : Type}
    (q : H → Q) (role : H → S) (p : H → T)
    (a : T → Q) (b : T → S) (hp : Function.Surjective p)
    (hq : q = a ∘ p) (hrole : role = b ∘ p) :
    Function.Surjective (roleLayerCorestriction q role) ∧
    ∃ g : T → {z : Q × S // RoleLayerRange q role z},
      g ∘ p = roleLayerCorestriction q role := by
  have hpair := role_layer_extension_coarsest q role p a b hq hrole
  constructor
  · rintro ⟨z, ⟨h, hh⟩⟩
    refine ⟨h, ?_⟩
    apply Subtype.ext
    exact hh
  · let g : T → {z : Q × S // RoleLayerRange q role z} := fun t =>
      ⟨(a t, b t), by
        obtain ⟨h, rfl⟩ := hp t
        exact ⟨h, congrFun hpair h⟩⟩
    refine ⟨g, ?_⟩
    funext h
    apply Subtype.ext
    exact (congrFun hpair h).symm

/-- F24 including the surjective corestriction form of minimality. -/
theorem paper_layer_multiplicity_with_corestriction {H Q S : Type}
    (q : H → Q) (role : H → S) (hq : Function.Surjective q)
    (memoryLayer hiddenUpstreamRole bridgeMediatedRole budgetedRole scopedRole
      coarsenedRole outsideRoleScope blockedNonClosure : Prop) :
    ((RoleDescends q role ↔ RoleObstructionEmpty q role) ∧
    (HasRoleSplit q role ↔ ¬ RoleObstructionEmpty q role) ∧
    (HasRoleSplit q role ↔
      StrictAccessExtension q (roleLayerExtension q role)) ∧
    (HasRoleSplit q role →
      LayerDecisionCosted
        (StrictAccessExtension q (roleLayerExtension q role))
        memoryLayer hiddenUpstreamRole bridgeMediatedRole budgetedRole
        scopedRole coarsenedRole outsideRoleScope blockedNonClosure)) ∧
    (∀ {T : Type} (p : H → T) (a : T → Q) (b : T → S),
      q = a ∘ p → role = b ∘ p →
        roleLayerExtension q role = (fun t => (a t, b t)) ∘ p) ∧
    Function.Surjective (roleLayerCorestriction q role) ∧
    (∀ {T : Type} (p : H → T) (a : T → Q) (b : T → S),
      Function.Surjective p → q = a ∘ p → role = b ∘ p →
      ∃ g : T → {z : Q × S // RoleLayerRange q role z},
        g ∘ p = roleLayerCorestriction q role) := by
  rcases paper_layer_multiplicity_with_minimality q role hq memoryLayer
    hiddenUpstreamRole bridgeMediatedRole budgetedRole scopedRole coarsenedRole
    outsideRoleScope blockedNonClosure with ⟨hcore, hminimal⟩
  refine ⟨hcore, hminimal, ?_, ?_⟩
  · intro z
    rcases z with ⟨z, h, hh⟩
    refine ⟨h, ?_⟩
    apply Subtype.ext
    exact hh
  · intro T p a b hp hqa hrole
    exact (role_layer_corestriction_coarsest q role p a b hp hqa hrole).2

/-- F24 with the role-split implication and the coarsest surjective role
quotient, stated without the optional layer-decision disjunction. -/
theorem paper_layer_multiplicity_role_split_corestriction {H Q S : Type}
    (q : H → Q) (role : H → S) (hq : Function.Surjective q) :
    (RoleDescends q role ↔ RoleObstructionEmpty q role) ∧
    (HasRoleSplit q role ↔ ¬ RoleObstructionEmpty q role) ∧
    (HasRoleSplit q role →
      StrictAccessExtension q (roleLayerExtension q role)) ∧
    (∀ {T : Type} (p : H → T) (a : T → Q) (b : T → S),
      q = a ∘ p → role = b ∘ p →
        roleLayerExtension q role = (fun t => (a t, b t)) ∘ p) ∧
    Function.Surjective (roleLayerCorestriction q role) ∧
    (∀ {T : Type} (p : H → T) (a : T → Q) (b : T → S),
      Function.Surjective p → q = a ∘ p → role = b ∘ p →
      ∃ g : T → {z : Q × S // RoleLayerRange q role z},
        g ∘ p = roleLayerCorestriction q role) := by
  refine ⟨role_descends_iff_no_split q role hq,
    has_role_split_iff_not_empty q role,
    role_extension_strict_of_split q role,
    (fun p a b hqa hrb => role_layer_extension_coarsest q role p a b hqa hrb),
    ?_, ?_⟩
  · intro z
    rcases z with ⟨z, h, hh⟩
    refine ⟨h, ?_⟩
    apply Subtype.ext
    exact hh
  · intro T p a b hp hqa hrb
    exact (role_layer_corestriction_coarsest q role p a b hp hqa hrb).2

/-- F24 with strictness equivalent to role splitting, plus both coarsest
factorization forms. -/
theorem paper_layer_multiplicity_strict_iff_corestriction {H Q S : Type}
    (q : H → Q) (role : H → S) (hq : Function.Surjective q) :
    (RoleDescends q role ↔ RoleObstructionEmpty q role) ∧
    (HasRoleSplit q role ↔ ¬ RoleObstructionEmpty q role) ∧
    (StrictAccessExtension q (roleLayerExtension q role) ↔
      HasRoleSplit q role) ∧
    (∀ {T : Type} (p : H → T) (a : T → Q) (b : T → S),
      q = a ∘ p → role = b ∘ p →
        roleLayerExtension q role = (fun t => (a t, b t)) ∘ p) ∧
    Function.Surjective (roleLayerCorestriction q role) ∧
    (∀ {T : Type} (p : H → T) (a : T → Q) (b : T → S),
      Function.Surjective p → q = a ∘ p → role = b ∘ p →
      ∃ g : T → {z : Q × S // RoleLayerRange q role z},
        g ∘ p = roleLayerCorestriction q role) := by
  rcases paper_layer_multiplicity_role_split_corestriction q role hq with
    ⟨hdescent, hsplit, hstrict, hminimal, hsurj, hcorestrict⟩
  exact ⟨hdescent, hsplit,
    ⟨role_split_of_strict_extension q role, hstrict⟩,
    hminimal, hsurj, hcorestrict⟩

end SixBirdsMetaMath.FoundationsIV.Access.LayerMultiplicity
