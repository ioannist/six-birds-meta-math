import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.AOR.Cascades

namespace SixBirdsMetaMath.AOR.Refinement

open SixBirdsMetaMath.AOR.PreSB
open SixBirdsMetaMath.AOR.DefectStrata
open SixBirdsMetaMath.AOR.ResidualAtlas
open SixBirdsMetaMath.AOR.Cascades

universe u v

/-!
This retained adapter is synchronized with the maintained Needles version.
References below to semantic AOR modules absent from this namespace mean
`SixBirdsNeedles.AOR.*`; this module does not re-export those endpoints.

Legacy paper-index interface and integer-cost model. Its conditional cocone
and tag-level hierarchy declarations are not the revised theory's semantic
endpoints. Use `PolicyColimit`, `PolicyRefinement`, `RealAsymptotic`,
`RealLimits`, `CompactPolicyLimit`, and `OperationalHierarchy` through `AOR.Core`.
The original unrestricted scope/limit claims and literal strict hierarchy have
counterexamples retained elsewhere in the library.


AOR paper §7 "Refinement chains, colimits, and asymptotic discharge".

This module hosts the directed-cocomplete refinement category:
- `def:aor:refinement-morphism`                  — typed refinement morphisms
- `def:aor:refinement-kinds-six`                 — the six refinement kinds A1–A6
- `def:aor:refpresb-category`                    — `RefPreSB` directed category
- `thm:aor:refpresb-cocomplete`                  — directed colimits exist
- `def:aor:asymptotic-statuses`                  — `asymptotic_budgeted`, `summable`, `contractive`, `eventual_zero`
- `thm:aor:asymptotic-soundness`                 — implication chain + colimit AOR closure
- `def:aor:refinement-stable-aor`                — `RefStableAOR`
- `thm:aor:refinement-stable-characterisation`   — characterisation via colimit witnesses

Statements are paper-grounded against `paper/aor/aor_paper.tex` §7.
The directed-colimit statement is conditional on an actual universal cocone;
the base object of a chain is not a colimit construction.
-/

/--
`def:aor:refinement-kinds-six`.

The six disjoint A1--A6 refinement annotations.
-/
inductive refinementKindsSix where
  | scopeExpansion
  | recordFieldExpansion
  | stageGrowth
  | constraintTightening
  | morphismStrengthening
  | carrierRefinement

/-- Per-field A1--A6 annotations for the seventeen PreSB carrier fields. -/
structure FieldRefinementAnnotations where
  H : refinementKindsSix
  q : refinementKindsSix
  Q : refinementKindsSix
  Gamma : refinementKindsSix
  R : refinementKindsSix
  Creg : refinementKindsSix
  Src : refinementKindsSix
  Ifc : refinementKindsSix
  Obs : refinementKindsSix
  Stage : refinementKindsSix
  Constr : refinementKindsSix
  Rewrite : refinementKindsSix
  Hol : refinementKindsSix
  Res : refinementKindsSix
  Stat : refinementKindsSix
  NC : refinementKindsSix
  Meta : refinementKindsSix

/-- Identity-strengthening annotations for an identity refinement morphism. -/
def identityAnnotations : FieldRefinementAnnotations where
  H := refinementKindsSix.morphismStrengthening
  q := refinementKindsSix.morphismStrengthening
  Q := refinementKindsSix.morphismStrengthening
  Gamma := refinementKindsSix.morphismStrengthening
  R := refinementKindsSix.morphismStrengthening
  Creg := refinementKindsSix.morphismStrengthening
  Src := refinementKindsSix.morphismStrengthening
  Ifc := refinementKindsSix.morphismStrengthening
  Obs := refinementKindsSix.morphismStrengthening
  Stage := refinementKindsSix.morphismStrengthening
  Constr := refinementKindsSix.morphismStrengthening
  Rewrite := refinementKindsSix.morphismStrengthening
  Hol := refinementKindsSix.morphismStrengthening
  Res := refinementKindsSix.morphismStrengthening
  Stat := refinementKindsSix.morphismStrengthening
  NC := refinementKindsSix.morphismStrengthening
  Meta := refinementKindsSix.morphismStrengthening

/-- Composition of annotations records that the composite is a strengthened refinement. -/
def composeAnnotations (_a _b : FieldRefinementAnnotations) : FieldRefinementAnnotations :=
  identityAnnotations

/--
`def:aor:refinement-morphism`.

An annotated presentation is a PreSB morphism with one A1--A6 annotation for
each carrier field. Annotations are metadata, not part of categorical arrow
equality: the composition below resets them and therefore cannot have identity
laws on the full decorated structure. The category uses `toPreSB` arrows.
-/
structure refinementMorphism {mathfrakS : scopeRecord.{u}}
    (C C' : preSBCarrier mathfrakS) where
  toPreSB : morphismPreSB C C'
  annotations : FieldRefinementAnnotations

/-- Identity refinement morphism. -/
def refinementIdentity {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : refinementMorphism C C where
  toPreSB := identityMorphism C
  annotations := identityAnnotations

/-- Componentwise composition of refinement morphisms. -/
def refinementCompose {mathfrakS : scopeRecord.{u}} {C C' C'' : preSBCarrier mathfrakS}
    (g : refinementMorphism C' C'') (f : refinementMorphism C C') :
    refinementMorphism C C'' where
  toPreSB := composeMorphism g.toPreSB f.toPreSB
  annotations := composeAnnotations g.annotations f.annotations

/-- `def:aor:refpresb-category`. Fixed-scope category of underlying field maps.
The A1--A6 annotations remain in presentations, outside categorical equality. -/
structure RefPreSBCategory (mathfrakS : scopeRecord.{u}) where
  Obj : Type (u + 1)
  Hom : preSBCarrier mathfrakS → preSBCarrier mathfrakS → Type u
  id : ∀ C, Hom C C
  comp : ∀ {C C' C''}, Hom C' C'' → Hom C C' → Hom C C''
  left_id : ∀ {C D} (f : Hom C D), comp (id D) f = f
  right_id : ∀ {C D} (f : Hom C D), comp f (id C) = f
  assoc : ∀ {A B C D} (h : Hom C D) (g : Hom B C) (f : Hom A B),
    comp h (comp g f) = comp (comp h g) f

/-- The concrete `RefPreSB_mathfrakS` category. -/
def refpresbCategory (mathfrakS : scopeRecord.{u}) : RefPreSBCategory mathfrakS where
  Obj := preSBCarrier mathfrakS
  Hom := fun C C' => morphismPreSB C C'
  id := identityMorphism
  comp := fun g f => composeMorphism g f
  left_id := composeMorphism_left_id
  right_id := composeMorphism_right_id
  assoc := composeMorphism_assoc

/-- Directed poset data used to index refinement chains. -/
structure DirectedPoset where
  Index : Type v
  base : Index
  le : Index → Index → Prop
  refl : ∀ i, le i i
  trans : ∀ {i j k}, le i j → le j k → le i k
  directed : ∀ i j, ∃ k, le i k ∧ le j k

/-- A refinement chain in `RefPreSB_mathfrakS`. -/
structure RefinementChain (mathfrakS : scopeRecord.{u}) where
  shape : DirectedPoset.{v}
  obj : shape.Index → preSBCarrier mathfrakS
  map : ∀ {i j}, shape.le i j → morphismPreSB (obj i) (obj j)
  map_id : ∀ i : shape.Index, map (shape.refl i) = identityMorphism (obj i)
  map_comp : ∀ {i j k : shape.Index} (hij : shape.le i j) (hjk : shape.le j k),
    map (shape.trans hij hjk) = composeMorphism (map hjk) (map hij)

/-- A compatible thread through a refinement chain. -/
structure CompatibleThread {mathfrakS : scopeRecord.{u}}
    (chain : RefinementChain mathfrakS) where
  carrierThread : ∀ i, (chain.obj i).H
  compatible : ∀ {i j} (hij : chain.shape.le i j),
    (chain.map hij).H_map (carrierThread i) = carrierThread j

/-- A cocone commutes with every map in the directed refinement diagram. -/
structure RefinementCocone {mathfrakS : scopeRecord.{u}}
    (chain : RefinementChain mathfrakS) where
  vertex : preSBCarrier mathfrakS
  leg : ∀ i, morphismPreSB (chain.obj i) vertex
  commutes : ∀ {i j} (hij : chain.shape.le i j),
    leg i = composeMorphism (leg j) (chain.map hij)

/-- A colimit must factor every cocone, uniquely as an arrow. -/
structure RefinementColimit {mathfrakS : scopeRecord.{u}}
    (chain : RefinementChain mathfrakS) where
  cocone : RefinementCocone chain
  descend : ∀ other : RefinementCocone chain,
    ∃ f : morphismPreSB cocone.vertex other.vertex,
      (∀ i, other.leg i = composeMorphism f (cocone.leg i)) ∧
      ∀ g : morphismPreSB cocone.vertex other.vertex,
        (∀ i, other.leg i = composeMorphism g (cocone.leg i)) → g = f

/-- Proof package for directed cocompleteness of `RefPreSB`. -/
structure RefPreSBCocompleteWitness (mathfrakS : scopeRecord.{u}) : Prop where
  directed_colimits :
    ∀ chain : RefinementChain.{u,v} mathfrakS,
      Nonempty (RefinementColimit chain)

/--
`thm:aor:refpresb-cocomplete`.

The package is obtained only when a construction of universal cocones for
every chain is supplied. No such construction follows from directedness alone
for the current scope-indexed carrier class and refinement morphisms.
-/
theorem refpresbCocomplete (mathfrakS : scopeRecord.{u})
    (hConstruct : ∀ chain : RefinementChain.{u,v} mathfrakS,
      Nonempty (RefinementColimit chain)) :
    RefPreSBCocompleteWitness.{u,v} mathfrakS where
  directed_colimits := hConstruct

/--
`def:aor:asymptotic-statuses`.

The four asymptotic statuses extending AOR-8 at refinement-chain colimits.
-/
inductive asymptoticStatuses where
  | asymptoticBudgeted
  | summable
  | contractive
  | eventualZero

/--
Asymptotic downstream table for limit-stage residuals.

This table is intentionally separate from `Cascades.costTable`, which is
indexed only by the 11 base AOR-8 statuses.  The explicit §7 rows used here
are: contractive limit closes, asymptotic-budgeted limit tightens to summable,
and summable/eventual-zero limit close.
-/
def asymptoticCostTable
    (t : SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve)
    (s : asymptoticStatuses) :
    List (SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve × asymptoticStatuses) :=
  match t, s with
  | residualTypesTwelve.limit, asymptoticStatuses.asymptoticBudgeted =>
      [(residualTypesTwelve.limit, asymptoticStatuses.summable)]
  | residualTypesTwelve.limit, asymptoticStatuses.summable => []
  | residualTypesTwelve.limit, asymptoticStatuses.contractive => []
  | residualTypesTwelve.limit, asymptoticStatuses.eventualZero => []
  | _, _ => []

/-- Implication order among asymptotic statuses. -/
inductive asymptoticStatusImplies : asymptoticStatuses → asymptoticStatuses → Prop where
  | refl (s) : asymptoticStatusImplies s s
  | eventualZero_contracts :
      asymptoticStatusImplies asymptoticStatuses.eventualZero asymptoticStatuses.contractive
  | contractive_summable :
      asymptoticStatusImplies asymptoticStatuses.contractive asymptoticStatuses.summable
  | summable_budgeted :
      asymptoticStatusImplies asymptoticStatuses.summable asymptoticStatuses.asymptoticBudgeted
  | trans {a b c} :
      asymptoticStatusImplies a b → asymptoticStatusImplies b c →
        asymptoticStatusImplies a c

/-- Finite partial sum of a quantitative residual-cost sequence. -/
def cumulativeLimitCost (cost : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cumulativeLimitCost cost n + cost n

/-- A genuine uniform bound across all refinement stages. -/
def limitCostBounded (cost : Nat → Nat) : Prop :=
  ∃ B : Nat, ∀ n, cost n ≤ B

/-- A status is a quantitative certificate about the original residual
sequence. In particular, the weak `budgeted` status needs a *uniform* bound,
not a bound on one finite record's depth. -/
def closesLimitResidual (status : asymptoticStatuses) (cost : Nat → Nat) : Prop :=
  limitCostBounded cost ∧
    match status with
    | asymptoticStatuses.eventualZero => ∃ N, ∀ n, N ≤ n → cost n = 0
    | asymptoticStatuses.contractive =>
        ∃ N, ∀ n, N ≤ n →
          cost (n + 1) < cost n ∨ (cost n = 0 ∧ cost (n + 1) = 0)
    | asymptoticStatuses.summable =>
        ∃ B, ∀ n, cumulativeLimitCost cost n ≤ B
    | asymptoticStatuses.asymptoticBudgeted => True

/-- A zero-absorbing strict descent of natural-number costs reaches zero. -/
theorem contractiveCost_eventuallyZero (cost : Nat → Nat) (N : Nat)
    (hStep : ∀ n, N ≤ n →
      cost (n + 1) < cost n ∨ (cost n = 0 ∧ cost (n + 1) = 0)) :
    ∃ M, ∀ n, M ≤ n → cost n = 0 := by
  have hDecrease : ∀ k, cost (N + k) ≤ cost N - k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h := hStep (N + k) (by omega)
        rw [show N + (k + 1) = N + k + 1 by omega]
        omega
  refine ⟨N + cost N, ?_⟩
  intro n hn
  have h := hDecrease (n - N)
  rw [show N + (n - N) = n by omega] at h
  omega

/-- A cost sequence that vanishes from a stage onward has bounded partial sums. -/
theorem eventuallyZeroCost_summable (cost : Nat → Nat) (M : Nat)
    (hZero : ∀ n, M ≤ n → cost n = 0) :
    ∃ B, ∀ n, cumulativeLimitCost cost n ≤ B := by
  refine ⟨cumulativeLimitCost cost M, ?_⟩
  intro n
  have hMono : ∀ a b, a ≤ b → cumulativeLimitCost cost a ≤ cumulativeLimitCost cost b := by
    intro a b hab
    induction hab with
    | refl => exact Nat.le_refl _
    | @step b _ ih =>
        simp only [cumulativeLimitCost]
        omega
  rcases Nat.le_total n M with h | h
  · exact hMono n M h
  · have hConst : ∀ k, cumulativeLimitCost cost (M + k) =
        cumulativeLimitCost cost M := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          simp only [cumulativeLimitCost]
          change cumulativeLimitCost cost (M + k) + cost (M + k) =
            cumulativeLimitCost cost M
          rw [hZero (M + k) (by omega)]
          omega
    have := hConst (n - M)
    rw [show M + (n - M) = n by omega] at this
    omega

/-- The status implications justified by the quantitative definitions.
Colimit continuity remains a separate analytic obligation. -/
structure AsymptoticSoundnessWitness : Prop where
  status_requires_bound :
    ∀ status cost, closesLimitResidual status cost → limitCostBounded cost
  eventual_zero_implies_contractive :
    ∀ cost, closesLimitResidual asymptoticStatuses.eventualZero cost →
      closesLimitResidual asymptoticStatuses.contractive cost
  contractive_implies_summable :
    ∀ cost, closesLimitResidual asymptoticStatuses.contractive cost →
      closesLimitResidual asymptoticStatuses.summable cost
  summable_implies_budgeted :
    ∀ cost, closesLimitResidual asymptoticStatuses.summable cost →
      closesLimitResidual asymptoticStatuses.asymptoticBudgeted cost

theorem asymptoticSoundness : AsymptoticSoundnessWitness where
  status_requires_bound := by
    intro status cost h
    exact h.1
  eventual_zero_implies_contractive := by
    intro cost h
    obtain ⟨hBound, N, hZero⟩ := h
    refine ⟨hBound, N, ?_⟩
    intro n hn
    right
    exact ⟨hZero n hn, hZero (n + 1) (Nat.le_succ_of_le hn)⟩
  contractive_implies_summable := by
    intro cost h
    obtain ⟨hBound, N, hStep⟩ := h
    obtain ⟨M, hZero⟩ := contractiveCost_eventuallyZero cost N hStep
    exact ⟨hBound, eventuallyZeroCost_summable cost M hZero⟩
  summable_implies_budgeted := by
    intro cost h
    exact ⟨h.1, True.intro⟩

/-- Residual atoms surviving refinement must have actual quantitative
payment on their own cost sequence. -/
def colimitAtomsPaid {mathfrakS : scopeRecord.{u}}
    (C : AORCarrierWithDischarge mathfrakS) : Prop :=
  ∀ atom : sigmaResidual (aorInclusionObj C.toCarrier),
    ∃ status, closesLimitResidual status (C.limitCost atom)

/--
`def:aor:refinement-stable-aor`.

Refinement-stable AOR carriers are cascade-stable carriers whose colimit-stage
residual atoms are paid by asymptotic statuses.
-/
def refinementStableAOR {mathfrakS : scopeRecord.{u}}
    (C : AORCarrierWithDischarge mathfrakS) : Prop :=
  cascadeStableAOR C ∧ colimitAtomsPaid C

/-- Characterisation predicate for `RefStableAOR`. -/
def refinementStableCharacterisationPredicate {mathfrakS : scopeRecord.{u}}
    (C : AORCarrierWithDischarge mathfrakS) : Prop :=
  cascadeStablePredicate C ∧ colimitAtomsPaid C

/--
`thm:aor:refinement-stable-characterisation`.

Refinement stability is equivalent to cascade stability plus asymptotic
payment of every residual atom that survives a colimit step.
-/
theorem refinementStableCharacterisation {mathfrakS : scopeRecord.{u}}
    (C : AORCarrierWithDischarge mathfrakS) :
    refinementStableAOR C ↔ refinementStableCharacterisationPredicate C := by
  constructor
  · intro h
    exact ⟨(cascadeStableCharacterisation C).mp h.1, h.2⟩
  · intro h
    exact ⟨(cascadeStableCharacterisation C).mpr h.1, h.2⟩

/-- Scope used by the finite strictness counterexample carriers. -/
def counterexampleScope : scopeRecord where
  carrierClass := fun _ => True
  sourceLedger := fun _ => True
  interfaceFamily := fun _ => True
  routeRegistry := fun _ => True

/-- Residual marker for a finite cascade that still has a limit-payment obstruction. -/
inductive CounterexampleLimitResidual where
  | limitAtom

/-- Residual marker for an AOR object with a blocked cascade obligation. -/
inductive CounterexampleBlockedResidual where
  | blockedAtom

/-- Shared finite PreSB carrier skeleton for strictness examples. -/
def counterexampleCarrier (ResTy : Type) : preSBCarrier counterexampleScope where
  H := Unit
  H_admissible := True.intro
  quotient := Unit
  q := id
  Q := fun _ _ => True
  Gamma := Unit
  Gamma_admissible := True.intro
  R := Unit
  Creg := Unit
  Src := Unit
  Src_admissible := True.intro
  Ifc := Unit
  Ifc_admissible := True.intro
  Obs := Unit
  Stage := Unit
  Constr := Unit
  Rewrite := Unit
  Hol := Unit
  Res := ResTy
  Stat := Unit
  NC := Unit
  Meta := Unit
  declaredRecordsTyped := True
  citedRoutesAudited := True
  residualsStatused := True
  nonclaimsRegistered := True
  metaAuditDischarged := True

/-- AOR-only separation carrier: structurally zero, with a blocked residual marker. -/
def counterexampleAOROnly : aorSubcategory counterexampleScope :=
  ⟨counterexampleCarrier CounterexampleBlockedResidual, by
    exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩⟩

/-- Cascade-only separation carrier: finite cascade, with a limit-payment marker. -/
def counterexampleCascadeOnly : aorSubcategory counterexampleScope :=
  ⟨counterexampleCarrier CounterexampleLimitResidual, by
    exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩⟩

/-- Cascade-only separation carrier with an explicit residual discharge assignment. -/
def counterexampleCascadeOnlyWithDischarge : AORCarrierWithDischarge counterexampleScope where
  toCarrier := counterexampleCascadeOnly
  dischargeAssignment := fun _ => AOR8Status.zero
  limitCost := fun _ n => n

/-- AOR-only separation carrier with an explicit residual discharge assignment. -/
def counterexampleAOROnlyWithDischarge : AORCarrierWithDischarge counterexampleScope where
  toCarrier := counterexampleAOROnly
  dischargeAssignment := fun _ => AOR8Status.blocked
  limitCost := fun _ _ => 0

/-- Typed obstruction recording that a limit atom has no asymptotic-status discharge yet. -/
inductive LimitAsymptoticNonpayment {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Prop where
  | witness : C.Res → LimitAsymptoticNonpayment C

/-- Typed obstruction recording a blocked residual cascade obligation. -/
inductive BlockedCascadeNontermination {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Prop where
  | witness : C.Res → BlockedCascadeNontermination C

/-- The cascade-only example is cascade-stable in the finite §6 sense. -/
theorem counterexampleCascadeOnly_cascadeStable :
    cascadeStableAOR counterexampleCascadeOnlyWithDischarge := by
  intro atom
  exact ⟨reachableFromZero_zero (residualPrimaryType atom), residualRecordOfAtom_eventuallyEmpty atom⟩

/-- The quantitative cost `n` has no uniform bound, so this finite
cascade-stable carrier really does fail refinement stability. -/
theorem counterexampleCascadeOnly_notRefinementStable :
    ¬ refinementStableAOR counterexampleCascadeOnlyWithDischarge := by
  intro hRefined
  let atom : sigmaResidual (aorInclusionObj counterexampleCascadeOnly) :=
    sigmaResidual.dischargeStatusMissing residualTypesTwelve.limit
      CounterexampleLimitResidual.limitAtom
  obtain ⟨status, hPaid⟩ := hRefined.2 atom
  obtain ⟨B, hB⟩ := hPaid.1
  have hImpossible := hB (B + 1)
  simp [counterexampleCascadeOnlyWithDischarge] at hImpossible
  omega

/-- The cascade-only example carries the documented limit-payment obstruction. -/
theorem counterexampleCascadeOnly_limitObstruction :
    LimitAsymptoticNonpayment (aorInclusionObj counterexampleCascadeOnly) :=
  LimitAsymptoticNonpayment.witness CounterexampleLimitResidual.limitAtom

/-- The AOR-only example carries the documented blocked-cascade obstruction. -/
theorem counterexampleAOROnly_blockedObstruction :
    BlockedCascadeNontermination (aorInclusionObj counterexampleAOROnly) :=
  BlockedCascadeNontermination.witness CounterexampleBlockedResidual.blockedAtom

/-- Strict hierarchy statement over predicates, with named finite counterexample carriers. -/
structure HierarchyWitness (mathfrakS : scopeRecord.{u}) : Prop where
  refStable_subset_cascadeStable :
    ∀ C : AORCarrierWithDischarge mathfrakS, refinementStableAOR C → cascadeStableAOR C
  cascadeStable_subset_AOR :
    ∀ C : AORCarrierWithDischarge mathfrakS, cascadeStableAOR C →
      structuralDefectZero (aorInclusionObj C.toCarrier)
  first_strict_obligation :
    ∃ (mathfrakS' : scopeRecord.{0}) (C : AORCarrierWithDischarge.{0} mathfrakS'),
      cascadeStableAOR C ∧ ¬ refinementStableAOR C ∧
        LimitAsymptoticNonpayment (aorInclusionObj C.toCarrier)
  second_strict_obligation :
    ∃ (mathfrakS' : scopeRecord.{0}) (C : AORCarrierWithDischarge.{0} mathfrakS'),
      structuralDefectZero (aorInclusionObj C.toCarrier) ∧
        BlockedCascadeNontermination (aorInclusionObj C.toCarrier)

/--
`thm:aor:hierarchy`.

The refinement-stable predicate implies cascade-stability. The first named
carrier now has an unbounded quantitative refinement cost, so its failure of
refinement stability is proved. The second AOR-versus-cascade witness remains
a typed blocked marker, not a proved negation of cascade stability; that
strictness claim requires a separate semantic redesign of the cost table.
-/
theorem hierarchy (mathfrakS : scopeRecord.{u}) : HierarchyWitness mathfrakS where
  refStable_subset_cascadeStable := by
    intro C h
    exact h.1
  cascadeStable_subset_AOR := by
    intro C h
    exact C.toCarrier.2
  first_strict_obligation :=
    ⟨counterexampleScope, counterexampleCascadeOnlyWithDischarge,
      counterexampleCascadeOnly_cascadeStable,
      counterexampleCascadeOnly_notRefinementStable,
      counterexampleCascadeOnly_limitObstruction⟩
  second_strict_obligation :=
    ⟨counterexampleScope, counterexampleAOROnlyWithDischarge, counterexampleAOROnly.2,
      counterexampleAOROnly_blockedObstruction⟩

end SixBirdsMetaMath.AOR.Refinement
