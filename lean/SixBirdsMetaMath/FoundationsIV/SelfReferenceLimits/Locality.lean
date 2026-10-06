import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F45 Locality / Domain of Dependence.

Locality is modeled as target sufficiency of a declared local past/interface
quotient. A domain of dependence is a minimal declared local quotient sufficient
for the target family.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Locality

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- A target is local to a declared local past/interface quotient when it
descends through that quotient. -/
def LocalToDomain {H L T : Type} (localQuotient : H → L) (target : H → T) :
    Prop :=
  Descends localQuotient (fun h : H => h) target

/-- Locality split-pair obstruction: same local data but different target. -/
def LocalityObstruction {H L T : Type} (localQuotient : H → L)
    (target : H → T) : (H × H) → Prop :=
  splitPairObstruction localQuotient (fun h : H => h) target

/-- No locality obstruction is present. -/
def LocalityObstructionEmpty {H L T : Type} (localQuotient : H → L)
    (target : H → T) : Prop :=
  ObstructionEmpty (LocalityObstruction localQuotient target)

/-- A target family is represented by a joint signature and is local exactly
when that signature descends through the local quotient. -/
def TargetFamilyLocal {H L Signature : Type} (localQuotient : H → L)
    (signature : H → Signature) : Prop :=
  LocalToDomain localQuotient signature

/-- Target-family locality obstruction. -/
def TargetFamilyLocalityObstruction {H L Signature : Type}
    (localQuotient : H → L) (signature : H → Signature) :
    (H × H) → Prop :=
  LocalityObstruction localQuotient signature

/-- No target-family locality obstruction is present. -/
def TargetFamilyLocalityObstructionEmpty {H L Signature : Type}
    (localQuotient : H → L) (signature : H → Signature) : Prop :=
  LocalityObstructionEmpty localQuotient signature

/-- A local dynamic law exists when the updated target quotient descends through
the local source quotient. -/
def DynamicLocality {H L H' Q' : Type} (localQuotient : H → L)
    (update : H → H') (targetQuotient : H' → Q') : Prop :=
  Descends localQuotient update targetQuotient

/-- Dynamic locality obstruction: same local source data but different updated
target quotient. -/
def DynamicLocalityObstruction {H L H' Q' : Type} (localQuotient : H → L)
    (update : H → H') (targetQuotient : H' → Q') : (H × H) → Prop :=
  splitPairObstruction localQuotient update targetQuotient

/-- No dynamic locality obstruction is present. -/
def DynamicLocalityObstructionEmpty {H L H' Q' : Type}
    (localQuotient : H → L) (update : H → H')
    (targetQuotient : H' → Q') : Prop :=
  ObstructionEmpty (DynamicLocalityObstruction localQuotient update targetQuotient)

/-- The smaller local quotient is realized from the larger one; the larger
domain carries at least as much local source data. -/
def DomainRefinement {H LSmall LLarge : Type} (smaller : H → LSmall)
    (larger : H → LLarge) : Prop :=
  Descends larger (fun h : H => h) smaller

/-- A sufficient domain is a declared domain whose local quotient carries the
target family. -/
def SufficientDomain {H L Signature : Type} (localQuotient : H → L)
    (signature : H → Signature) : Prop :=
  TargetFamilyLocal localQuotient signature

/-- Minimal domain of dependence over a declared domain class and strict-smaller
relation. -/
def MinimalDomainOfDependence {H L Signature : Type} (localQuotient : H → L)
    (signature : H → Signature)
    (DomainClass : {L' : Type} → (H → L') → Prop)
    (StrictlySmaller : {L₁ L₂ : Type} → (H → L₁) → (H → L₂) → Prop) :
    Prop :=
  DomainClass localQuotient ∧
    SufficientDomain localQuotient signature ∧
      ∀ (L' : Type) (candidate : H → L'),
        DomainClass candidate →
          StrictlySmaller candidate localQuotient →
            ¬ SufficientDomain candidate signature

/-- A sufficient but nonminimal locality claim. -/
def NonminimalLocality {H L Signature : Type} (localQuotient : H → L)
    (signature : H → Signature)
    (DomainClass : {L' : Type} → (H → L') → Prop)
    (StrictlySmaller : {L₁ L₂ : Type} → (H → L₁) → (H → L₂) → Prop) :
    Prop :=
  DomainClass localQuotient ∧
    SufficientDomain localQuotient signature ∧
      ∃ (L' : Type), ∃ candidate : H → L',
        DomainClass candidate ∧
          StrictlySmaller candidate localQuotient ∧
            SufficientDomain candidate signature

/-- Nonlocality relative to a declared domain class. -/
def NonlocalRelativeToClass {H Signature : Type} (signature : H → Signature)
    (DomainClass : {L' : Type} → (H → L') → Prop) : Prop :=
  ∀ (L' : Type) (candidate : H → L'),
    DomainClass candidate → ¬ SufficientDomain candidate signature

/-- Finite propagation relative to a declared domain family: each indexed
target is carried by the actual local quotient selected by its radius.
The local quotient cannot be replaced by an unrelated existential witness.
The radius and carrying discipline remain supplied application data. -/
def FinitePropagation {Index H Domain Target : Type}
    (Local : Domain → Type) (localAt : (d : Domain) → H → Local d)
    (radius : Index → Domain)
    (targetAt : Index → H → Target)
    (LocalCarries : {L : Type} → (H → L) → (H → Target) → Prop) : Prop :=
  ∀ n, LocalCarries (localAt (radius n)) (targetAt n)

/-- A constant local domain cannot carry the changing Boolean target. This
would incorrectly pass if the local quotient could be chosen independently
of the declared domain, using the identity map on Bool. -/
theorem finite_propagation_constant_domain_cannot_recover_bool :
    ¬ FinitePropagation (fun _ : Unit => Unit)
      (fun (_ : Unit) (_ : Bool) => ()) (fun _ : Unit => ())
      (fun (_ : Unit) (b : Bool) => b)
      (fun {_} q t => LocalToDomain q t) := by
  intro h
  obtain ⟨f, hf⟩ := h ()
  have hfalse := congrFun hf false
  have htrue := congrFun hf true
  have hbad : (false : Bool) = true := hfalse.symm.trans htrue
  cases hbad

/-- Probabilistic locality: the target law/kernel descends through the local
quotient. -/
def ProbabilisticLocality {H L Law : Type} (localQuotient : H → L)
    (kernel : H → Law) : Prop :=
  Descends localQuotient (fun h : H => h) kernel

/-- Budgeted locality: exact locality may fail, but local residuals are within
the declared budget. -/
def BudgetedLocality {Index Residual Budget : Type} (residual : Index → Residual)
    (budget : Budget) (WithinBudget : Residual → Budget → Prop) : Prop :=
  ∀ i, WithinBudget (residual i) budget

/-- Emergent locality: a coarse target descends through a coarse local quotient,
without claiming microscopic locality. -/
def EmergentLocality {H LCoarse TCoarse : Type} (coarseLocal : H → LCoarse)
    (coarseTarget : H → TCoarse) : Prop :=
  LocalToDomain coarseLocal coarseTarget

/-- Canonical repair for locality failure: remember the local quotient and the
target signature. -/
def localDomainRepairQuotient {H L T : Type} (localQuotient : H → L)
    (target : H → T) : H → L × T :=
  sourceRepairQuotient localQuotient (fun h : H => h) target

/-- Source status vocabulary for locality claims. -/
inductive LocalityStatus where
  | exactLocality
  | minimalDomainOfDependence
  | nonminimalLocality
  | domainOfDependenceModuli
  | targetSpecificLocality
  | dynamicLocality
  | finitePropagation
  | nonlocalRelativeToDomain
  | hiddenNonlocalDependency
  | localInterfaceLeakage
  | targetOverreach
  | probabilisticLocality
  | budgetedLocality
  | emergentLocality
  | localDomainOnly
  | globalDomainObstructed
  | complementaryLocality
  | protocolLocalityArtifact
  | presentationLocalityArtifact
  | continuumLocalityFailure
  | localityRoleMismatch
  | irreduciblyNonlocal
  | localityOverread
deriving DecidableEq

/-- Meaning assignment for the F45 locality status vocabulary. -/
def LocalityStatusHolds (exact minimal nonminimal moduli targetSpecific dynamic
    finitePropagation nonlocal hidden leakage overreach probabilistic budgeted emergent
    localOnly globalObstructed complementary protocolArtifact presentationArtifact
    continuumFailure roleMismatch irreduciblyNonlocal overread : Prop) :
    LocalityStatus → Prop
  | LocalityStatus.exactLocality => exact
  | LocalityStatus.minimalDomainOfDependence => minimal
  | LocalityStatus.nonminimalLocality => nonminimal
  | LocalityStatus.domainOfDependenceModuli => moduli
  | LocalityStatus.targetSpecificLocality => targetSpecific
  | LocalityStatus.dynamicLocality => dynamic
  | LocalityStatus.finitePropagation => finitePropagation
  | LocalityStatus.nonlocalRelativeToDomain => nonlocal
  | LocalityStatus.hiddenNonlocalDependency => hidden
  | LocalityStatus.localInterfaceLeakage => leakage
  | LocalityStatus.targetOverreach => overreach
  | LocalityStatus.probabilisticLocality => probabilistic
  | LocalityStatus.budgetedLocality => budgeted
  | LocalityStatus.emergentLocality => emergent
  | LocalityStatus.localDomainOnly => localOnly
  | LocalityStatus.globalDomainObstructed => globalObstructed
  | LocalityStatus.complementaryLocality => complementary
  | LocalityStatus.protocolLocalityArtifact => protocolArtifact
  | LocalityStatus.presentationLocalityArtifact => presentationArtifact
  | LocalityStatus.continuumLocalityFailure => continuumFailure
  | LocalityStatus.localityRoleMismatch => roleMismatch
  | LocalityStatus.irreduciblyNonlocal => irreduciblyNonlocal
  | LocalityStatus.localityOverread => overread

/-- Exact locality iff the locality split-pair obstruction is empty. -/
theorem locality_iff_no_obstruction {H L T : Type} (localQuotient : H → L)
    (target : H → T) (hlocal : Function.Surjective localQuotient) :
    LocalToDomain localQuotient target ↔
      LocalityObstructionEmpty localQuotient target :=
  descent_repair_normal_form localQuotient (fun h : H => h) target hlocal

/-- Exact locality in explicit factorization form. -/
theorem locality_iff_factorization {H L T : Type} (localQuotient : H → L)
    (target : H → T) :
    LocalToDomain localQuotient target ↔
      ∃ targetBar : L → T, targetBar ∘ localQuotient = target := by
  constructor
  · intro hlocal
    rcases hlocal with ⟨targetBar, htargetBar⟩
    exact ⟨targetBar, by simpa [Function.comp] using htargetBar⟩
  · intro hfactor
    rcases hfactor with ⟨targetBar, htargetBar⟩
    exact ⟨targetBar, by simpa [Function.comp] using htargetBar⟩

/-- Target-family locality is the same descent theorem for the joint
signature. -/
theorem target_family_local_iff_no_obstruction {H L Signature : Type}
    (localQuotient : H → L) (signature : H → Signature)
    (hlocal : Function.Surjective localQuotient) :
    TargetFamilyLocal localQuotient signature ↔
      TargetFamilyLocalityObstructionEmpty localQuotient signature :=
  locality_iff_no_obstruction localQuotient signature hlocal

/-- Dynamic locality iff the dynamic split-pair obstruction is empty. -/
theorem dynamic_locality_iff_no_obstruction {H L H' Q' : Type}
    (localQuotient : H → L) (update : H → H')
    (targetQuotient : H' → Q') (hlocal : Function.Surjective localQuotient) :
    DynamicLocality localQuotient update targetQuotient ↔
      DynamicLocalityObstructionEmpty localQuotient update targetQuotient :=
  descent_repair_normal_form localQuotient update targetQuotient hlocal

/-- Minimal domain of dependence is sufficient locality plus no strictly smaller
declared sufficient domain. -/
theorem minimal_domain_iff_sufficient_and_no_smaller
    {H L Signature : Type} (localQuotient : H → L) (signature : H → Signature)
    (DomainClass : {L' : Type} → (H → L') → Prop)
    (StrictlySmaller : {L₁ L₂ : Type} → (H → L₁) → (H → L₂) → Prop) :
    MinimalDomainOfDependence localQuotient signature DomainClass StrictlySmaller ↔
      DomainClass localQuotient ∧
        SufficientDomain localQuotient signature ∧
          ∀ (L' : Type) (candidate : H → L'),
            DomainClass candidate →
              StrictlySmaller candidate localQuotient →
                ¬ SufficientDomain candidate signature := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- The local repair quotient retains the original local data. -/
theorem local_domain_repair_refines {H L T : Type} (localQuotient : H → L)
    (target : H → T) :
    SourceRefinement (localDomainRepairQuotient localQuotient target)
      localQuotient :=
  source_repair_refines localQuotient (fun h : H => h) target

/-- The local repair quotient carries the target, closing the locality
obstruction by construction. -/
theorem local_domain_repair_local {H L T : Type} (localQuotient : H → L)
    (target : H → T) :
    LocalToDomain (localDomainRepairQuotient localQuotient target) target :=
  source_repair_descends localQuotient (fun h : H => h) target

/--
Locality / Domain of Dependence Normal Form. A target or target family is local
to a declared domain exactly when it descends through that local quotient, or
equivalently when the same-local-data/different-target obstruction is empty.
A domain of dependence is a minimal sufficient domain in the declared domain
class; dynamic locality is the same descent criterion for updated targets.
-/
theorem locality_domain_of_dependence {H L T H' Q' Signature : Type}
    (localQuotient : H → L) (target : H → T) (signature : H → Signature)
    (update : H → H') (targetQuotient : H' → Q')
    (DomainClass : {L' : Type} → (H → L') → Prop)
    (StrictlySmaller : {L₁ L₂ : Type} → (H → L₁) → (H → L₂) → Prop)
    (hlocal : Function.Surjective localQuotient) :
    (LocalToDomain localQuotient target ↔
      LocalityObstructionEmpty localQuotient target) ∧
      (TargetFamilyLocal localQuotient signature ↔
        TargetFamilyLocalityObstructionEmpty localQuotient signature) ∧
        (DynamicLocality localQuotient update targetQuotient ↔
          DynamicLocalityObstructionEmpty localQuotient update targetQuotient) ∧
          (MinimalDomainOfDependence localQuotient signature DomainClass
              StrictlySmaller ↔
            DomainClass localQuotient ∧
              SufficientDomain localQuotient signature ∧
                ∀ (L' : Type) (candidate : H → L'),
                  DomainClass candidate →
                    StrictlySmaller candidate localQuotient →
                      ¬ SufficientDomain candidate signature) ∧
            LocalToDomain (localDomainRepairQuotient localQuotient target) target := by
  exact ⟨locality_iff_no_obstruction localQuotient target hlocal,
    target_family_local_iff_no_obstruction localQuotient signature hlocal,
    dynamic_locality_iff_no_obstruction localQuotient update targetQuotient hlocal,
    minimal_domain_iff_sufficient_and_no_smaller localQuotient signature
      DomainClass StrictlySmaller,
    local_domain_repair_local localQuotient target⟩

/-- Within a declared class containing the candidate, minimality means
locality and the absence of a smaller local candidate. -/
theorem minimal_domain_iff_target_family_local_no_smaller
    {H L Signature : Type} (localQuotient : H → L)
    (signature : H → Signature)
    (DomainClass : {L' : Type} → (H → L') → Prop)
    (StrictlySmaller : {L₁ L₂ : Type} → (H → L₁) → (H → L₂) → Prop)
    (hclass : DomainClass localQuotient) :
    MinimalDomainOfDependence localQuotient signature DomainClass
        StrictlySmaller ↔
      TargetFamilyLocal localQuotient signature ∧
        ∀ (L' : Type) (candidate : H → L'),
          DomainClass candidate →
            StrictlySmaller candidate localQuotient →
              ¬ TargetFamilyLocal candidate signature := by
  constructor
  · intro h
    exact ⟨h.2.1, h.2.2⟩
  · intro h
    exact ⟨hclass, h.1, h.2⟩

/-- F45 with explicit repair locality and minimality in the domain class. -/
theorem locality_domain_of_dependence_paper {H L T H' Q' Signature : Type}
    (localQuotient : H → L) (target : H → T) (signature : H → Signature)
    (update : H → H') (targetQuotient : H' → Q')
    (DomainClass : {L' : Type} → (H → L') → Prop)
    (StrictlySmaller : {L₁ L₂ : Type} → (H → L₁) → (H → L₂) → Prop)
    (hlocal : Function.Surjective localQuotient) :
    (LocalToDomain localQuotient target ↔
      LocalityObstructionEmpty localQuotient target) ∧
    (TargetFamilyLocal localQuotient signature ↔
      TargetFamilyLocalityObstructionEmpty localQuotient signature) ∧
    (DynamicLocality localQuotient update targetQuotient ↔
      DynamicLocalityObstructionEmpty localQuotient update targetQuotient) ∧
    LocalToDomain (localDomainRepairQuotient localQuotient target) target ∧
    (DomainClass localQuotient →
      (MinimalDomainOfDependence localQuotient signature DomainClass
          StrictlySmaller ↔
        TargetFamilyLocal localQuotient signature ∧
          ∀ (L' : Type) (candidate : H → L'),
            DomainClass candidate →
              StrictlySmaller candidate localQuotient →
                ¬ TargetFamilyLocal candidate signature)) := by
  rcases locality_domain_of_dependence localQuotient target signature update
      targetQuotient DomainClass StrictlySmaller hlocal with
    ⟨h1, h2, h3, _, hrepair⟩
  exact ⟨h1, h2, h3, hrepair,
    minimal_domain_iff_target_family_local_no_smaller localQuotient signature
      DomainClass StrictlySmaller⟩

/-- Strict factorization of a candidate through a proposed local domain. -/
def StrictDomainFactorization {H L₁ L₂ : Type}
    (candidate : H → L₁) (localQuotient : H → L₂) : Prop :=
  DomainRefinement candidate localQuotient ∧
    ¬ DomainRefinement localQuotient candidate

/-- A fiber-constant map factors through its source map when the history
carrier is inhabited, including when the quotient has unused values. -/
theorem factor_of_fiber_constancy_of_inhabited
    {H A B : Type} (h₀ : H) (p : H → A) (t : H → B)
    (hk : ∀ x y, p x = p y → t x = t y) :
    Descends p (fun h : H => h) t := by
  classical
  let f : A → B := fun a =>
    if ha : ∃ x : H, p x = a then t (Classical.choose ha) else t h₀
  refine ⟨f, ?_⟩
  funext x
  have hx : ∃ y : H, p y = p x := ⟨x, rfl⟩
  change f (p x) = t x
  dsimp [f]
  rw [dif_pos hx]
  exact hk (Classical.choose hx) x (Classical.choose_spec hx)

/-- With an inhabited history type, a declared class containing the signature
has a minimal factorization domain exactly at the signature's kernel. -/
theorem minimal_domain_strict_factorization_iff_same_fibers
    {H L Signature : Type} (h₀ : H)
    (localQuotient : H → L) (signature : H → Signature)
    (DomainClass : {L' : Type} → (H → L') → Prop)
    (hlocal : DomainClass localQuotient)
    (hsignature : DomainClass signature) :
    MinimalDomainOfDependence localQuotient signature DomainClass
        StrictDomainFactorization ↔
      ∀ x y, localQuotient x = localQuotient y ↔
        signature x = signature y := by
  constructor
  · intro hmin x y
    have hsig : TargetFamilyLocal localQuotient signature := hmin.2.1
    have hlocalSig : DomainRefinement localQuotient signature := by
      by_cases he : DomainRefinement localQuotient signature
      · exact he
      · exfalso
        apply hmin.2.2 Signature signature hsignature ⟨hsig, he⟩
        exact ⟨id, rfl⟩
    constructor
    · intro hxy
      obtain ⟨f, hf⟩ := hsig
      calc
        signature x = f (localQuotient x) := (congrFun hf x).symm
        _ = f (localQuotient y) := congrArg f hxy
        _ = signature y := congrFun hf y
    · intro hxy
      obtain ⟨f, hf⟩ := hlocalSig
      calc
        localQuotient x = f (signature x) := (congrFun hf x).symm
        _ = f (signature y) := congrArg f hxy
        _ = localQuotient y := congrFun hf y
  · intro hkernel
    have hsig : TargetFamilyLocal localQuotient signature :=
      factor_of_fiber_constancy_of_inhabited h₀ localQuotient signature
        (fun x y hxy => (hkernel x y).mp hxy)
    have hlocalSig : DomainRefinement localQuotient signature :=
      factor_of_fiber_constancy_of_inhabited h₀ signature localQuotient
        (fun x y hxy => (hkernel x y).mpr hxy)
    refine ⟨hlocal, hsig, ?_⟩
    intro L' candidate _ hstrict hcand
    obtain ⟨f, hf⟩ := hlocalSig
    obtain ⟨g, hg⟩ := hcand
    apply hstrict.2
    refine ⟨f ∘ g, ?_⟩
    funext x
    calc
      (f ∘ g) (candidate x) = f (signature x) := congrArg f (congrFun hg x)
      _ = localQuotient x := congrFun hf x

/-- The unqualified minimality/fiber-equivalence claim fails for an empty
history type: the empty map to Unit is strictly smaller than the empty map to
Empty because there is no map Unit to Empty. -/
theorem minimal_domain_same_fibers_empty_counterexample :
    (∀ x y : Empty,
      (Empty.elim : Empty → Empty) x = (Empty.elim : Empty → Empty) y ↔
        (fun _ : Empty => ()) x = (fun _ : Empty => ()) y) ∧
    ¬ MinimalDomainOfDependence (Empty.elim : Empty → Empty)
      (fun _ : Empty => ()) (fun {_} _ => True)
      StrictDomainFactorization := by
  constructor
  · intro x
    exact x.elim
  · intro hmin
    have hstrict : StrictDomainFactorization (fun _ : Empty => ())
        (Empty.elim : Empty → Empty) := by
      constructor
      · exact ⟨Empty.elim, rfl⟩
      · rintro ⟨f, _⟩
        exact (f ()).elim
    have hlocal : SufficientDomain (fun _ : Empty => ())
        (fun _ : Empty => ()) := ⟨id, rfl⟩
    exact hmin.2.2 Unit (fun _ : Empty => ()) trivial hstrict hlocal

theorem locality_domain_of_dependence_paper_strict {H L T H' Q' Signature : Type}
    (localQuotient : H → L) (target : H → T) (signature : H → Signature)
    (update : H → H') (targetQuotient : H' → Q')
    (DomainClass : {L' : Type} → (H → L') → Prop)
    (hlocal : Function.Surjective localQuotient) :
(    (LocalToDomain localQuotient target ↔
      LocalityObstructionEmpty localQuotient target) ∧
    (TargetFamilyLocal localQuotient signature ↔
      TargetFamilyLocalityObstructionEmpty localQuotient signature) ∧
    (DynamicLocality localQuotient update targetQuotient ↔
      DynamicLocalityObstructionEmpty localQuotient update targetQuotient) ∧
    LocalToDomain (localDomainRepairQuotient localQuotient target) target ∧
    (DomainClass localQuotient →
      (MinimalDomainOfDependence localQuotient signature DomainClass
          StrictDomainFactorization ↔
        TargetFamilyLocal localQuotient signature ∧
          ∀ (L' : Type) (candidate : H → L'),
            DomainClass candidate →
              StrictDomainFactorization candidate localQuotient →
                ¬ TargetFamilyLocal candidate signature))) ∧
    (∀ (_h₀ : H), DomainClass localQuotient → DomainClass signature →
      (MinimalDomainOfDependence localQuotient signature DomainClass
          StrictDomainFactorization ↔
        ∀ x y, localQuotient x = localQuotient y ↔
          signature x = signature y)) := by
  refine ⟨locality_domain_of_dependence_paper localQuotient target signature
    update targetQuotient DomainClass StrictDomainFactorization hlocal, ?_⟩
  intro h₀ hclass hsig
  exact minimal_domain_strict_factorization_iff_same_fibers h₀
    localQuotient signature DomainClass hclass hsig

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Locality
