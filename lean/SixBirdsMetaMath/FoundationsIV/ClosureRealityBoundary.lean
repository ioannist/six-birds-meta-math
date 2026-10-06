import SixBirdsMetaMath.AOR.ClSB
import SixBirdsNeedles.AOR.KernelReflection
import Mathlib.Data.Set.Basic

/-!
F53 Closure-Reality Boundary / retained Sat₅ and current AOR distinction.

The retained five-flag saturation in this module is Sat₅, with legacy Lean
names `ClSB` and `SixBirdsClosed`. Its fixed points are exactly carriers with
all five structural flags true. This is not the current evidence-preserving
AOR inference reflector: that reflector closes rules with evidence unchanged,
and full discharge requires separate supplied witnesses. The imported
accounting equivalence and concrete closed-but-unpaid control below make this
distinction explicit. The generic CER no-go results remain independent of it.
-/

namespace SixBirdsMetaMath.FoundationsIV.ClosureRealityBoundary

open SixBirdsMetaMath.AOR.PreSB
open SixBirdsMetaMath.AOR.ClSB

universe u

/-- Retained Sat₅ closedness on the declared scope; not current AOR inference closure. -/
def SixBirdsClosed {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Prop :=
  aorInclusionObj (clSBOperator C) = C

/-- Retained five-flag operational predicate, defined by structural zero defect.
It does not assert full discharge of the current AOR evidence ledger. -/
def FiniteAuditedOperationalRealisable {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Prop :=
  structuralDefectZero C

/-- Bare physical instantiation is an external predicate, independent of the retained Sat₅ five-flag discharge condition. -/
def BarePhysicalInstantiation {mathfrakS : scopeRecord.{u}}
    (Phys : preSBCarrier mathfrakS → Prop) (C : preSBCarrier mathfrakS) : Prop :=
  Phys C

/-- Bare physical realisability schema on a declared scope. The negative F53
direct theorem assumes reduct-stability data for such a schema, not a raw
counterexample. -/
abbrev BarePhysicalRealisability (mathfrakS : scopeRecord.{u}) : Type _ :=
  preSBCarrier mathfrakS → Prop

/-- Formal retained Sat₅ schema (legacy ClSB name) with an intended physical instantiation predicate; the converse assumes a formal-carrier gap. -/
abbrev ClSBSchema (mathfrakS : scopeRecord.{u}) : Type _ :=
  preSBCarrier mathfrakS → Prop

/-- The retained Sat₅ completion is Sat₅-fixed (legacy SixBirdsClosed). -/
def ClSBCompletionClosed {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Prop :=
  SixBirdsClosed (aorInclusionObj (clSBOperator C))

/-- A carrier has no retained Sat₅ defect when all five structural flags hold. -/
def ClosureDefectEmpty {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Prop :=
  SixBirdsClosed C

/-- A retained Sat₅ defect means the five structural flags do not all hold. The legacy ClSB completion exists even for a seed that is not Sat₅-fixed; this is not current AOR evidence accounting. -/
def ClosureDefectPresent {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Prop :=
  ¬ SixBirdsClosed C

/-- Direct CER counterexample: bare physical instantiation does not force Six
Birds closure. -/
def CERDirectCounterexample {mathfrakS : scopeRecord.{u}}
    (Phys : preSBCarrier mathfrakS → Prop) : Prop :=
  ∃ C : preSBCarrier mathfrakS, BarePhysicalInstantiation Phys C ∧
    ¬ SixBirdsClosed C

/-- Converse CER counterexample: Six Birds closure does not force bare physical
instantiation. -/
def CERConverseCounterexample {mathfrakS : scopeRecord.{u}}
    (Phys : preSBCarrier mathfrakS → Prop) : Prop :=
  ∃ C : preSBCarrier mathfrakS, SixBirdsClosed C ∧
    ¬ BarePhysicalInstantiation Phys C

/-- Opaque source-side marker: the bare physical realisability predicate is
stable under the reduct construction used in source 53.md. -/
opaque ReductStabilityAssumption {mathfrakS : scopeRecord.{u}}
    (P : BarePhysicalRealisability mathfrakS) : Prop

/-- Opaque source marker for the missing-physical-instantiation construction on a retained Sat₅ schema used in source 53.md. -/
opaque FormalCarrierGapAssumption {mathfrakS : scopeRecord.{u}}
    (S : ClSBSchema mathfrakS) : Prop

/-- Reduct-stability obstruction: from a bare physical realisability schema,
the source construction supplies a physically realised reduct whose closure
breaks. This models the reduct argument, rather than assuming a raw CER-direct
counterexample. -/
structure RealisabilityReductObstruction {mathfrakS : scopeRecord.{u}}
    (P : BarePhysicalRealisability mathfrakS) : Type _ where
  reductStable : ReductStabilityAssumption P
  reductCarrier : preSBCarrier mathfrakS
  reductRealisable : BarePhysicalInstantiation P reductCarrier
  reductBreaksClosure : ¬ SixBirdsClosed reductCarrier

/-- A formal retained Sat₅ schema supplies a Sat₅-fixed carrier with no bare physical instantiation, modeling the formal-carrier gap. -/
structure ClosureInstantiationGap {mathfrakS : scopeRecord.{u}}
    (S : ClSBSchema mathfrakS) : Type _ where
  formalGapAssumption : FormalCarrierGapAssumption S
  formalCarrier : preSBCarrier mathfrakS
  formalClosed : SixBirdsClosed formalCarrier
  missingPhysicalInstantiation : ¬ BarePhysicalInstantiation S formalCarrier

/-- Unrestricted CER direct schema. -/
def CERDirect {mathfrakS : scopeRecord.{u}}
    (Phys : preSBCarrier mathfrakS → Prop) : Prop :=
  ∀ C : preSBCarrier mathfrakS, BarePhysicalInstantiation Phys C → SixBirdsClosed C

/-- Unrestricted CER converse schema. -/
def CERConverse {mathfrakS : scopeRecord.{u}}
    (Phys : preSBCarrier mathfrakS → Prop) : Prop :=
  ∀ C : preSBCarrier mathfrakS, SixBirdsClosed C → BarePhysicalInstantiation Phys C

/-- Unrestricted CER equivalence schema. -/
def CEREq {mathfrakS : scopeRecord.{u}}
    (Phys : preSBCarrier mathfrakS → Prop) : Prop :=
  CERDirect Phys ∧ CERConverse Phys

/-- Legacy CERAOR equivalence: retained Sat₅ fixedness is equivalent to all five structural flags holding. This is not current AOR inference closure or full evidence discharge. -/
def CERAOR {mathfrakS : scopeRecord.{u}} (C : preSBCarrier mathfrakS) : Prop :=
  SixBirdsClosed C ↔ FiniteAuditedOperationalRealisable C

/-- Source status vocabulary for the closure-reality boundary. -/
inductive ClosureRealityStatus where
  | bareCERDirectFails
  | bareCERConverseFails
  | bareCEREqFails
  | clSBCompletionExists
  | closureDefectPresent
  | alreadyClosed
  | auditedOperationalRealisable
  | internalOperationalRealisable
  | physicalisationRequiresExtraAxiom
  | recordFullOperationalCarrier
  | hypotheticalClosure
  | recognitionContentNotAutomatic
deriving DecidableEq

/-- Meaning assignment for the F53 status vocabulary. -/
def ClosureRealityStatusHolds (directFails converseFails eqFails completionExists
    defectPresent alreadyClosed audited internal physicalisation recordFull hypothetical
    recognitionNotAutomatic : Prop) : ClosureRealityStatus → Prop
  | ClosureRealityStatus.bareCERDirectFails => directFails
  | ClosureRealityStatus.bareCERConverseFails => converseFails
  | ClosureRealityStatus.bareCEREqFails => eqFails
  | ClosureRealityStatus.clSBCompletionExists => completionExists
  | ClosureRealityStatus.closureDefectPresent => defectPresent
  | ClosureRealityStatus.alreadyClosed => alreadyClosed
  | ClosureRealityStatus.auditedOperationalRealisable => audited
  | ClosureRealityStatus.internalOperationalRealisable => internal
  | ClosureRealityStatus.physicalisationRequiresExtraAxiom => physicalisation
  | ClosureRealityStatus.recordFullOperationalCarrier => recordFull
  | ClosureRealityStatus.hypotheticalClosure => hypothetical
  | ClosureRealityStatus.recognitionContentNotAutomatic => recognitionNotAutomatic

/-- A PreSB carrier is fixed by retained Sat₅ (legacy ClSB) exactly when all five structural flags hold. -/
theorem clSB_fixed_iff_structural_defect_zero {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) :
    aorInclusionObj (clSBOperator C) = C ↔ structuralDefectZero C := by
  constructor
  · intro h
    rw [← h]
    exact (clSBOperator C).2
  · intro h
    cases C
    simp_all [structuralDefectZero, aorInclusionObj, clSBOperator, saturatedCarrier]


/-- Retained Sat₅ (legacy ClSB) sets all five structural flags, yielding a Sat₅-fixed carrier; it does not perform current AOR inference reflection. -/
theorem clSB_completion_closed {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) :
    ClSBCompletionClosed C := by
  exact (clSB_fixed_iff_structural_defect_zero
    (aorInclusionObj (clSBOperator C))).2 (clSBOperator C).2

/-- The legacy unit witnesses the retained Sat₅ completion map C → aorInclusionObj (clSBOperator C). -/
theorem clSB_reflection_unit_exists {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) :
    Nonempty (morphismPreSB C (aorInclusionObj (clSBOperator C))) := by
  exact ⟨reflectionUnit C⟩

/-- The retained Sat₅ legacy adjunction witness is available at every scope, separately from the current AOR inference reflector. -/
theorem clSB_adjoint_reflection {mathfrakS : scopeRecord.{u}} :
    ∃ _ : ClSBAdjunctionWitness mathfrakS, True :=
  clSBAdjunction mathfrakS

/-- Retained Sat₅ fixedness (legacy SixBirdsClosed/ClSB) is equivalent to all five structural flags holding (legacy FiniteAuditedOperationalRealisable). Neither side denotes current AOR inference closure or full evidence discharge. -/
theorem closed_iff_aor {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) :
    CERAOR C := by
  exact clSB_fixed_iff_structural_defect_zero C

/-- If a reduct/formal counterexample to CER-direct is supplied, the
unrestricted direct schema is false. -/
theorem cer_direct_fails_of_counterexample {mathfrakS : scopeRecord.{u}}
    (Phys : preSBCarrier mathfrakS → Prop) :
    CERDirectCounterexample Phys → ¬ CERDirect Phys := by
  intro hcounter hdirect
  rcases hcounter with ⟨C, hphys, hnotClosed⟩
  exact hnotClosed (hdirect C hphys)

/-- If a closed formal carrier without bare physical instantiation is supplied,
the unrestricted converse schema is false. -/
theorem cer_converse_fails_of_counterexample {mathfrakS : scopeRecord.{u}}
    (Phys : preSBCarrier mathfrakS → Prop) :
    CERConverseCounterexample Phys → ¬ CERConverse Phys := by
  intro hcounter hconverse
  rcases hcounter with ⟨C, hclosed, hnotPhys⟩
  exact hnotPhys (hconverse C hclosed)

/-- The reduct-stability structural obstruction derives the direct CER
counterexample used by the no-go theorem. -/
theorem cer_direct_counterexample_of_reduct_obstruction
    {mathfrakS : scopeRecord.{u}} (P : BarePhysicalRealisability mathfrakS)
    (h : RealisabilityReductObstruction P) :
    CERDirectCounterexample P := by
  exact ⟨h.reductCarrier, h.reductRealisable, h.reductBreaksClosure⟩

/-- The formal-carrier gap derives the converse CER counterexample used by the
no-go theorem. -/
theorem cer_converse_counterexample_of_instantiation_gap
    {mathfrakS : scopeRecord.{u}} (S : ClSBSchema mathfrakS)
    (h : ClosureInstantiationGap S) :
    CERConverseCounterexample S := by
  exact ⟨h.formalCarrier, h.formalClosed, h.missingPhysicalInstantiation⟩

/-- No-go theorem for unrestricted CER-direct, derived from the modeled
reduct-stability obstruction rather than from a raw counterexample
hypothesis. -/
theorem cer_direct_no_go {mathfrakS : scopeRecord.{u}}
    (P : BarePhysicalRealisability mathfrakS)
    (h : RealisabilityReductObstruction P) :
    ¬ CERDirect P := by
  exact cer_direct_fails_of_counterexample P
    (cer_direct_counterexample_of_reduct_obstruction P h)

/-- No-go theorem for unrestricted CER-converse, derived from the modeled
formal-carrier instantiation gap rather than from a raw counterexample
hypothesis. -/
theorem cer_converse_no_go {mathfrakS : scopeRecord.{u}}
    (S : ClSBSchema mathfrakS) (h : ClosureInstantiationGap S) :
    ¬ CERConverse S := by
  exact cer_converse_fails_of_counterexample S
    (cer_converse_counterexample_of_instantiation_gap S h)

/-- Failure of either unrestricted direction blocks unrestricted CER
equivalence. -/
theorem cer_equivalence_fails_of_direct_counterexample {mathfrakS : scopeRecord.{u}}
    (Phys : preSBCarrier mathfrakS → Prop) :
    CERDirectCounterexample Phys → ¬ CEREq Phys := by
  intro hcounter hcer
  exact cer_direct_fails_of_counterexample Phys hcounter hcer.1

/-- The reduct-stability obstruction blocks unrestricted CER equivalence. -/
theorem cer_equivalence_fails_of_reduct_obstruction {mathfrakS : scopeRecord.{u}}
    (P : BarePhysicalRealisability mathfrakS)
    (h : RealisabilityReductObstruction P) :
    ¬ CEREq P := by
  intro hcer
  exact cer_direct_no_go P h hcer.1

/-- Reduct-stability and formal-carrier gap data derive the CER no-go conclusions. The positive legacy clause identifies retained Sat₅ fixedness with all five structural flags holding and supplies Sat₅ completion/unit/adjunction witnesses. It does not identify Sat₅ with the current AOR inference reflector or its evidence discharge. -/
theorem closure_reality_boundary {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) (Phys : preSBCarrier mathfrakS → Prop)
    (hDirectObstruction : RealisabilityReductObstruction Phys)
    (hConverseGap : ClosureInstantiationGap Phys) :
    CERAOR C ∧
      ClSBCompletionClosed C ∧
        Nonempty (morphismPreSB C (aorInclusionObj (clSBOperator C))) ∧
          (∃ _ : ClSBAdjunctionWitness mathfrakS, True) ∧
            ¬ CERDirect Phys ∧
              ¬ CERConverse Phys ∧
                ¬ CEREq Phys := by
  refine ⟨closed_iff_aor C, ?_⟩
  refine ⟨clSB_completion_closed C, ?_⟩
  refine ⟨clSB_reflection_unit_exists C, ?_⟩
  refine ⟨clSB_adjoint_reflection, ?_⟩
  refine ⟨cer_direct_no_go Phys hDirectObstruction, ?_⟩
  refine ⟨cer_converse_no_go Phys hConverseGap, ?_⟩
  exact cer_equivalence_fails_of_reduct_obstruction Phys hDirectObstruction

/-- Failure of closure implying bare reality is exactly a closed carrier
without bare realisation. -/
theorem cer_converse_failure_iff_closed_not_bare
    {Carrier : Type} (Cl : Carrier → Carrier) (BareReal : Carrier → Prop) :
    ¬ (∀ C, Cl C = C → BareReal C) ↔
      ∃ C, Cl C = C ∧ ¬ BareReal C := by
  classical
  constructor
  · intro h
    exact Classical.byContradiction (fun hn =>
      h (fun C hc => Classical.byContradiction (fun hb =>
        hn ⟨C, hc, hb⟩)))
  · rintro ⟨C, hc, hb⟩ h
    exact hb (h C hc)

/-- Bare realisability relative to a chosen carrier means inclusion in it. -/
def CERBareRealBelow {X : Type} (C0 C : Set X) : Prop := C ⊆ C0

/-- Any nonfixed carrier of an extensive closure gives both CER failures.
Monotonicity and idempotence are included as the declared closure laws. -/
theorem cer_no_go_any_nontrivial_closure
    {X : Type} (Cl : Set X → Set X)
    (hext : ∀ A : Set X, A ⊆ Cl A)
    (_hmono : ∀ A B : Set X, A ⊆ B → Cl A ⊆ Cl B)
    (_hidem : ∀ A : Set X, Cl (Cl A) = Cl A)
    (C0 : Set X) (hnonfixed : Cl C0 ≠ C0) :
    (∀ Red : Set X → Set X,
      (∀ C : Set X, Red C ⊆ C) →
        ∀ C, CERBareRealBelow C0 C → CERBareRealBelow C0 (Red C)) ∧
    (CERBareRealBelow C0 C0 ∧ Cl C0 ≠ C0) ∧
    (Cl Set.univ = Set.univ ∧ ¬ CERBareRealBelow C0 Set.univ) := by
  have huniv : Cl Set.univ = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    exact hext Set.univ (Set.mem_univ x)
  refine ⟨?_, ⟨Set.Subset.rfl, hnonfixed⟩, huniv, ?_⟩
  · intro Red hred C hbare x hx
    exact hbare (hred C hx)
  · intro hbare
    have hC0 : C0 = Set.univ := Set.Subset.antisymm (Set.subset_univ C0) hbare
    apply hnonfixed
    rw [hC0]
    exact huniv

/-- A closure operator different from the identity has a carrier to which
the general direct and converse CER no-go applies. -/
theorem cer_no_go_of_nonidentity_closure
    {X : Type} (Cl : Set X → Set X)
    (hext : ∀ A : Set X, A ⊆ Cl A)
    (hmono : ∀ A B : Set X, A ⊆ B → Cl A ⊆ Cl B)
    (hidem : ∀ A : Set X, Cl (Cl A) = Cl A)
    (hnonidentity : Cl ≠ id) :
    ∃ C0 : Set X,
      Cl C0 ≠ C0 ∧
      (∀ Red : Set X → Set X,
        (∀ C : Set X, Red C ⊆ C) →
          ∀ C, CERBareRealBelow C0 C → CERBareRealBelow C0 (Red C)) ∧
      (CERBareRealBelow C0 C0 ∧ Cl C0 ≠ C0) ∧
      (Cl Set.univ = Set.univ ∧ ¬ CERBareRealBelow C0 Set.univ) := by
  classical
  have hex : ∃ C0 : Set X, Cl C0 ≠ C0 := by
    by_contra hnone
    apply hnonidentity
    funext C
    have hnot : ¬ Cl C ≠ C := by
      intro hne
      exact hnone ⟨C, hne⟩
    exact Classical.byContradiction hnot
  obtain ⟨C0, hnonfixed⟩ := hex
  exact ⟨C0, hnonfixed,
    cer_no_go_any_nontrivial_closure Cl hext hmono hidem C0 hnonfixed⟩

/-- Three records, represented by membership propositions for `d`, `e`,
and `f`. -/
abbrev FiniteCERCarrier := Prop × Prop × Prop

/-- The claim `e` needs the record `d`; closure adds `d` when `e` is present. -/
def finiteCERClosure (C : FiniteCERCarrier) : FiniteCERCarrier :=
  (C.1 ∨ C.2.1, C.2.1, C.2.2)

/-- Bare realisation permits only the realised-system records `d,e`. -/
def finiteCERBare (C : FiniteCERCarrier) : Prop := ¬ C.2.2

/-- Reduct forgets the closure-relevant record `d`. -/
def finiteCERReduct (C : FiniteCERCarrier) : FiniteCERCarrier :=
  (False, C.2.1, C.2.2)

/-- The paper's `C⁺={d,e}`, direct witness `{e}`, and converse witness `{f}`. -/
def finiteCERRich : FiniteCERCarrier := (True, True, False)
def finiteCERMissingD : FiniteCERCarrier := (False, True, False)
def finiteCERFormalOnly : FiniteCERCarrier := (False, False, True)

/-- Inclusion of the three record sets, coordinate by coordinate. -/
def finiteCERSubset (C D : FiniteCERCarrier) : Prop :=
  (C.1 → D.1) ∧ (C.2.1 → D.2.1) ∧ (C.2.2 → D.2.2)

/-- The finite model's operator is extensive, monotone and idempotent. -/
theorem finite_cer_closure_laws :
    (∀ C, finiteCERSubset C (finiteCERClosure C)) ∧
    (∀ C D, finiteCERSubset C D →
      finiteCERSubset (finiteCERClosure C) (finiteCERClosure D)) ∧
    (∀ C, finiteCERClosure (finiteCERClosure C) = finiteCERClosure C) := by
  constructor
  · intro C
    exact ⟨Or.inl, id, id⟩
  constructor
  · intro C D h
    exact ⟨fun hc => hc.elim (fun hd => Or.inl (h.1 hd))
      (fun he => Or.inr (h.2.1 he)), h.2.1, h.2.2⟩
  · intro C
    cases C with
    | mk d ef =>
      cases ef with
      | mk e f =>
        simp [finiteCERClosure]

/-- The finite model witnesses failure of both CER implications and
reduct-stability of bare realisation. -/
theorem finite_cer_model :
    (∀ C, finiteCERBare C → finiteCERBare (finiteCERReduct C)) ∧
    finiteCERBare finiteCERRich ∧
    finiteCERReduct finiteCERRich = finiteCERMissingD ∧
    finiteCERBare finiteCERMissingD ∧
    finiteCERClosure finiteCERMissingD ≠ finiteCERMissingD ∧
    finiteCERClosure finiteCERFormalOnly = finiteCERFormalOnly ∧
    ¬ finiteCERBare finiteCERFormalOnly := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C h
    exact h
  · simp [finiteCERBare, finiteCERRich]
  · rfl
  · simp [finiteCERBare, finiteCERMissingD]
  · intro h
    have hd := congrArg Prod.fst h
    simp [finiteCERClosure, finiteCERMissingD] at hd
  · simp [finiteCERClosure, finiteCERFormalOnly]
  · intro h
    exact h trivial

/-- The concrete three-record model refutes both unrestricted implications. -/
theorem finite_cer_no_go :
    ¬ (∀ C : FiniteCERCarrier,
        finiteCERBare C → finiteCERClosure C = C) ∧
    ¬ (∀ C : FiniteCERCarrier,
        finiteCERClosure C = C → finiteCERBare C) := by
  constructor
  · intro h
    exact finite_cer_model.2.2.2.2.1
      (h finiteCERMissingD finite_cer_model.2.2.2.1)
  · intro h
    exact finite_cer_model.2.2.2.2.2.2
      (h finiteCERFormalOnly finite_cer_model.2.2.2.2.2.1)

/-- The abstract reduct-obstruction hypotheses give a bare-real carrier
whose closure changes it. -/
theorem cer_direct_reduct_witness {Carrier : Type}
    (Cl Red : Carrier → Carrier) (BareReal : Carrier → Prop)
    (Cplus : Carrier) (h1 : BareReal Cplus)
    (h2 : ∀ C, BareReal C → BareReal (Red C))
    (h3 : Cl (Red Cplus) ≠ Red Cplus) :
    ∃ C, BareReal C ∧ Cl C ≠ C := by
  exact ⟨Red Cplus, h2 Cplus h1, h3⟩

/-- A closed non-bare carrier is the converse obstruction witness. -/
theorem cer_converse_closed_witness {Carrier : Type}
    (Cl : Carrier → Carrier) (BareReal : Carrier → Prop)
    (Cformal : Carrier) (hclosed : Cl Cformal = Cformal)
    (hnotBare : ¬ BareReal Cformal) :
    ∃ C, Cl C = C ∧ ¬ BareReal C := by
  exact ⟨Cformal, hclosed, hnotBare⟩

/-- The paper's `{d,e}` reduct supplies the abstract direct obstruction. -/
theorem finite_cer_direct_instance :
    ∃ C : FiniteCERCarrier,
      finiteCERBare C ∧ finiteCERClosure C ≠ C := by
  exact cer_direct_reduct_witness finiteCERClosure finiteCERReduct
    finiteCERBare finiteCERRich finite_cer_model.2.1 finite_cer_model.1
    (by rw [finite_cer_model.2.2.1]; exact finite_cer_model.2.2.2.2.1)

/-- The paper's `{f}` supplies the abstract converse obstruction. -/
theorem finite_cer_converse_instance :
    ∃ C : FiniteCERCarrier,
      finiteCERClosure C = C ∧ ¬ finiteCERBare C := by
  exact cer_converse_closed_witness finiteCERClosure finiteCERBare
    finiteCERFormalOnly finite_cer_model.2.2.2.2.2.1
    finite_cer_model.2.2.2.2.2.2

/-- The finite CER model has a genuine closure operator, reduct-stable bare
reality, and explicit direct and converse counterexamples. -/
theorem finite_cer_paper_bundle :
    (∀ C, finiteCERSubset C (finiteCERClosure C)) ∧
    (∀ C D, finiteCERSubset C D →
      finiteCERSubset (finiteCERClosure C) (finiteCERClosure D)) ∧
    (∀ C, finiteCERClosure (finiteCERClosure C) = finiteCERClosure C) ∧
    (∀ C, finiteCERBare C → finiteCERBare (finiteCERReduct C)) ∧
    finiteCERBare finiteCERRich ∧
    finiteCERReduct finiteCERRich = finiteCERMissingD ∧
    finiteCERBare finiteCERMissingD ∧
    finiteCERClosure finiteCERMissingD ≠ finiteCERMissingD ∧
    finiteCERClosure finiteCERFormalOnly = finiteCERFormalOnly ∧
    ¬ finiteCERBare finiteCERFormalOnly := by
  rcases finite_cer_closure_laws with ⟨hext, hmono, hidem⟩
  rcases finite_cer_model with ⟨hred, hrich, hforget, hbare, hdirect,
    hclosed, hconverse⟩
  exact ⟨hext, hmono, hidem, hred, hrich, hforget, hbare, hdirect,
    hclosed, hconverse⟩


/-- The general CER no-go needs only an extensive nonidentity operator;
monotonicity and idempotence play no role in either counterexample. -/
theorem cer_no_go_of_nonidentity_extensive_operator
    {X : Type} (Cl : Set X → Set X)
    (hext : ∀ A : Set X, A ⊆ Cl A) (hnonidentity : Cl ≠ id) :
    ∃ C0 : Set X,
      Cl C0 ≠ C0 ∧
      (∀ Red : Set X → Set X,
        (∀ C : Set X, Red C ⊆ C) →
          ∀ C, CERBareRealBelow C0 C → CERBareRealBelow C0 (Red C)) ∧
      (CERBareRealBelow C0 C0 ∧ Cl C0 ≠ C0) ∧
      (Cl Set.univ = Set.univ ∧ ¬ CERBareRealBelow C0 Set.univ) := by
  classical
  have hex : ∃ C0 : Set X, Cl C0 ≠ C0 := by
    by_contra hnone
    apply hnonidentity
    funext C
    exact Classical.byContradiction (fun hne => hnone ⟨C, hne⟩)
  obtain ⟨C0, hnonfixed⟩ := hex
  have huniv : Cl Set.univ = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    exact hext Set.univ (Set.mem_univ x)
  refine ⟨C0, hnonfixed, ?_, ⟨Set.Subset.rfl, hnonfixed⟩, huniv, ?_⟩
  · intro Red hred C hbare x hx
    exact hbare (hred C hx)
  · intro hbare
    have hC0 : C0 = Set.univ := Set.Subset.antisymm (Set.subset_univ C0) hbare
    apply hnonfixed
    rw [hC0]
    exact huniv

/-- Stability under every reduct that only forgets elements of a carrier. -/
def CERAllReductStable {X : Type} (BareReal : Set X → Prop) : Prop :=
  ∀ Red : Set X → Set X, (∀ C : Set X, Red C ⊆ C) →
    ∀ C, BareReal C → BareReal (Red C)

/-- Every extensive operator fixes the whole carrier, including the identity. -/
theorem cer_extensive_operator_fixes_univ {X : Type}
    (Cl : Set X → Set X) (hext : ∀ A : Set X, A ⊆ Cl A) :
    Cl Set.univ = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  exact hext Set.univ (Set.mem_univ x)

/-- The always-false predicate is stable under every reduct and refutes the
converse CER implication at the whole carrier for every extensive operator. -/
theorem cer_false_predicate_converse_failure {X : Type}
    (Cl : Set X → Set X) (hext : ∀ A : Set X, A ⊆ Cl A) :
    Cl Set.univ = Set.univ ∧
    CERAllReductStable (fun _ : Set X => False) ∧
    ¬ (Cl Set.univ = Set.univ → (fun _ : Set X => False) Set.univ) := by
  have huniv := cer_extensive_operator_fixes_univ Cl hext
  exact ⟨huniv, fun _ _ _ hfalse => hfalse, fun hconverse => hconverse huniv⟩

/-- A reduct-stable predicate refutes direct CER exactly when the extensive
operator is not the identity. -/
theorem cer_direct_failure_iff_nonidentity_extensive_operator {X : Type}
    (Cl : Set X → Set X) (hext : ∀ A : Set X, A ⊆ Cl A) :
    (∃ BareReal : Set X → Prop,
      CERAllReductStable BareReal ∧
      ¬ (∀ C : Set X, BareReal C → Cl C = C)) ↔ Cl ≠ id := by
  constructor
  · rintro ⟨BareReal, _, hfailure⟩ hidentity
    apply hfailure
    intro C _
    rw [hidentity]
    rfl
  · intro hnonidentity
    obtain ⟨C0, _, hstable, hbare, _⟩ :=
      cer_no_go_of_nonidentity_extensive_operator Cl hext hnonidentity
    exact ⟨CERBareRealBelow C0, hstable,
      fun hdirect => hbare.2 (hdirect C0 hbare.1)⟩

/-- One predicate stable under every reduct refutes both CER implications
exactly when the extensive operator is not the identity. -/
theorem cer_both_failures_iff_nonidentity_extensive_operator {X : Type}
    (Cl : Set X → Set X) (hext : ∀ A : Set X, A ⊆ Cl A) :
    (∃ BareReal : Set X → Prop,
      CERAllReductStable BareReal ∧
      ¬ (∀ C : Set X, BareReal C → Cl C = C) ∧
      ¬ (∀ C : Set X, Cl C = C → BareReal C)) ↔ Cl ≠ id := by
  constructor
  · rintro ⟨BareReal, hstable, hdirect, _⟩
    exact (cer_direct_failure_iff_nonidentity_extensive_operator Cl hext).mp
      ⟨BareReal, hstable, hdirect⟩
  · intro hnonidentity
    obtain ⟨C0, _, hstable, hbare, huniv, hnotBare⟩ :=
      cer_no_go_of_nonidentity_extensive_operator Cl hext hnonidentity
    exact ⟨CERBareRealBelow C0, hstable,
      fun hdirect => hbare.2 (hdirect C0 hbare.1),
      fun hconverse => hnotBare (hconverse Set.univ huniv)⟩

/-- The converse can fail for every extensive operator; direct failure and
simultaneous failure by a reduct-stable predicate characterize nonidentity. -/
theorem cer_no_go_iff_nonidentity_extensive_operator {X : Type}
    (Cl : Set X → Set X) (hext : ∀ A : Set X, A ⊆ Cl A) :
    (Cl Set.univ = Set.univ ∧
      CERAllReductStable (fun _ : Set X => False) ∧
      ¬ (Cl Set.univ = Set.univ → (fun _ : Set X => False) Set.univ)) ∧
    ((∃ BareReal : Set X → Prop,
      CERAllReductStable BareReal ∧
      ¬ (∀ C : Set X, BareReal C → Cl C = C)) ↔ Cl ≠ id) ∧
    ((∃ BareReal : Set X → Prop,
      CERAllReductStable BareReal ∧
      ¬ (∀ C : Set X, BareReal C → Cl C = C) ∧
      ¬ (∀ C : Set X, Cl C = C → BareReal C)) ↔ Cl ≠ id) := by
  exact ⟨cer_false_predicate_converse_failure Cl hext,
    cer_direct_failure_iff_nonidentity_extensive_operator Cl hext,
    cer_both_failures_iff_nonidentity_extensive_operator Cl hext⟩

/-- Any nonidentity operator has a nonfixed carrier whose inclusion predicate
is stable under every reduct and refutes direct CER. -/
theorem cer_direct_no_go_of_nonidentity_operator
    {X : Type} (Cl : Set X → Set X) (hnonidentity : Cl ≠ id) :
    ∃ C0 : Set X,
      Cl C0 ≠ C0 ∧
      (∀ Red : Set X → Set X,
        (∀ C : Set X, Red C ⊆ C) →
          ∀ C, CERBareRealBelow C0 C → CERBareRealBelow C0 (Red C)) ∧
      (CERBareRealBelow C0 C0 ∧ Cl C0 ≠ C0) := by
  classical
  have hex : ∃ C0 : Set X, Cl C0 ≠ C0 := by
    by_contra hnone
    apply hnonidentity
    funext C
    exact Classical.byContradiction (fun hne => hnone ⟨C, hne⟩)
  obtain ⟨C0, hnonfixed⟩ := hex
  refine ⟨C0, hnonfixed, ?_, ⟨Set.Subset.rfl, hnonfixed⟩⟩
  intro Red hred C hbare x hx
  exact hbare (hred C hx)

/-- For any operator, a reduct-stable predicate refutes direct CER exactly
when the operator is not the identity. -/
theorem cer_direct_failure_iff_nonidentity_operator {X : Type}
    (Cl : Set X → Set X) :
    (∃ BareReal : Set X → Prop,
      CERAllReductStable BareReal ∧
      ¬ (∀ C : Set X, BareReal C → Cl C = C)) ↔ Cl ≠ id := by
  constructor
  · rintro ⟨BareReal, _, hfailure⟩ hidentity
    apply hfailure
    intro C _
    rw [hidentity]
    rfl
  · intro hnonidentity
    obtain ⟨C0, _, hstable, hbare⟩ :=
      cer_direct_no_go_of_nonidentity_operator Cl hnonidentity
    exact ⟨CERBareRealBelow C0, hstable,
      fun hdirect => hbare.2 (hdirect C0 hbare.1)⟩

/-- For any carrier operator, both CER implications hold exactly when
bare realisability is its fixed-point predicate. -/
theorem cer_both_implications_iff_fixed_point_predicate {Carrier : Type u}
    (Cl : Carrier → Carrier) (B : Carrier → Prop) :
    ((∀ C, B C → Cl C = C) ∧ (∀ C, Cl C = C → B C)) ↔
      ∀ C, B C ↔ Cl C = C := by
  constructor
  · intro h C
    exact ⟨h.1 C, h.2 C⟩
  · intro h
    exact ⟨fun C => (h C).1, fun C => (h C).2⟩

/-- The retained Sat₅ zero-defect predicate is uniquely characterized by both CER implications for Sat₅, with legacy AOR names retained. -/
theorem aor_realisability_unique_fixed_point_predicate {mathfrakS : scopeRecord.{u}}
    (B : preSBCarrier mathfrakS → Prop) :
    ((∀ C, B C → aorInclusionObj (clSBOperator C) = C) ∧
      (∀ C, aorInclusionObj (clSBOperator C) = C → B C)) ↔
      B = structuralDefectZero := by
  constructor
  · intro h
    have hfixed := (cer_both_implications_iff_fixed_point_predicate
      (fun C => aorInclusionObj (clSBOperator C)) B).mp h
    funext C
    exact propext ((hfixed C).trans (clSB_fixed_iff_structural_defect_zero C))
  · intro h
    subst B
    exact ⟨fun C hzero => (clSB_fixed_iff_structural_defect_zero C).mpr hzero,
      fun C hfixed => (clSB_fixed_iff_structural_defect_zero C).mp hfixed⟩

/-- Exactly one predicate satisfies both CER implications for retained Sat₅: all five structural flags hold. The legacy AOR names do not refer to the current inference reflector. -/
theorem aor_realisability_unique_cer_predicate {mathfrakS : scopeRecord.{u}} :
    ∃! B : preSBCarrier mathfrakS → Prop,
      (∀ C, B C → aorInclusionObj (clSBOperator C) = C) ∧
      (∀ C, aorInclusionObj (clSBOperator C) = C → B C) := by
  refine ⟨structuralDefectZero,
    (aor_realisability_unique_fixed_point_predicate structuralDefectZero).mpr rfl, ?_⟩
  intro B h
  exact (aor_realisability_unique_fixed_point_predicate B).mp h

/-- The five structural-flag labels of the retained Sat₅ encoding, with legacy AOR names. -/
inductive AORObligation where
  | recordsTyped
  | routesAudited
  | residualsStatused
  | nonclaimsRegistered
  | metaAuditDischarged
  deriving DecidableEq

/-- The set D(C) of obligations that the carrier declares discharged. -/
def AORDischargedObligations {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Set AORObligation
  | .recordsTyped => C.declaredRecordsTyped
  | .routesAudited => C.citedRoutesAudited
  | .residualsStatused => C.residualsStatused
  | .nonclaimsRegistered => C.nonclaimsRegistered
  | .metaAuditDischarged => C.metaAuditDischarged

/-- Bare realisability below a declared set of discharged obligations. -/
def AORBareBelow {mathfrakS : scopeRecord.{u}} (D0 : Set AORObligation)
    (C : preSBCarrier mathfrakS) : Prop :=
  AORDischargedObligations C ⊆ D0

/-- A reduct is a same-scope carrier endomap that only removes discharged
obligations. This imposes no additional condition on the typed components. -/
def AORObligationReduct {mathfrakS : scopeRecord.{u}}
    (Red : preSBCarrier mathfrakS → preSBCarrier mathfrakS) : Prop :=
  ∀ C, AORDischargedObligations (Red C) ⊆ AORDischargedObligations C

/-- Explicitly retain the seed's typed components while clearing all five
obligation flags. -/
def aorUndischargedCarrier {mathfrakS : scopeRecord.{u}}
    (seed : preSBCarrier mathfrakS) : preSBCarrier mathfrakS :=
  { seed with
    declaredRecordsTyped := False
    citedRoutesAudited := False
    residualsStatused := False
    nonclaimsRegistered := False
    metaAuditDischarged := False }

/-- The declared bare predicate is stable under every obligation-removing reduct. -/
theorem aor_bare_below_reduct_stable {mathfrakS : scopeRecord.{u}}
    (D0 : Set AORObligation) :
    ∀ Red : preSBCarrier mathfrakS → preSBCarrier mathfrakS,
      AORObligationReduct Red → ∀ C, AORBareBelow D0 C → AORBareBelow D0 (Red C) := by
  intro Red hred C hbare obligation hdischarged
  exact hbare (hred C hdischarged)

/-- The concrete saturation discharges exactly all five obligations. -/
theorem aor_saturation_discharged_eq_univ {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) :
    AORDischargedObligations (aorInclusionObj (clSBOperator C)) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro obligation
  cases obligation <;> exact True.intro

/-- On any populated scope and for any proper discharged-obligation allowance,
one reduct-stable bare predicate refutes both CER implications for saturation. -/
theorem aor_saturation_cer_both_fail {mathfrakS : scopeRecord.{u}}
    (seed : preSBCarrier mathfrakS) (D0 : Set AORObligation)
    (hproper : D0 ≠ Set.univ) :
    (∀ Red : preSBCarrier mathfrakS → preSBCarrier mathfrakS,
      AORObligationReduct Red → ∀ C, AORBareBelow D0 C → AORBareBelow D0 (Red C)) ∧
    (∃ C : preSBCarrier mathfrakS,
      AORBareBelow D0 C ∧ aorInclusionObj (clSBOperator C) ≠ C) ∧
    (∃ C : preSBCarrier mathfrakS,
      aorInclusionObj (clSBOperator C) = C ∧ ¬ AORBareBelow D0 C) := by
  have hbare : AORBareBelow D0 (aorUndischargedCarrier seed) := by
    intro obligation hdischarged
    cases obligation <;> exact False.elim hdischarged
  have hnonfixed : aorInclusionObj (clSBOperator (aorUndischargedCarrier seed)) ≠
      aorUndischargedCarrier seed := by
    intro hfixed
    exact ((clSB_fixed_iff_structural_defect_zero
      (aorUndischargedCarrier seed)).mp hfixed).1
  have hfixed : aorInclusionObj (clSBOperator (aorInclusionObj (clSBOperator seed))) =
      aorInclusionObj (clSBOperator seed) :=
    (clSB_fixed_iff_structural_defect_zero
      (aorInclusionObj (clSBOperator seed))).mpr (clSBOperator seed).2
  have hnotBare : ¬ AORBareBelow D0 (aorInclusionObj (clSBOperator seed)) := by
    intro hbareSaturated
    apply hproper
    apply Set.eq_univ_iff_forall.mpr
    intro obligation
    apply hbareSaturated
    rw [aor_saturation_discharged_eq_univ seed]
    exact Set.mem_univ obligation
  exact ⟨aor_bare_below_reduct_stable D0,
    ⟨aorUndischargedCarrier seed, hbare, hnonfixed⟩,
    ⟨aorInclusionObj (clSBOperator seed), hfixed, hnotBare⟩⟩

/-- A concrete populated scope, admitting Unit in all four typed registries. -/
def aorCERScope : scopeRecord.{0} where
  carrierClass := fun _ => True
  sourceLedger := fun _ => True
  interfaceFamily := fun _ => True
  routeRegistry := fun _ => True

/-- An explicit seed carrier with Unit components and no discharged obligations. -/
def aorCERSeed : preSBCarrier aorCERScope where
  H := Unit
  H_admissible := trivial
  quotient := Unit
  q := id
  Q := fun _ _ => True
  Gamma := Unit
  Gamma_admissible := trivial
  R := Unit
  Creg := Unit
  Src := Unit
  Src_admissible := trivial
  Ifc := Unit
  Ifc_admissible := trivial
  Obs := Unit
  Stage := Unit
  Constr := Unit
  Rewrite := Unit
  Hol := Unit
  Res := Unit
  Stat := Unit
  NC := Unit
  Meta := Unit
  declaredRecordsTyped := False
  citedRoutesAudited := False
  residualsStatused := False
  nonclaimsRegistered := False
  metaAuditDischarged := False

/-- Concrete saturation counterexamples with D0 allowing four obligations but
excluding the meta-audit obligation; all scope and carrier data are constructed. -/
theorem aor_saturation_cer_both_fail_instance :
    (∀ Red : preSBCarrier aorCERScope → preSBCarrier aorCERScope,
      AORObligationReduct Red → ∀ C,
        AORBareBelow {i | i ≠ AORObligation.metaAuditDischarged} C →
        AORBareBelow {i | i ≠ AORObligation.metaAuditDischarged} (Red C)) ∧
    (∃ C : preSBCarrier aorCERScope,
      AORBareBelow {i | i ≠ AORObligation.metaAuditDischarged} C ∧
        aorInclusionObj (clSBOperator C) ≠ C) ∧
    (∃ C : preSBCarrier aorCERScope,
      aorInclusionObj (clSBOperator C) = C ∧
        ¬ AORBareBelow {i | i ≠ AORObligation.metaAuditDischarged} C) := by
  apply aor_saturation_cer_both_fail aorCERSeed
  intro h
  have hmem : AORObligation.metaAuditDischarged ∈
      {i | i ≠ AORObligation.metaAuditDischarged} := h.symm ▸ Set.mem_univ _
  exact hmem rfl

/-- The current, fixed-meaning AOR reflector is fully discharged exactly when
its source has supplied witnesses for all reachable records. -/
theorem current_aor_accounted_completion_iff
    {T : SixBirdsNeedles.AOR.AuditKernel.Theory.{u}}
    (S : SixBirdsNeedles.AOR.AuditKernel.State T) :
    SixBirdsNeedles.AOR.EvidenceAudit.FullyDischarged
      (SixBirdsNeedles.AOR.ScopedEvidence.reflect
        (SixBirdsNeedles.AOR.KernelReflection.present S)).base.model
      (SixBirdsNeedles.AOR.ScopedEvidence.reflect
        (SixBirdsNeedles.AOR.KernelReflection.present S)).base.ledger ↔
      SixBirdsNeedles.AOR.AuditKernel.Accounted S :=
  SixBirdsNeedles.AOR.KernelReflection.accounted_completion_iff S

/-- Actual current AOR inference closure leaves the false budget obligation
5 ≤ 2 unpaid. Therefore inference fixed points do not imply full discharge. -/
theorem current_aor_inference_closed_not_fully_discharged :
    SixBirdsNeedles.AOR.EvidenceReflection.IsClosed
      SixBirdsNeedles.AOR.EvidenceReflection.budgetObject ∧
    ¬ SixBirdsNeedles.AOR.EvidenceAudit.FullyDischarged
      SixBirdsNeedles.AOR.EvidenceReflection.budgetObject.model
      SixBirdsNeedles.AOR.EvidenceReflection.budgetObject.ledger := by
  refine ⟨SixBirdsNeedles.AOR.EvidenceReflection.budgetObject_closed, ?_⟩
  intro h
  have unpaid := h (5, 2) (by trivial)
  change (5 : Nat) ≤ 2 at unpaid
  omega

end SixBirdsMetaMath.FoundationsIV.ClosureRealityBoundary
