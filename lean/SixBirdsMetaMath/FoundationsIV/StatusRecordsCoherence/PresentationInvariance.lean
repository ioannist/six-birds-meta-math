import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
import Mathlib.Logic.Relation

/-!
F29 Presentation Invariance.

Truth/readout/status belongs to represented content exactly when it descends
through the presentation quotient. Section-relative and covariant claims are
lawful but are typed separately from exact presentation invariance.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.PresentationInvariance

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- A readout/status/truth expression is presentation-invariant when it descends
through the presentation quotient. -/
def PresentationInvariant {P Pi V : Type} (pi : P → Pi) (T : P → V) : Prop :=
  Descends pi (fun p : P => p) T

/-- Presentation split-pair obstruction: same represented content, different
readout value. -/
def PresentationObstruction {P Pi V : Type} (pi : P → Pi) (T : P → V) :
    (P × P) → Prop :=
  splitPairObstruction pi (fun p : P => p) T

/-- No presentation obstruction is present. -/
def PresentationObstructionEmpty {P Pi V : Type} (pi : P → Pi) (T : P → V) :
    Prop :=
  ObstructionEmpty (PresentationObstruction pi T)

/-- A declared presentation-equivalence relation is represented by a quotient
map when quotient equality is exactly equivalence. -/
def PresentationQuotientCompatible {P Pi : Type} (pi : P → Pi)
    (Equivalent : P → P → Prop) : Prop :=
  ∀ p p', pi p = pi p' ↔ Equivalent p p'

/-- Equivalence-relation spelling of presentation invariance. -/
def EquivalentPresentationInvariant {P V : Type} (Equivalent : P → P → Prop)
    (T : P → V) : Prop :=
  ∀ p p', Equivalent p p' → T p = T p'

/-- Relation-valued presentation invariance on an abstract tuple carrier. -/
def PresentationRelationInvariant {TupleP TuplePi : Type} (tuplePi : TupleP → TuplePi)
    (R : TupleP → Prop) : Prop :=
  Descends tuplePi (fun t : TupleP => t) R

/-- Relation-valued presentation obstruction. -/
def PresentationRelationObstruction {TupleP TuplePi : Type}
    (tuplePi : TupleP → TuplePi) (R : TupleP → Prop) : (TupleP × TupleP) → Prop :=
  splitPairObstruction tuplePi (fun t : TupleP => t) R

/-- No relation-valued presentation obstruction is present. -/
def PresentationRelationObstructionEmpty {TupleP TuplePi : Type}
    (tuplePi : TupleP → TuplePi) (R : TupleP → Prop) : Prop :=
  ObstructionEmpty (PresentationRelationObstruction tuplePi R)

/-- A section-relative expression agrees with the expression computed at the
chosen representative. -/
def SectionIndependent {P Pi V : Type} (pi : P → Pi) (sect : Pi → P)
    (T : P → V) : Prop :=
  ∀ p, T p = T (sect (pi p))

/-- A covariant readout transforms lawfully under presentation changes. -/
def CovariantReadout {G P V : Type} (actP : G → P → P) (actV : G → V → V)
    (T : P → V) : Prop :=
  ∀ g p, T (actP g p) = actV g (T p)

/-- The paper's group equivariance is the intertwining equation. -/
def GroupEquivariant {G P V : Type} (actP : G → P → P)
    (actV : G → V → V) (T : P → V) : Prop :=
  CovariantReadout actP actV T

/-- A map out of the covariant codomain is invariant under the codomain action. -/
def InvariantMap {G V W : Type} (actV : G → V → V) (I : V → W) : Prop :=
  ∀ g v, I (actV g v) = I v

/-- The invariantized readout is unchanged under presentation-action
generators. -/
def ActionPresentationInvariant {G P W : Type} (actP : G → P → P)
    (expr : P → W) : Prop :=
  ∀ g p, expr (actP g p) = expr p

/-- Canonical strict-extension repair: retain the represented quotient and add
the presentation-sensitive readout. -/
def presentationExtension {P Pi V : Type} (pi : P → Pi) (T : P → V) :
    P → Pi × V :=
  fun p => (pi p, T p)

/-- The presentation extension retains the original presentation quotient. -/
def RetainsPresentationQuotient {P Pi E : Type} (pi : P → Pi) (extension : P → E) :
    Prop :=
  Descends extension (fun p : P => p) pi

/-- The presentation extension carries the presentation-sensitive readout. -/
def CarriesPresentationReadout {P E V : Type} (extension : P → E) (T : P → V) :
    Prop :=
  Descends extension (fun p : P => p) T

/-- Strict presentation extension: the readout does not descend through the old
presentation quotient, while the extension carries both old quotient and
readout. -/
def StrictPresentationExtension {P Pi V : Type} (pi : P → Pi) (T : P → V) :
    Prop :=
  ¬ PresentationInvariant pi T ∧
    RetainsPresentationQuotient pi (presentationExtension pi T) ∧
      CarriesPresentationReadout (presentationExtension pi T) T

/-- Source status vocabulary for presentation-invariance claims. -/
inductive PresentationInvarianceStatus where
  | presentationInvariant
  | presentationLevelFact
  | sectionRelative
  | covariantReadout
  | invariantCoarsening
  | presentationOverread
  | presentationQuotientAbsent
  | presentationQuotientMisaligned
  | bridgeMediatedPresentationInvariance
  | localPresentationInvariance
  | budgetedPresentationInvariance
  | protocolPresentationArtifact
deriving DecidableEq

/-- Meaning assignment for F29 presentation-invariance statuses. -/
def PresentationInvarianceStatusHolds (invariant presentationLevel sectionRelative
    covariant coarsening overread quotientAbsent quotientMisaligned bridge localStatus
    budgeted protocol : Prop) : PresentationInvarianceStatus → Prop
  | PresentationInvarianceStatus.presentationInvariant => invariant
  | PresentationInvarianceStatus.presentationLevelFact => presentationLevel
  | PresentationInvarianceStatus.sectionRelative => sectionRelative
  | PresentationInvarianceStatus.covariantReadout => covariant
  | PresentationInvarianceStatus.invariantCoarsening => coarsening
  | PresentationInvarianceStatus.presentationOverread => overread
  | PresentationInvarianceStatus.presentationQuotientAbsent => quotientAbsent
  | PresentationInvarianceStatus.presentationQuotientMisaligned => quotientMisaligned
  | PresentationInvarianceStatus.bridgeMediatedPresentationInvariance => bridge
  | PresentationInvarianceStatus.localPresentationInvariance => localStatus
  | PresentationInvarianceStatus.budgetedPresentationInvariance => budgeted
  | PresentationInvarianceStatus.protocolPresentationArtifact => protocol

/-- Functional Presentation Invariance Normal Form. -/
theorem presentation_invariant_iff_no_obstruction {P Pi V : Type}
    (pi : P → Pi) (T : P → V) (hpi : Function.Surjective pi) :
    PresentationInvariant pi T ↔ PresentationObstructionEmpty pi T :=
  descent_repair_normal_form pi (fun p : P => p) T hpi

/-- Presentation invariance against an explicit equivalence relation is the
same as quotient descent when the quotient map represents that equivalence. -/
theorem presentation_invariant_iff_equivalent_invariant {P Pi V : Type}
    (pi : P → Pi) (Equivalent : P → P → Prop) (T : P → V)
    (hpi : Function.Surjective pi)
    (hcompat : PresentationQuotientCompatible pi Equivalent) :
    PresentationInvariant pi T ↔ EquivalentPresentationInvariant Equivalent T := by
  constructor
  · intro hinv p p' heqv
    rcases hinv with ⟨Tbar, hcomm⟩
    have hp : pi p = pi p' := (hcompat p p').2 heqv
    have hpv : Tbar (pi p) = T p := congrFun hcomm p
    have hpv' : Tbar (pi p') = T p' := congrFun hcomm p'
    calc
      T p = Tbar (pi p) := hpv.symm
      _ = Tbar (pi p') := by rw [hp]
      _ = T p' := hpv'
  · intro hequiv
    have hempty : PresentationObstructionEmpty pi T := by
      intro pair hpair
      exact hpair.2 (hequiv pair.1 pair.2 ((hcompat pair.1 pair.2).1 hpair.1))
    exact (presentation_invariant_iff_no_obstruction pi T hpi).2 hempty

/-- Relation-valued Presentation Invariance Normal Form. -/
theorem presentation_relation_invariant_iff_no_obstruction
    {TupleP TuplePi : Type} (tuplePi : TupleP → TuplePi) (R : TupleP → Prop)
    (htuplePi : Function.Surjective tuplePi) :
    PresentationRelationInvariant tuplePi R ↔
      PresentationRelationObstructionEmpty tuplePi R :=
  descent_repair_normal_form tuplePi (fun t : TupleP => t) R htuplePi

/-- Section independence is equivalent to quotient descent when the sect is
a right inverse to the quotient map. -/
theorem section_independent_iff_presentation_invariant {P Pi V : Type}
    (pi : P → Pi) (sect : Pi → P) (T : P → V)
    (hsection : ∀ x, pi (sect x) = x) :
    SectionIndependent pi sect T ↔ PresentationInvariant pi T := by
  constructor
  · intro hsectionIndependent
    refine ⟨fun x => T (sect x), ?_⟩
    funext p
    exact (hsectionIndependent p).symm
  · intro hinv p
    rcases hinv with ⟨Tbar, hcomm⟩
    have hp : Tbar (pi p) = T p := congrFun hcomm p
    have hsp : Tbar (pi (sect (pi p))) = T (sect (pi p)) :=
      congrFun hcomm (sect (pi p))
    calc
      T p = Tbar (pi p) := hp.symm
      _ = Tbar (pi (sect (pi p))) := by rw [hsection (pi p)]
      _ = T (sect (pi p)) := hsp

/-- Invariant functions of covariant readouts are invariant under presentation
action generators. -/
theorem invariant_map_of_covariant_readout {G P V W : Type}
    (actP : G → P → P) (actV : G → V → V) (T : P → V) (I : V → W) :
    CovariantReadout actP actV T → InvariantMap actV I →
      ActionPresentationInvariant actP (I ∘ T) := by
  intro hcov hinv g p
  calc
    I (T (actP g p)) = I (actV g (T p)) := by rw [hcov g p]
    _ = I (T p) := hinv g (T p)

/-- The presentation extension retains the old quotient. -/
theorem presentation_extension_retains {P Pi V : Type} (pi : P → Pi) (T : P → V) :
    RetainsPresentationQuotient pi (presentationExtension pi T) := by
  refine ⟨Prod.fst, ?_⟩
  funext p
  rfl

/-- The presentation extension carries the added readout. -/
theorem presentation_extension_carries {P Pi V : Type} (pi : P → Pi) (T : P → V) :
    CarriesPresentationReadout (presentationExtension pi T) T := by
  refine ⟨Prod.snd, ?_⟩
  funext p
  rfl

/-- Strict presentation extension is exactly non-descent plus the canonical
retention/carrying repair. -/
theorem strict_presentation_extension_iff_not_invariant {P Pi V : Type}
    (pi : P → Pi) (T : P → V) :
    StrictPresentationExtension pi T ↔ ¬ PresentationInvariant pi T := by
  constructor
  · intro hstrict
    exact hstrict.1
  · intro hnot
    exact ⟨hnot, presentation_extension_retains pi T, presentation_extension_carries pi T⟩

/--
Presentation Invariance Normal Form. Functional and relation-valued claims are
presentation-invariant exactly when their split-pair obstructions are empty.
Equivalently, they factor through the declared presentation quotient. Section
claims require sect independence, covariant claims require invariantization,
and presentation-sensitive readouts become represented data only by strict
presentation extension.
-/
theorem presentation_invariance {P Pi V TupleP TuplePi G W : Type}
    (pi : P → Pi) (T : P → V) (tuplePi : TupleP → TuplePi) (R : TupleP → Prop)
    (Equivalent : P → P → Prop) (sect : Pi → P)
    (actP : G → P → P) (actV : G → V → V) (I : V → W)
    (hpi : Function.Surjective pi) (htuplePi : Function.Surjective tuplePi)
    (hcompat : PresentationQuotientCompatible pi Equivalent)
    (hsection : ∀ x, pi (sect x) = x) :
    (PresentationInvariant pi T ↔ PresentationObstructionEmpty pi T) ∧
      (PresentationInvariant pi T ↔ EquivalentPresentationInvariant Equivalent T) ∧
        (PresentationRelationInvariant tuplePi R ↔
          PresentationRelationObstructionEmpty tuplePi R) ∧
          (SectionIndependent pi sect T ↔ PresentationInvariant pi T) ∧
            (CovariantReadout actP actV T → InvariantMap actV I →
              ActionPresentationInvariant actP (I ∘ T)) ∧
              RetainsPresentationQuotient pi (presentationExtension pi T) ∧
                CarriesPresentationReadout (presentationExtension pi T) T ∧
                  (StrictPresentationExtension pi T ↔ ¬ PresentationInvariant pi T) ∧
                  (GroupEquivariant actP actV T ↔
                    ∀ g p, T (actP g p) = actV g (T p)) := by
  exact ⟨presentation_invariant_iff_no_obstruction pi T hpi,
    presentation_invariant_iff_equivalent_invariant pi Equivalent T hpi hcompat,
    presentation_relation_invariant_iff_no_obstruction tuplePi R htuplePi,
    section_independent_iff_presentation_invariant pi sect T hsection,
    invariant_map_of_covariant_readout actP actV T I,
    presentation_extension_retains pi T,
    presentation_extension_carries pi T,
    strict_presentation_extension_iff_not_invariant pi T, Iff.rfl⟩

/-- F29 with the paper's fiber-constancy definitions stated explicitly. -/
theorem presentation_invariance_paper_exact
    {P Pi V TupleP TuplePi G W : Type}
    (pi : P → Pi) (T : P → V) (tuplePi : TupleP → TuplePi)
    (R : TupleP → Prop) (Equivalent : P → P → Prop) (sect : Pi → P)
    (actP : G → P → P) (actV : G → V → V) (I : V → W)
    (hpi : Function.Surjective pi) (htuplePi : Function.Surjective tuplePi)
    (hcompat : PresentationQuotientCompatible pi Equivalent)
    (hsection : ∀ x, pi (sect x) = x) :
    (PresentationInvariant pi T ↔
      ∀ p p', pi p = pi p' → T p = T p') ∧
    (PresentationInvariant pi T ↔
      ∃ Tbar : Pi → V, Tbar ∘ pi = T) ∧
    (PresentationInvariant pi T ↔ EquivalentPresentationInvariant Equivalent T) ∧
    (PresentationRelationInvariant tuplePi R ↔
      ∀ x y, tuplePi x = tuplePi y → (R x ↔ R y)) ∧
    (SectionIndependent pi sect T ↔ PresentationInvariant pi T) ∧
    (GroupEquivariant actP actV T ↔
      ∀ g p, T (actP g p) = actV g (T p)) := by
  classical
  have hfull := presentation_invariance pi T tuplePi R Equivalent sect
    actP actV I hpi htuplePi hcompat hsection
  have hkernel : PresentationInvariant pi T ↔
      ∀ p p', pi p = pi p' → T p = T p' := by
    constructor
    · rintro ⟨Tbar, hcomm⟩ p p' hpp'
      have hp := congrFun hcomm p
      have hp' := congrFun hcomm p'
      exact hp.symm.trans ((congrArg Tbar hpp').trans hp')
    · intro hconst
      let rep : Pi → P := fun x => Classical.choose (hpi x)
      refine ⟨fun x => T (rep x), ?_⟩
      funext p
      exact hconst (rep (pi p)) p (Classical.choose_spec (hpi (pi p)))
  have hrelation : PresentationRelationInvariant tuplePi R ↔
      ∀ x y, tuplePi x = tuplePi y → (R x ↔ R y) := by
    constructor
    · rintro ⟨Rbar, hcomm⟩ x y hxy
      have hx := congrFun hcomm x
      have hy := congrFun hcomm y
      exact iff_of_eq (by
        simpa only [Function.comp_apply] using
          hx.symm.trans ((congrArg Rbar hxy).trans hy))
    · intro hconst
      let rep : TuplePi → TupleP := fun x => Classical.choose (htuplePi x)
      refine ⟨fun x => R (rep x), ?_⟩
      funext x
      apply propext
      exact hconst (rep (tuplePi x)) x
        (Classical.choose_spec (htuplePi (tuplePi x)))
  exact ⟨hkernel, Iff.rfl, hfull.2.1, hrelation,
    hfull.2.2.2.1, hfull.2.2.2.2.2.2.2.2⟩

/-- A genuine Bool swap action has a presentation-invariant readout that is
not equivariant for the trivial action on readout values. -/
theorem bool_presentation_invariant_not_equivariant :
    (∀ p : Bool, Bool.xor false p = p) ∧
    (∀ g g' p : Bool,
      Bool.xor (Bool.xor g g') p = Bool.xor g (Bool.xor g' p)) ∧
    PresentationInvariant (id : Bool → Bool) (id : Bool → Bool) ∧
    ¬ GroupEquivariant (fun g p : Bool => Bool.xor g p)
        (fun (_ : Bool) (v : Bool) => v) (id : Bool → Bool) := by
  refine ⟨by decide, by decide, ⟨id, rfl⟩, ?_⟩
  intro hequiv
  have hbad := hequiv true false
  exact (by decide : true ≠ false) hbad

/-- F29 with tuple surjectivity confined to the tuple clause and an explicit
non-equivariance witness. The section supplies surjectivity of `pi`. -/
theorem presentation_invariance_paper_conditional
    {P Pi V TupleP TuplePi G : Type}
    (pi : P → Pi) (T : P → V) (tuplePi : TupleP → TuplePi)
    (R : TupleP → Prop) (Equivalent : P → P → Prop) (sect : Pi → P)
    (actP : G → P → P) (actV : G → V → V)
    (hcompat : PresentationQuotientCompatible pi Equivalent)
    (hsection : ∀ x, pi (sect x) = x) :
    (PresentationInvariant pi T ↔
      ∀ p p', pi p = pi p' → T p = T p') ∧
    (PresentationInvariant pi T ↔
      ∃ Tbar : Pi → V, T = Tbar ∘ pi) ∧
    (PresentationInvariant pi T ↔ EquivalentPresentationInvariant Equivalent T) ∧
    (PresentationInvariant pi T ↔ SectionIndependent pi sect T) ∧
    (Function.Surjective tuplePi →
      (PresentationRelationInvariant tuplePi R ↔
        ∀ x y, tuplePi x = tuplePi y → (R x ↔ R y)) ∧
      (PresentationRelationInvariant tuplePi R ↔
        ∃ Rbar : TuplePi → Prop, R = Rbar ∘ tuplePi)) ∧
    (GroupEquivariant actP actV T ↔
      ∀ g p, T (actP g p) = actV g (T p)) ∧
    (PresentationInvariant (id : Bool → Bool) (id : Bool → Bool) ∧
      ¬ GroupEquivariant (fun g p : Bool => Bool.xor g p)
        (fun (_ : Bool) (v : Bool) => v) (id : Bool → Bool)) := by
  have hpi : Function.Surjective pi := fun x => ⟨sect x, hsection x⟩
  have hsectionIff := section_independent_iff_presentation_invariant
    pi sect T hsection
  have hcompatIff := presentation_invariant_iff_equivalent_invariant
    pi Equivalent T hpi hcompat
  have hkernel : PresentationInvariant pi T ↔
      ∀ p p', pi p = pi p' → T p = T p' := by
    constructor
    · rintro ⟨Tbar, hcomm⟩ p p' hpp'
      have hp := congrFun hcomm p
      have hp' := congrFun hcomm p'
      exact hp.symm.trans ((congrArg Tbar hpp').trans hp')
    · intro hconst
      refine ⟨T ∘ sect, ?_⟩
      funext p
      exact hconst (sect (pi p)) p (hsection (pi p))
  refine ⟨hkernel, ?_, hcompatIff, hsectionIff.symm, ?_, Iff.rfl,
    bool_presentation_invariant_not_equivariant.2.2⟩
  · constructor
    · rintro ⟨Tbar, hcomm⟩
      exact ⟨Tbar, hcomm.symm⟩
    · rintro ⟨Tbar, hcomm⟩
      exact ⟨Tbar, hcomm.symm⟩
  · intro htuplePi
    have htuple : PresentationRelationInvariant tuplePi R ↔
        ∀ x y, tuplePi x = tuplePi y → (R x ↔ R y) := by
      classical
      constructor
      · rintro ⟨Rbar, hcomm⟩ x y hxy
        have hx := congrFun hcomm x
        have hy := congrFun hcomm y
        exact iff_of_eq (by
          simpa only [Function.comp_apply] using
            hx.symm.trans ((congrArg Rbar hxy).trans hy))
      · intro hconst
        let rep : TuplePi → TupleP := fun x => Classical.choose (htuplePi x)
        refine ⟨fun x => R (rep x), ?_⟩
        funext x
        apply propext
        exact hconst (rep (tuplePi x)) x
          (Classical.choose_spec (htuplePi (tuplePi x)))
    exact ⟨htuple, ⟨fun ⟨Rbar, hcomm⟩ => ⟨Rbar, hcomm.symm⟩,
      fun ⟨Rbar, hcomm⟩ => ⟨Rbar, hcomm.symm⟩⟩⟩

/-- Constancy on quotient fibers is equivalent to invariance under generators
when their equivalence closure is precisely the quotient kernel. -/
theorem presentation_kernel_invariant_iff_generators {P Pi V : Type}
    (pi : P → Pi) (T : P → V) (r : P → P → Prop)
    (hgen : ∀ p p', pi p = pi p' ↔ Relation.EqvGen r p p') :
    (∀ p p', pi p = pi p' → T p = T p') ↔
      (∀ p p', r p p' → T p = T p') := by
  constructor
  · intro hkernel p p' hr
    exact hkernel p p' ((hgen p p').2 (Relation.EqvGen.rel p p' hr))
  · intro hstep p p' hpp'
    have hclosure := (hgen p p').1 hpp'
    clear hpp'
    induction hclosure with
    | rel x y hxy => exact hstep x y hxy
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- F29 with the generator criterion for every relation whose equivalence
closure equals the presentation-quotient kernel. -/
theorem presentation_invariance_paper_conditional_strengthened
    {P Pi V TupleP TuplePi G : Type}
    (pi : P → Pi) (T : P → V) (tuplePi : TupleP → TuplePi)
    (R : TupleP → Prop) (Equivalent : P → P → Prop) (sect : Pi → P)
    (actP : G → P → P) (actV : G → V → V)
    (hcompat : PresentationQuotientCompatible pi Equivalent)
    (hsection : ∀ x, pi (sect x) = x) :
    ((PresentationInvariant pi T ↔
      ∀ p p', pi p = pi p' → T p = T p') ∧
    (PresentationInvariant pi T ↔
      ∃ Tbar : Pi → V, T = Tbar ∘ pi) ∧
    (PresentationInvariant pi T ↔ EquivalentPresentationInvariant Equivalent T) ∧
    (PresentationInvariant pi T ↔ SectionIndependent pi sect T) ∧
    (Function.Surjective tuplePi →
      (PresentationRelationInvariant tuplePi R ↔
        ∀ x y, tuplePi x = tuplePi y → (R x ↔ R y)) ∧
      (PresentationRelationInvariant tuplePi R ↔
        ∃ Rbar : TuplePi → Prop, R = Rbar ∘ tuplePi)) ∧
    (GroupEquivariant actP actV T ↔
      ∀ g p, T (actP g p) = actV g (T p)) ∧
    (PresentationInvariant (id : Bool → Bool) (id : Bool → Bool) ∧
      ¬ GroupEquivariant (fun g p : Bool => Bool.xor g p)
        (fun (_ : Bool) (v : Bool) => v) (id : Bool → Bool))) ∧
    (∀ r : P → P → Prop,
      (∀ p p', pi p = pi p' ↔ Relation.EqvGen r p p') →
      ((∀ p p', pi p = pi p' → T p = T p') ↔
        (∀ p p', r p p' → T p = T p'))) := by
  refine ⟨presentation_invariance_paper_conditional pi T tuplePi R Equivalent
    sect actP actV hcompat hsection, ?_⟩
  intro r hgen
  exact presentation_kernel_invariant_iff_generators pi T r hgen

/-- A compatible relation inherits presentation invariance. For an equivalence
relation, its Bool-valued invariant readouts detect whether it is the entire
quotient kernel; Bool supplies values even outside the image of the quotient. -/
theorem presentation_invariance_general_relation {P Pi : Type}
    (pi : P → Pi) (Equivalent : P → P → Prop)
    (hcompat : ∀ p p', Equivalent p p' → pi p = pi p') :
    (∀ {V : Type} (T : P → V), PresentationInvariant pi T →
      EquivalentPresentationInvariant Equivalent T) ∧
    (Equivalence Equivalent →
      ((∀ T : P → Bool, EquivalentPresentationInvariant Equivalent T →
          PresentationInvariant pi T) ↔
        (∀ p p', Equivalent p p' ↔ pi p = pi p'))) := by
  classical
  constructor
  · intro V T hdesc p p' hpp'
    obtain ⟨Tbar, hcomm⟩ := hdesc
    exact (congrFun hcomm p).symm.trans
      ((congrArg Tbar (hcompat p p' hpp')).trans (congrFun hcomm p'))
  · intro hequiv
    constructor
    · intro hall p p'
      refine ⟨hcompat p p', ?_⟩
      intro hpi
      let T : P → Bool := fun x => if Equivalent p x then true else false
      have hT : EquivalentPresentationInvariant Equivalent T := by
        intro x y hxy
        have hiff : Equivalent p x ↔ Equivalent p y :=
          ⟨fun hx => hequiv.trans hx hxy,
            fun hy => hequiv.trans hy (hequiv.symm hxy)⟩
        by_cases hx : Equivalent p x
        · simp [T, hx, hiff.mp hx]
        · have hy : ¬ Equivalent p y := fun hy => hx (hiff.mpr hy)
          simp [T, hx, hy]
      obtain ⟨Tbar, hcomm⟩ := hall T hT
      have hvalues : T p = T p' := (congrFun hcomm p).symm.trans
        ((congrArg Tbar hpi).trans (congrFun hcomm p'))
      have hp : T p = true := by simp [T, hequiv.refl p]
      have hp' : T p' = true := hvalues.symm.trans hp
      by_cases hpp' : Equivalent p p'
      · exact hpp'
      · simp [T, hpp'] at hp'
    · intro hkernel T hT
      let Tbar : Pi → Bool := fun a =>
        if h : ∃ p, pi p = a then T (Classical.choose h) else false
      refine ⟨Tbar, ?_⟩
      funext p
      have himage : ∃ p', pi p' = pi p := ⟨p, rfl⟩
      change (if h : ∃ p', pi p' = pi p then T (Classical.choose h)
        else false) = T p
      rw [dif_pos himage]
      exact hT _ p ((hkernel _ p).mpr (Classical.choose_spec himage))

/-- Prop-valued presentation relations extend by existential image, giving
fiber constancy, factorization, and empty obstruction for every presentation map. -/
theorem presentation_relation_invariance_any_presentation
    {TupleP TuplePi : Type} (tuplePi : TupleP → TuplePi) (R : TupleP → Prop) :
    (PresentationRelationInvariant tuplePi R ↔
      ∀ x y, tuplePi x = tuplePi y → (R x ↔ R y)) ∧
    (PresentationRelationInvariant tuplePi R ↔
      ∃ Rbar : TuplePi → Prop, R = Rbar ∘ tuplePi) ∧
    (PresentationRelationInvariant tuplePi R ↔
      PresentationRelationObstructionEmpty tuplePi R) := by
  have hkernel : PresentationRelationInvariant tuplePi R ↔
      ∀ x y, tuplePi x = tuplePi y → (R x ↔ R y) := by
    constructor
    · rintro ⟨Rbar, hcomm⟩ x y hxy
      exact iff_of_eq ((congrFun hcomm x).symm.trans
        ((congrArg Rbar hxy).trans (congrFun hcomm y)))
    · intro hconstant
      refine ⟨fun z => ∃ x, tuplePi x = z ∧ R x, ?_⟩
      funext x
      apply propext
      constructor
      · rintro ⟨y, heq, hy⟩
        exact (hconstant y x heq).mp hy
      · intro hx
        exact ⟨x, rfl, hx⟩
  refine ⟨hkernel, ?_, ?_⟩
  · constructor
    · rintro ⟨Rbar, hcomm⟩
      exact ⟨Rbar, hcomm.symm⟩
    · rintro ⟨Rbar, hcomm⟩
      exact ⟨Rbar, hcomm.symm⟩
  · constructor
    · intro hinvariant pair ⟨heq, hne⟩
      exact hne (propext ((hkernel.mp hinvariant) pair.1 pair.2 heq))
    · intro hempty
      apply hkernel.mpr
      intro x y heq
      exact iff_of_eq (Classical.byContradiction (fun hne =>
        hempty (x, y) ⟨heq, hne⟩))

/-- The relation-obstruction equivalence needs no presentation-map surjectivity. -/
theorem presentation_relation_invariant_iff_no_obstruction_any_presentation
    {TupleP TuplePi : Type} (tuplePi : TupleP → TuplePi) (R : TupleP → Prop) :
    PresentationRelationInvariant tuplePi R ↔
      PresentationRelationObstructionEmpty tuplePi R :=
  (presentation_relation_invariance_any_presentation tuplePi R).2.2

/-- The full paper-exact bundle for arbitrary tuple presentation maps. -/
theorem presentation_invariance_paper_exact_any_presentation
    {P Pi V TupleP TuplePi G W : Type}
    (pi : P → Pi) (T : P → V) (tuplePi : TupleP → TuplePi)
    (R : TupleP → Prop) (Equivalent : P → P → Prop) (sect : Pi → P)
    (actP : G → P → P) (actV : G → V → V) (I : V → W)
    (hpi : Function.Surjective pi)
    (hcompat : PresentationQuotientCompatible pi Equivalent)
    (hsection : ∀ x, pi (sect x) = x) :
    (PresentationInvariant pi T ↔
      ∀ p p', pi p = pi p' → T p = T p') ∧
    (PresentationInvariant pi T ↔
      ∃ Tbar : Pi → V, Tbar ∘ pi = T) ∧
    (PresentationInvariant pi T ↔ EquivalentPresentationInvariant Equivalent T) ∧
    (PresentationRelationInvariant tuplePi R ↔
      ∀ x y, tuplePi x = tuplePi y → (R x ↔ R y)) ∧
    (SectionIndependent pi sect T ↔ PresentationInvariant pi T) ∧
    (GroupEquivariant actP actV T ↔
      ∀ g p, T (actP g p) = actV g (T p)) := by
  let _ := I
  have hkernel : PresentationInvariant pi T ↔
      ∀ p p', pi p = pi p' → T p = T p' := by
    constructor
    · rintro ⟨Tbar, hcomm⟩ p p' hpp'
      exact (congrFun hcomm p).symm.trans
        ((congrArg Tbar hpp').trans (congrFun hcomm p'))
    · intro hconstant
      classical
      let rep : Pi → P := fun x => Classical.choose (hpi x)
      refine ⟨fun x => T (rep x), ?_⟩
      funext p
      exact hconstant (rep (pi p)) p (Classical.choose_spec (hpi (pi p)))
  exact ⟨hkernel, Iff.rfl,
    presentation_invariant_iff_equivalent_invariant pi Equivalent T hpi hcompat,
    (presentation_relation_invariance_any_presentation tuplePi R).1,
    section_independent_iff_presentation_invariant pi sect T hsection,
    Iff.rfl⟩

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.PresentationInvariance
