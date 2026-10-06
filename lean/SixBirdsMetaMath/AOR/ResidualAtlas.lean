import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.AOR.DefectStrata

namespace SixBirdsMetaMath.AOR.ResidualAtlas

open SixBirdsMetaMath.AOR.PreSB
open SixBirdsMetaMath.AOR.DefectStrata

universe u

/-!
This retained adapter is synchronized with the maintained Needles version.
References below to semantic AOR modules absent from this namespace mean
`SixBirdsNeedles.AOR.*`; this module does not re-export those endpoints.

AOR paper §4 "The Sigma_residual atlas" and §5 "AOR-8 statuses".

This module hosts the residual-type atlas, partial order, and atom theory:
- `def:aor:residual-types-twelve`     — the twelve residual types as an inductive
- `def:aor:residual-partial-order`    — atom-refinement partial order
- `def:aor:residual-atom`             — minimality predicate
- `thm:aor:atom-decomposition`        — every residual has a finite atom decomposition
- `thm:aor:residual-product`          — product behaviour over carrier products
- `thm:aor:forced-residual`           — fixed forced-secondary types per primary type
- `def:aor:aor-8-statuses`            — the AOR-8 status catalogue (11 entries)
- `def:aor:discharge-record`          — `(atom, status, witness)` triple
- `def:aor:discharge-witness`         — family of discharge records per atom

Statements are paper-grounded against `paper/aor/aor_paper.tex` §4–§5.
Realized as inductive types and accompanying decidable equality / case
analysis; no project-local postulates. The AOR-8 status catalogue is a
needles-local enum declared per `paper/notation_and_terminology.md` §8.
-/

/--
`def:aor:residual-types-twelve`.

Compatibility name for the residual-type enum carried by
`DefectStrata.sigmaResidual`.
-/
abbrev residualTypesTwelve := SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve

/-- A residual record in `Sigma_residual`, with primary and secondary types. -/
structure ResidualRecord where
  primary : residualTypesTwelve
  secondary : List residualTypesTwelve
  refinementDepth : Nat

/--
`def:aor:residual-partial-order`.

The generated order records atom refinement by increasing refinement depth and
type inclusion by adding forced secondary obligations while keeping the same
primary type.
-/
def residualPartialOrder (a b : ResidualRecord) : Prop :=
  a.primary = b.primary ∧ a.refinementDepth ≤ b.refinementDepth ∧
    a.secondary.Sublist b.secondary

/-- Refinement respects the actual secondary obligations, not just their
number. In particular two differently tagged singleton lists are distinct. -/
theorem residualPartialOrder_antisymm (a b : ResidualRecord)
    (hab : residualPartialOrder a b)
    (hba : residualPartialOrder b a) : a = b := by
  obtain ⟨hprimary, hdepth, hsecondary⟩ := hab
  obtain ⟨_, hdepth', hsecondary'⟩ := hba
  have hdepthEq := Nat.le_antisymm hdepth hdepth'
  have hsecondaryEq :=
    List.Sublist.eq_of_length_le hsecondary (List.Sublist.length_le hsecondary')
  cases a
  cases b
  simp_all

/-- The canonical atom for a primary residual type. -/
def residualAtomRecord (primary : residualTypesTwelve) : ResidualRecord where
  primary := primary
  secondary := []
  refinementDepth := 0

/--
`def:aor:residual-atom`.

A residual atom is a non-refined residual with a unique primary type and no
proper non-empty secondary refinement.
-/
def residualAtom (a : ResidualRecord) : Prop :=
  a = residualAtomRecord a.primary

/-- The computable primary-type projection for residual-stratum entries. -/
def residualPrimaryType {mathfrakS : scopeRecord.{u}} {C : preSBCarrier mathfrakS}
    (atom : sigmaResidual C) : residualTypesTwelve :=
  match atom with
  | sigmaResidual.dischargeStatusMissing primary _ => primary

/-- The canonical syntactic atom expansion: one atom for the primary tag and
one for each secondary tag, preserving multiplicity and order. -/
def atomDecompositionList (r : ResidualRecord) : List ResidualRecord :=
  residualAtomRecord r.primary :: r.secondary.map residualAtomRecord

/-- Reconstruct the record from its ordered atoms and depth metadata. The
depth is explicit because tag atoms alone cannot encode it. -/
def residualFromAtoms (atoms : List ResidualRecord) (depth : Nat) :
    Option ResidualRecord :=
  match atoms with
  | [] => none
  | head :: secondary =>
      some ⟨head.primary, secondary.map ResidualRecord.primary, depth⟩

theorem residualFromAtoms_canonical (r : ResidualRecord) :
    residualFromAtoms (atomDecompositionList r) r.refinementDepth = some r := by
  cases r with
  | mk primary secondary depth =>
      simp only [residualFromAtoms, atomDecompositionList, residualAtomRecord,
        List.map_map, Option.some.injEq, ResidualRecord.mk.injEq]
      change True ∧ List.map (fun x => x) secondary = secondary ∧ True
      simp

/-- A list realizes the atom decomposition of a residual record. -/
def realizesAtomDecomposition (r : ResidualRecord) (atoms : List ResidualRecord) : Prop :=
  residualFromAtoms atoms r.refinementDepth = some r ∧
    ∀ a, List.Mem a atoms → residualAtom a

/-- The canonical decomposition list realizes the atom decomposition. -/
theorem atomDecompositionList_realizes (r : ResidualRecord) :
    realizesAtomDecomposition r (atomDecompositionList r) := by
  constructor
  · exact residualFromAtoms_canonical r
  · intro a h
    change a ∈ residualAtomRecord r.primary :: r.secondary.map residualAtomRecord at h
    rcases List.mem_cons.mp h with hprimary | hsecondary
    · subst a
      rfl
    · obtain ⟨tag, _htag, htagAtom⟩ := List.mem_map.mp hsecondary
      subst a
      rfl

/-- Uniqueness follows from reconstruction and atomicity, not from placing
equality to the designated output in the realization predicate. -/
theorem atomDecomposition_unique (r : ResidualRecord) (atoms : List ResidualRecord)
    (h : realizesAtomDecomposition r atoms) : atoms = atomDecompositionList r := by
  obtain ⟨hrec, hatoms⟩ := h
  have normalize : ∀ xs : List ResidualRecord,
      (∀ a, a ∈ xs → residualAtom a) →
      xs.map (fun a => residualAtomRecord a.primary) = xs := by
    intro xs hs
    induction xs with
    | nil => rfl
    | cons a tail ih =>
        have ha := hs a (List.Mem.head _)
        have ht := ih (fun b hb => hs b (List.Mem.tail _ hb))
        change residualAtomRecord a.primary :: tail.map (fun b => residualAtomRecord b.primary) = a :: tail
        rw [ht, ← ha]
  cases atoms with
  | nil => cases hrec
  | cons a tail =>
      have ha := hatoms a (List.Mem.head _)
      have ht := normalize tail (fun b hb => hatoms b (List.Mem.tail _ hb))
      have hr : ResidualRecord.mk a.primary (tail.map ResidualRecord.primary) r.refinementDepth = r :=
        Option.some.inj hrec
      have hp := congrArg ResidualRecord.primary hr
      have hs := congrArg ResidualRecord.secondary hr
      change a :: tail = residualAtomRecord r.primary :: r.secondary.map residualAtomRecord
      rw [← hp, ← hs, List.map_map]
      change a :: tail = residualAtomRecord a.primary :: tail.map (fun b => residualAtomRecord b.primary)
      rw [ht, ← ha]

/-- Canonical tag atoms really are minimal for the repaired record order. -/
theorem residualAtom_iff_minimal (a : ResidualRecord) : residualAtom a ↔
    ∀ b, residualPartialOrder b a → b = a := by
  constructor
  · intro ha b hb
    obtain ⟨hp, hd, hs⟩ := hb
    have hda : a.refinementDepth = 0 := congrArg ResidualRecord.refinementDepth ha
    have hsa : a.secondary = [] := congrArg ResidualRecord.secondary ha
    have hdb : b.refinementDepth = 0 := by omega
    have hsb : b.secondary = [] := by
      rw [hsa] at hs
      exact List.Sublist.eq_of_length_le hs (by simp)
    cases a
    cases b
    simp_all
  · intro h
    have hb : residualPartialOrder (residualAtomRecord a.primary) a :=
      ⟨rfl, Nat.zero_le _, List.nil_sublist _⟩
    exact (h _ hb).symm

/-- Proof package for atom decomposition. -/
structure AtomDecompositionWitness (r : ResidualRecord) : Prop where
  finite_decomposition : ∃ atoms, realizesAtomDecomposition r atoms
  unique_up_to_permutation :
    ∀ atoms, realizesAtomDecomposition r atoms → atoms = atomDecompositionList r
  computable_from_field_data :
    residualFromAtoms (atomDecompositionList r) r.refinementDepth = some r

/--
`thm:aor:atom-decomposition`.

Every residual record has a canonical finite syntactic expansion, retaining
its primary and secondary tags and reconstructing its depth from metadata.
Uniqueness follows from reconstruction and minimality in this record grammar,
not uniqueness of an arbitrary analytic probe refinement. Depth remains explicit
metadata rather than a tag atom.
-/
theorem atomDecomposition (r : ResidualRecord) : AtomDecompositionWitness r where
  finite_decomposition := ⟨atomDecompositionList r, atomDecompositionList_realizes r⟩
  unique_up_to_permutation := by
    intro atoms h
    exact atomDecomposition_unique r atoms h
  computable_from_field_data := residualFromAtoms_canonical r

/-- Residual primary types that may arise from a product pairing. -/
inductive CrossResidualPrimary where
  | interface
  | local
  | global
  | sym

/-- Convert a cross-product residual type into the atlas primary type. -/
def crossResidualType : CrossResidualPrimary → residualTypesTwelve
  | CrossResidualPrimary.interface => residualTypesTwelve.interface
  | CrossResidualPrimary.local => residualTypesTwelve.local
  | CrossResidualPrimary.global => residualTypesTwelve.global
  | CrossResidualPrimary.sym => residualTypesTwelve.sym

/-- Product residuals split as left, right, and cross terms. -/
inductive ProductResidual {mathfrakS : scopeRecord.{u}}
    (C₁ C₂ : preSBCarrier mathfrakS) : Type u where
  | left : sigmaResidual C₁ → ProductResidual C₁ C₂
  | right : sigmaResidual C₂ → ProductResidual C₁ C₂
  | cross : CrossResidualPrimary → C₁.Res → C₂.Res → ProductResidual C₁ C₂

/-- Primary types excluded from this syntactic cross constructor. There are
nine, since the legacy twelve-type enumeration actually contains thirteen. -/
def additiveAcrossProducts : residualTypesTwelve → Prop
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.interface => False
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.local => False
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.global => False
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.sym => False
  | _ => True

/-- The primary label of a syntactic product entry. -/
def productPrimary {mathfrakS : scopeRecord.{u}} {C₁ C₂ : preSBCarrier mathfrakS} :
    ProductResidual C₁ C₂ → residualTypesTwelve
  | .left r => residualPrimaryType r
  | .right r => residualPrimaryType r
  | .cross t _ _ => crossResidualType t

/-- Proof package for the syntactic sum, not actual carrier-product defects.
`CarrierProduct` constructs the carrier product and gives a raw-tag obstruction;
`ResidualBudget` proves actual budget interaction estimates. -/
structure ResidualProductWitness {mathfrakS : scopeRecord.{u}}
    (C₁ C₂ : preSBCarrier mathfrakS) : Prop where
  product_decomposes :
    ∀ x : ProductResidual C₁ C₂,
      (∃ r, x = ProductResidual.left r) ∨
        (∃ r, x = ProductResidual.right r) ∨
          ∃ t r₁ r₂, x = ProductResidual.cross t r₁ r₂
  cross_only :
    ∀ t : CrossResidualPrimary,
      crossResidualType t = residualTypesTwelve.interface ∨
        crossResidualType t = residualTypesTwelve.local ∨
          crossResidualType t = residualTypesTwelve.global ∨
            crossResidualType t = residualTypesTwelve.sym
  additive_eight :
    ∀ x : ProductResidual C₁ C₂, additiveAcrossProducts (productPrimary x) →
      (∃ r, x = ProductResidual.left r) ∨ ∃ r, x = ProductResidual.right r

/--
`thm:aor:residual-product`.

For the declared syntactic sum, entries split into left, right and cross
constructors, and non-cross labels lie in the first two summands. This does
not identify this sum with the residuals of an actual componentwise carrier
product. In particular, the restricted cross labels are chosen by definition,
not derived from product semantics.
-/
theorem residualProduct {mathfrakS : scopeRecord.{u}}
    (C₁ C₂ : preSBCarrier mathfrakS) : ResidualProductWitness C₁ C₂ where
  product_decomposes := by
    intro x
    cases x with
    | left r =>
        exact Or.inl ⟨r, rfl⟩
    | right r =>
        exact Or.inr (Or.inl ⟨r, rfl⟩)
    | cross t r₁ r₂ =>
        exact Or.inr (Or.inr ⟨t, r₁, r₂, rfl⟩)
  cross_only := by
    intro t
    cases t <;> simp [crossResidualType]
  additive_eight := by
    intro x h
    cases x with
    | left r => exact Or.inl ⟨r, rfl⟩
    | right r => exact Or.inr ⟨r, rfl⟩
    | cross t a b =>
      cases t <;> exact False.elim h

/-- Fixed minimal set of forced secondary residual types for each primary. -/
def forcedSecondaryTypes : residualTypesTwelve → List residualTypesTwelve
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.source =>
      [residualTypesTwelve.transport, residualTypesTwelve.scale,
        residualTypesTwelve.role, residualTypesTwelve.target]
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.transport =>
      [residualTypesTwelve.scale, residualTypesTwelve.limit, residualTypesTwelve.role,
        residualTypesTwelve.target, residualTypesTwelve.presentation]
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.scale =>
      [residualTypesTwelve.limit, residualTypesTwelve.horizon, residualTypesTwelve.source,
        residualTypesTwelve.target, residualTypesTwelve.presentation]
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.limit =>
      [residualTypesTwelve.scale, residualTypesTwelve.horizon]
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.target =>
      [residualTypesTwelve.role, residualTypesTwelve.presentation]
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.role =>
      [residualTypesTwelve.target]
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.descent =>
      [residualTypesTwelve.target]
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.interface =>
      [residualTypesTwelve.local, residualTypesTwelve.global]
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.presentation => []
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.horizon => []
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.sym => []
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.local => [residualTypesTwelve.global]
  | SixBirdsMetaMath.AOR.DefectStrata.residualTypesTwelve.global => [residualTypesTwelve.local]

/-- A discharge closes every forced secondary type for a primary residual type. -/
def closesForcedSecondaries (primary : residualTypesTwelve)
    (closed : List residualTypesTwelve) : Prop :=
  ∀ t, List.Mem t (forcedSecondaryTypes primary) → List.Mem t closed

/-- Syntactic failure retains the actual missing secondary tag. Semantic
faithfulness is proved for recursive budget ledgers in `ForcedObligations`. -/
def faithfulForcingFailure (primary : residualTypesTwelve)
    (closed : List residualTypesTwelve) : Prop :=
  (∃ t, List.Mem t (forcedSecondaryTypes primary) ∧ ¬ List.Mem t closed) →
    ∃ r : ResidualRecord, r.primary = primary ∧
      ∃ t, t ∈ r.secondary ∧ t ∈ forcedSecondaryTypes primary ∧ t ∉ closed

/-- Proof package for the forced-secondary table. -/
structure ForcedResidualWitness : Prop where
  source_forces :
    forcedSecondaryTypes residualTypesTwelve.source =
      [residualTypesTwelve.transport, residualTypesTwelve.scale,
        residualTypesTwelve.role, residualTypesTwelve.target]
  transport_forces :
    forcedSecondaryTypes residualTypesTwelve.transport =
      [residualTypesTwelve.scale, residualTypesTwelve.limit, residualTypesTwelve.role,
        residualTypesTwelve.target, residualTypesTwelve.presentation]
  scale_forces :
    forcedSecondaryTypes residualTypesTwelve.scale =
      [residualTypesTwelve.limit, residualTypesTwelve.horizon, residualTypesTwelve.source,
        residualTypesTwelve.target, residualTypesTwelve.presentation]
  limit_forces :
    forcedSecondaryTypes residualTypesTwelve.limit =
      [residualTypesTwelve.scale, residualTypesTwelve.horizon]
  target_forces :
    forcedSecondaryTypes residualTypesTwelve.target =
      [residualTypesTwelve.role, residualTypesTwelve.presentation]
  role_forces :
    forcedSecondaryTypes residualTypesTwelve.role = [residualTypesTwelve.target]
  descent_forces :
    forcedSecondaryTypes residualTypesTwelve.descent = [residualTypesTwelve.target]
  interface_forces :
    forcedSecondaryTypes residualTypesTwelve.interface =
      [residualTypesTwelve.local, residualTypesTwelve.global]
  presentation_forces : forcedSecondaryTypes residualTypesTwelve.presentation = []
  horizon_forces : forcedSecondaryTypes residualTypesTwelve.horizon = []
  sym_forces : forcedSecondaryTypes residualTypesTwelve.sym = []
  local_global_force_each_other :
    forcedSecondaryTypes residualTypesTwelve.local = [residualTypesTwelve.global] ∧
      forcedSecondaryTypes residualTypesTwelve.global = [residualTypesTwelve.local]
  forcing_faithful :
    ∀ primary closed, faithfulForcingFailure primary closed

/--
`thm:aor:forced-residual`.

This verifies the prescribed table and retains a genuinely missing tag in a
syntactic record. It does not derive universal semantic implications between
residual types. See `ForcedObligations` for actual recursive coverage, unpaid
budget witnesses, and the cyclic-table obstruction to finite cascades.
-/
theorem forcedResidual : ForcedResidualWitness where
  source_forces := rfl
  transport_forces := rfl
  scale_forces := rfl
  limit_forces := rfl
  target_forces := rfl
  role_forces := rfl
  descent_forces := rfl
  interface_forces := rfl
  presentation_forces := rfl
  horizon_forces := rfl
  sym_forces := rfl
  local_global_force_each_other := ⟨rfl, rfl⟩
  forcing_faithful := by
    intro primary closed h
    obtain ⟨t, ht, hn⟩ := h
    exact ⟨{ primary := primary, secondary := forcedSecondaryTypes primary, refinementDepth := 0 },
      rfl, t, ht, ht, hn⟩

end SixBirdsMetaMath.AOR.ResidualAtlas
