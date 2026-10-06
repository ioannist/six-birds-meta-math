import SixBirdsMetaMath.Terminology

namespace SixBirdsMetaMath.AOR.PreSB

universe u

/-!
This retained adapter is synchronized with the maintained Needles version.
References below to semantic AOR modules absent from this namespace mean
`SixBirdsNeedles.AOR.*`; this module does not re-export those endpoints.

AOR paper §1 "PreSB carriers and the AOR full subcategory".

This module hosts the AOR meta-theory carrier objects:
- `def:aor:presb-carrier`   — the 17-field PreSB carrier tuple
- `def:aor:scope-record`    — scope record `\mathfrak S`
- `def:aor:morphism-presb`  — typed scope-preserving morphisms
- `def:aor:aor-subcategory` — full subcategory `AOR ↪ PreSB`
- `thm:aor:aor-full-subcat` — `\iota : AOR \hookrightarrow PreSB` is fully faithful

Statements are paper-grounded against `paper/aor/aor_paper.tex` §1.
Realized as Lean `structure`s and `class`es; no project-local
postulates. The eight-stratum defect `Xi_SB` (used by `def:aor:aor-subcategory`)
is declared in `SixBirdsMetaMath.AOR.DefectStrata`.
-/

/--
`def:aor:scope-record`.

A scope record is the typed declaration against which a PreSB carrier is
audited: an admissible carrier class, source ledger, interface family, and
route registry.  Scope is a first-class parameter; all morphisms below are
formed only between carriers with the same `mathfrakS`.
-/
structure scopeRecord where
  carrierClass : Type u → Prop
  sourceLedger : Type u → Prop
  interfaceFamily : Type u → Prop
  routeRegistry : Type u → Prop

/--
`def:aor:presb-carrier`.

The seventeen paper fields are represented by typed components.  The final
five propositions are the zero-defect audit obligations used in the
equivalent description of `AOR_mathfrakS`: records are typed, cited routes
are audited, residuals are statused, nonclaims are registered, and
meta-audit obligations are discharged.
-/
structure preSBCarrier (mathfrakS : scopeRecord.{u}) where
  H : Type u
  H_admissible : mathfrakS.carrierClass H
  quotient : Type u
  q : H → quotient
  Q : quotient → quotient → Prop
  Gamma : Type u
  Gamma_admissible : mathfrakS.routeRegistry Gamma
  R : Type u
  Creg : Type u
  Src : Type u
  Src_admissible : mathfrakS.sourceLedger Src
  Ifc : Type u
  Ifc_admissible : mathfrakS.interfaceFamily Ifc
  Obs : Type u
  Stage : Type u
  Constr : Type u
  Rewrite : Type u
  Hol : Type u
  Res : Type u
  Stat : Type u
  NC : Type u
  Meta : Type u
  declaredRecordsTyped : Prop
  citedRoutesAudited : Prop
  residualsStatused : Prop
  nonclaimsRegistered : Prop
  metaAuditDischarged : Prop

/-- The AOR structural-defect-zero predicate `Xi_SB(C) = 0` in §1 form. -/
def structuralDefectZero {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : Prop :=
  C.declaredRecordsTyped ∧
    C.citedRoutesAudited ∧
      C.residualsStatused ∧ C.nonclaimsRegistered ∧ C.metaAuditDischarged

/--
`def:aor:morphism-presb`.

A PreSB morphism is a tuple of typed field maps between carriers of the same
scope.  The quotient square commutes by `q_commutes`; route registries and
audit pairings are transported by `Gamma_map` and `Q_transport`.  The final
field records that structural zero-defect is preserved by the morphism, which
is what makes the AOR full subcategory stable under isomorphism below.
-/
structure morphismPreSB {mathfrakS : scopeRecord.{u}}
    (C C' : preSBCarrier mathfrakS) where
  H_map : C.H → C'.H
  quotient_map : C.quotient → C'.quotient
  q_commutes : ∀ x, quotient_map (C.q x) = C'.q (H_map x)
  Q_transport : ∀ x y, C.Q x y → C'.Q (quotient_map x) (quotient_map y)
  Gamma_map : C.Gamma → C'.Gamma
  R_map : C.R → C'.R
  Creg_map : C.Creg → C'.Creg
  Src_map : C.Src → C'.Src
  Ifc_map : C.Ifc → C'.Ifc
  Obs_map : C.Obs → C'.Obs
  Stage_map : C.Stage → C'.Stage
  Constr_map : C.Constr → C'.Constr
  Rewrite_map : C.Rewrite → C'.Rewrite
  Hol_map : C.Hol → C'.Hol
  Res_map : C.Res → C'.Res
  Stat_map : C.Stat → C'.Stat
  NC_map : C.NC → C'.NC
  Meta_map : C.Meta → C'.Meta
  preservesStructuralDefectZero :
    structuralDefectZero C → structuralDefectZero C'

/-- Identity PreSB morphism. -/
def identityMorphism {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : morphismPreSB C C where
  H_map := id
  quotient_map := id
  q_commutes := fun _ => rfl
  Q_transport := fun _ _ h => h
  Gamma_map := id
  R_map := id
  Creg_map := id
  Src_map := id
  Ifc_map := id
  Obs_map := id
  Stage_map := id
  Constr_map := id
  Rewrite_map := id
  Hol_map := id
  Res_map := id
  Stat_map := id
  NC_map := id
  Meta_map := id
  preservesStructuralDefectZero := fun h => h

/-- Componentwise composition of PreSB morphisms. -/
def composeMorphism {mathfrakS : scopeRecord.{u}} {C C' C'' : preSBCarrier mathfrakS}
    (g : morphismPreSB C' C'') (f : morphismPreSB C C') : morphismPreSB C C'' where
  H_map := fun x => g.H_map (f.H_map x)
  quotient_map := fun x => g.quotient_map (f.quotient_map x)
  q_commutes := by
    intro x
    rw [f.q_commutes x, g.q_commutes (f.H_map x)]
  Q_transport := fun x y h => g.Q_transport (f.quotient_map x) (f.quotient_map y)
    (f.Q_transport x y h)
  Gamma_map := fun x => g.Gamma_map (f.Gamma_map x)
  R_map := fun x => g.R_map (f.R_map x)
  Creg_map := fun x => g.Creg_map (f.Creg_map x)
  Src_map := fun x => g.Src_map (f.Src_map x)
  Ifc_map := fun x => g.Ifc_map (f.Ifc_map x)
  Obs_map := fun x => g.Obs_map (f.Obs_map x)
  Stage_map := fun x => g.Stage_map (f.Stage_map x)
  Constr_map := fun x => g.Constr_map (f.Constr_map x)
  Rewrite_map := fun x => g.Rewrite_map (f.Rewrite_map x)
  Hol_map := fun x => g.Hol_map (f.Hol_map x)
  Res_map := fun x => g.Res_map (f.Res_map x)
  Stat_map := fun x => g.Stat_map (f.Stat_map x)
  NC_map := fun x => g.NC_map (f.NC_map x)
  Meta_map := fun x => g.Meta_map (f.Meta_map x)
  preservesStructuralDefectZero := fun h => g.preservesStructuralDefectZero
    (f.preservesStructuralDefectZero h)

/-- The field maps form a category; proof fields are propositionally irrelevant. -/
theorem composeMorphism_left_id {mathfrakS : scopeRecord.{u}}
    {C D : preSBCarrier mathfrakS} (f : morphismPreSB C D) :
    composeMorphism (identityMorphism D) f = f := by
  cases f
  rfl

theorem composeMorphism_right_id {mathfrakS : scopeRecord.{u}}
    {C D : preSBCarrier mathfrakS} (f : morphismPreSB C D) :
    composeMorphism f (identityMorphism C) = f := by
  cases f
  rfl

theorem composeMorphism_assoc {mathfrakS : scopeRecord.{u}}
    {A B C D : preSBCarrier mathfrakS}
    (h : morphismPreSB C D) (g : morphismPreSB B C) (f : morphismPreSB A B) :
    composeMorphism h (composeMorphism g f) =
      composeMorphism (composeMorphism h g) f := rfl

/--
`def:aor:aor-subcategory`.

The AOR subcategory at scope `mathfrakS` consists of PreSB carriers whose
structural defect predicate is zero.
-/
def aorSubcategory (mathfrakS : scopeRecord.{u}) : Type (u + 1) :=
  { C : preSBCarrier mathfrakS // structuralDefectZero C }

/-- Morphisms in the full AOR subcategory are exactly ambient PreSB morphisms. -/
structure AORMorphism {mathfrakS : scopeRecord.{u}}
    (C C' : aorSubcategory mathfrakS) where
  toPreSB : morphismPreSB C.1 C'.1

/-- Object part of the inclusion `AOR_mathfrakS ↪ PreSB_mathfrakS`. -/
def aorInclusionObj {mathfrakS : scopeRecord.{u}}
    (C : aorSubcategory mathfrakS) : preSBCarrier mathfrakS :=
  C.1

/-- Arrow part of the inclusion `AOR_mathfrakS ↪ PreSB_mathfrakS`. -/
def aorInclusionHom {mathfrakS : scopeRecord.{u}} {C C' : aorSubcategory mathfrakS}
    (f : AORMorphism C C') : morphismPreSB (aorInclusionObj C) (aorInclusionObj C') :=
  f.toPreSB

/-- Isomorphism in the fixed-scope PreSB category. -/
structure PreSBIso {mathfrakS : scopeRecord.{u}}
    (C C' : preSBCarrier mathfrakS) where
  hom : morphismPreSB C C'
  inv : morphismPreSB C' C
  hom_inv_id : composeMorphism hom inv = identityMorphism C'
  inv_hom_id : composeMorphism inv hom = identityMorphism C

/-- The isomorphism structure includes actual inverse laws. -/
def identityIso {mathfrakS : scopeRecord.{u}} (C : preSBCarrier mathfrakS) : PreSBIso C C where
  hom := identityMorphism C
  inv := identityMorphism C
  hom_inv_id := composeMorphism_left_id _
  inv_hom_id := composeMorphism_left_id _

/-- The fully-faithful and isomorphism-invariant content of the inclusion. -/
structure FullSubcategoryWitness (mathfrakS : scopeRecord.{u}) where
  full :
    ∀ (C C' : aorSubcategory mathfrakS)
      (f : morphismPreSB (aorInclusionObj C) (aorInclusionObj C')),
      ∃ g : AORMorphism C C', aorInclusionHom g = f
  faithful :
    ∀ (C C' : aorSubcategory mathfrakS) (f g : AORMorphism C C'),
      aorInclusionHom f = aorInclusionHom g → f = g
  iso_preserves :
    ∀ {C C' : preSBCarrier mathfrakS}, PreSBIso C C' →
      structuralDefectZero C → structuralDefectZero C'
  iso_reflects :
    ∀ {C C' : preSBCarrier mathfrakS}, PreSBIso C C' →
      structuralDefectZero C' → structuralDefectZero C

/--
`thm:aor:aor-full-subcat`.

The inclusion from `AOR_mathfrakS` to `PreSB_mathfrakS` is full and faithful.
Moreover, because an isomorphism carries morphisms in both directions and
PreSB morphisms preserve the zero-defect predicate, AOR membership is
preserved and reflected by isomorphism within the fixed scope.
-/
theorem aorFullSubcat (mathfrakS : scopeRecord.{u}) :
    FullSubcategoryWitness mathfrakS where
  full := by
    intro C C' f
    exact ⟨⟨f⟩, rfl⟩
  faithful := by
    intro C C' f g h
    cases f
    cases g
    cases h
    rfl
  iso_preserves := by
    intro C C' e h
    exact e.hom.preservesStructuralDefectZero h
  iso_reflects := by
    intro C C' e h
    exact e.inv.preservesStructuralDefectZero h

end SixBirdsMetaMath.AOR.PreSB
