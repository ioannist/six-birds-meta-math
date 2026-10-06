import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.AOR.PreSB

namespace SixBirdsMetaMath.AOR.ClSB

open SixBirdsMetaMath.AOR.PreSB

universe u

/-!
This retained adapter is synchronized with the maintained Needles version.
References below to semantic AOR modules absent from this namespace mean
`SixBirdsNeedles.AOR.*`; this module does not re-export those endpoints.

Legacy compatibility model: the five-flag syntactic saturation below is not
the revised semantic closure. Use `AOR.Core`, `AuditKernel.canonical_closure`
and `PolicyCategory.reflection_universal` for inference closure with exact
certificate preservation. Arbitrary witness-adding reflection is refuted in
`WitnessReflectionObstruction`; the legacy theorem names are retained for
traceability and do not establish that stronger claim.


AOR paper §2 "The closure-completion functor `Cl_{SB}`".

This module hosts the AOR reflection adjunction:
- `def:aor:cl-sb-operator`              — closure-completion operator
- `thm:aor:cl-sb-construction`          — syntactic saturation is idempotent
- `thm:aor:cl-sb-universal-property`    — universal property of the reflection
- `thm:aor:cl-sb-adjunction`            — `Cl_{SB} ⊣ \iota`

The construction is a concrete syntactic saturation in this simplified Lean
carrier: it preserves all typed carrier fields and replaces exactly the five
`Prop` audit fields by `True`. It does not construct the paper's semantic
least completion or an extension lattice for Knaster--Tarski.
-/

/-- Legacy flag saturation keeps typed data and sets the five audit flags to True.
It does not construct semantic status payloads. -/
def saturatedCarrier {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : preSBCarrier mathfrakS where
  H := C.H
  H_admissible := C.H_admissible
  quotient := C.quotient
  q := C.q
  Q := C.Q
  Gamma := C.Gamma
  Gamma_admissible := C.Gamma_admissible
  R := C.R
  Creg := C.Creg
  Src := C.Src
  Src_admissible := C.Src_admissible
  Ifc := C.Ifc
  Ifc_admissible := C.Ifc_admissible
  Obs := C.Obs
  Stage := C.Stage
  Constr := C.Constr
  Rewrite := C.Rewrite
  Hol := C.Hol
  Res := C.Res
  Stat := C.Stat
  NC := C.NC
  Meta := C.Meta
  declaredRecordsTyped := True
  citedRoutesAudited := True
  residualsStatused := True
  nonclaimsRegistered := True
  metaAuditDischarged := True

/-- The saturated carrier has zero AOR structural defect. -/
theorem saturatedCarrier_zero {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : structuralDefectZero (saturatedCarrier C) := by
  exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩

/-- The saturation endomap is idempotent, hence a Foundations I closure operator. -/
def saturationClosure (mathfrakS : scopeRecord.{u}) :
    SixBirdsMetaMath.F1ClosureOp (preSBCarrier mathfrakS) where
  toFun := saturatedCarrier
  idempotent := by
    intro C
    cases C
    rfl

/--
`def:aor:cl-sb-operator`.

`Cl_SB` here sends a PreSB carrier to the syntactically saturated carrier.
The companion `reflectionUnit` is identity on the typed fields.
-/
def clSBOperator {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) : aorSubcategory mathfrakS :=
  ⟨saturatedCarrier C, saturatedCarrier_zero C⟩

/-- The unit `eta_C : C -> Cl_SB(C)` is the identity on all carrier fields. -/
def reflectionUnit {mathfrakS : scopeRecord.{u}}
    (C : preSBCarrier mathfrakS) :
    morphismPreSB C (aorInclusionObj (clSBOperator C)) where
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
  preservesStructuralDefectZero := fun _ => saturatedCarrier_zero C

/-- The subcarrier order used by the local fixed-point construction. -/
def subcarrierOrder {mathfrakS : scopeRecord.{u}}
    (C D : preSBCarrier mathfrakS) : Prop :=
  Nonempty (morphismPreSB C D)

/-- Saturation transports PreSB morphisms componentwise. -/
def saturatedMorphism {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (f : morphismPreSB C D) : morphismPreSB (saturatedCarrier C) (saturatedCarrier D) where
  H_map := f.H_map
  quotient_map := f.quotient_map
  q_commutes := f.q_commutes
  Q_transport := f.Q_transport
  Gamma_map := f.Gamma_map
  R_map := f.R_map
  Creg_map := f.Creg_map
  Src_map := f.Src_map
  Ifc_map := f.Ifc_map
  Obs_map := f.Obs_map
  Stage_map := f.Stage_map
  Constr_map := f.Constr_map
  Rewrite_map := f.Rewrite_map
  Hol_map := f.Hol_map
  Res_map := f.Res_map
  Stat_map := f.Stat_map
  NC_map := f.NC_map
  Meta_map := f.Meta_map
  preservesStructuralDefectZero := fun _ => saturatedCarrier_zero D

/-- Monotonicity of the saturation map with respect to `subcarrierOrder`. -/
theorem saturationMonotone {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS} :
    subcarrierOrder C D → subcarrierOrder (saturatedCarrier C) (saturatedCarrier D) := by
  intro h
  cases h with
  | intro f =>
      exact ⟨saturatedMorphism f⟩

/-- Lift a map from the seed carrier to an AOR carrier across saturation. -/
def liftAcrossClSB {mathfrakS : scopeRecord.{u}} {C : preSBCarrier mathfrakS}
    (D : aorSubcategory mathfrakS) (g : morphismPreSB C (aorInclusionObj D)) :
    AORMorphism (clSBOperator C) D where
  toPreSB :=
    { H_map := g.H_map
      quotient_map := g.quotient_map
      q_commutes := g.q_commutes
      Q_transport := g.Q_transport
      Gamma_map := g.Gamma_map
      R_map := g.R_map
      Creg_map := g.Creg_map
      Src_map := g.Src_map
      Ifc_map := g.Ifc_map
      Obs_map := g.Obs_map
      Stage_map := g.Stage_map
      Constr_map := g.Constr_map
      Rewrite_map := g.Rewrite_map
      Hol_map := g.Hol_map
      Res_map := g.Res_map
      Stat_map := g.Stat_map
      NC_map := g.NC_map
      Meta_map := g.Meta_map
      preservesStructuralDefectZero := fun _ => D.2 }

/-- Fieldwise equality of PreSB morphisms, avoiding irrelevant proof components. -/
def morphismAgrees {mathfrakS : scopeRecord.{u}} {C D : preSBCarrier mathfrakS}
    (f g : morphismPreSB C D) : Prop :=
  f.H_map = g.H_map ∧
    f.quotient_map = g.quotient_map ∧
      f.Gamma_map = g.Gamma_map ∧
        f.R_map = g.R_map ∧
          f.Creg_map = g.Creg_map ∧
            f.Src_map = g.Src_map ∧
              f.Ifc_map = g.Ifc_map ∧
                f.Obs_map = g.Obs_map ∧
                  f.Stage_map = g.Stage_map ∧
                    f.Constr_map = g.Constr_map ∧
                      f.Rewrite_map = g.Rewrite_map ∧
                        f.Hol_map = g.Hol_map ∧
                          f.Res_map = g.Res_map ∧
                            f.Stat_map = g.Stat_map ∧
                              f.NC_map = g.NC_map ∧ f.Meta_map = g.Meta_map

/-- The factorization equation `g = iota(bar_g) o eta_C`, fieldwise. -/
def factorsThroughUnit {mathfrakS : scopeRecord.{u}} {C : preSBCarrier mathfrakS}
    {D : aorSubcategory mathfrakS} (g : morphismPreSB C (aorInclusionObj D))
    (bar_g : AORMorphism (clSBOperator C) D) : Prop :=
  morphismAgrees g (composeMorphism (aorInclusionHom bar_g) (reflectionUnit C))

/-- The constructed lift factors through the reflection unit. -/
theorem liftAcrossClSB_factors {mathfrakS : scopeRecord.{u}} {C : preSBCarrier mathfrakS}
    (D : aorSubcategory mathfrakS) (g : morphismPreSB C (aorInclusionObj D)) :
    factorsThroughUnit g (liftAcrossClSB D g) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The canonical lift is unique at the level of underlying field maps. -/
theorem liftAcrossClSB_unique {mathfrakS : scopeRecord.{u}} {C : preSBCarrier mathfrakS}
    (D : aorSubcategory mathfrakS) (g : morphismPreSB C (aorInclusionObj D))
    (bar_g : AORMorphism (clSBOperator C) D) :
    factorsThroughUnit g bar_g →
      morphismAgrees (aorInclusionHom (liftAcrossClSB D g)) (aorInclusionHom bar_g) := by
  intro hbar
  have hlift := liftAcrossClSB_factors D g
  rcases hlift with
    ⟨h₁H, h₁q, h₁Gamma, h₁R, h₁Creg, h₁Src, h₁Ifc, h₁Obs,
      h₁Stage, h₁Constr, h₁Rewrite, h₁Hol, h₁Res, h₁Stat, h₁NC, h₁Meta⟩
  rcases hbar with
    ⟨h₂H, h₂q, h₂Gamma, h₂R, h₂Creg, h₂Src, h₂Ifc, h₂Obs,
      h₂Stage, h₂Constr, h₂Rewrite, h₂Hol, h₂Res, h₂Stat, h₂NC, h₂Meta⟩
  exact ⟨h₁H.symm.trans h₂H,
    h₁q.symm.trans h₂q,
    h₁Gamma.symm.trans h₂Gamma,
    h₁R.symm.trans h₂R,
    h₁Creg.symm.trans h₂Creg,
    h₁Src.symm.trans h₂Src,
    h₁Ifc.symm.trans h₂Ifc,
    h₁Obs.symm.trans h₂Obs,
    h₁Stage.symm.trans h₂Stage,
    h₁Constr.symm.trans h₂Constr,
    h₁Rewrite.symm.trans h₂Rewrite,
    h₁Hol.symm.trans h₂Hol,
    h₁Res.symm.trans h₂Res,
    h₁Stat.symm.trans h₂Stat,
    h₁NC.symm.trans h₂NC,
    h₁Meta.symm.trans h₂Meta⟩

/-- The limited data proved for syntactic audit-proposition saturation. -/
structure ClSBConstructionWitness (mathfrakS : scopeRecord.{u}) where
  closureOperator : SixBirdsMetaMath.F1ClosureOp (preSBCarrier mathfrakS)
  saturation_monotone :
    ∀ {C D : preSBCarrier mathfrakS},
      subcarrierOrder C D → subcarrierOrder (closureOperator C) (closureOperator D)
  saturation_fixedPoint :
    ∀ C : preSBCarrier mathfrakS, closureOperator (closureOperator C) = closureOperator C
  syntactic_factorization :
    ∀ C : preSBCarrier mathfrakS, ∀ D : aorSubcategory mathfrakS,
      ∀ g : morphismPreSB C (aorInclusionObj D),
        ∃ bar_g : AORMorphism (clSBOperator C) D,
          factorsThroughUnit g bar_g ∧
            ∀ bar_g' : AORMorphism (clSBOperator C) D,
              factorsThroughUnit g bar_g' →
                morphismAgrees (aorInclusionHom bar_g) (aorInclusionHom bar_g')
  belongsToAOR :
    ∀ C : preSBCarrier mathfrakS, structuralDefectZero (closureOperator C)
  wellDefined :
    ∀ C : preSBCarrier mathfrakS, clSBOperator C = ⟨closureOperator C, belongsToAOR C⟩

/--
`thm:aor:cl-sb-construction`.

The concrete audit-proposition saturation is monotone under the encoded
morphism-existence relation and idempotent. This witness has no complete-lattice
or semantic leastness field.
-/
theorem clSBConstruction (mathfrakS : scopeRecord.{u}) :
    ∃ _ : ClSBConstructionWitness mathfrakS, True := by
  exact ⟨{
    closureOperator := saturationClosure mathfrakS
    saturation_monotone := by
      intro C D h
      exact saturationMonotone h
    saturation_fixedPoint := by
      intro C
      exact (saturationClosure mathfrakS).idempotent C
    syntactic_factorization := by
      intro C D g
      exact ⟨liftAcrossClSB D g, liftAcrossClSB_factors D g,
        fun bar_g' hbar => liftAcrossClSB_unique D g bar_g' hbar⟩
    belongsToAOR := saturatedCarrier_zero
    wellDefined := by
      intro C
      rfl
  }, True.intro⟩

/-- Universal property package for the reflection `Cl_SB`. -/
structure ClSBUniversalPropertyWitness (mathfrakS : scopeRecord.{u}) : Prop where
  factor :
    ∀ (C : preSBCarrier mathfrakS) (D : aorSubcategory mathfrakS)
      (g : morphismPreSB C (aorInclusionObj D)),
      ∃ bar_g : AORMorphism (clSBOperator C) D, factorsThroughUnit g bar_g
  unique :
    ∀ (C : preSBCarrier mathfrakS) (D : aorSubcategory mathfrakS)
      (g : morphismPreSB C (aorInclusionObj D))
      (bar_g₁ bar_g₂ : AORMorphism (clSBOperator C) D),
      factorsThroughUnit g bar_g₁ →
        factorsThroughUnit g bar_g₂ →
          morphismAgrees (aorInclusionHom bar_g₁) (aorInclusionHom bar_g₂)

/--
`thm:aor:cl-sb-universal-property`.

Every PreSB morphism from `C` to an included AOR carrier factors through
`eta_C`, and the factor is unique at the level of the underlying field maps.
This is a property of the simplified carrier whose audit fields are bare
propositions; it is not a free-choice theorem for semantic audit fillers.
-/
theorem clSBUniversalProperty (mathfrakS : scopeRecord.{u}) :
    ClSBUniversalPropertyWitness mathfrakS where
  factor := by
    intro C D g
    exact ⟨liftAcrossClSB D g, liftAcrossClSB_factors D g⟩
  unique := by
    intro C D g bar_g₁ bar_g₂ h₁ h₂
    rcases h₁ with
      ⟨h₁H, h₁q, h₁Gamma, h₁R, h₁Creg, h₁Src, h₁Ifc, h₁Obs,
        h₁Stage, h₁Constr, h₁Rewrite, h₁Hol, h₁Res, h₁Stat, h₁NC, h₁Meta⟩
    rcases h₂ with
      ⟨h₂H, h₂q, h₂Gamma, h₂R, h₂Creg, h₂Src, h₂Ifc, h₂Obs,
        h₂Stage, h₂Constr, h₂Rewrite, h₂Hol, h₂Res, h₂Stat, h₂NC, h₂Meta⟩
    exact ⟨h₁H.symm.trans h₂H,
      h₁q.symm.trans h₂q,
      h₁Gamma.symm.trans h₂Gamma,
      h₁R.symm.trans h₂R,
      h₁Creg.symm.trans h₂Creg,
      h₁Src.symm.trans h₂Src,
      h₁Ifc.symm.trans h₂Ifc,
      h₁Obs.symm.trans h₂Obs,
      h₁Stage.symm.trans h₂Stage,
      h₁Constr.symm.trans h₂Constr,
      h₁Rewrite.symm.trans h₂Rewrite,
      h₁Hol.symm.trans h₂Hol,
      h₁Res.symm.trans h₂Res,
      h₁Stat.symm.trans h₂Stat,
      h₁NC.symm.trans h₂NC,
      h₁Meta.symm.trans h₂Meta⟩

/-- Identity-like counit: all field maps are identities on the AOR carrier. -/
def identityLikeCounit {mathfrakS : scopeRecord.{u}} (D : aorSubcategory mathfrakS)
    (f : AORMorphism (clSBOperator (aorInclusionObj D)) D) : Prop :=
  f.toPreSB.H_map = id ∧
    f.toPreSB.quotient_map = id ∧
      f.toPreSB.Gamma_map = id ∧
        f.toPreSB.R_map = id ∧
          f.toPreSB.Creg_map = id ∧
            f.toPreSB.Src_map = id ∧
              f.toPreSB.Ifc_map = id ∧
                f.toPreSB.Obs_map = id ∧
                  f.toPreSB.Stage_map = id ∧
                    f.toPreSB.Constr_map = id ∧
                      f.toPreSB.Rewrite_map = id ∧
                        f.toPreSB.Hol_map = id ∧
                          f.toPreSB.Res_map = id ∧
                            f.toPreSB.Stat_map = id ∧
                              f.toPreSB.NC_map = id ∧ f.toPreSB.Meta_map = id

/-- The counit at an AOR object is identity on all carrier fields. -/
def clSBCounit {mathfrakS : scopeRecord.{u}} (D : aorSubcategory mathfrakS) :
    AORMorphism (clSBOperator (aorInclusionObj D)) D where
  toPreSB :=
    { H_map := id
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
      preservesStructuralDefectZero := fun _ => D.2 }

/-- Adjunction package for `Cl_SB ⊣ iota`. -/
structure ClSBAdjunctionWitness (mathfrakS : scopeRecord.{u}) where
  onHom :
    ∀ {C D : preSBCarrier mathfrakS}, morphismPreSB C D →
      AORMorphism (clSBOperator C) (clSBOperator D)
  unit : ∀ C : preSBCarrier mathfrakS, morphismPreSB C (aorInclusionObj (clSBOperator C))
  universalProperty : ClSBUniversalPropertyWitness mathfrakS
  counit : ∀ D : aorSubcategory mathfrakS, AORMorphism (clSBOperator (aorInclusionObj D)) D
  counit_identity : ∀ D : aorSubcategory mathfrakS, identityLikeCounit D (counit D)

/--
`thm:aor:cl-sb-adjunction`.

The syntactic saturation extends on the encoded field maps, with a fieldwise
factorization and identity-field counit. The witness does not include functor
laws, naturality, or triangle identities for the paper's semantic categories.
-/
theorem clSBAdjunction (mathfrakS : scopeRecord.{u}) :
    ∃ _ : ClSBAdjunctionWitness mathfrakS, True := by
  exact ⟨{
    onHom := fun f => ⟨saturatedMorphism f⟩
    unit := reflectionUnit
    universalProperty := clSBUniversalProperty mathfrakS
    counit := clSBCounit
    counit_identity := by
      intro D
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl⟩
  }, True.intro⟩

end SixBirdsMetaMath.AOR.ClSB
