import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F35 Scale Descent / Renormalization.

A coarse law is a target, relation, or dynamic readout that descends through a
scale quotient. Renormalization is descent of already-descended law data along
the next coarsening map in the scale tower.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.ScaleDescentRenormalization

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- A target readout survives at a scale when it descends through that scale
quotient. -/
def ScaleTargetDescends {H Q T : Type} (scale : H → Q) (target : H → T) :
    Prop :=
  Descends scale (fun h : H => h) target

/-- Scale-descent obstruction for a target readout. -/
def ScaleTargetObstruction {H Q T : Type} (scale : H → Q) (target : H → T) :
    (H × H) → Prop :=
  splitPairObstruction scale (fun h : H => h) target

/-- No scale-descent obstruction is present. -/
def ScaleTargetObstructionEmpty {H Q T : Type} (scale : H → Q)
    (target : H → T) : Prop :=
  ObstructionEmpty (ScaleTargetObstruction scale target)

/-- Target-family scale descent, represented by a joint signature. -/
def ScaleFamilyDescends {H Q Signature : Type} (scale : H → Q)
    (signature : H → Signature) : Prop :=
  ScaleTargetDescends scale signature

/-- Target-family scale obstruction. -/
def ScaleFamilyObstruction {H Q Signature : Type} (scale : H → Q)
    (signature : H → Signature) : (H × H) → Prop :=
  ScaleTargetObstruction scale signature

/-- No target-family scale obstruction is present. -/
def ScaleFamilyObstructionEmpty {H Q Signature : Type} (scale : H → Q)
    (signature : H → Signature) : Prop :=
  ScaleTargetObstructionEmpty scale signature

/-- A relation law descends through an abstract tuple-scale quotient. -/
def RelationScaleLaw {TupleH TupleQ : Type} (tupleScale : TupleH → TupleQ)
    (relation : TupleH → Prop) : Prop :=
  Descends tupleScale (fun tuple : TupleH => tuple) relation

/-- Relation-law scale obstruction. -/
def RelationScaleObstruction {TupleH TupleQ : Type} (tupleScale : TupleH → TupleQ)
    (relation : TupleH → Prop) : (TupleH × TupleH) → Prop :=
  splitPairObstruction tupleScale (fun tuple : TupleH => tuple) relation

/-- No relation-law scale obstruction is present. -/
def RelationScaleObstructionEmpty {TupleH TupleQ : Type}
    (tupleScale : TupleH → TupleQ) (relation : TupleH → Prop) : Prop :=
  ObstructionEmpty (RelationScaleObstruction tupleScale relation)

/-- Fine dynamics descends to the scale when the updated scale quotient is
determined by the current scale quotient. -/
def DynamicScaleDescends {H Q : Type} (scale : H → Q) (update : H → H) :
    Prop :=
  Descends scale update scale

/-- Dynamic scale obstruction. -/
def DynamicScaleObstruction {H Q : Type} (scale : H → Q) (update : H → H) :
    (H × H) → Prop :=
  splitPairObstruction scale update scale

/-- No dynamic scale obstruction is present. -/
def DynamicScaleObstructionEmpty {H Q : Type} (scale : H → Q)
    (update : H → H) : Prop :=
  ObstructionEmpty (DynamicScaleObstruction scale update)

/-- A law/readout on scale `n` renormalizes to scale `n+1` when it descends
through the scale coarsening map. -/
def Renormalizes {Qn Qnext V : Type} (coarsen : Qn → Qnext)
    (law : Qn → V) : Prop :=
  Descends coarsen (fun q : Qn => q) law

/-- Law-coarsening obstruction for renormalization. -/
def RenormalizationObstruction {Qn Qnext V : Type} (coarsen : Qn → Qnext)
    (law : Qn → V) : (Qn × Qn) → Prop :=
  splitPairObstruction coarsen (fun q : Qn => q) law

/-- No law-coarsening obstruction is present. -/
def RenormalizationObstructionEmpty {Qn Qnext V : Type} (coarsen : Qn → Qnext)
    (law : Qn → V) : Prop :=
  ObstructionEmpty (RenormalizationObstruction coarsen law)

/-- A declared scale tower step: `q_{n+1} = s_n ∘ q_n`. -/
def ScaleTowerStep {H Qn Qnext : Type} (scale : H → Qn) (nextScale : H → Qnext)
    (coarsen : Qn → Qnext) : Prop :=
  coarsen ∘ scale = nextScale

/-- A budgeted scale law carries an explicit residual budget. -/
def BudgetedScaleLaw {Index Residual Budget : Type} (residual : Index → Residual)
    (budget : Budget) (WithinBudget : Residual → Budget → Prop) : Prop :=
  ∀ i, WithinBudget (residual i) budget

/-- An asymptotic scale law has a declared convergence predicate for residuals
along the tower. -/
def AsymptoticScaleLaw {Index Residual : Type} (residual : Index → Residual)
    (Vanishes : (Index → Residual) → Prop) : Prop :=
  Vanishes residual

/-- Universality: two lower packages descend or budget to a common coarse law
class. -/
def UniversalityClass {Pkg₁ Pkg₂ Coarse : Type} (descend₁ : Pkg₁ → Coarse)
    (descend₂ : Pkg₂ → Coarse) (pkg₁ : Pkg₁) (pkg₂ : Pkg₂) : Prop :=
  descend₁ pkg₁ = descend₂ pkg₂

/-- Fixed point status for an abstract renormalization operator. -/
def ScaleFixedPoint {LawClass : Type} (renormalize : LawClass → LawClass)
    (law : LawClass) : Prop :=
  renormalize law = law

/-- Relevance status is a declared comparison of residual effect against a
threshold. -/
def RelevantDistinction {Effect Threshold : Type} (effect : Effect)
    (threshold : Threshold) (PersistsAbove : Effect → Threshold → Prop) : Prop :=
  PersistsAbove effect threshold

/-- Irrelevance status is a declared comparison that the residual effect
vanishes or stays within budget. -/
def IrrelevantDistinction {Effect Budget : Type} (effect : Effect)
    (budget : Budget) (WithinBudget : Effect → Budget → Prop) : Prop :=
  WithinBudget effect budget

/-- Marginal status is a declared scale-neutral/boundary classification. -/
def MarginalDistinction {Effect : Type} (effect : Effect)
    (ScaleNeutral : Effect → Prop) : Prop :=
  ScaleNeutral effect

/-- Canonical strict repair for a target that fails to descend: remember the
old scale quotient and the target signature. -/
def scaleTargetRepairQuotient {H Q T : Type} (scale : H → Q) (target : H → T) :
    H → Q × T :=
  sourceRepairQuotient scale (fun h : H => h) target

/-- Source status vocabulary for scale descent and renormalization. -/
inductive ScaleDescentStatus where
  | exactScaleLaw
  | exactRenormalizedLaw
  | dynamicCoarseLaw
  | budgetedScaleLaw
  | asymptoticScaleLaw
  | universalityClass
  | scaleFixedPoint
  | relevantDistinction
  | irrelevantDistinction
  | marginalDistinction
  | coarseLawOverreach
  | scaleTowerAbsent
  | localScaleLaw
  | globalScaleObstructed
  | presentationDependentScaleLaw
  | protocolScaleArtifact
deriving DecidableEq

/-- Meaning assignment for the F35 status vocabulary. -/
def ScaleDescentStatusHolds (exact renormalized dynamic budgeted asymptotic
    universal fixed relevant irrelevant marginal overreach towerAbsent localOnly
    globalObstructed presentationDependent protocol : Prop) :
    ScaleDescentStatus → Prop
  | ScaleDescentStatus.exactScaleLaw => exact
  | ScaleDescentStatus.exactRenormalizedLaw => renormalized
  | ScaleDescentStatus.dynamicCoarseLaw => dynamic
  | ScaleDescentStatus.budgetedScaleLaw => budgeted
  | ScaleDescentStatus.asymptoticScaleLaw => asymptotic
  | ScaleDescentStatus.universalityClass => universal
  | ScaleDescentStatus.scaleFixedPoint => fixed
  | ScaleDescentStatus.relevantDistinction => relevant
  | ScaleDescentStatus.irrelevantDistinction => irrelevant
  | ScaleDescentStatus.marginalDistinction => marginal
  | ScaleDescentStatus.coarseLawOverreach => overreach
  | ScaleDescentStatus.scaleTowerAbsent => towerAbsent
  | ScaleDescentStatus.localScaleLaw => localOnly
  | ScaleDescentStatus.globalScaleObstructed => globalObstructed
  | ScaleDescentStatus.presentationDependentScaleLaw => presentationDependent
  | ScaleDescentStatus.protocolScaleArtifact => protocol

/-- Exact target scale descent iff no target scale obstruction is present. -/
theorem scale_target_descends_iff_no_obstruction {H Q T : Type}
    (scale : H → Q) (target : H → T) (hscale : Function.Surjective scale) :
    ScaleTargetDescends scale target ↔ ScaleTargetObstructionEmpty scale target :=
  descent_repair_normal_form scale (fun h : H => h) target hscale

/-- Factorization form of exact target scale descent. -/
theorem scale_target_descends_iff_factorization {H Q T : Type}
    (scale : H → Q) (target : H → T) :
    ScaleTargetDescends scale target ↔
      ∃ targetBar : Q → T, targetBar ∘ scale = target := by
  constructor
  · intro hdesc
    rcases hdesc with ⟨targetBar, htargetBar⟩
    exact ⟨targetBar, by simpa [Function.comp] using htargetBar⟩
  · intro hfactor
    rcases hfactor with ⟨targetBar, htargetBar⟩
    exact ⟨targetBar, by simpa [Function.comp] using htargetBar⟩

/-- Target-family scale descent iff no joint-signature obstruction is present. -/
theorem scale_family_descends_iff_no_obstruction {H Q Signature : Type}
    (scale : H → Q) (signature : H → Signature)
    (hscale : Function.Surjective scale) :
    ScaleFamilyDescends scale signature ↔
      ScaleFamilyObstructionEmpty scale signature :=
  scale_target_descends_iff_no_obstruction scale signature hscale

/-- Relation-law scale descent iff no relation obstruction is present. -/
theorem relation_scale_law_iff_no_obstruction {TupleH TupleQ : Type}
    (tupleScale : TupleH → TupleQ) (relation : TupleH → Prop)
    (htupleScale : Function.Surjective tupleScale) :
    RelationScaleLaw tupleScale relation ↔
      RelationScaleObstructionEmpty tupleScale relation :=
  descent_repair_normal_form tupleScale (fun tuple : TupleH => tuple) relation
    htupleScale

/-- Dynamic scale descent iff no dynamic obstruction is present. -/
theorem dynamic_scale_descends_iff_no_obstruction {H Q : Type}
    (scale : H → Q) (update : H → H) (hscale : Function.Surjective scale) :
    DynamicScaleDescends scale update ↔ DynamicScaleObstructionEmpty scale update :=
  descent_repair_normal_form scale update scale hscale

/-- Exact renormalization of a scale law iff no law-coarsening obstruction is
present. -/
theorem renormalizes_iff_no_obstruction {Qn Qnext V : Type}
    (coarsen : Qn → Qnext) (law : Qn → V)
    (hcoarsen : Function.Surjective coarsen) :
    Renormalizes coarsen law ↔ RenormalizationObstructionEmpty coarsen law :=
  descent_repair_normal_form coarsen (fun q : Qn => q) law hcoarsen

/-- Factorization form of exact renormalization. -/
theorem renormalizes_iff_factorization {Qn Qnext V : Type}
    (coarsen : Qn → Qnext) (law : Qn → V) :
    Renormalizes coarsen law ↔
      ∃ lawNext : Qnext → V, lawNext ∘ coarsen = law := by
  constructor
  · intro hren
    rcases hren with ⟨lawNext, hlawNext⟩
    exact ⟨lawNext, by simpa [Function.comp] using hlawNext⟩
  · intro hfactor
    rcases hfactor with ⟨lawNext, hlawNext⟩
    exact ⟨lawNext, by simpa [Function.comp] using hlawNext⟩

/-- A declared tower step gives forward descent from the finer scale quotient
to the coarser one. -/
theorem scale_tower_step_forward_descends {H Qn Qnext : Type}
    (scale : H → Qn) (nextScale : H → Qnext) (coarsen : Qn → Qnext) :
    ScaleTowerStep scale nextScale coarsen →
      Descends scale (fun h : H => h) nextScale := by
  intro hstep
  refine ⟨coarsen, ?_⟩
  simpa [Function.comp, ScaleTowerStep] using hstep

/-- The canonical target repair refines the original scale quotient. -/
theorem scale_target_repair_refines {H Q T : Type} (scale : H → Q)
    (target : H → T) :
    SourceRefinement (scaleTargetRepairQuotient scale target) scale :=
  source_repair_refines scale (fun h : H => h) target

/-- After canonical repair, the target descends by projection. -/
theorem scale_target_repair_descends {H Q T : Type} (scale : H → Q)
    (target : H → T) :
    ScaleTargetDescends (scaleTargetRepairQuotient scale target) target :=
  source_repair_descends scale (fun h : H => h) target

/--
Scale Descent / Renormalization Normal Form. Exact coarse target lawhood,
target-family lawhood, relation lawhood, dynamic descent, and renormalized
law descent are all split-pair obstruction criteria for the relevant quotient
map in the scale tower.
-/
theorem scale_descent_renormalization {H Qn Qnext T Signature TupleH TupleQ V : Type}
    (scale : H → Qn) (nextScale : H → Qnext) (coarsen : Qn → Qnext)
    (target : H → T) (signature : H → Signature) (update : H → H)
    (tupleScale : TupleH → TupleQ) (relation : TupleH → Prop)
    (law : Qn → V)
    (hscale : Function.Surjective scale)
    (hcoarsen : Function.Surjective coarsen)
    (htupleScale : Function.Surjective tupleScale) :
    (ScaleTargetDescends scale target ↔ ScaleTargetObstructionEmpty scale target) ∧
      (ScaleTargetDescends scale target ↔
        ∃ targetBar : Qn → T, targetBar ∘ scale = target) ∧
        (ScaleFamilyDescends scale signature ↔
          ScaleFamilyObstructionEmpty scale signature) ∧
          (RelationScaleLaw tupleScale relation ↔
            RelationScaleObstructionEmpty tupleScale relation) ∧
            (DynamicScaleDescends scale update ↔
              DynamicScaleObstructionEmpty scale update) ∧
              (Renormalizes coarsen law ↔
                RenormalizationObstructionEmpty coarsen law) ∧
                (Renormalizes coarsen law ↔
                  ∃ lawNext : Qnext → V, lawNext ∘ coarsen = law) ∧
                  (ScaleTowerStep scale nextScale coarsen →
                    Descends scale (fun h : H => h) nextScale) ∧
                    SourceRefinement (scaleTargetRepairQuotient scale target) scale ∧
                    ScaleTargetDescends (scaleTargetRepairQuotient scale target)
                      target := by
  exact ⟨scale_target_descends_iff_no_obstruction scale target hscale,
    scale_target_descends_iff_factorization scale target,
    scale_family_descends_iff_no_obstruction scale signature hscale,
    relation_scale_law_iff_no_obstruction tupleScale relation htupleScale,
    dynamic_scale_descends_iff_no_obstruction scale update hscale,
    renormalizes_iff_no_obstruction coarsen law hcoarsen,
    renormalizes_iff_factorization coarsen law,
    scale_tower_step_forward_descends scale nextScale coarsen,
    scale_target_repair_refines scale target,
    scale_target_repair_descends scale target⟩

/-- Paper F35: target descent is fiber constancy, its quotient readout is
unique, and renormalization is constancy on the coarsening fibers. -/
theorem scale_descent_renormalization_paper {H Qn Qnext T : Type}
    (q_n : H → Qn) (q_next : H → Qnext) (c : Qn → Qnext)
    (t : H → T)
    (hq_n : Function.Surjective q_n)
    (hc : Function.Surjective c)
    (_hstep : c ∘ q_n = q_next) :
    ((∃ tb : Qn → T, tb ∘ q_n = t) ↔
      ∀ h h', q_n h = q_n h' → t h = t h') ∧
    (∀ tb tb' : Qn → T,
      tb ∘ q_n = t → tb' ∘ q_n = t → tb = tb') ∧
    (∀ tb : Qn → T, tb ∘ q_n = t →
      ((∃ tb' : Qnext → T, tb' ∘ c = tb) ↔
        ∀ x x', c x = c x' → tb x = tb x')) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨tb, htb⟩ h h' heq
      have hh := congrFun htb h
      have hh' := congrFun htb h'
      calc
        t h = tb (q_n h) := hh.symm
        _ = tb (q_n h') := congrArg tb heq
        _ = t h' := hh'
    · intro hfiber
      let tb : Qn → T := fun x => t (Classical.choose (hq_n x))
      refine ⟨tb, ?_⟩
      funext h
      exact hfiber (Classical.choose (hq_n (q_n h))) h
        (Classical.choose_spec (hq_n (q_n h)))
  · intro tb tb' htb htb'
    funext x
    obtain ⟨h, rfl⟩ := hq_n x
    calc
      tb (q_n h) = t h := congrFun htb h
      _ = tb' (q_n h) := (congrFun htb' h).symm
  · intro tb _
    constructor
    · rintro ⟨tb', htb'⟩ x x' heq
      calc
        tb x = tb' (c x) := (congrFun htb' x).symm
        _ = tb' (c x') := congrArg tb' heq
        _ = tb x' := congrFun htb' x'
    · intro hfiber
      let tb' : Qnext → T := fun y => tb (Classical.choose (hc y))
      refine ⟨tb', ?_⟩
      funext x
      exact hfiber (Classical.choose (hc (c x))) x
        (Classical.choose_spec (hc (c x)))

/-- Coherent readouts at consecutive scales reconstruct the raw target at
the next scale; this is where the tower equation is used. -/
theorem coherent_next_scale_readout_recovers_target
    {H Qn Qnext T : Type}
    (q_n : H → Qn) (q_next : H → Qnext) (c : Qn → Qnext)
    (t : H → T) (hstep : c ∘ q_n = q_next)
    (tb_n : Qn → T) (tb_next : Qnext → T)
    (htb_n : tb_n ∘ q_n = t) (hcoherent : tb_n = tb_next ∘ c) :
    t = tb_next ∘ q_next := by
  calc
    t = tb_n ∘ q_n := htb_n.symm
    _ = (tb_next ∘ c) ∘ q_n := by rw [hcoherent]
    _ = tb_next ∘ q_next := by
      funext h
      exact congrArg tb_next (congrFun hstep h)

/-- For a descended readout at scale n, descent at scale n+1 is precisely
constancy of that readout on the coarsening fibers. -/
theorem next_scale_descends_iff_coarsening_fiber_constant
    {H Qn Qnext T : Type}
    (q_n : H → Qn) (q_next : H → Qnext) (c : Qn → Qnext)
    (t : H → T) (hq_n : Function.Surjective q_n)
    (hc : Function.Surjective c) (hstep : c ∘ q_n = q_next)
    (tb_n : Qn → T) (htb_n : tb_n ∘ q_n = t) :
    (∃ tb_next : Qnext → T, tb_next ∘ q_next = t) ↔
      ∀ x x', c x = c x' → tb_n x = tb_n x' := by
  constructor
  · rintro ⟨tb_next, htb_next⟩
    have hcoherent : tb_n = tb_next ∘ c := by
      funext x
      obtain ⟨h, rfl⟩ := hq_n x
      calc
        tb_n (q_n h) = t h := congrFun htb_n h
        _ = tb_next (q_next h) := (congrFun htb_next h).symm
        _ = tb_next (c (q_n h)) :=
          congrArg tb_next (congrFun hstep h).symm
    intro x x' heq
    calc
      tb_n x = tb_next (c x) := congrFun hcoherent x
      _ = tb_next (c x') := congrArg tb_next heq
      _ = tb_n x' := (congrFun hcoherent x').symm
  · intro hfiber
    let tb_next : Qnext → T := fun y => tb_n (Classical.choose (hc y))
    have hcoherent : tb_n = tb_next ∘ c := by
      funext x
      exact (hfiber (Classical.choose (hc (c x))) x
        (Classical.choose_spec (hc (c x)))).symm
    exact ⟨tb_next,
      (coherent_next_scale_readout_recovers_target q_n q_next c t hstep
        tb_n tb_next htb_n hcoherent).symm⟩

/-- F35 with the tower-composition law and the direct next-scale criterion. -/
theorem scale_descent_renormalization_paper_tower
    {H Qn Qnext T : Type}
    (q_n : H → Qn) (q_next : H → Qnext) (c : Qn → Qnext)
    (t : H → T)
    (hq_n : Function.Surjective q_n)
    (hc : Function.Surjective c)
    (hstep : c ∘ q_n = q_next) :
    ((∃ tb : Qn → T, tb ∘ q_n = t) ↔
      ∀ h h', q_n h = q_n h' → t h = t h') ∧
    (∀ tb tb' : Qn → T,
      tb ∘ q_n = t → tb' ∘ q_n = t → tb = tb') ∧
    (∀ tb : Qn → T, tb ∘ q_n = t →
      ((∃ tb' : Qnext → T, tb' ∘ c = tb) ↔
        ∀ x x', c x = c x' → tb x = tb x')) ∧
    (∀ tb_n : Qn → T, ∀ tb_next : Qnext → T,
      tb_n ∘ q_n = t → tb_n = tb_next ∘ c →
        t = tb_next ∘ q_next) ∧
    (∀ tb_n : Qn → T, tb_n ∘ q_n = t →
      ((∃ tb_next : Qnext → T, tb_next ∘ q_next = t) ↔
        ∀ x x', c x = c x' → tb_n x = tb_n x')) := by
  rcases scale_descent_renormalization_paper q_n q_next c t hq_n hc
      hstep with ⟨hdescent, hunique, hrenormalize⟩
  exact ⟨hdescent, hunique, hrenormalize,
    fun tb_n tb_next htb_n hcoherent =>
      coherent_next_scale_readout_recovers_target q_n q_next c t
        hstep tb_n tb_next htb_n hcoherent,
    fun tb_n htb_n =>
      next_scale_descends_iff_coarsening_fiber_constant q_n q_next c t
        hq_n hc hstep tb_n htb_n⟩

/-- A next-scale factorization pulls back along the coarsening map. -/
theorem next_scale_descent_implies_current_descent
    {H Qn Qnext T : Type}
    (q_n : H → Qn) (q_next : H → Qnext) (c : Qn → Qnext)
    (t : H → T) (hstep : c ∘ q_n = q_next) :
    (∃ tb_next : Qnext → T, tb_next ∘ q_next = t) →
      ∃ tb_n : Qn → T, tb_n ∘ q_n = t := by
  rintro ⟨tb_next, htb_next⟩
  refine ⟨tb_next ∘ c, ?_⟩
  funext h
  exact (congrArg tb_next (congrFun hstep h)).trans (congrFun htb_next h)

/-- Descent at the next scale is equivalent to existence of a current-scale
readout constant on the coarsening fibers; no readout is presupposed. -/
theorem next_scale_descends_iff_exists_current_fiber_constant
    {H Qn Qnext T : Type}
    (q_n : H → Qn) (q_next : H → Qnext) (c : Qn → Qnext)
    (t : H → T) (hc : Function.Surjective c) (hstep : c ∘ q_n = q_next) :
    (∃ tb_next : Qnext → T, tb_next ∘ q_next = t) ↔
      ∃ tb_n : Qn → T, tb_n ∘ q_n = t ∧
        ∀ x x', c x = c x' → tb_n x = tb_n x' := by
  constructor
  · rintro ⟨tb_next, htb_next⟩
    refine ⟨tb_next ∘ c, ?_, ?_⟩
    · funext h
      exact (congrArg tb_next (congrFun hstep h)).trans (congrFun htb_next h)
    · intro x x' hxx'
      exact congrArg tb_next hxx'
  · rintro ⟨tb_n, htb_n, hfiber⟩
    let tb_next : Qnext → T := fun y => tb_n (Classical.choose (hc y))
    have hcoherent : tb_n = tb_next ∘ c := by
      funext x
      exact (hfiber (Classical.choose (hc (c x))) x
        (Classical.choose_spec (hc (c x)))).symm
    exact ⟨tb_next,
      (coherent_next_scale_readout_recovers_target q_n q_next c t hstep
        tb_n tb_next htb_n hcoherent).symm⟩

/-- F35's tower clauses with downward descent and the full existential
next-scale criterion, without assuming a supplied current-scale readout. -/
theorem scale_descent_renormalization_paper_tower_strengthened
    {H Qn Qnext T : Type}
    (q_n : H → Qn) (q_next : H → Qnext) (c : Qn → Qnext)
    (t : H → T)
    (hq_n : Function.Surjective q_n)
    (hc : Function.Surjective c)
    (hstep : c ∘ q_n = q_next) :
    (((∃ tb : Qn → T, tb ∘ q_n = t) ↔
      ∀ h h', q_n h = q_n h' → t h = t h') ∧
    (∀ tb tb' : Qn → T,
      tb ∘ q_n = t → tb' ∘ q_n = t → tb = tb') ∧
    (∀ tb : Qn → T, tb ∘ q_n = t →
      ((∃ tb' : Qnext → T, tb' ∘ c = tb) ↔
        ∀ x x', c x = c x' → tb x = tb x')) ∧
    (∀ tb_n : Qn → T, ∀ tb_next : Qnext → T,
      tb_n ∘ q_n = t → tb_n = tb_next ∘ c →
        t = tb_next ∘ q_next) ∧
    (∀ tb_n : Qn → T, tb_n ∘ q_n = t →
      ((∃ tb_next : Qnext → T, tb_next ∘ q_next = t) ↔
        ∀ x x', c x = c x' → tb_n x = tb_n x'))) ∧
    ((∃ tb_next : Qnext → T, tb_next ∘ q_next = t) →
      ∃ tb_n : Qn → T, tb_n ∘ q_n = t) ∧
    ((∃ tb_next : Qnext → T, tb_next ∘ q_next = t) ↔
      ∃ tb_n : Qn → T, tb_n ∘ q_n = t ∧
        ∀ x x', c x = c x' → tb_n x = tb_n x') := by
  exact ⟨scale_descent_renormalization_paper_tower q_n q_next c t hq_n hc hstep,
    next_scale_descent_implies_current_descent q_n q_next c t hstep,
    next_scale_descends_iff_exists_current_fiber_constant q_n q_next c t
      hc hstep⟩

/-- A renormalized law is unique because the coarsening map is surjective.
This applies to any scale-tower step without using its other hypotheses. -/
theorem scale_descent_renormalized_unique {Qn Qnext T : Type}
    (c : Qn → Qnext) (hc : Function.Surjective c)
    (tb_n : Qn → T) (tb_next tb_next' : Qnext → T)
    (htb_next : tb_next ∘ c = tb_n)
    (htb_next' : tb_next' ∘ c = tb_n) :
    tb_next = tb_next' := by
  funext y
  obtain ⟨x, rfl⟩ := hc y
  exact (congrFun htb_next x).trans (congrFun htb_next' x).symm

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.ScaleDescentRenormalization
