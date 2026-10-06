import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
import Mathlib.Logic.ExistsUnique

/-!
F25 Causality as Stable Intervention Transport.

The crucial qualification from the source is part of the formal signature:
correlation is not causation. A causal effect is a stable nonzero residue of
lawful, admissible intervention-route contrast from the same quotient context.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.CausalityAsStableInterventionTransport

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- The context/action product quotient `(h, u) ↦ (q h, alpha u)`. -/
def productInterventionQuotient {H Q A Abar : Type} (q : H → Q)
    (alpha : A → Abar) : H × A → Q × Abar :=
  fun pair => (q pair.1, alpha pair.2)

/-- The target-visible deterministic outcome of a raw intervention transport. -/
def interventionTarget {H A H' R : Type} (Gamma : H × A → H') (r : H' → R) :
    H × A → R :=
  fun pair => r (Gamma pair)

/-- Generic quotient-level intervention descent for deterministic outcomes or
already-pushed probabilistic kernels. -/
def QuotientInterventionDescends {H Q A Abar Outcome : Type} (q : H → Q)
    (alpha : A → Abar) (outcome : H × A → Outcome) : Prop :=
  Descends (productInterventionQuotient q alpha) (fun pair : H × A => pair)
    outcome

/-- Generic intervention split obstruction: same context and same intervention
class, different target-visible outcome. -/
def InterventionSplitObstruction {H Q A Abar Outcome : Type} (q : H → Q)
    (alpha : A → Abar) (outcome : H × A → Outcome) :
    (H × A) × (H × A) → Prop :=
  fun pair =>
    q pair.1.1 = q pair.2.1 ∧ alpha pair.1.2 = alpha pair.2.2 ∧
      outcome pair.1 ≠ outcome pair.2

/-- No generic intervention split obstruction is present. -/
def InterventionSplitObstructionEmpty {H Q A Abar Outcome : Type} (q : H → Q)
    (alpha : A → Abar) (outcome : H × A → Outcome) : Prop :=
  ObstructionEmpty (InterventionSplitObstruction q alpha outcome)

/-- Deterministic intervention transport descends through the context and
intervention quotients. -/
def InterventionTransportDescends {H Q A Abar H' R : Type} (q : H → Q)
    (alpha : A → Abar) (Gamma : H × A → H') (r : H' → R) : Prop :=
  QuotientInterventionDescends q alpha (interventionTarget Gamma r)

/-- Deterministic intervention transport obstruction. -/
def InterventionTransportObstruction {H Q A Abar H' R : Type} (q : H → Q)
    (alpha : A → Abar) (Gamma : H × A → H') (r : H' → R) :
    (H × A) × (H × A) → Prop :=
  InterventionSplitObstruction q alpha (interventionTarget Gamma r)

/-- No deterministic intervention transport obstruction is present. -/
def InterventionTransportObstructionEmpty {H Q A Abar H' R : Type}
    (q : H → Q) (alpha : A → Abar) (Gamma : H × A → H') (r : H' → R) :
    Prop :=
  ObstructionEmpty (InterventionTransportObstruction q alpha Gamma r)

/-- Probabilistic intervention transport, modeled after target pushforward:
`kernelOutcome (h,u)` is the induced quotient distribution/measure. -/
def ProbabilisticInterventionTransportDescends {H Q A Abar KernelOutcome : Type}
    (q : H → Q) (alpha : A → Abar) (kernelOutcome : H × A → KernelOutcome) :
    Prop :=
  QuotientInterventionDescends q alpha kernelOutcome

/-- Probabilistic intervention obstruction: same context/action class but
different induced quotient distribution. -/
def ProbabilisticInterventionObstruction {H Q A Abar KernelOutcome : Type}
    (q : H → Q) (alpha : A → Abar) (kernelOutcome : H × A → KernelOutcome) :
    (H × A) × (H × A) → Prop :=
  InterventionSplitObstruction q alpha kernelOutcome

/-- No probabilistic intervention obstruction is present. -/
def ProbabilisticInterventionObstructionEmpty {H Q A Abar KernelOutcome : Type}
    (q : H → Q) (alpha : A → Abar) (kernelOutcome : H × A → KernelOutcome) :
    Prop :=
  ObstructionEmpty (ProbabilisticInterventionObstruction q alpha kernelOutcome)

/-- A context-level intervention contrast is admissible only when both route
classes belong to the declared intervention package at that context. -/
def CounterfactualSupported {Q Abar : Type} (Admissible : Q → Abar → Prop)
    (a : Q) (u v : Abar) : Prop :=
  Admissible a u ∧ Admissible a v

/-- Deterministic nonzero causal residue at the quotient layer. -/
def NonzeroCausalResidue {Q Abar R : Type} (GammaBar : Q × Abar → R)
    (a : Q) (u v : Abar) : Prop :=
  GammaBar (a, u) ≠ GammaBar (a, v)

/-- Zero residue: a valid no-effect status, not a transport failure. -/
def InertInterventionContrast {Q Abar R : Type} (GammaBar : Q × Abar → R)
    (a : Q) (u v : Abar) : Prop :=
  GammaBar (a, u) = GammaBar (a, v)

/-- Stable deterministic causal effect: admissible contrast, nonzero residue,
and declared stability/readout support. -/
def StableCausalEffect {Q Abar R : Type} (GammaBar : Q × Abar → R)
    (Admissible : Q → Abar → Prop)
    (ResidueStable : Q → Abar → Abar → Prop) (a : Q) (u v : Abar) : Prop :=
  CounterfactualSupported Admissible a u v ∧
    NonzeroCausalResidue GammaBar a u v ∧ ResidueStable a u v

/-- Probabilistic nonzero causal residue: the induced quotient distributions
differ. -/
def NonzeroProbabilisticResidue {Q Abar KernelOutcome : Type}
    (Kbar : Q × Abar → KernelOutcome) (a : Q) (u v : Abar) : Prop :=
  Kbar (a, u) ≠ Kbar (a, v)

/-- Stable probabilistic causal effect: admissible contrast, nonzero
distributional residue, and declared downstream stochastic stability. -/
def StableProbabilisticCausalEffect {Q Abar KernelOutcome : Type}
    (Kbar : Q × Abar → KernelOutcome) (Admissible : Q → Abar → Prop)
    (ResidueStable : Q → Abar → Abar → Prop) (a : Q) (u v : Abar) : Prop :=
  CounterfactualSupported Admissible a u v ∧
    NonzeroProbabilisticResidue Kbar a u v ∧ ResidueStable a u v

/-- Observational association without an intervention bridge is not a causal
route-contrast claim. -/
def ObservationalAssociationOnly (association bridgeToIntervention : Prop) :
    Prop :=
  association ∧ ¬ bridgeToIntervention

/-- A route-supported causal claim explicitly supplies intervention routes,
transport descent, admissible contrast, and stable residue. -/
def RouteSupportedCausalClaim {Q Abar R : Type} (hasRouteFamily : Prop)
    (transportDescends : Prop) (GammaBar : Q × Abar → R)
    (Admissible : Q → Abar → Prop)
    (ResidueStable : Q → Abar → Abar → Prop) (a : Q) (u v : Abar) : Prop :=
  hasRouteFamily ∧ transportDescends ∧
    StableCausalEffect GammaBar Admissible ResidueStable a u v

/-- A mediated effect factors the quotient causal transport through an
intermediate quotient. This is stronger than an effect claim. -/
def MediatedCausalTransport {Q Abar M R : Type} (GammaBar : Q × Abar → R)
    (GammaM : Q × Abar → M) (T : M → R) : Prop :=
  ∀ a u, GammaBar (a, u) = T (GammaM (a, u))

/-- Source status vocabulary for causal claims. -/
inductive CausalityStatus where
  | exactCausalEffect
  | probabilisticCausalEffect
  | noCausalEffect
  | contextInsufficient
  | interventionUnderdefined
  | counterfactualSupportAbsent
  | observationalAssociation
  | protocolArtifact
  | unstableEffect
  | mediatedCausalEffect
  | scopedCausalLaw
  | causalOverread
deriving DecidableEq

/-- Meaning assignment for F25 causal statuses. -/
def CausalityStatusHolds (exact probabilistic noEffect contextInsufficient
    interventionUnderdefined supportAbsent observational protocol unstable mediated scopedLaw
    overread : Prop) : CausalityStatus → Prop
  | CausalityStatus.exactCausalEffect => exact
  | CausalityStatus.probabilisticCausalEffect => probabilistic
  | CausalityStatus.noCausalEffect => noEffect
  | CausalityStatus.contextInsufficient => contextInsufficient
  | CausalityStatus.interventionUnderdefined => interventionUnderdefined
  | CausalityStatus.counterfactualSupportAbsent => supportAbsent
  | CausalityStatus.observationalAssociation => observational
  | CausalityStatus.protocolArtifact => protocol
  | CausalityStatus.unstableEffect => unstable
  | CausalityStatus.mediatedCausalEffect => mediated
  | CausalityStatus.scopedCausalLaw => scopedLaw
  | CausalityStatus.causalOverread => overread

/-- Product intervention quotients are surjective when both component quotient
maps are surjective. -/
theorem product_intervention_quotient_surjective {H Q A Abar : Type}
    (q : H → Q) (alpha : A → Abar) (hq : Function.Surjective q)
    (halpha : Function.Surjective alpha) :
    Function.Surjective (productInterventionQuotient q alpha) := by
  intro target
  rcases target with ⟨a, ubar⟩
  rcases hq a with ⟨h, hh⟩
  rcases halpha ubar with ⟨u, hu⟩
  exact ⟨(h, u), Prod.ext hh hu⟩

/-- Generic intervention transport descent is exactly absence of the
intervention split obstruction. -/
theorem quotient_intervention_descends_iff_no_obstruction
    {H Q A Abar Outcome : Type} (q : H → Q) (alpha : A → Abar)
    (outcome : H × A → Outcome) (hq : Function.Surjective q)
    (halpha : Function.Surjective alpha) :
    QuotientInterventionDescends q alpha outcome ↔
      InterventionSplitObstructionEmpty q alpha outcome := by
  constructor
  · intro hdesc
    rcases hdesc with ⟨outcomeBar, hcomm⟩
    intro pair hpair
    rcases pair with ⟨hu, hu'⟩
    rcases hu with ⟨h, u⟩
    rcases hu' with ⟨h', u'⟩
    rcases hpair with ⟨hcontext, hintervention, hout_ne⟩
    have hhu : outcomeBar (q h, alpha u) = outcome (h, u) := congrFun hcomm (h, u)
    have hhu' : outcomeBar (q h', alpha u') = outcome (h', u') :=
      congrFun hcomm (h', u')
    have hout : outcome (h, u) = outcome (h', u') := by
      calc
        outcome (h, u) = outcomeBar (q h, alpha u) := hhu.symm
        _ = outcomeBar (q h', alpha u') := by rw [hcontext, hintervention]
        _ = outcome (h', u') := hhu'
    exact hout_ne hout
  · intro hempty
    have hsplit :
        ObstructionEmpty
          (splitPairObstruction (productInterventionQuotient q alpha)
            (fun pair : H × A => pair) outcome) := by
      intro pair hpair
      rcases pair with ⟨hu, hu'⟩
      rcases hu with ⟨h, u⟩
      rcases hu' with ⟨h', u'⟩
      have hcontext : q h = q h' := congrArg Prod.fst hpair.1
      have hintervention : alpha u = alpha u' := congrArg Prod.snd hpair.1
      exact hempty ((h, u), (h', u')) ⟨hcontext, hintervention, hpair.2⟩
    exact
      (descent_repair_normal_form (productInterventionQuotient q alpha)
        (fun pair : H × A => pair) outcome
        (product_intervention_quotient_surjective q alpha hq halpha)).2 hsplit

/-- The descended quotient-level intervention map is unique because
`(q, alpha)` is surjective onto the declared product quotient. -/
theorem quotient_intervention_lower_unique {H Q A Abar Outcome : Type}
    (q : H → Q) (alpha : A → Abar) (outcome : H × A → Outcome)
    (hq : Function.Surjective q) (halpha : Function.Surjective alpha)
    (lower lower' : Q × Abar → Outcome)
    (hlower : lower ∘ productInterventionQuotient q alpha =
      outcome ∘ (fun pair : H × A => pair))
    (hlower' : lower' ∘ productInterventionQuotient q alpha =
      outcome ∘ (fun pair : H × A => pair)) :
    lower = lower' := by
  funext qa
  rcases product_intervention_quotient_surjective q alpha hq halpha qa with ⟨hu, hhu⟩
  calc
    lower qa = lower (productInterventionQuotient q alpha hu) := by rw [hhu]
    _ = outcome hu := congrFun hlower hu
    _ = lower' (productInterventionQuotient q alpha hu) := (congrFun hlower' hu).symm
    _ = lower' qa := by rw [hhu]

/-- Deterministic intervention transport normal form. -/
theorem intervention_transport_descends_iff_no_obstruction {H Q A Abar H' R : Type}
    (q : H → Q) (alpha : A → Abar) (Gamma : H × A → H') (r : H' → R)
    (hq : Function.Surjective q) (halpha : Function.Surjective alpha) :
    InterventionTransportDescends q alpha Gamma r ↔
      InterventionTransportObstructionEmpty q alpha Gamma r :=
  quotient_intervention_descends_iff_no_obstruction q alpha (interventionTarget Gamma r)
    hq halpha

/-- Probabilistic intervention transport normal form. -/
theorem probabilistic_intervention_descends_iff_no_obstruction
    {H Q A Abar KernelOutcome : Type} (q : H → Q) (alpha : A → Abar)
    (kernelOutcome : H × A → KernelOutcome) (hq : Function.Surjective q)
    (halpha : Function.Surjective alpha) :
    ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ProbabilisticInterventionObstructionEmpty q alpha kernelOutcome :=
  quotient_intervention_descends_iff_no_obstruction q alpha kernelOutcome hq halpha

/-- Stable deterministic causal effect is exactly admissible route contrast,
nonzero quotient residue, and declared stability of that residue. -/
theorem stable_causal_effect_iff_supported_nonzero_stable {Q Abar R : Type}
    (GammaBar : Q × Abar → R) (Admissible : Q → Abar → Prop)
    (ResidueStable : Q → Abar → Abar → Prop) (a : Q) (u v : Abar) :
    StableCausalEffect GammaBar Admissible ResidueStable a u v ↔
      CounterfactualSupported Admissible a u v ∧
        NonzeroCausalResidue GammaBar a u v ∧ ResidueStable a u v := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- A stable causal effect excludes the no-effect/inert status for the same
contrast. -/
theorem stable_causal_effect_excludes_inert {Q Abar R : Type}
    (GammaBar : Q × Abar → R) (Admissible : Q → Abar → Prop)
    (ResidueStable : Q → Abar → Abar → Prop) (a : Q) (u v : Abar) :
    StableCausalEffect GammaBar Admissible ResidueStable a u v →
      ¬ InertInterventionContrast GammaBar a u v := by
  intro heffect hinert
  exact heffect.2.1 hinert

/-- Stable probabilistic causal effect is exactly admissible route contrast,
nonzero distributional residue, and declared downstream stability. -/
theorem stable_probabilistic_causal_effect_iff_supported_nonzero_stable
    {Q Abar KernelOutcome : Type} (Kbar : Q × Abar → KernelOutcome)
    (Admissible : Q → Abar → Prop)
    (ResidueStable : Q → Abar → Abar → Prop) (a : Q) (u v : Abar) :
    StableProbabilisticCausalEffect Kbar Admissible ResidueStable a u v ↔
      CounterfactualSupported Admissible a u v ∧
        NonzeroProbabilisticResidue Kbar a u v ∧ ResidueStable a u v := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- An observational association without a bridge does not satisfy a
route-supported causal claim requiring that bridge as its route family. -/
theorem observational_association_without_bridge_not_route_supported
    {Q Abar R : Type} (association bridgeToIntervention transportDescends : Prop)
    (GammaBar : Q × Abar → R) (Admissible : Q → Abar → Prop)
    (ResidueStable : Q → Abar → Abar → Prop) (a : Q) (u v : Abar) :
    ObservationalAssociationOnly association bridgeToIntervention →
      ¬ RouteSupportedCausalClaim bridgeToIntervention transportDescends GammaBar
        Admissible ResidueStable a u v := by
  intro hobs hclaim
  exact hobs.2 hclaim.1

/--
Causality as Stable Intervention Transport Normal Form. Deterministic and
probabilistic intervention transports descend exactly when their same-context,
same-intervention split obstructions are empty. A causal effect then requires
the crucial extra data: admissible counterfactual route support and stable
nonzero target residue. Observational association without an intervention
bridge remains non-causal.
-/
theorem causality_as_stable_intervention_transport
    {H Q A Abar H' R KernelOutcome : Type} (q : H → Q) (alpha : A → Abar)
    (Gamma : H × A → H') (r : H' → R) (kernelOutcome : H × A → KernelOutcome)
    (GammaBar : Q × Abar → R) (Kbar : Q × Abar → KernelOutcome)
    (Admissible : Q → Abar → Prop)
    (ResidueStable ProbResidueStable : Q → Abar → Abar → Prop)
    (association bridgeToIntervention transportDescends : Prop)
    (a : Q) (u v : Abar) (hq : Function.Surjective q)
    (halpha : Function.Surjective alpha) :
    (InterventionTransportDescends q alpha Gamma r ↔
      InterventionTransportObstructionEmpty q alpha Gamma r) ∧
      (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
        ProbabilisticInterventionObstructionEmpty q alpha kernelOutcome) ∧
        (StableCausalEffect GammaBar Admissible ResidueStable a u v ↔
          CounterfactualSupported Admissible a u v ∧
            NonzeroCausalResidue GammaBar a u v ∧ ResidueStable a u v) ∧
          (StableCausalEffect GammaBar Admissible ResidueStable a u v →
            ¬ InertInterventionContrast GammaBar a u v) ∧
            (StableProbabilisticCausalEffect Kbar Admissible ProbResidueStable a u v ↔
              CounterfactualSupported Admissible a u v ∧
                NonzeroProbabilisticResidue Kbar a u v ∧
                  ProbResidueStable a u v) ∧
              (ObservationalAssociationOnly association bridgeToIntervention →
                ¬ RouteSupportedCausalClaim bridgeToIntervention transportDescends
                  GammaBar Admissible ResidueStable a u v) := by
  exact ⟨intervention_transport_descends_iff_no_obstruction q alpha Gamma r hq halpha,
    probabilistic_intervention_descends_iff_no_obstruction q alpha kernelOutcome hq halpha,
    stable_causal_effect_iff_supported_nonzero_stable GammaBar Admissible
      ResidueStable a u v,
    stable_causal_effect_excludes_inert GammaBar Admissible ResidueStable a u v,
    stable_probabilistic_causal_effect_iff_supported_nonzero_stable Kbar Admissible
      ProbResidueStable a u v,
    observational_association_without_bridge_not_route_supported association
      bridgeToIntervention transportDescends GammaBar Admissible ResidueStable a u v⟩


/-- Explicit factorization at every context and intervention representative. -/
theorem intervention_descends_iff_pointwise_factorization
    {H Q A Abar Outcome : Type} (q : H → Q) (alpha : A → Abar)
    (outcome : H × A → Outcome) :
    QuotientInterventionDescends q alpha outcome ↔
      ∃ lower : Q × Abar → Outcome,
        ∀ h a, lower (q h, alpha a) = outcome (h,a) := by
  constructor
  · rintro ⟨lower,hcomm⟩
    refine ⟨lower, ?_⟩
    intro h a
    exact congrFun hcomm (h,a)
  · rintro ⟨lower,hpoint⟩
    refine ⟨lower, ?_⟩
    funext pair
    exact hpoint pair.1 pair.2

/-- The paper's deterministic and probabilistic intervention criteria. -/
theorem paper_causality_as_stable_intervention_transport
    {H Q A Abar H' R KernelOutcome : Type} (q : H → Q)
    (alpha : A → Abar) (Gamma : H × A → H') (r : H' → R)
    (kernelOutcome : H × A → KernelOutcome)
    (GammaBar : Q × Abar → R) (Kbar : Q × Abar → KernelOutcome)
    (Admissible : Q → Abar → Prop)
    (ResidueStable ProbResidueStable : Q → Abar → Abar → Prop)
    (a : Q) (u v : Abar) (hq : Function.Surjective q)
    (halpha : Function.Surjective alpha) :
    (InterventionTransportDescends q alpha Gamma r ↔
      InterventionTransportObstructionEmpty q alpha Gamma r) ∧
    (InterventionTransportDescends q alpha Gamma r ↔
      ∃ g : Q × Abar → R,
        ∀ h act, g (q h, alpha act) = r (Gamma (h,act))) ∧
    (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ProbabilisticInterventionObstructionEmpty q alpha kernelOutcome) ∧
    (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ∃ k : Q × Abar → KernelOutcome,
        ∀ h act, k (q h, alpha act) = kernelOutcome (h,act)) ∧
    (StableCausalEffect GammaBar Admissible ResidueStable a u v ↔
      Admissible a u ∧ Admissible a v ∧
        GammaBar (a,u) ≠ GammaBar (a,v) ∧ ResidueStable a u v) ∧
    (StableProbabilisticCausalEffect Kbar Admissible ProbResidueStable a u v ↔
      Admissible a u ∧ Admissible a v ∧
        Kbar (a,u) ≠ Kbar (a,v) ∧ ProbResidueStable a u v) := by
  exact ⟨intervention_transport_descends_iff_no_obstruction q alpha Gamma r hq halpha,
    intervention_descends_iff_pointwise_factorization q alpha
      (interventionTarget Gamma r),
    probabilistic_intervention_descends_iff_no_obstruction q alpha kernelOutcome
      hq halpha,
    intervention_descends_iff_pointwise_factorization q alpha kernelOutcome,
    (by
      constructor
      · rintro ⟨⟨hu,hv⟩,hne,hs⟩
        exact ⟨hu,hv,hne,hs⟩
      · rintro ⟨hu,hv,hne,hs⟩
        exact ⟨⟨hu,hv⟩,hne,hs⟩),
    (by
      constructor
      · rintro ⟨⟨hu,hv⟩,hne,hs⟩
        exact ⟨hu,hv,hne,hs⟩
      · rintro ⟨hu,hv,hne,hs⟩
        exact ⟨⟨hu,hv⟩,hne,hs⟩)⟩


/-- Quotient-level causal contrasts have raw witnesses when both declared
quotient transports agree with their raw transports. -/
theorem causal_effect_has_raw_witness
    {H Q A Abar H' R KernelOutcome : Type}
    (q : H → Q) (alpha : A → Abar)
    (Gamma : H × A → H') (r : H' → R)
    (kernelOutcome : H × A → KernelOutcome)
    (GammaBar : Q × Abar → R) (Kbar : Q × Abar → KernelOutcome)
    (Admissible : Q → Abar → Prop)
    (ResidueStable ProbResidueStable : Q → Abar → Abar → Prop)
    (hq : Function.Surjective q) (halpha : Function.Surjective alpha)
    (hGamma : ∀ h act, GammaBar (q h, alpha act) = r (Gamma (h,act)))
    (hK : ∀ h act, Kbar (q h, alpha act) = kernelOutcome (h,act)) :
    (∀ a u v, StableCausalEffect GammaBar Admissible ResidueStable a u v →
      ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
        r (Gamma (h,act₁)) ≠ r (Gamma (h,act₂))) ∧
    (∀ a u v, StableProbabilisticCausalEffect Kbar Admissible
        ProbResidueStable a u v →
      ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
        kernelOutcome (h,act₁) ≠ kernelOutcome (h,act₂)) := by
  constructor
  · intro a u v hcaus
    obtain ⟨h, hh⟩ := hq a
    obtain ⟨act₁, h₁⟩ := halpha u
    obtain ⟨act₂, h₂⟩ := halpha v
    refine ⟨h, act₁, act₂, hh, h₁, h₂, ?_⟩
    intro heq
    apply hcaus.2.1
    calc
      GammaBar (a,u) = r (Gamma (h,act₁)) := by rw [← hh, ← h₁]; exact hGamma h act₁
      _ = r (Gamma (h,act₂)) := heq
      _ = GammaBar (a,v) := by rw [← hh, ← h₂]; exact (hGamma h act₂).symm
  · intro a u v hcaus
    obtain ⟨h, hh⟩ := hq a
    obtain ⟨act₁, h₁⟩ := halpha u
    obtain ⟨act₂, h₂⟩ := halpha v
    refine ⟨h, act₁, act₂, hh, h₁, h₂, ?_⟩
    intro heq
    apply hcaus.2.1
    calc
      Kbar (a,u) = kernelOutcome (h,act₁) := by rw [← hh, ← h₁]; exact hK h act₁
      _ = kernelOutcome (h,act₂) := heq
      _ = Kbar (a,v) := by rw [← hh, ← h₂]; exact (hK h act₂).symm

/-- F25 including raw witnesses for both descended causal contrasts. -/
theorem paper_causality_as_stable_intervention_transport_with_raw_witness
    {H Q A Abar H' R KernelOutcome : Type} (q : H → Q)
    (alpha : A → Abar) (Gamma : H × A → H') (r : H' → R)
    (kernelOutcome : H × A → KernelOutcome)
    (GammaBar : Q × Abar → R) (Kbar : Q × Abar → KernelOutcome)
    (Admissible : Q → Abar → Prop)
    (ResidueStable ProbResidueStable : Q → Abar → Abar → Prop)
    (a : Q) (u v : Abar) (hq : Function.Surjective q)
    (halpha : Function.Surjective alpha)
    (hGamma : ∀ h act, GammaBar (q h, alpha act) = r (Gamma (h,act)))
    (hK : ∀ h act, Kbar (q h, alpha act) = kernelOutcome (h,act)) :
    ((InterventionTransportDescends q alpha Gamma r ↔
      InterventionTransportObstructionEmpty q alpha Gamma r) ∧
    (InterventionTransportDescends q alpha Gamma r ↔
      ∃ g : Q × Abar → R,
        ∀ h act, g (q h, alpha act) = r (Gamma (h,act))) ∧
    (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ProbabilisticInterventionObstructionEmpty q alpha kernelOutcome) ∧
    (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ∃ k : Q × Abar → KernelOutcome,
        ∀ h act, k (q h, alpha act) = kernelOutcome (h,act)) ∧
    (StableCausalEffect GammaBar Admissible ResidueStable a u v ↔
      Admissible a u ∧ Admissible a v ∧
        GammaBar (a,u) ≠ GammaBar (a,v) ∧ ResidueStable a u v) ∧
    (StableProbabilisticCausalEffect Kbar Admissible ProbResidueStable a u v ↔
      Admissible a u ∧ Admissible a v ∧
        Kbar (a,u) ≠ Kbar (a,v) ∧ ProbResidueStable a u v)) ∧
    ((∀ a u v, StableCausalEffect GammaBar Admissible ResidueStable a u v →
      ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
        r (Gamma (h,act₁)) ≠ r (Gamma (h,act₂))) ∧
    (∀ a u v, StableProbabilisticCausalEffect Kbar Admissible
        ProbResidueStable a u v →
      ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
        kernelOutcome (h,act₁) ≠ kernelOutcome (h,act₂))) := by
  exact ⟨paper_causality_as_stable_intervention_transport q alpha Gamma r
      kernelOutcome GammaBar Kbar Admissible ResidueStable ProbResidueStable
      a u v hq halpha,
    causal_effect_has_raw_witness q alpha Gamma r kernelOutcome GammaBar Kbar
      Admissible ResidueStable ProbResidueStable hq halpha hGamma hK⟩

/-- F25 for arbitrary quotient-level transports, with raw witnesses only
when both declared transports satisfy their descent equations. -/
theorem paper_causality_transport_conditional_raw_witness
    {H Q A Abar H' R KernelOutcome : Type} (q : H → Q)
    (alpha : A → Abar) (Gamma : H × A → H') (r : H' → R)
    (kernelOutcome : H × A → KernelOutcome)
    (GammaBar : Q × Abar → R) (Kbar : Q × Abar → KernelOutcome)
    (Admissible : Q → Abar → Prop)
    (ResidueStable ProbResidueStable : Q → Abar → Abar → Prop)
    (a : Q) (u v : Abar) (hq : Function.Surjective q)
    (halpha : Function.Surjective alpha) :
    (InterventionTransportDescends q alpha Gamma r ↔
      InterventionTransportObstructionEmpty q alpha Gamma r) ∧
    (InterventionTransportDescends q alpha Gamma r ↔
      ∃ g : Q × Abar → R,
        ∀ h act, g (q h, alpha act) = r (Gamma (h,act))) ∧
    (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ProbabilisticInterventionObstructionEmpty q alpha kernelOutcome) ∧
    (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ∃ k : Q × Abar → KernelOutcome,
        ∀ h act, k (q h, alpha act) = kernelOutcome (h,act)) ∧
    (StableCausalEffect GammaBar Admissible ResidueStable a u v ↔
      Admissible a u ∧ Admissible a v ∧
        GammaBar (a,u) ≠ GammaBar (a,v) ∧ ResidueStable a u v) ∧
    (StableProbabilisticCausalEffect Kbar Admissible ProbResidueStable a u v ↔
      Admissible a u ∧ Admissible a v ∧
        Kbar (a,u) ≠ Kbar (a,v) ∧ ProbResidueStable a u v) ∧
    ((∀ h act, GammaBar (q h, alpha act) = r (Gamma (h,act))) →
      (∀ h act, Kbar (q h, alpha act) = kernelOutcome (h,act)) →
        (∀ a u v, StableCausalEffect GammaBar Admissible ResidueStable a u v →
          ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
            r (Gamma (h,act₁)) ≠ r (Gamma (h,act₂))) ∧
        (∀ a u v, StableProbabilisticCausalEffect Kbar Admissible
            ProbResidueStable a u v →
          ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
            kernelOutcome (h,act₁) ≠ kernelOutcome (h,act₂))) := by
  rcases paper_causality_as_stable_intervention_transport q alpha Gamma r
    kernelOutcome GammaBar Kbar Admissible ResidueStable ProbResidueStable
    a u v hq halpha with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, h4, h5, h6,
    fun hGamma hK => causal_effect_has_raw_witness q alpha Gamma r
      kernelOutcome GammaBar Kbar Admissible ResidueStable ProbResidueStable
      hq halpha hGamma hK⟩

/-- The deterministic raw witness uses only the descent equation for GammaBar. -/
theorem causal_effect_raw_witness_of_gamma_descent
    {H Q A Abar H' R : Type} (q : H → Q) (alpha : A → Abar)
    (Gamma : H × A → H') (r : H' → R) (GammaBar : Q × Abar → R)
    (Admissible : Q → Abar → Prop)
    (ResidueStable : Q → Abar → Abar → Prop)
    (hq : Function.Surjective q) (halpha : Function.Surjective alpha)
    (hGamma : ∀ h act, GammaBar (q h, alpha act) = r (Gamma (h,act))) :
    ∀ a u v, StableCausalEffect GammaBar Admissible ResidueStable a u v →
      ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
        r (Gamma (h,act₁)) ≠ r (Gamma (h,act₂)) := by
  intro a u v hcaus
  obtain ⟨h, hh⟩ := hq a
  obtain ⟨act₁, h₁⟩ := halpha u
  obtain ⟨act₂, h₂⟩ := halpha v
  refine ⟨h, act₁, act₂, hh, h₁, h₂, ?_⟩
  intro heq
  apply hcaus.2.1
  calc
    GammaBar (a,u) = r (Gamma (h,act₁)) := by rw [← hh, ← h₁]; exact hGamma h act₁
    _ = r (Gamma (h,act₂)) := heq
    _ = GammaBar (a,v) := by rw [← hh, ← h₂]; exact (hGamma h act₂).symm

/-- The probabilistic raw witness uses only the descent equation for Kbar. -/
theorem probabilistic_causal_effect_raw_witness_of_kernel_descent
    {H Q A Abar KernelOutcome : Type} (q : H → Q) (alpha : A → Abar)
    (kernelOutcome : H × A → KernelOutcome)
    (Kbar : Q × Abar → KernelOutcome) (Admissible : Q → Abar → Prop)
    (ProbResidueStable : Q → Abar → Abar → Prop)
    (hq : Function.Surjective q) (halpha : Function.Surjective alpha)
    (hK : ∀ h act, Kbar (q h, alpha act) = kernelOutcome (h,act)) :
    ∀ a u v, StableProbabilisticCausalEffect Kbar Admissible
        ProbResidueStable a u v →
      ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
        kernelOutcome (h,act₁) ≠ kernelOutcome (h,act₂) := by
  intro a u v hcaus
  obtain ⟨h, hh⟩ := hq a
  obtain ⟨act₁, h₁⟩ := halpha u
  obtain ⟨act₂, h₂⟩ := halpha v
  refine ⟨h, act₁, act₂, hh, h₁, h₂, ?_⟩
  intro heq
  apply hcaus.2.1
  calc
    Kbar (a,u) = kernelOutcome (h,act₁) := by rw [← hh, ← h₁]; exact hK h act₁
    _ = kernelOutcome (h,act₂) := heq
    _ = Kbar (a,v) := by rw [← hh, ← h₂]; exact (hK h act₂).symm

/-- F25 with each raw-witness conclusion guarded only by its own descent
equation. -/
theorem paper_causality_transport_separate_raw_witness
    {H Q A Abar H' R KernelOutcome : Type} (q : H → Q)
    (alpha : A → Abar) (Gamma : H × A → H') (r : H' → R)
    (kernelOutcome : H × A → KernelOutcome)
    (GammaBar : Q × Abar → R) (Kbar : Q × Abar → KernelOutcome)
    (Admissible : Q → Abar → Prop)
    (ResidueStable ProbResidueStable : Q → Abar → Abar → Prop)
    (a : Q) (u v : Abar) (hq : Function.Surjective q)
    (halpha : Function.Surjective alpha) :
    (InterventionTransportDescends q alpha Gamma r ↔
      InterventionTransportObstructionEmpty q alpha Gamma r) ∧
    (InterventionTransportDescends q alpha Gamma r ↔
      ∃ g : Q × Abar → R,
        ∀ h act, g (q h, alpha act) = r (Gamma (h,act))) ∧
    (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ProbabilisticInterventionObstructionEmpty q alpha kernelOutcome) ∧
    (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ∃ k : Q × Abar → KernelOutcome,
        ∀ h act, k (q h, alpha act) = kernelOutcome (h,act)) ∧
    (StableCausalEffect GammaBar Admissible ResidueStable a u v ↔
      Admissible a u ∧ Admissible a v ∧
        GammaBar (a,u) ≠ GammaBar (a,v) ∧ ResidueStable a u v) ∧
    (StableProbabilisticCausalEffect Kbar Admissible ProbResidueStable a u v ↔
      Admissible a u ∧ Admissible a v ∧
        Kbar (a,u) ≠ Kbar (a,v) ∧ ProbResidueStable a u v) ∧
    ((∀ h act, GammaBar (q h, alpha act) = r (Gamma (h,act))) →
      ∀ a u v, StableCausalEffect GammaBar Admissible ResidueStable a u v →
        ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
          r (Gamma (h,act₁)) ≠ r (Gamma (h,act₂))) ∧
    ((∀ h act, Kbar (q h, alpha act) = kernelOutcome (h,act)) →
      ∀ a u v, StableProbabilisticCausalEffect Kbar Admissible
          ProbResidueStable a u v →
        ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
          kernelOutcome (h,act₁) ≠ kernelOutcome (h,act₂)) := by
  rcases paper_causality_as_stable_intervention_transport q alpha Gamma r
    kernelOutcome GammaBar Kbar Admissible ResidueStable ProbResidueStable
    a u v hq halpha with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, h4, h5, h6,
    fun hGamma => causal_effect_raw_witness_of_gamma_descent q alpha Gamma r
      GammaBar Admissible ResidueStable hq halpha hGamma,
    fun hK => probabilistic_causal_effect_raw_witness_of_kernel_descent
      q alpha kernelOutcome Kbar Admissible ProbResidueStable hq halpha hK⟩

/-- Surjective context and intervention quotients give a unique pointwise
factorization of every descending outcome. -/
theorem intervention_descends_iff_unique_pointwise_factorization
    {H Q A Abar Outcome : Type} (q : H → Q) (alpha : A → Abar)
    (outcome : H × A → Outcome) (hq : Function.Surjective q)
    (halpha : Function.Surjective alpha) :
    QuotientInterventionDescends q alpha outcome ↔
      ∃! lower : Q × Abar → Outcome,
        ∀ h act, lower (q h, alpha act) = outcome (h,act) := by
  constructor
  · intro hdesc
    obtain ⟨lower, hlower⟩ :=
      (intervention_descends_iff_pointwise_factorization q alpha outcome).mp hdesc
    refine ⟨lower, hlower, ?_⟩
    intro lower' hlower'
    apply quotient_intervention_lower_unique q alpha outcome hq halpha lower' lower
    · funext pair
      exact hlower' pair.1 pair.2
    · funext pair
      exact hlower pair.1 pair.2
  · rintro ⟨lower, hlower, _⟩
    exact (intervention_descends_iff_pointwise_factorization q alpha outcome).mpr
      ⟨lower, hlower⟩

/-- Full F25 bundle: both descended outcomes factor uniquely through the
product quotient, with raw witnesses guarded by their separate descent laws. -/
theorem paper_causality_transport_separate_raw_witness_full
    {H Q A Abar H' R KernelOutcome : Type} (q : H → Q)
    (alpha : A → Abar) (Gamma : H × A → H') (r : H' → R)
    (kernelOutcome : H × A → KernelOutcome)
    (GammaBar : Q × Abar → R) (Kbar : Q × Abar → KernelOutcome)
    (Admissible : Q → Abar → Prop)
    (ResidueStable ProbResidueStable : Q → Abar → Abar → Prop)
    (a : Q) (u v : Abar) (hq : Function.Surjective q)
    (halpha : Function.Surjective alpha) :
    ((InterventionTransportDescends q alpha Gamma r ↔
      InterventionTransportObstructionEmpty q alpha Gamma r) ∧
    (InterventionTransportDescends q alpha Gamma r ↔
      ∃ g : Q × Abar → R,
        ∀ h act, g (q h, alpha act) = r (Gamma (h,act))) ∧
    (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ProbabilisticInterventionObstructionEmpty q alpha kernelOutcome) ∧
    (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ∃ k : Q × Abar → KernelOutcome,
        ∀ h act, k (q h, alpha act) = kernelOutcome (h,act)) ∧
    (StableCausalEffect GammaBar Admissible ResidueStable a u v ↔
      Admissible a u ∧ Admissible a v ∧
        GammaBar (a,u) ≠ GammaBar (a,v) ∧ ResidueStable a u v) ∧
    (StableProbabilisticCausalEffect Kbar Admissible ProbResidueStable a u v ↔
      Admissible a u ∧ Admissible a v ∧
        Kbar (a,u) ≠ Kbar (a,v) ∧ ProbResidueStable a u v) ∧
    ((∀ h act, GammaBar (q h, alpha act) = r (Gamma (h,act))) →
      ∀ a u v, StableCausalEffect GammaBar Admissible ResidueStable a u v →
        ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
          r (Gamma (h,act₁)) ≠ r (Gamma (h,act₂))) ∧
    ((∀ h act, Kbar (q h, alpha act) = kernelOutcome (h,act)) →
      ∀ a u v, StableProbabilisticCausalEffect Kbar Admissible
          ProbResidueStable a u v →
        ∃ h act₁ act₂, q h = a ∧ alpha act₁ = u ∧ alpha act₂ = v ∧
          kernelOutcome (h,act₁) ≠ kernelOutcome (h,act₂))) ∧
    (InterventionTransportDescends q alpha Gamma r ↔
      ∃! g : Q × Abar → R,
        ∀ h act, g (q h, alpha act) = r (Gamma (h,act))) ∧
    (ProbabilisticInterventionTransportDescends q alpha kernelOutcome ↔
      ∃! k : Q × Abar → KernelOutcome,
        ∀ h act, k (q h, alpha act) = kernelOutcome (h,act)) := by
  exact ⟨paper_causality_transport_separate_raw_witness q alpha Gamma r
      kernelOutcome GammaBar Kbar Admissible ResidueStable ProbResidueStable
      a u v hq halpha,
    intervention_descends_iff_unique_pointwise_factorization q alpha
      (interventionTarget Gamma r) hq halpha,
    intervention_descends_iff_unique_pointwise_factorization q alpha
      kernelOutcome hq halpha⟩

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.CausalityAsStableInterventionTransport
