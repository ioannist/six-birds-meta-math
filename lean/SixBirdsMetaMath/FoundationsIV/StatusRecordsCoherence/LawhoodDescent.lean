import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F18 Lawhood Descent.

A layer-law is a relation that descends through the layer quotient and is
coherent under declared transports. Static relation descent, route descent, and
transport stability are separate gates.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.LawhoodDescent

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- A relation descends through the tuple quotient. `tupleQ` abstracts the
componentwise map `(h_1,...,h_k) ↦ (q h_1,...,q h_k)`. -/
def RelationDescends {TupleH TupleQ : Type} (tupleQ : TupleH → TupleQ)
    (R : TupleH → Prop) : Prop :=
  Descends tupleQ (fun t : TupleH => t) R

/-- Static layer-law is relation descent through the layer tuple quotient. -/
def StaticLayerLaw {TupleH TupleQ : Type} (tupleQ : TupleH → TupleQ)
    (R : TupleH → Prop) : Prop :=
  RelationDescends tupleQ R

/-- Law descent obstruction: same quotient tuple, different truth value. -/
def LawDescentObstruction {TupleH TupleQ : Type} (tupleQ : TupleH → TupleQ)
    (R : TupleH → Prop) : (TupleH × TupleH) → Prop :=
  splitPairObstruction tupleQ (fun t : TupleH => t) R

/-- No law descent obstruction is present. -/
def LawDescentObstructionEmpty {TupleH TupleQ : Type} (tupleQ : TupleH → TupleQ)
    (R : TupleH → Prop) : Prop :=
  ObstructionEmpty (LawDescentObstruction tupleQ R)

/-- A declared route descends between source and target layer quotients. -/
def RouteDescends {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : Prop :=
  Descends qi γ qj

/-- Route descent obstruction. -/
def RouteDescentObstruction {Hi Qi Hj Qj : Type} (qi : Hi → Qi) (γ : Hi → Hj)
    (qj : Hj → Qj) : (Hi × Hi) → Prop :=
  splitPairObstruction qi γ qj

/-- No route descent obstruction is present. -/
def RouteDescentObstructionEmpty {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (γ : Hi → Hj) (qj : Hj → Qj) : Prop :=
  ObstructionEmpty (RouteDescentObstruction qi γ qj)

/-- Forward relation stability along the tuple-level route. -/
def ForwardStable {TupleI TupleJ : Type} (tupleRoute : TupleI → TupleJ)
    (Ri : TupleI → Prop) (Rj : TupleJ → Prop) : Prop :=
  ∀ t : TupleI, Ri t → Rj (tupleRoute t)

/-- Forward transport obstruction: source relation holds but target relation
fails after transport. -/
def ForwardTransportObstruction {TupleI TupleJ : Type}
    (tupleRoute : TupleI → TupleJ) (Ri : TupleI → Prop) (Rj : TupleJ → Prop) :
    TupleI → Prop :=
  fun t => Ri t ∧ ¬ Rj (tupleRoute t)

/-- No forward transport obstruction is present. -/
def ForwardTransportObstructionEmpty {TupleI TupleJ : Type}
    (tupleRoute : TupleI → TupleJ) (Ri : TupleI → Prop) (Rj : TupleJ → Prop) :
    Prop :=
  ObstructionEmpty (ForwardTransportObstruction tupleRoute Ri Rj)

/-- Invariant relation transport along the tuple-level route. -/
def RelationInvariant {TupleI TupleJ : Type} (tupleRoute : TupleI → TupleJ)
    (Ri : TupleI → Prop) (Rj : TupleJ → Prop) : Prop :=
  ∀ t : TupleI, Ri t = Rj (tupleRoute t)

/-- Invariance obstruction: source and transported target truth values differ. -/
def InvarianceObstruction {TupleI TupleJ : Type} (tupleRoute : TupleI → TupleJ)
    (Ri : TupleI → Prop) (Rj : TupleJ → Prop) : TupleI → Prop :=
  fun t => Ri t ≠ Rj (tupleRoute t)

/-- No invariance obstruction is present. -/
def InvarianceObstructionEmpty {TupleI TupleJ : Type} (tupleRoute : TupleI → TupleJ)
    (Ri : TupleI → Prop) (Rj : TupleJ → Prop) : Prop :=
  ObstructionEmpty (InvarianceObstruction tupleRoute Ri Rj)

/-- Forward dynamic lawhood: source and target relations descend, the route
descends, and the transported relation is preserved. -/
def ForwardDynamicLayerLaw {TupleI TupleQI TupleJ TupleQJ Hi Qi Hj Qj : Type}
    (tupleQi : TupleI → TupleQI) (Ri : TupleI → Prop)
    (tupleQj : TupleJ → TupleQJ) (Rj : TupleJ → Prop)
    (qi : Hi → Qi) (γ : Hi → Hj) (qj : Hj → Qj)
    (tupleRoute : TupleI → TupleJ) : Prop :=
  StaticLayerLaw tupleQi Ri ∧ StaticLayerLaw tupleQj Rj ∧
    RouteDescends qi γ qj ∧ ForwardStable tupleRoute Ri Rj

/-- Invariant dynamic lawhood: source and target relations descend, the route
descends, and relation truth is invariant along transport. -/
def InvariantDynamicLayerLaw {TupleI TupleQI TupleJ TupleQJ Hi Qi Hj Qj : Type}
    (tupleQi : TupleI → TupleQI) (Ri : TupleI → Prop)
    (tupleQj : TupleJ → TupleQJ) (Rj : TupleJ → Prop)
    (qi : Hi → Qi) (γ : Hi → Hj) (qj : Hj → Qj)
    (tupleRoute : TupleI → TupleJ) : Prop :=
  StaticLayerLaw tupleQi Ri ∧ StaticLayerLaw tupleQj Rj ∧
    RouteDescends qi γ qj ∧ RelationInvariant tupleRoute Ri Rj

/-- Canonical law-supporting extension, abstracted by a relation signature. -/
def lawQuotientExtension {H Q Sig : Type} (q : H → Q) (signature : H → Sig) :
    H → Q × Sig :=
  fun h => (q h, signature h)

/-- The law-supporting extension retains the old quotient. -/
def RetainsLayerQuotient {H Q E : Type} (q : H → Q) (extension : H → E) :
    Prop :=
  Descends extension (fun h : H => h) q

/-- The law-supporting extension carries the relation signature. -/
def CarriesLawSignature {H E Sig : Type} (extension : H → E)
    (signature : H → Sig) : Prop :=
  Descends extension (fun h : H => h) signature

/-- Core exact/failure statuses for descended dynamic lawhood. -/
inductive CoreLawhoodStatus where
  | exactLayerLaw
  | upstairsLaw
  | routeDescentFailure
  | transportUnstableRelation
deriving DecidableEq

/-- Meaning of core dynamic lawhood statuses. -/
def CoreLawhoodStatusHolds (static route stable : Prop) :
    CoreLawhoodStatus → Prop
  | CoreLawhoodStatus.exactLayerLaw => static ∧ route ∧ stable
  | CoreLawhoodStatus.upstairsLaw => ¬ static
  | CoreLawhoodStatus.routeDescentFailure => static ∧ ¬ route
  | CoreLawhoodStatus.transportUnstableRelation => static ∧ route ∧ ¬ stable

/-- Exactly one core lawhood status applies. -/
def ExactlyOneCoreLawhoodStatus (static route stable : Prop) : Prop :=
  ∃ status : CoreLawhoodStatus,
    CoreLawhoodStatusHolds static route stable status ∧
      ∀ other : CoreLawhoodStatus,
        CoreLawhoodStatusHolds static route stable other → other = status

/-- Extended source status vocabulary for lawhood claims and repairs. -/
inductive LawhoodStatus where
  | exactLayerLaw
  | staticLayerRelation
  | upstairsLaw
  | lawhoodOverread
  | routeDescentFailure
  | transportUnstableRelation
  | budgetedLaw
  | laxLaw
  | scopedLaw
  | localOnlyLaw
  | globallyObstructedLaw
  | protocolArtifact
  | unstatusedLawhoodClaim
  | notFormed
  | memoryLaw
deriving DecidableEq

/-- Meaning assignment for the broader F18 lawhood status vocabulary. -/
def LawhoodStatusHolds (exact static upstairs overread routeFailure unstable
    budgeted lax scopedStatus localOnly globalObstructed protocol unstatused notFormed
    memory : Prop) : LawhoodStatus → Prop
  | LawhoodStatus.exactLayerLaw => exact
  | LawhoodStatus.staticLayerRelation => static
  | LawhoodStatus.upstairsLaw => upstairs
  | LawhoodStatus.lawhoodOverread => overread
  | LawhoodStatus.routeDescentFailure => routeFailure
  | LawhoodStatus.transportUnstableRelation => unstable
  | LawhoodStatus.budgetedLaw => budgeted
  | LawhoodStatus.laxLaw => lax
  | LawhoodStatus.scopedLaw => scopedStatus
  | LawhoodStatus.localOnlyLaw => localOnly
  | LawhoodStatus.globallyObstructedLaw => globalObstructed
  | LawhoodStatus.protocolArtifact => protocol
  | LawhoodStatus.unstatusedLawhoodClaim => unstatused
  | LawhoodStatus.notFormed => notFormed
  | LawhoodStatus.memoryLaw => memory

/-- Static relation lawhood is exactly absence of the law descent obstruction. -/
theorem static_law_iff_no_obstruction {TupleH TupleQ : Type}
    (tupleQ : TupleH → TupleQ) (R : TupleH → Prop)
    (htupleQ : Function.Surjective tupleQ) :
    StaticLayerLaw tupleQ R ↔ LawDescentObstructionEmpty tupleQ R :=
  descent_repair_normal_form tupleQ (fun t : TupleH => t) R htupleQ

/-- Route descent is exactly absence of the route descent obstruction. -/
theorem route_descends_iff_no_obstruction {Hi Qi Hj Qj : Type} (qi : Hi → Qi)
    (γ : Hi → Hj) (qj : Hj → Qj) (hqi : Function.Surjective qi) :
    RouteDescends qi γ qj ↔ RouteDescentObstructionEmpty qi γ qj :=
  descent_repair_normal_form qi γ qj hqi

/-- Forward transport stability is exactly absence of the forward transport
obstruction. -/
theorem forward_stable_iff_no_obstruction {TupleI TupleJ : Type}
    (tupleRoute : TupleI → TupleJ) (Ri : TupleI → Prop) (Rj : TupleJ → Prop) :
    ForwardStable tupleRoute Ri Rj ↔
      ForwardTransportObstructionEmpty tupleRoute Ri Rj := by
  constructor
  · intro hstable t hobs
    exact hobs.2 (hstable t hobs.1)
  · intro hempty t hRi
    exact Classical.byContradiction (fun hnot =>
      hempty t ⟨hRi, hnot⟩)

/-- Invariant transport is exactly absence of the invariance obstruction. -/
theorem invariant_iff_no_obstruction {TupleI TupleJ : Type}
    (tupleRoute : TupleI → TupleJ) (Ri : TupleI → Prop) (Rj : TupleJ → Prop) :
    RelationInvariant tupleRoute Ri Rj ↔
      InvarianceObstructionEmpty tupleRoute Ri Rj := by
  constructor
  · intro hinv t hobs
    exact hobs (hinv t)
  · intro hempty t
    exact Classical.byContradiction (fun hneq => hempty t hneq)

/-- The law-supporting extension retains the old quotient. -/
theorem law_extension_retains_quotient {H Q Sig : Type} (q : H → Q)
    (signature : H → Sig) :
    RetainsLayerQuotient q (lawQuotientExtension q signature) := by
  refine ⟨Prod.fst, ?_⟩
  funext h
  rfl

/-- The law-supporting extension carries the law signature. -/
theorem law_extension_carries_signature {H Q Sig : Type} (q : H → Q)
    (signature : H → Sig) :
    CarriesLawSignature (lawQuotientExtension q signature) signature := by
  refine ⟨Prod.snd, ?_⟩
  funext h
  rfl

/-- Forward dynamic lawhood is the conjunction of the three typed obstruction
gates plus target static descent. -/
theorem forward_dynamic_law_iff_no_obstructions
    {TupleI TupleQI TupleJ TupleQJ Hi Qi Hj Qj : Type}
    (tupleQi : TupleI → TupleQI) (Ri : TupleI → Prop)
    (tupleQj : TupleJ → TupleQJ) (Rj : TupleJ → Prop)
    (qi : Hi → Qi) (γ : Hi → Hj) (qj : Hj → Qj)
    (tupleRoute : TupleI → TupleJ)
    (htupleQi : Function.Surjective tupleQi)
    (htupleQj : Function.Surjective tupleQj)
    (hqi : Function.Surjective qi) :
    ForwardDynamicLayerLaw tupleQi Ri tupleQj Rj qi γ qj tupleRoute ↔
      LawDescentObstructionEmpty tupleQi Ri ∧
        LawDescentObstructionEmpty tupleQj Rj ∧
          RouteDescentObstructionEmpty qi γ qj ∧
            ForwardTransportObstructionEmpty tupleRoute Ri Rj := by
  constructor
  · intro h
    exact ⟨(static_law_iff_no_obstruction tupleQi Ri htupleQi).1 h.1,
      (static_law_iff_no_obstruction tupleQj Rj htupleQj).1 h.2.1,
      (route_descends_iff_no_obstruction qi γ qj hqi).1 h.2.2.1,
      (forward_stable_iff_no_obstruction tupleRoute Ri Rj).1 h.2.2.2⟩
  · intro h
    exact ⟨(static_law_iff_no_obstruction tupleQi Ri htupleQi).2 h.1,
      (static_law_iff_no_obstruction tupleQj Rj htupleQj).2 h.2.1,
      (route_descends_iff_no_obstruction qi γ qj hqi).2 h.2.2.1,
      (forward_stable_iff_no_obstruction tupleRoute Ri Rj).2 h.2.2.2⟩

/-- Invariant dynamic lawhood is the conjunction of static descent, route
descent, and invariance-obstruction emptiness. -/
theorem invariant_dynamic_law_iff_no_obstructions
    {TupleI TupleQI TupleJ TupleQJ Hi Qi Hj Qj : Type}
    (tupleQi : TupleI → TupleQI) (Ri : TupleI → Prop)
    (tupleQj : TupleJ → TupleQJ) (Rj : TupleJ → Prop)
    (qi : Hi → Qi) (γ : Hi → Hj) (qj : Hj → Qj)
    (tupleRoute : TupleI → TupleJ)
    (htupleQi : Function.Surjective tupleQi)
    (htupleQj : Function.Surjective tupleQj)
    (hqi : Function.Surjective qi) :
    InvariantDynamicLayerLaw tupleQi Ri tupleQj Rj qi γ qj tupleRoute ↔
      LawDescentObstructionEmpty tupleQi Ri ∧
        LawDescentObstructionEmpty tupleQj Rj ∧
          RouteDescentObstructionEmpty qi γ qj ∧
            InvarianceObstructionEmpty tupleRoute Ri Rj := by
  constructor
  · intro h
    exact ⟨(static_law_iff_no_obstruction tupleQi Ri htupleQi).1 h.1,
      (static_law_iff_no_obstruction tupleQj Rj htupleQj).1 h.2.1,
      (route_descends_iff_no_obstruction qi γ qj hqi).1 h.2.2.1,
      (invariant_iff_no_obstruction tupleRoute Ri Rj).1 h.2.2.2⟩
  · intro h
    exact ⟨(static_law_iff_no_obstruction tupleQi Ri htupleQi).2 h.1,
      (static_law_iff_no_obstruction tupleQj Rj htupleQj).2 h.2.1,
      (route_descends_iff_no_obstruction qi γ qj hqi).2 h.2.2.1,
      (invariant_iff_no_obstruction tupleRoute Ri Rj).2 h.2.2.2⟩

/-- The three core lawhood bits have an exhaustive status. -/
theorem core_lawhood_status_partition (static route stable : Prop) :
    ExactlyOneCoreLawhoodStatus static route stable := by
  classical
  by_cases hstatic : static
  · by_cases hroute : route
    · by_cases hstable : stable
      · refine ⟨CoreLawhoodStatus.exactLayerLaw,
          ⟨hstatic, hroute, hstable⟩, ?_⟩
        intro other hother
        cases other with
        | exactLayerLaw => rfl
        | upstairsLaw => exact False.elim (hother hstatic)
        | routeDescentFailure => exact False.elim (hother.2 hroute)
        | transportUnstableRelation => exact False.elim (hother.2.2 hstable)
      · refine ⟨CoreLawhoodStatus.transportUnstableRelation,
          ⟨hstatic, hroute, hstable⟩, ?_⟩
        intro other hother
        cases other with
        | exactLayerLaw => exact False.elim (hstable hother.2.2)
        | upstairsLaw => exact False.elim (hother hstatic)
        | routeDescentFailure => exact False.elim (hother.2 hroute)
        | transportUnstableRelation => rfl
    · refine ⟨CoreLawhoodStatus.routeDescentFailure, ⟨hstatic, hroute⟩, ?_⟩
      intro other hother
      cases other with
      | exactLayerLaw => exact False.elim (hroute hother.2.1)
      | upstairsLaw => exact False.elim (hother hstatic)
      | routeDescentFailure => rfl
      | transportUnstableRelation => exact False.elim (hroute hother.2.1)
  · refine ⟨CoreLawhoodStatus.upstairsLaw, hstatic, ?_⟩
    intro other hother
    cases other with
    | exactLayerLaw => exact False.elim (hstatic hother.1)
    | upstairsLaw => rfl
    | routeDescentFailure => exact False.elim (hstatic hother.1)
    | transportUnstableRelation => exact False.elim (hstatic hother.1)

/--
Lawhood Descent Normal Form. Static lawhood is quotient descent for a
Prop-valued relation; route lawhood is route descent; dynamic lawhood adds
forward stability or invariance. The canonical law extension retains the old
quotient and carries a law signature, recording the no-free-distinction repair.
-/
theorem lawhood_descent {TupleI TupleQI TupleJ TupleQJ Hi Qi Hj Qj H Q Sig : Type}
    (tupleQi : TupleI → TupleQI) (Ri : TupleI → Prop)
    (tupleQj : TupleJ → TupleQJ) (Rj : TupleJ → Prop)
    (qi : Hi → Qi) (γ : Hi → Hj) (qj : Hj → Qj)
    (tupleRoute : TupleI → TupleJ)
    (htupleQi : Function.Surjective tupleQi)
    (htupleQj : Function.Surjective tupleQj)
    (hqi : Function.Surjective qi)
    (q : H → Q) (signature : H → Sig) :
    (StaticLayerLaw tupleQi Ri ↔ LawDescentObstructionEmpty tupleQi Ri) ∧
      (RouteDescends qi γ qj ↔ RouteDescentObstructionEmpty qi γ qj) ∧
        (ForwardStable tupleRoute Ri Rj ↔
          ForwardTransportObstructionEmpty tupleRoute Ri Rj) ∧
          (RelationInvariant tupleRoute Ri Rj ↔
            InvarianceObstructionEmpty tupleRoute Ri Rj) ∧
            (ForwardDynamicLayerLaw tupleQi Ri tupleQj Rj qi γ qj tupleRoute ↔
              LawDescentObstructionEmpty tupleQi Ri ∧
                LawDescentObstructionEmpty tupleQj Rj ∧
                  RouteDescentObstructionEmpty qi γ qj ∧
                    ForwardTransportObstructionEmpty tupleRoute Ri Rj) ∧
              (InvariantDynamicLayerLaw tupleQi Ri tupleQj Rj qi γ qj tupleRoute ↔
                LawDescentObstructionEmpty tupleQi Ri ∧
                  LawDescentObstructionEmpty tupleQj Rj ∧
                    RouteDescentObstructionEmpty qi γ qj ∧
                      InvarianceObstructionEmpty tupleRoute Ri Rj) ∧
                RetainsLayerQuotient q (lawQuotientExtension q signature) ∧
                  CarriesLawSignature (lawQuotientExtension q signature) signature ∧
                    ExactlyOneCoreLawhoodStatus
                      (StaticLayerLaw tupleQi Ri ∧ StaticLayerLaw tupleQj Rj)
                      (RouteDescends qi γ qj)
                      (ForwardStable tupleRoute Ri Rj) := by
  exact ⟨static_law_iff_no_obstruction tupleQi Ri htupleQi,
    route_descends_iff_no_obstruction qi γ qj hqi,
    forward_stable_iff_no_obstruction tupleRoute Ri Rj,
    invariant_iff_no_obstruction tupleRoute Ri Rj,
    forward_dynamic_law_iff_no_obstructions tupleQi Ri tupleQj Rj qi γ qj
      tupleRoute htupleQi htupleQj hqi,
    invariant_dynamic_law_iff_no_obstructions tupleQi Ri tupleQj Rj qi γ qj
      tupleRoute htupleQi htupleQj hqi,
    law_extension_retains_quotient q signature,
    law_extension_carries_signature q signature,
    core_lawhood_status_partition
      (StaticLayerLaw tupleQi Ri ∧ StaticLayerLaw tupleQj Rj)
      (RouteDescends qi γ qj)
      (ForwardStable tupleRoute Ri Rj)⟩

/-- Swap two histories, leaving all others fixed. -/
private def fiberSwap {H : Type} [DecidableEq H] (a b x : H) : H :=
  if x = a then b else if x = b then a else x

private theorem fiberSwap_involutive {H : Type} [DecidableEq H]
    (a b : H) : ∀ x, fiberSwap a b (fiberSwap a b x) = x := by
  intro x
  by_cases hab : a = b
  · subst b
    by_cases hxa : x = a
    · simp [fiberSwap, hxa]
    · simp [fiberSwap, hxa]
  by_cases hxa : x = a
  · subst x
    simp [fiberSwap, Ne.symm hab]
  by_cases hxb : x = b
  · subst x
    simp [fiberSwap, Ne.symm hab]
  simp [fiberSwap, hxa, hxb]

/-- Invariance under every fiber-preserving bijection is exactly predicate
descent through the surjective access quotient. -/
theorem predicate_invariant_under_fiber_bijections_iff_descends
    {H Q : Type} (q : H → Q) (P : H → Prop)
    (hq : Function.Surjective q) :
    (∀ σ : H → H, Function.Injective σ → Function.Surjective σ →
      (∀ x, q (σ x) = q x) → ∀ x, P (σ x) ↔ P x) ↔
      RelationDescends q P := by
  classical
  constructor
  · intro hinv
    apply (descent_repair_normal_form q (fun x : H => x) P hq).2
    intro ⟨a,b⟩ ⟨hqa,hne⟩
    let σ := fiberSwap a b
    have hσa : σ a = b := by simp [σ, fiberSwap]
    have hσinv := fiberSwap_involutive a b
    have hinj : Function.Injective σ := by
      intro x y heq
      calc
        x = σ (σ x) := (hσinv x).symm
        _ = σ (σ y) := congrArg σ heq
        _ = y := hσinv y
    have hsurj : Function.Surjective σ := by
      intro x
      exact ⟨σ x, hσinv x⟩
    have hpres : ∀ x, q (σ x) = q x := by
      intro x
      by_cases hxa : x = a
      · subst x
        simpa [hσa] using hqa.symm
      by_cases hxb : x = b
      · subst x
        simpa [σ, fiberSwap, hxa] using hqa
      · simp [σ, fiberSwap, hxa, hxb]
    have hi := hinv σ hinj hsurj hpres a
    rw [hσa] at hi
    exact hne (propext hi.symm)
  · rintro ⟨Pbar, hcomm⟩ σ _ _ hpres x
    have hx := congrFun hcomm x
    have hσx := congrFun hcomm (σ x)
    apply Iff.of_eq
    calc
      P (σ x) = Pbar (q (σ x)) := hσx.symm
      _ = Pbar (q x) := congrArg Pbar (hpres x)
      _ = P x := hx

/-- F18 for an arbitrary value-valued candidate law. The existing
Prop-valued predicate version remains available above. -/
theorem readout_invariant_under_fiber_bijections_iff_descends
    {H Q V : Type} (q : H → Q) (P : H → V)
    (hq : Function.Surjective q) :
    (∀ σ : H → H, Function.Injective σ → Function.Surjective σ →
      (∀ x, q (σ x) = q x) → ∀ x, P (σ x) = P x) ↔
      Descends q (fun x : H => x) P := by
  classical
  constructor
  · intro hinv
    apply (descent_repair_normal_form q (fun x : H => x) P hq).2
    intro ⟨a,b⟩ ⟨hqa,hne⟩
    let σ := fiberSwap a b
    have hσa : σ a = b := by simp [σ, fiberSwap]
    have hσinv := fiberSwap_involutive a b
    have hinj : Function.Injective σ := by
      intro x y heq
      calc
        x = σ (σ x) := (hσinv x).symm
        _ = σ (σ y) := congrArg σ heq
        _ = y := hσinv y
    have hsurj : Function.Surjective σ := by
      intro x
      exact ⟨σ x, hσinv x⟩
    have hpres : ∀ x, q (σ x) = q x := by
      intro x
      by_cases hxa : x = a
      · subst x
        simpa [hσa] using hqa.symm
      by_cases hxb : x = b
      · subst x
        simpa [σ, fiberSwap, hxa] using hqa
      · simp [σ, fiberSwap, hxa, hxb]
    have hi := hinv σ hinj hsurj hpres a
    rw [hσa] at hi
    exact hne hi.symm
  · rintro ⟨Pbar, hcomm⟩ σ _ _ hpres x
    have hx := congrFun hcomm x
    have hσx := congrFun hcomm (σ x)
    calc
      P (σ x) = Pbar (q (σ x)) := hσx.symm
      _ = Pbar (q x) := congrArg Pbar (hpres x)
      _ = P x := hx

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.LawhoodDescent
