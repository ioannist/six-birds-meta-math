import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F42 Irreducibility / No Short Closed Description.

Irreducibility is modeled as the absence of a smaller admissible quotient that
uses only the declared base, preserves the declared target signature, and closes
under the declared transport family.
-/

namespace SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Irreducibility

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- A candidate description uses only distinctions available in the base
quotient. -/
def SourceAdmissible {H B E : Type} (base : H → B) (compression : H → E) :
    Prop :=
  Descends base (fun h : H => h) compression

/-- The target signature is preserved by the candidate quotient. -/
def TargetPreserving {H E Target : Type} (compression : H → E)
    (target : H → Target) : Prop :=
  Descends compression (fun h : H => h) target

/-- A declared route updates autonomously on the candidate quotient. -/
def TransportStable {H E : Type} (compression : H → E) (route : H → H) :
    Prop :=
  Descends compression route compression

/-- Every declared route updates autonomously on the candidate quotient. -/
def TransportFamilyStable {H E Route : Type} (compression : H → E)
    (routes : Route → H → H) : Prop :=
  ∀ route, TransportStable compression (routes route)

/-- Source-overread obstruction: same base value but different compressed
description. -/
def SourceObstruction {H B E : Type} (base : H → B) (compression : H → E) :
    (H × H) → Prop :=
  splitPairObstruction base (fun h : H => h) compression

/-- No source-overread obstruction is present. -/
def SourceObstructionEmpty {H B E : Type} (base : H → B)
    (compression : H → E) : Prop :=
  ObstructionEmpty (SourceObstruction base compression)

/-- Target-loss obstruction: same compressed description but different target
signature. -/
def TargetObstruction {H E Target : Type} (compression : H → E)
    (target : H → Target) : (H × H) → Prop :=
  splitPairObstruction compression (fun h : H => h) target

/-- No target-loss obstruction is present. -/
def TargetObstructionEmpty {H E Target : Type} (compression : H → E)
    (target : H → Target) : Prop :=
  ObstructionEmpty (TargetObstruction compression target)

/-- Transport obstruction for one route: same compressed state now, different
compressed state after the route. -/
def TransportObstruction {H E : Type} (compression : H → E) (route : H → H) :
    (H × H) → Prop :=
  splitPairObstruction compression route compression

/-- No transport obstruction is present for one route. -/
def TransportObstructionEmpty {H E : Type} (compression : H → E)
    (route : H → H) : Prop :=
  ObstructionEmpty (TransportObstruction compression route)

/-- Transport obstruction for a declared route family. -/
def TransportFamilyObstruction {H E Route : Type} (compression : H → E)
    (routes : Route → H → H) : (Route × (H × H)) → Prop :=
  fun routeAndPair =>
    TransportObstruction compression (routes routeAndPair.1) routeAndPair.2

/-- No route in the declared family has a transport obstruction. -/
def TransportFamilyObstructionEmpty {H E Route : Type} (compression : H → E)
    (routes : Route → H → H) : Prop :=
  ObstructionEmpty (TransportFamilyObstruction compression routes)

/-- Closed target-preserving compression: source-admissible, target-preserving,
and transport-stable for every declared route. -/
def ClosedCompression {H B E Target Route : Type} (base : H → B)
    (compression : H → E) (target : H → Target)
    (routes : Route → H → H) : Prop :=
  SourceAdmissible base compression ∧
    TargetPreserving compression target ∧
      TransportFamilyStable compression routes

/-- The obstruction-normal-form side of closed compression. -/
def ClosedCompressionObstructionsEmpty {H B E Target Route : Type}
    (base : H → B) (compression : H → E) (target : H → Target)
    (routes : Route → H → H) : Prop :=
  SourceObstructionEmpty base compression ∧
    TargetObstructionEmpty compression target ∧
      TransportFamilyObstructionEmpty compression routes

/-- Static compression preserves the target but is not dynamically closed. -/
def StaticCompressionOnly {H B E Target Route : Type} (base : H → B)
    (compression : H → E) (target : H → Target)
    (routes : Route → H → H) : Prop :=
  SourceAdmissible base compression ∧
    TargetPreserving compression target ∧
      ¬ TransportFamilyStable compression routes

/-- Strict quotient compression: the candidate descends from the base, while
the base does not descend back through the candidate. -/
def StrictQuotientCompression {H B E : Type} (base : H → B)
    (compression : H → E) : Prop :=
  SourceAdmissible base compression ∧
    ¬ Descends compression (fun h : H => h) base

/-- A scoped reducer is a shorter admissible closed compression. -/
def ReducibleByShortClosedDescription {H B Target Route Cost : Type}
    (base : H → B) (target : H → Target) (routes : Route → H → H)
    (Admissible : {E : Type} → (H → E) → Prop)
    (cost : {E : Type} → (H → E) → Cost) (CostLt : Cost → Cost → Prop) :
    Prop :=
  ∃ (E : Type), ∃ compression : H → E,
    Admissible compression ∧
      ClosedCompression base compression target routes ∧
        CostLt (cost compression) (cost base)

/-- Irreducibility is the scoped universal negative: every admissible closed
compression is not shorter under the declared cost ledger. -/
def Irreducible {H B Target Route Cost : Type} (base : H → B)
    (target : H → Target) (routes : Route → H → H)
    (Admissible : {E : Type} → (H → E) → Prop)
    (cost : {E : Type} → (H → E) → Cost) (CostLt : Cost → Cost → Prop) :
    Prop :=
  ∀ (E : Type) (compression : H → E),
    Admissible compression →
      ClosedCompression base compression target routes →
        ¬ CostLt (cost compression) (cost base)

/-- Finite-horizon compression is target preservation for a declared finite
target signature, without claiming uniform closure beyond that scope. -/
def FiniteHorizonCompression {H B E Target : Type} (base : H → B)
    (compression : H → E) (finiteTarget : H → Target) : Prop :=
  SourceAdmissible base compression ∧ TargetPreserving compression finiteTarget

/-- Uniform closed compression uses one quotient for target and transport
closure across the declared route family. -/
def UniformClosedCompression {H B E Target Route : Type} (base : H → B)
    (compression : H → E) (target : H → Target)
    (routes : Route → H → H) : Prop :=
  ClosedCompression base compression target routes

/-- Source status vocabulary for irreducibility claims. -/
inductive IrreducibilityStatus where
  | reducible
  | irreducible
  | staticCompressionOnly
  | targetRestatement
  | sourceOverread
  | targetLoss
  | oracleShortcut
  | protocolShortcut
  | memoryCompressed
  | probabilisticCompression
  | budgetedCompression
  | approximateIrreducible
  | asymptoticallyReducible
  | asymptoticallyIrreducible
  | scopedIrreducible
  | localCompression
  | globalIrreducible
  | presentationDependentCompression
  | costLedgerDependent
  | irreducibilityOverread
deriving DecidableEq

/-- Meaning assignment for the F42 irreducibility status vocabulary. -/
def IrreducibilityStatusHolds (reducibleStatus irreducibleStatus staticOnly
    targetRestatement sourceOverread targetLoss oracle protocol memory probabilistic
    budgeted approximate asymptoticReducible asymptoticIrreducible scopedStatus localOnly
    globalIrreducible presentationDependent costDependent overread : Prop) :
    IrreducibilityStatus → Prop
  | IrreducibilityStatus.reducible => reducibleStatus
  | IrreducibilityStatus.irreducible => irreducibleStatus
  | IrreducibilityStatus.staticCompressionOnly => staticOnly
  | IrreducibilityStatus.targetRestatement => targetRestatement
  | IrreducibilityStatus.sourceOverread => sourceOverread
  | IrreducibilityStatus.targetLoss => targetLoss
  | IrreducibilityStatus.oracleShortcut => oracle
  | IrreducibilityStatus.protocolShortcut => protocol
  | IrreducibilityStatus.memoryCompressed => memory
  | IrreducibilityStatus.probabilisticCompression => probabilistic
  | IrreducibilityStatus.budgetedCompression => budgeted
  | IrreducibilityStatus.approximateIrreducible => approximate
  | IrreducibilityStatus.asymptoticallyReducible => asymptoticReducible
  | IrreducibilityStatus.asymptoticallyIrreducible => asymptoticIrreducible
  | IrreducibilityStatus.scopedIrreducible => scopedStatus
  | IrreducibilityStatus.localCompression => localOnly
  | IrreducibilityStatus.globalIrreducible => globalIrreducible
  | IrreducibilityStatus.presentationDependentCompression => presentationDependent
  | IrreducibilityStatus.costLedgerDependent => costDependent
  | IrreducibilityStatus.irreducibilityOverread => overread

/-- Source admissibility iff there is no source-overread obstruction. -/
theorem source_admissible_iff_no_source_obstruction {H B E : Type}
    (base : H → B) (compression : H → E)
    (hbase : Function.Surjective base) :
    SourceAdmissible base compression ↔ SourceObstructionEmpty base compression :=
  descent_repair_normal_form base (fun h : H => h) compression hbase

/-- Target preservation iff there is no target-loss obstruction. -/
theorem target_preserving_iff_no_target_obstruction {H E Target : Type}
    (compression : H → E) (target : H → Target)
    (hcompression : Function.Surjective compression) :
    TargetPreserving compression target ↔
      TargetObstructionEmpty compression target :=
  descent_repair_normal_form compression (fun h : H => h) target hcompression

/-- One-route transport stability iff no transport split pair exists. -/
theorem transport_stable_iff_no_transport_obstruction {H E : Type}
    (compression : H → E) (route : H → H)
    (hcompression : Function.Surjective compression) :
    TransportStable compression route ↔
      TransportObstructionEmpty compression route :=
  descent_repair_normal_form compression route compression hcompression

/-- Route-family closure iff every route obstruction is empty. -/
theorem transport_family_stable_iff_no_obstruction {H E Route : Type}
    (compression : H → E) (routes : Route → H → H)
    (hcompression : Function.Surjective compression) :
    TransportFamilyStable compression routes ↔
      TransportFamilyObstructionEmpty compression routes := by
  constructor
  · intro hstable routeAndPair hpair
    rcases routeAndPair with ⟨route, pair⟩
    have hempty :
        TransportObstructionEmpty compression (routes route) :=
      (transport_stable_iff_no_transport_obstruction compression (routes route)
        hcompression).mp (hstable route)
    exact hempty pair hpair
  · intro hempty route
    refine (transport_stable_iff_no_transport_obstruction compression
      (routes route) hcompression).mpr ?_
    intro pair hpair
    exact hempty (route, pair) hpair

/-- Closed compression iff all three obstruction families are empty. -/
theorem closed_compression_iff_empty_obstructions {H B E Target Route : Type}
    (base : H → B) (compression : H → E) (target : H → Target)
    (routes : Route → H → H) (hbase : Function.Surjective base)
    (hcompression : Function.Surjective compression) :
    ClosedCompression base compression target routes ↔
      ClosedCompressionObstructionsEmpty base compression target routes := by
  constructor
  · intro hclosed
    exact ⟨(source_admissible_iff_no_source_obstruction base compression hbase).mp
        hclosed.1,
      (target_preserving_iff_no_target_obstruction compression target
        hcompression).mp hclosed.2.1,
      (transport_family_stable_iff_no_obstruction compression routes
        hcompression).mp hclosed.2.2⟩
  · intro hempty
    exact ⟨(source_admissible_iff_no_source_obstruction base compression hbase).mpr
        hempty.1,
      (target_preserving_iff_no_target_obstruction compression target
        hcompression).mpr hempty.2.1,
      (transport_family_stable_iff_no_obstruction compression routes
        hcompression).mpr hempty.2.2⟩

/-- Static compression only is source and target descent together with failure
of transport closure. -/
theorem static_compression_only_iff {H B E Target Route : Type}
    (base : H → B) (compression : H → E) (target : H → Target)
    (routes : Route → H → H) :
    StaticCompressionOnly base compression target routes ↔
      SourceAdmissible base compression ∧
        TargetPreserving compression target ∧
          ¬ TransportFamilyStable compression routes := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Irreducibility is equivalent to the absence of a shorter admissible closed
description. -/
theorem irreducible_iff_no_reducer {H B Target Route Cost : Type}
    (base : H → B) (target : H → Target) (routes : Route → H → H)
    (Admissible : {E : Type} → (H → E) → Prop)
    (cost : {E : Type} → (H → E) → Cost) (CostLt : Cost → Cost → Prop) :
    Irreducible base target routes Admissible cost CostLt ↔
      ¬ ReducibleByShortClosedDescription base target routes Admissible cost
        CostLt := by
  constructor
  · intro hirred hred
    rcases hred with ⟨E, compression, hadmissible, hclosed, hshort⟩
    exact hirred E compression hadmissible hclosed hshort
  · intro hno E compression hadmissible hclosed hshort
    exact hno ⟨E, compression, hadmissible, hclosed, hshort⟩

/--
Irreducibility / No Short Closed Description Normal Form. A candidate closed
compression is exactly source descent, target descent, and route-family
descent; the base is irreducible exactly when no admissible candidate satisfying
those gates is shorter under the declared cost ledger.
-/
theorem irreducibility_no_short_closed_description
    {H B E Target Route Cost : Type} (base : H → B) (compression : H → E)
    (target : H → Target) (routes : Route → H → H)
    (Admissible : {E' : Type} → (H → E') → Prop)
    (cost : {E' : Type} → (H → E') → Cost) (CostLt : Cost → Cost → Prop)
    (hbase : Function.Surjective base)
    (hcompression : Function.Surjective compression) :
    (ClosedCompression base compression target routes ↔
      ClosedCompressionObstructionsEmpty base compression target routes) ∧
      (StaticCompressionOnly base compression target routes ↔
        SourceAdmissible base compression ∧
          TargetPreserving compression target ∧
            ¬ TransportFamilyStable compression routes) ∧
        (Irreducible base target routes Admissible cost CostLt ↔
          ¬ ReducibleByShortClosedDescription base target routes Admissible
            cost CostLt) := by
  exact ⟨closed_compression_iff_empty_obstructions base compression target
      routes hbase hcompression,
    static_compression_only_iff base compression target routes,
    irreducible_iff_no_reducer base target routes Admissible cost CostLt⟩


/-- Target split pairs in the selected compression fiber. -/
def PointTargetObstruction {H E T : Type} (e : H → E) (h : H)
    (t : H → T) (pair : H × H) : Prop :=
  e pair.1 = e h ∧ e pair.2 = e h ∧ t pair.1 ≠ t pair.2

/-- Route split pairs in the selected compression fiber. -/
def PointRouteObstruction {H E : Type} (e : H → E) (h : H)
    (route : H → H) (pair : H × H) : Prop :=
  e pair.1 = e h ∧ e pair.2 = e h ∧ e (route pair.1) ≠ e (route pair.2)

/-- Pointwise closedness requires target and route constancy in the selected fiber. -/
def PointClosedCompression {H E T Route : Type} (e : H → E) (h : H)
    (t : H → T) (routes : Route → H → H) : Prop :=
  (∀ x y, e x = e h → e y = e h → t x = t y) ∧
    ∀ γ x y, e x = e h → e y = e h →
      e (routes γ x) = e (routes γ y)

/-- Pointwise irreducibility compares descriptions at the chosen object. -/
def PointIrreducible {H E T Route Cost : Type} (e : H → E) (h : H)
    (t : H → T) (routes : Route → H → H) (cost : E → Cost)
    (Lt : Cost → Cost → Prop) : Prop :=
  ∀ e' : H → E, PointClosedCompression e' h t routes →
    ¬ Lt (cost (e' h)) (cost (e h))

/-- Pointwise closure is exactly emptiness of the two split-pair sets;
pointwise irreducibility excludes every cheaper closed candidate. -/
theorem paper_irreducibility {H E T Route Cost : Type} (e : H → E) (h : H)
    (t : H → T) (routes : Route → H → H) (cost : E → Cost)
    (Lt : Cost → Cost → Prop) :
    (PointClosedCompression e h t routes ↔
      (∀ pair, ¬ PointTargetObstruction e h t pair) ∧
      (∀ γ pair, ¬ PointRouteObstruction e h (routes γ) pair)) ∧
    (PointIrreducible e h t routes cost Lt ↔
      ¬ ∃ e' : H → E, PointClosedCompression e' h t routes ∧
        Lt (cost (e' h)) (cost (e h))) := by
  constructor
  · constructor
    · rintro ⟨ht,hr⟩
      constructor
      · rintro ⟨x,y⟩ ⟨hx,hy,hne⟩
        exact hne (ht x y hx hy)
      · rintro γ ⟨x,y⟩ ⟨hx,hy,hne⟩
        exact hne (hr γ x y hx hy)
    · rintro ⟨ht,hr⟩
      constructor
      · intro x y hx hy
        exact Classical.byContradiction (fun hne => ht (x,y) ⟨hx,hy,hne⟩)
      · intro γ x y hx hy
        exact Classical.byContradiction (fun hne => hr γ (x,y) ⟨hx,hy,hne⟩)
  · constructor
    · intro hir ⟨e',hclosed,hcheap⟩
      exact hir e' hclosed hcheap
    · intro hnot e' hclosed hcheap
      exact hnot ⟨e',hclosed,hcheap⟩

/-- A well-founded cost order gives a minimal closed compression whenever
the closed candidates at the chosen object are inhabited. -/
theorem point_closed_compression_has_irreducible_minimum
    {H E T Route Cost : Type} (h : H) (t : H → T)
    (routes : Route → H → H) (cost : E → Cost)
    (Lt : Cost → Cost → Prop) (hwf : WellFounded Lt)
    (hex : ∃ e : H → E, PointClosedCompression e h t routes) :
    ∃ eStar : H → E,
      PointClosedCompression eStar h t routes ∧
        PointIrreducible eStar h t routes cost Lt := by
  classical
  obtain ⟨e, he⟩ := hex
  have hmin : ∀ v : Cost, ∀ e : H → E, cost (e h) = v →
      PointClosedCompression e h t routes →
      ∃ eStar : H → E, PointClosedCompression eStar h t routes ∧
        PointIrreducible eStar h t routes cost Lt := by
    intro v
    induction v using hwf.induction with
    | h v ih =>
      intro e hcost hclosed
      by_cases hcheaper : ∃ e' : H → E,
          PointClosedCompression e' h t routes ∧
            Lt (cost (e' h)) (cost (e h))
      · obtain ⟨e', he', hlt⟩ := hcheaper
        exact ih (cost (e' h)) (hcost ▸ hlt) e' rfl he'
      · exact ⟨e, hclosed, by
          intro e' he' hlt
          exact hcheaper ⟨e', he', hlt⟩⟩
  exact hmin (cost (e h)) e rfl he

/-- F42 obstruction and irreducibility tests together with existence of a
minimum for an inhabited family of closed candidates in a well-founded cost. -/
theorem paper_irreducibility_with_minimum
    {H E T Route Cost : Type} (e : H → E) (h : H)
    (t : H → T) (routes : Route → H → H) (cost : E → Cost)
    (Lt : Cost → Cost → Prop) (hwf : WellFounded Lt)
    (hex : ∃ e' : H → E, PointClosedCompression e' h t routes) :
    ((PointClosedCompression e h t routes ↔
      (∀ pair, ¬ PointTargetObstruction e h t pair) ∧
      (∀ γ pair, ¬ PointRouteObstruction e h (routes γ) pair)) ∧
    (PointIrreducible e h t routes cost Lt ↔
      ¬ ∃ e' : H → E, PointClosedCompression e' h t routes ∧
        Lt (cost (e' h)) (cost (e h)))) ∧
    ∃ eStar : H → E,
      PointClosedCompression eStar h t routes ∧
        PointIrreducible eStar h t routes cost Lt := by
  exact ⟨paper_irreducibility e h t routes cost Lt,
    point_closed_compression_has_irreducible_minimum h t routes cost Lt hwf hex⟩


/-- Pointwise irreducibility among a declared class of admissible compressions. -/
def PointIrreducibleIn {H E T Route Cost : Type}
    (Admissible : (H → E) → Prop) (e : H → E) (h : H)
    (t : H → T) (routes : Route → H → H) (cost : E → Cost)
    (Lt : Cost → Cost → Prop) : Prop :=
  ∀ e' : H → E, Admissible e' →
    PointClosedCompression e' h t routes →
      ¬ Lt (cost (e' h)) (cost (e h))

/-- The old unrestricted predicate is the all-maps specialization. -/
theorem point_irreducible_all_maps_iff {H E T Route Cost : Type}
    (e : H → E) (h : H) (t : H → T) (routes : Route → H → H)
    (cost : E → Cost) (Lt : Cost → Cost → Prop) :
    PointIrreducible e h t routes cost Lt ↔
      PointIrreducibleIn (fun _ => True) e h t routes cost Lt := by
  constructor
  · intro hir e' _ hclosed
    exact hir e' hclosed
  · intro hir e' hclosed
    exact hir e' trivial hclosed

/-- A well-founded cost order selects a minimum from any inhabited class of
admissible compressions closed at the chosen object. -/
theorem point_closed_admissible_has_irreducible_minimum
    {H E T Route Cost : Type}
    (Admissible : (H → E) → Prop) (h : H) (t : H → T)
    (routes : Route → H → H) (cost : E → Cost)
    (Lt : Cost → Cost → Prop) (hwf : WellFounded Lt)
    (hex : ∃ e : H → E, Admissible e ∧
      PointClosedCompression e h t routes) :
    ∃ eStar : H → E,
      Admissible eStar ∧ PointClosedCompression eStar h t routes ∧
        PointIrreducibleIn Admissible eStar h t routes cost Lt := by
  classical
  obtain ⟨e, hadm, hclosed⟩ := hex
  have hmin : ∀ v : Cost, ∀ e : H → E, cost (e h) = v →
      Admissible e → PointClosedCompression e h t routes →
      ∃ eStar : H → E,
        Admissible eStar ∧ PointClosedCompression eStar h t routes ∧
          PointIrreducibleIn Admissible eStar h t routes cost Lt := by
    intro v
    induction v using hwf.induction with
    | h v ih =>
      intro e hcost headm heclosed
      by_cases hcheaper : ∃ e' : H → E,
          Admissible e' ∧ PointClosedCompression e' h t routes ∧
            Lt (cost (e' h)) (cost (e h))
      · obtain ⟨e', he'adm, he'closed, hlt⟩ := hcheaper
        exact ih (cost (e' h)) (hcost ▸ hlt) e' rfl he'adm he'closed
      · refine ⟨e, headm, heclosed, ?_⟩
        intro e' he'adm he'closed hlt
        exact hcheaper ⟨e', he'adm, he'closed, hlt⟩
  exact hmin (cost (e h)) e rfl hadm hclosed

/-- F42 with pointwise comparisons restricted to admissible compressions. -/
theorem paper_irreducibility_admissible
    {H E T Route Cost : Type}
    (Admissible : (H → E) → Prop) (e : H → E) (h : H)
    (t : H → T) (routes : Route → H → H) (cost : E → Cost)
    (Lt : Cost → Cost → Prop) :
    (PointClosedCompression e h t routes ↔
      (∀ pair, ¬ PointTargetObstruction e h t pair) ∧
      (∀ γ pair, ¬ PointRouteObstruction e h (routes γ) pair)) ∧
    (PointIrreducibleIn Admissible e h t routes cost Lt ↔
      ¬ ∃ e' : H → E, Admissible e' ∧
        PointClosedCompression e' h t routes ∧
          Lt (cost (e' h)) (cost (e h))) ∧
    (WellFounded Lt →
      (∃ e' : H → E, Admissible e' ∧
        PointClosedCompression e' h t routes) →
      ∃ eStar : H → E, Admissible eStar ∧
        PointClosedCompression eStar h t routes ∧
          PointIrreducibleIn Admissible eStar h t routes cost Lt) := by
  refine ⟨(paper_irreducibility e h t routes cost Lt).1, ?_, ?_⟩
  · constructor
    · intro hir ⟨e', headm, hclosed, hcheap⟩
      exact hir e' headm hclosed hcheap
    · intro hnot e' headm hclosed hcheap
      exact hnot ⟨e', headm, hclosed, hcheap⟩
  · intro hwf hex
    exact point_closed_admissible_has_irreducible_minimum Admissible h t
      routes cost Lt hwf hex

/-- If admissible maps can isolate the chosen object at every output value,
pointwise irreducibility reduces to the absence of a cheaper output value. -/
theorem point_irreducible_isolating_maps_collapses
    {H E T Route Cost : Type}
    (Admissible : (H → E) → Prop) (e : H → E) (h : H)
    (t : H → T) (routes : Route → H → H) (cost : E → Cost)
    (Lt : Cost → Cost → Prop)
    (hisolate : ∀ v : E, ∃ e' : H → E, Admissible e' ∧ e' h = v ∧
      ∀ x : H, x ≠ h → e' x ≠ v) :
    PointIrreducibleIn Admissible e h t routes cost Lt ↔
      ¬ ∃ v : E, Lt (cost v) (cost (e h)) := by
  classical
  constructor
  · intro hir ⟨v, hcheap⟩
    obtain ⟨e', hadm, heh, hisolated⟩ := hisolate v
    have hsingleton : ∀ x, e' x = e' h → x = h := by
      intro x hx
      by_cases hxh : x = h
      · exact hxh
      · exact False.elim (hisolated x hxh (hx.trans heh))
    have hclosed : PointClosedCompression e' h t routes := by
      constructor
      · intro x y hx hy
        rw [hsingleton x hx, hsingleton y hy]
      · intro γ x y hx hy
        rw [hsingleton x hx, hsingleton y hy]
    exact hir e' hadm hclosed (heh.symm ▸ hcheap)
  · intro hnone e' _ _ hcheap
    exact hnone ⟨e' h, hcheap⟩

/-- With unrestricted admissibility and two output values, a singleton fiber
can be made at h for every chosen value. Pointwise irreducibility then ignores
the target and routes and reduces to a cost-minimum test on E. -/
theorem point_irreducible_all_maps_collapses
    {H E T Route Cost : Type}
    (Admissible : (H → E) → Prop) (e : H → E) (h : H)
    (t : H → T) (routes : Route → H → H) (cost : E → Cost)
    (Lt : Cost → Cost → Prop)
    (hall : ∀ e' : H → E, Admissible e')
    (hnontrivial : ∃ a b : E, a ≠ b) :
    PointIrreducibleIn Admissible e h t routes cost Lt ↔
      ¬ ∃ v : E, Lt (cost v) (cost (e h)) := by
  classical
  apply point_irreducible_isolating_maps_collapses Admissible e h t routes cost Lt
  intro v
  obtain ⟨a, b, hab⟩ := hnontrivial
  let w : E := if v = a then b else a
  have hwv : w ≠ v := by
    by_cases hva : v = a
    · simp only [w, if_pos hva]
      intro hbv
      exact hab (hva.symm.trans hbv.symm)
    · simp only [w, if_neg hva]
      intro hav
      exact hva hav.symm
  let e' : H → E := fun x => if x = h then v else w
  refine ⟨e', hall e', by simp [e'], ?_⟩
  intro x hxh
  simpa [e', hxh] using hwv

/-- Source admissibility composes as factorization of maps; no surjectivity
of the base or either description is required. -/
theorem source_admissible_trans {H B E E' : Type}
    (base : H → B) (compression : H → E) (next : H → E') :
    SourceAdmissible base compression → SourceAdmissible compression next →
      SourceAdmissible base next := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨b ∘ a, ?_⟩
  funext h
  exact (congrArg b (congrFun ha h)).trans (congrFun hb h)

/-- A well-founded cost order selects a globally cheapest admissible closed
compression over the base. It is also irreducible when used as the new base,
since all descriptions closed over it already factor through the old base. -/
theorem admissible_closed_compression_has_irreducible_minimum
    {H B Target Route Cost : Type}
    (base : H → B) (target : H → Target) (routes : Route → H → H)
    (Admissible : {E : Type} → (H → E) → Prop)
    (cost : {E : Type} → (H → E) → Cost) (CostLt : Cost → Cost → Prop)
    (hwf : WellFounded CostLt)
    (hex : ∃ (E : Type) (e : H → E),
      Admissible e ∧ ClosedCompression base e target routes) :
    ∃ (EStar : Type) (eStar : H → EStar),
      Admissible eStar ∧ ClosedCompression base eStar target routes ∧
      (∀ (E' : Type) (e' : H → E'), Admissible e' →
        ClosedCompression base e' target routes → ¬ CostLt (cost e') (cost eStar)) ∧
      Irreducible eStar target routes Admissible cost CostLt := by
  classical
  have hmin : ∀ v : Cost, ∀ (E : Type) (e : H → E), cost e = v →
      Admissible e → ClosedCompression base e target routes →
      ∃ (EStar : Type) (eStar : H → EStar),
        Admissible eStar ∧ ClosedCompression base eStar target routes ∧
        (∀ (E' : Type) (e' : H → E'), Admissible e' →
          ClosedCompression base e' target routes → ¬ CostLt (cost e') (cost eStar)) ∧
        Irreducible eStar target routes Admissible cost CostLt := by
    intro v
    induction v using hwf.induction with
    | h v ih =>
      intro E e hcost hadm hclosed
      by_cases hcheaper : ∃ (E' : Type) (e' : H → E'), Admissible e' ∧
          ClosedCompression base e' target routes ∧ CostLt (cost e') (cost e)
      · obtain ⟨E', e', he'adm, he'closed, hlt⟩ := hcheaper
        exact ih (cost e') (hcost ▸ hlt) E' e' rfl he'adm he'closed
      · refine ⟨E, e, hadm, hclosed, ?_, ?_⟩
        · intro E' e' he'adm he'closed hlt
          exact hcheaper ⟨E', e', he'adm, he'closed, hlt⟩
        · intro E' e' he'adm he'closed hlt
          have hclosedBase : ClosedCompression base e' target routes :=
            ⟨source_admissible_trans base e e' hclosed.1 he'closed.1, he'closed.2⟩
          exact hcheaper ⟨E', e', he'adm, hclosedBase, hlt⟩
  obtain ⟨E, e, hadm, hclosed⟩ := hex
  exact hmin (cost e) E e rfl hadm hclosed

end SixBirdsMetaMath.FoundationsIV.SelfReferenceLimits.Irreducibility
