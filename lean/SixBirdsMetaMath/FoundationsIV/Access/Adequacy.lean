import SixBirdsMetaMath.FoundationsIV.Access.Quotientality

/-!
F11 Adequacy / No-Overread.

Accepted current-layer claims must stay inside the declared access quotient:
suppressed dependencies need admissible bridges, and exact readouts must factor
through the access quotient. The same factorization/no-split-pair shape models
exact adequacy of a target probe through a native probe family.
-/

namespace SixBirdsMetaMath.FoundationsIV.Access.Adequacy

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair
open SixBirdsMetaMath.FoundationsIV.Stability.SufficiencyClosure
open SixBirdsMetaMath.FoundationsIV.Access.Quotientality

/-- A dependency is overread when it is used, suppressed by the instrument, and
has no admissible bridge. -/
def OverreadDefect {Dep : Type} (use suppressed permits : Dep → Prop) :
    Dep → Prop :=
  fun dep => use dep ∧ suppressed dep ∧ ¬ permits dep

/-- A defect predicate has no witnesses. -/
def DefectEmpty {α : Type} (defect : α → Prop) : Prop :=
  ∀ x : α, ¬ defect x

/-- Qualitative no-overread: no used suppressed dependency is unbridged. -/
def NoOverread {Dep : Type} (use suppressed permits : Dep → Prop) : Prop :=
  DefectEmpty (OverreadDefect use suppressed permits)

/-- Weak-bridge defect: a used bridge is present but below the claim's requested
strength. -/
def WeakBridgeDefect {Dep Strength : Type} (use : Dep → Prop)
    (bridgeStrength requiredStrength : Dep → Strength)
    (below : Strength → Strength → Prop) : Dep → Prop :=
  fun dep => use dep ∧ below (bridgeStrength dep) (requiredStrength dep)

/-- Outside-scope content used by the claim. -/
def OutsideDefect {Dep : Type} (use outside : Dep → Prop) : Dep → Prop :=
  fun dep => use dep ∧ outside dep

/-- Unknown-visibility content used by the claim. -/
def UnknownDefect {Dep : Type} (use unknown : Dep → Prop) : Dep → Prop :=
  fun dep => use dep ∧ unknown dep

/-- The visibility defect is the union of overread, weak-bridge, outside, and
unknown defects. -/
def VisibilityDefect {Dep : Type} (overread weak outside unknown : Dep → Prop) :
    Dep → Prop :=
  fun dep => overread dep ∨ weak dep ∨ outside dep ∨ unknown dep

/-- A current-layer claim classifier records the access discipline needed for
accepted claims. -/
structure AccessClaimClassifier (Claim Dep H QI W : Type) (qI : H → QI) where
  Accepted : Claim → Prop
  Asserted : Claim → H → W
  Use : Claim → Dep → Prop
  Suppressed : Dep → Prop
  BridgePermits : Claim → Dep → Prop
  accepted_bridges_suppressed :
    ∀ {claim : Claim} {dep : Dep},
      Accepted claim → Use claim dep → Suppressed dep → BridgePermits claim dep
  accepted_current_visible :
    ∀ {claim : Claim}, Accepted claim → CurrentVisible qI (Asserted claim)

/-- The semantic split-pair defect for a current-layer expression. -/
def SemanticOverreadDefect {H QI W : Type} (qI : H → QI) (expr : H → W) :
    (H × H) → Prop :=
  SufficiencySplitPair qI expr

/-- Exact semantic no-overread is emptiness of the semantic split-pair defect. -/
def SemanticNoOverread {H QI W : Type} (qI : H → QI) (expr : H → W) : Prop :=
  ObstructionEmpty (SemanticOverreadDefect qI expr)

/-- An exact current claim is a claim whose expression factors through access. -/
def ExactCurrentClaim {H QI W : Type} (qI : H → QI) (expr : H → W) : Prop :=
  FactorsThroughAccess qI expr

/-- Exact adequacy split-pair: the native probe agrees but the target probe
does not. -/
def AdequacySplitPair {E Y Z : Type} (native : E → Y) (target : E → Z) :
    (E × E) → Prop :=
  SufficiencySplitPair native target

/-- Exact target adequacy through the native probe family. -/
def ExactAdequacy {E Y Z : Type} (native : E → Y) (target : E → Z) : Prop :=
  FactorsThroughQ native target

/-- No exact adequacy blind spot: there is no native-equal/target-different
split pair. -/
def AdequacyBlindSpotAbsent {E Y Z : Type} (native : E → Y) (target : E → Z) :
    Prop :=
  ObstructionEmpty (AdequacySplitPair native target)

/-- Abstract budgeted adequacy: the residual is within a declared budget. -/
def BudgetedAdequacy {Residual Budget : Type} (residual : Residual)
    (budget : Budget) (withinBudget : Residual → Budget → Prop) : Prop :=
  withinBudget residual budget

/-- A claim beyond exact access is lawful only through a bridge or a priced
residual. -/
def LawfulBeyondAccess (exact bridged priced : Prop) : Prop :=
  exact ∨ bridged ∨ priced

/-- The forbidden case: no exact factorization, no bridge, and no price. -/
def UnpricedBlindSpot (exact bridged priced : Prop) : Prop :=
  ¬ exact ∧ ¬ bridged ∧ ¬ priced

/-- Access-side statuses for the adequacy/no-overread classifier. -/
inductive AdequacyNoOverreadStatus where
  | exactVisibleAdequacy
  | bridgedAdequacy
  | budgetedAdequacy
  | unbridgedOverread
  | weakBridge
  | activeAdequacyBlindSpot
  | outsideOrUnknown
deriving DecidableEq

/-- Meaning of each access-side adequacy status. -/
def AdequacyNoOverreadStatusHolds
    (exactVisible bridged budgeted overread weakBridge activeBlindSpot
      outsideOrUnknown : Prop) :
    AdequacyNoOverreadStatus → Prop
  | AdequacyNoOverreadStatus.exactVisibleAdequacy => exactVisible
  | AdequacyNoOverreadStatus.bridgedAdequacy => bridged
  | AdequacyNoOverreadStatus.budgetedAdequacy => budgeted
  | AdequacyNoOverreadStatus.unbridgedOverread => overread
  | AdequacyNoOverreadStatus.weakBridge => weakBridge
  | AdequacyNoOverreadStatus.activeAdequacyBlindSpot => activeBlindSpot
  | AdequacyNoOverreadStatus.outsideOrUnknown => outsideOrUnknown

/-- Empty overread defect is equivalent to every used suppressed dependency
being bridged. -/
theorem no_overread_iff_all_suppressed_bridged {Dep : Type}
    (use suppressed permits : Dep → Prop) :
    NoOverread use suppressed permits ↔
      ∀ dep : Dep, use dep → suppressed dep → permits dep := by
  constructor
  · intro hno dep huse hsuppressed
    exact Classical.byContradiction (fun hmissing =>
      hno dep ⟨huse, hsuppressed, hmissing⟩)
  · intro hall dep hoverread
    exact hoverread.2.2 (hall dep hoverread.1 hoverread.2.1)

/-- An accepted claim has no unbridged suppressed dependency. -/
theorem accepted_claim_no_overread {Claim Dep H QI W : Type} {qI : H → QI}
    (classifier : AccessClaimClassifier Claim Dep H QI W qI) (claim : Claim) :
    classifier.Accepted claim →
      NoOverread (classifier.Use claim) classifier.Suppressed
        (classifier.BridgePermits claim) := by
  intro haccepted
  exact (no_overread_iff_all_suppressed_bridged
    (classifier.Use claim) classifier.Suppressed
      (classifier.BridgePermits claim)).2
    (fun dep huse hsuppressed =>
      classifier.accepted_bridges_suppressed haccepted huse hsuppressed)

/-- Overread defects are visibility defects. -/
theorem overread_subset_visibility {Dep : Type}
    (overread weak outside unknown : Dep → Prop) :
    ∀ dep : Dep, overread dep → VisibilityDefect overread weak outside unknown dep := by
  intro dep hoverread
  exact Or.inl hoverread

/-- Semantic exact visibility is the same as absence of semantic split pairs. -/
theorem semantic_no_overread_iff_current_visible {H QI W : Type}
    (qI : H → QI) (expr : H → W) (hqI : Function.Surjective qI) :
    CurrentVisible qI expr ↔ SemanticNoOverread qI expr := by
  change PackageClosed qI expr ↔ ObstructionEmpty (SufficiencySplitPair qI expr)
  exact (sufficiency_closure qI expr hqI).2.1

/-- Exact factorization through access is the same as semantic no-overread. -/
theorem exact_current_claim_iff_semantic_no_overread {H QI W : Type}
    (qI : H → QI) (expr : H → W) (hqI : Function.Surjective qI) :
    ExactCurrentClaim qI expr ↔ SemanticNoOverread qI expr := by
  constructor
  · intro hfactors
    have hclosed : CurrentVisible qI expr :=
      (sufficiency_closure qI expr hqI).1.2 hfactors
    exact (semantic_no_overread_iff_current_visible qI expr hqI).1 hclosed
  · intro hno
    have hclosed : CurrentVisible qI expr :=
      (semantic_no_overread_iff_current_visible qI expr hqI).2 hno
    exact (sufficiency_closure qI expr hqI).1.1 hclosed

/-- Exact adequacy is the no-blind-spot split-pair condition. -/
theorem exact_adequacy_iff_no_blind_spot {E Y Z : Type}
    (native : E → Y) (target : E → Z) (hnative : Function.Surjective native) :
    ExactAdequacy native target ↔ AdequacyBlindSpotAbsent native target := by
  constructor
  · intro hfactors
    have hclosed : PackageClosed native target :=
      (sufficiency_closure native target hnative).1.2 hfactors
    exact (sufficiency_closure native target hnative).2.1.1 hclosed
  · intro hno
    have hclosed : PackageClosed native target :=
      (sufficiency_closure native target hnative).2.1.2 hno
    exact (sufficiency_closure native target hnative).1.1 hclosed

/-- "Exact, bridged, or priced" is precisely the negation of an unpriced blind
spot. -/
theorem lawful_support_iff_no_unpriced_blind_spot
    (exact bridged priced : Prop) :
    LawfulBeyondAccess exact bridged priced ↔
      ¬ UnpricedBlindSpot exact bridged priced := by
  classical
  constructor
  · intro hsupport hblind
    cases hsupport with
    | inl hexact =>
        exact hblind.1 hexact
    | inr hrest =>
        cases hrest with
        | inl hbridged =>
            exact hblind.2.1 hbridged
        | inr hpriced =>
            exact hblind.2.2 hpriced
  · intro hnotBlind
    by_cases hexact : exact
    · exact Or.inl hexact
    · by_cases hbridged : bridged
      · exact Or.inr (Or.inl hbridged)
      · by_cases hpriced : priced
        · exact Or.inr (Or.inr hpriced)
        · exact False.elim (hnotBlind ⟨hexact, hbridged, hpriced⟩)

/--
Adequacy / No-Overread Normal Form. An accepted current-layer claim has no
unbridged suppressed dependencies and its asserted current expression factors
through the access quotient. Exact semantic visibility and exact native-target
adequacy are both no-split-pair factorization laws; beyond exact access, lawful
support is exactly bridge-or-budget pricing rather than an unpriced blind spot.
-/
theorem adequacy_no_overread {Claim Dep H QI W E Y Z Residual Budget : Type}
    (qI : H → QI)
    (classifier : AccessClaimClassifier Claim Dep H QI W qI) (claim : Claim)
    (hqI : Function.Surjective qI)
    (native : E → Y) (target : E → Z) (hnative : Function.Surjective native)
    (residual : Residual) (budget : Budget)
    (withinBudget : Residual → Budget → Prop) (bridged : Prop) :
    classifier.Accepted claim →
      NoOverread (classifier.Use claim) classifier.Suppressed
          (classifier.BridgePermits claim) ∧
        FactorsThroughAccess qI (classifier.Asserted claim) ∧
          (CurrentVisible qI (classifier.Asserted claim) ↔
            SemanticNoOverread qI (classifier.Asserted claim)) ∧
            (ExactAdequacy native target ↔
              AdequacyBlindSpotAbsent native target) ∧
              (LawfulBeyondAccess (ExactAdequacy native target) bridged
                  (BudgetedAdequacy residual budget withinBudget) ↔
                ¬ UnpricedBlindSpot (ExactAdequacy native target) bridged
                  (BudgetedAdequacy residual budget withinBudget)) := by
  intro haccepted
  have hnoOverread :
      NoOverread (classifier.Use claim) classifier.Suppressed
        (classifier.BridgePermits claim) :=
    accepted_claim_no_overread classifier claim haccepted
  have hvisible : CurrentVisible qI (classifier.Asserted claim) :=
    classifier.accepted_current_visible haccepted
  have hfactors : FactorsThroughAccess qI (classifier.Asserted claim) :=
    (sufficiency_closure qI (classifier.Asserted claim) hqI).1.1 hvisible
  exact ⟨hnoOverread, hfactors,
    semantic_no_overread_iff_current_visible qI (classifier.Asserted claim) hqI,
    exact_adequacy_iff_no_blind_spot native target hnative,
    lawful_support_iff_no_unpriced_blind_spot
      (ExactAdequacy native target) bridged
      (BudgetedAdequacy residual budget withinBudget)⟩

/-- F11's semantic no-overread and unique factorization, with the acceptance
rule stated as a hypothesis instead of a classifier field. -/
theorem paper_adequacy_unique_without_record_no
    {H QI W : Type} (accessQ : H → QI) (F : H → W)
    (Accepted : (H → W) → Prop)
    (hNO : ∀ G, Accepted G →
      ∀ h h', accessQ h = accessQ h' → G h = G h')
    (haccepted : Accepted F) (hq : Function.Surjective accessQ) :
    ((∀ h h', accessQ h = accessQ h' → F h = F h') ↔
      SemanticNoOverread accessQ F) ∧
    (SemanticNoOverread accessQ F ↔
      ∃ Fbar : QI → W, F = Fbar ∘ accessQ ∧
        ∀ Fbar' : QI → W, F = Fbar' ∘ accessQ → Fbar' = Fbar) ∧
    (∀ h h', accessQ h = accessQ h' → F h = F h') ∧
    (∃ Fbar : QI → W, F = Fbar ∘ accessQ ∧
      ∀ Fbar' : QI → W, F = Fbar' ∘ accessQ → Fbar' = Fbar) := by
  let KernelConstant : Prop :=
    ∀ h h', accessQ h = accessQ h' → F h = F h'
  have hkernel : KernelConstant ↔ SemanticNoOverread accessQ F := by
    constructor
    · intro h ⟨x,y⟩ ⟨hxy,hne⟩
      exact hne (h x y hxy)
    · intro h x y hxy
      exact Classical.byContradiction (fun hne => h (x,y) ⟨hxy,hne⟩)
  have hfactor : KernelConstant ↔
      ∃ Fbar : QI → W, F = Fbar ∘ accessQ ∧
        ∀ Fbar' : QI → W, F = Fbar' ∘ accessQ → Fbar' = Fbar := by
    constructor
    · intro h
      rcases (sufficiency_closure accessQ F hq).1.1 h with ⟨Fbar, hcomm⟩
      refine ⟨Fbar, hcomm.symm, ?_⟩
      intro Fbar' hcomm'
      funext a
      obtain ⟨x, rfl⟩ := hq a
      have hx := congrFun hcomm x
      have hx' := congrFun hcomm' x
      dsimp [Function.comp] at hx hx'
      exact hx'.symm.trans hx.symm
    · rintro ⟨Fbar, hcomm, _⟩ x y hxy
      have hx := congrFun hcomm x
      have hy := congrFun hcomm y
      dsimp [Function.comp] at hx hy
      exact hx.trans ((congrArg Fbar hxy).trans hy.symm)
  have hconst : KernelConstant := hNO F haccepted
  exact ⟨hkernel, hkernel.symm.trans hfactor, hconst, hfactor.mp hconst⟩

/-- The global no-overread rule is exactly unique factorization of every
accepted exact current claim through the surjective access quotient. -/
theorem no_overread_iff_all_accepted_factor_uniquely
    {H QI W : Type} (accessQ : H → QI)
    (Accepted : (H → W) → Prop) (hq : Function.Surjective accessQ) :
    (∀ F, Accepted F →
      ∀ h h', accessQ h = accessQ h' → F h = F h') ↔
    ∀ F, Accepted F →
      ∃ Fbar : QI → W, F = Fbar ∘ accessQ ∧
        ∀ Fbar' : QI → W, F = Fbar' ∘ accessQ → Fbar' = Fbar := by
  constructor
  · intro hNO F haccepted
    exact (paper_adequacy_unique_without_record_no accessQ F Accepted
      hNO haccepted hq).2.2.2
  · intro hfactor F haccepted h h' hsame
    obtain ⟨Fbar, hF, _⟩ := hfactor F haccepted
    have hx := congrFun hF h
    have hy := congrFun hF h'
    exact hx.trans ((congrArg Fbar hsame).trans hy.symm)

/-- F11 with the global characterization of (NO) and its accepted-claim
consequences in one paper-facing statement. -/
theorem paper_adequacy_global_no_overread
    {H QI W : Type} (accessQ : H → QI) (F : H → W)
    (Accepted : (H → W) → Prop) (hq : Function.Surjective accessQ) :
    ((∀ G, Accepted G →
      ∀ h h', accessQ h = accessQ h' → G h = G h') ↔
      ∀ G, Accepted G →
        ∃ Gbar : QI → W, G = Gbar ∘ accessQ ∧
          ∀ Gbar' : QI → W, G = Gbar' ∘ accessQ → Gbar' = Gbar) ∧
    ((∀ G, Accepted G →
      ∀ h h', accessQ h = accessQ h' → G h = G h') →
      Accepted F →
        ((∀ h h', accessQ h = accessQ h' → F h = F h') ↔
          SemanticNoOverread accessQ F) ∧
        (SemanticNoOverread accessQ F ↔
          ∃ Fbar : QI → W, F = Fbar ∘ accessQ ∧
            ∀ Fbar' : QI → W, F = Fbar' ∘ accessQ → Fbar' = Fbar) ∧
        (∀ h h', accessQ h = accessQ h' → F h = F h') ∧
        (∃ Fbar : QI → W, F = Fbar ∘ accessQ ∧
          ∀ Fbar' : QI → W, F = Fbar' ∘ accessQ → Fbar' = Fbar)) := by
  exact ⟨no_overread_iff_all_accepted_factor_uniquely accessQ Accepted hq,
    fun hNO haccepted =>
      paper_adequacy_unique_without_record_no accessQ F Accepted
        hNO haccepted hq⟩

/-- For every claim, no semantic overread is equivalent to constancy and
unique factorization, independently of acceptance or the global NO rule. -/
theorem adequacy_every_claim_equivalences
    {H QI W : Type} (accessQ : H → QI) (F : H → W)
    (hq : Function.Surjective accessQ) :
    ((∀ h h', accessQ h = accessQ h' → F h = F h') ↔
      SemanticNoOverread accessQ F) ∧
    (SemanticNoOverread accessQ F ↔
      ∃ Fbar : QI → W, F = Fbar ∘ accessQ ∧
        ∀ Fbar' : QI → W, F = Fbar' ∘ accessQ → Fbar' = Fbar) := by
  classical
  have hkernel :
      (∀ h h', accessQ h = accessQ h' → F h = F h') ↔
        SemanticNoOverread accessQ F := by
    constructor
    · intro h ⟨x, y⟩ ⟨hxy, hne⟩
      exact hne (h x y hxy)
    · intro h x y hxy
      exact Classical.byContradiction (fun hne => h (x, y) ⟨hxy, hne⟩)
  have hfactor :
      (∀ h h', accessQ h = accessQ h' → F h = F h') ↔
        ∃ Fbar : QI → W, F = Fbar ∘ accessQ ∧
          ∀ Fbar' : QI → W, F = Fbar' ∘ accessQ → Fbar' = Fbar := by
    constructor
    · intro h
      rcases (sufficiency_closure accessQ F hq).1.1 h with ⟨Fbar, hcomm⟩
      refine ⟨Fbar, hcomm.symm, ?_⟩
      intro Fbar' hcomm'
      funext a
      obtain ⟨x, rfl⟩ := hq a
      have hx := congrFun hcomm x
      have hx' := congrFun hcomm' x
      dsimp [Function.comp] at hx hx'
      exact hx'.symm.trans hx.symm
    · rintro ⟨Fbar, hcomm, _⟩ x y hxy
      have hx := congrFun hcomm x
      have hy := congrFun hcomm y
      dsimp [Function.comp] at hx hy
      exact hx.trans ((congrArg Fbar hxy).trans hy.symm)
  exact ⟨hkernel, hkernel.symm.trans hfactor⟩

/-- Paper F11: unconditional claim equivalences, accepted claims under NO,
and the global characterization of NO. -/
theorem paper_adequacy_three_parts
    {H QI W : Type} (accessQ : H → QI)
    (Accepted : (H → W) → Prop) (hq : Function.Surjective accessQ) :
    (∀ F : H → W,
      ((∀ h h', accessQ h = accessQ h' → F h = F h') ↔
        SemanticNoOverread accessQ F) ∧
      (SemanticNoOverread accessQ F ↔
        ∃ Fbar : QI → W, F = Fbar ∘ accessQ ∧
          ∀ Fbar' : QI → W, F = Fbar' ∘ accessQ → Fbar' = Fbar)) ∧
    ((∀ G, Accepted G →
      ∀ h h', accessQ h = accessQ h' → G h = G h') →
      ∀ F, Accepted F →
        (∀ h h', accessQ h = accessQ h' → F h = F h') ∧
        (∃ Fbar : QI → W, F = Fbar ∘ accessQ ∧
          ∀ Fbar' : QI → W, F = Fbar' ∘ accessQ → Fbar' = Fbar)) ∧
    ((∀ G, Accepted G →
      ∀ h h', accessQ h = accessQ h' → G h = G h') ↔
      ∀ G, Accepted G →
        ∃ Gbar : QI → W, G = Gbar ∘ accessQ ∧
          ∀ Gbar' : QI → W, G = Gbar' ∘ accessQ → Gbar' = Gbar) := by
  refine ⟨fun F => adequacy_every_claim_equivalences accessQ F hq,
    ?_, no_overread_iff_all_accepted_factor_uniquely accessQ Accepted hq⟩
  intro hNO F haccepted
  have hequiv := adequacy_every_claim_equivalences accessQ F hq
  have hconst := hNO F haccepted
  exact ⟨hconst, hequiv.2.mp (hequiv.1.mp hconst)⟩

end SixBirdsMetaMath.FoundationsIV.Access.Adequacy
