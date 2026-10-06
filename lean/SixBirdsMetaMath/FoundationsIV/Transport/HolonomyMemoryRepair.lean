import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F3 Holonomy-Memory Repair Normal Form.

Route residue has no unallocated status: if two route outcomes are invisible
to the current quotient `Q` but distinguished by future probes on the
predictive quotient `M`, then the route forces memory. The canonical repair is
the promotion from the current quotient to the predictive quotient.
-/

namespace SixBirdsMetaMath.FoundationsIV.Transport.HolonomyMemoryRepair

/-- Two route handles are indistinguishable by every current-quotient probe. -/
def CurrentQInvisible {Route Q : Type} (currentVisible : Route → Q → Prop)
    (r₁ r₂ : Route) : Prop :=
  ∀ q : Q, currentVisible r₁ q ↔ currentVisible r₂ q

/-- Two route handles are distinguished by at least one predictive-quotient
future probe. -/
def FutureMVisible {Route M : Type} (futureVisible : Route → M → Prop)
    (r₁ r₂ : Route) : Prop :=
  ∃ m : M, futureVisible r₁ m ≠ futureVisible r₂ m

/-- Hidden route residue: current-invisible, future-visible route difference. -/
def HiddenRouteResidue {Route Q M : Type}
    (currentVisible : Route → Q → Prop) (futureVisible : Route → M → Prop)
    (r₁ r₂ : Route) : Prop :=
  CurrentQInvisible currentVisible r₁ r₂ ∧ FutureMVisible futureVisible r₁ r₂

/-- A memory witness is a route with some hidden route-residue mate. -/
def MemoryWitness {Route Q M : Type}
    (currentVisible : Route → Q → Prop) (futureVisible : Route → M → Prop)
    (route : Route) : Prop :=
  ∃ other : Route, HiddenRouteResidue currentVisible futureVisible route other

/--
The predictive repair witness records the same hidden route residue at the
`M`-level, together with the fact that the predictive witness has a current
shadow through `π : M -> Q`.
-/
def PredictiveRepairWitness {Route Q M : Type} (π : M → Q)
    (currentVisible : Route → Q → Prop) (futureVisible : Route → M → Prop)
    (r₁ r₂ : Route) : Prop :=
  CurrentQInvisible currentVisible r₁ r₂ ∧
    ∃ m : M,
      futureVisible r₁ m ≠ futureVisible r₂ m ∧
        (currentVisible r₁ (π m) ↔ currentVisible r₂ (π m))

/-- Hidden route residue always supplies the predictive repair witness. -/
theorem hidden_residue_gives_predictive_repair {Route Q M : Type} (π : M → Q)
    (currentVisible : Route → Q → Prop) (futureVisible : Route → M → Prop)
    {r₁ r₂ : Route} :
    HiddenRouteResidue currentVisible futureVisible r₁ r₂ →
      PredictiveRepairWitness π currentVisible futureVisible r₁ r₂ := by
  intro h
  rcases h with ⟨hcurrent, ⟨m, hfuture⟩⟩
  exact ⟨hcurrent, ⟨m, hfuture, hcurrent (π m)⟩⟩

/-- A predictive repair witness forgets back to hidden route residue. -/
theorem predictive_repair_gives_hidden_residue {Route Q M : Type} (π : M → Q)
    (currentVisible : Route → Q → Prop) (futureVisible : Route → M → Prop)
    {r₁ r₂ : Route} :
    PredictiveRepairWitness π currentVisible futureVisible r₁ r₂ →
      HiddenRouteResidue currentVisible futureVisible r₁ r₂ := by
  intro h
  rcases h with ⟨hcurrent, ⟨m, hfuture, _hshadow⟩⟩
  exact ⟨hcurrent, ⟨m, hfuture⟩⟩

/--
Holonomy-Memory Repair Normal Form: a route forces memory exactly when it has
a current-invisible mate that is visible to the predictive quotient. The
comparison map `π : M -> Q` records that the M-level repair still has a
current quotient shadow.
-/
theorem holonomy_memory_repair_normal_form {Route Q M : Type} (π : M → Q)
    (currentVisible : Route → Q → Prop) (futureVisible : Route → M → Prop)
    (route : Route) :
    MemoryWitness currentVisible futureVisible route ↔
      ∃ r₁ r₂ : Route,
        r₁ = route ∧
          PredictiveRepairWitness π currentVisible futureVisible r₁ r₂ := by
  constructor
  · intro hmemory
    rcases hmemory with ⟨other, hhidden⟩
    exact ⟨route, other, rfl,
      hidden_residue_gives_predictive_repair π currentVisible futureVisible hhidden⟩
  · intro hrepair
    rcases hrepair with ⟨r₁, r₂, hroute, hpredictive⟩
    subst hroute
    exact ⟨r₂,
      predictive_repair_gives_hidden_residue π currentVisible futureVisible hpredictive⟩

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- The two route outputs force memory when no current-quotient readout can
recover both predictive values. -/
def MemoryForced {H Z Q M : Type} (curQ : Z → Q) (predM : Z → M)
    (γ η : H → Z) (h : H) : Prop :=
  ¬ ∃ g : Q → M,
    g (curQ (γ h)) = predM (γ h) ∧
      g (curQ (η h)) = predM (η h)

/-- The two routes have the same current class and different predictive
values. -/
def RouteResidue {H Z Q M : Type} (curQ : Z → Q) (predM : Z → M)
    (γ η : H → Z) (h : H) : Prop :=
  curQ (γ h) = curQ (η h) ∧ predM (γ h) ≠ predM (η h)

/-- Memory is forced exactly by a route residue. -/
theorem memory_forced_iff_route_residue {H Z Q M : Type}
    (curQ : Z → Q) (predM : Z → M) (γ η : H → Z) (h : H) :
    MemoryForced curQ predM γ η h ↔ RouteResidue curQ predM γ η h := by
  classical
  constructor
  · intro hforced
    by_cases hq : curQ (γ h) = curQ (η h)
    · refine ⟨hq, ?_⟩
      intro hm
      apply hforced
      exact ⟨fun _ => predM (γ h), rfl, hm⟩
    · exact False.elim (hforced ⟨
        fun q => if q = curQ (γ h) then predM (γ h) else predM (η h),
        by simp,
        by
          have hne : curQ (η h) ≠ curQ (γ h) := fun heq => hq heq.symm
          simp [hne]⟩)
  · intro ⟨hq, hm⟩ ⟨g, hgγ, hgη⟩
    exact hm (hgγ.symm.trans ((congrArg g hq).trans hgη))

/-- The canonical memory repair records current and predictive values. -/
def memoryRepair {Z Q M : Type} (curQ : Z → Q) (predM : Z → M) :
    Z → Q × M :=
  fun z => (curQ z, predM z)

/-- The memory repair refines the current quotient. -/
theorem memory_repair_refines {Z Q M : Type} (curQ : Z → Q)
    (predM : Z → M) : SourceRefinement (memoryRepair curQ predM) curQ := by
  change SourceRefinement
    (sourceRepairQuotient curQ (fun z : Z => z) predM) curQ
  exact source_repair_refines curQ (fun z : Z => z) predM

/-- Predictive memory descends through the memory repair. -/
theorem memory_repair_descends {Z Q M : Type} (curQ : Z → Q)
    (predM : Z → M) :
    Descends (memoryRepair curQ predM) (fun z : Z => z) predM := by
  change Descends
    (sourceRepairQuotient curQ (fun z : Z => z) predM)
    (fun z : Z => z) predM
  exact source_repair_descends curQ (fun z : Z => z) predM

/-- Every refinement admitting predictive descent refines the memory repair
in kernel form. -/
theorem memory_repair_coarsest {Z Q Q' M : Type} (curQ : Z → Q)
    (predM : Z → M) (q' : Z → Q')
    (href : SourceRefinement q' curQ)
    (hdesc : Descends q' (fun z : Z => z) predM) :
    ∀ z z', q' z = q' z' → memoryRepair curQ predM z =
      memoryRepair curQ predM z' := by
  exact source_repair_coarsest curQ (fun z : Z => z) predM q' href hdesc

/-- Route residue separates the repaired classes of the two route outputs. -/
theorem route_residue_separates_repair {H Z Q M : Type}
    (curQ : Z → Q) (predM : Z → M) (γ η : H → Z) (h : H)
    (hresidue : RouteResidue curQ predM γ η h) :
    memoryRepair curQ predM (γ h) ≠ memoryRepair curQ predM (η h) := by
  intro heq
  exact hresidue.2 (congrArg Prod.snd heq)

/-- The strengthened paper statement of holonomy-memory repair. -/
theorem paper_holonomy_memory_repair {H Z Q M : Type}
    (curQ : Z → Q) (predM : Z → M) (γ η : H → Z) (h : H) :
    (MemoryForced curQ predM γ η h ↔ RouteResidue curQ predM γ η h) ∧
    (SourceRefinement (memoryRepair curQ predM) curQ ∧
      Descends (memoryRepair curQ predM) (fun z : Z => z) predM ∧
      ∀ {Q' : Type} (q' : Z → Q'),
        SourceRefinement q' curQ →
          Descends q' (fun z : Z => z) predM →
            ∀ z z', q' z = q' z' →
              memoryRepair curQ predM z = memoryRepair curQ predM z') ∧
    (RouteResidue curQ predM γ η h →
      memoryRepair curQ predM (γ h) ≠ memoryRepair curQ predM (η h)) := by
  refine ⟨memory_forced_iff_route_residue curQ predM γ η h,
    ⟨memory_repair_refines curQ predM, memory_repair_descends curQ predM, ?_⟩,
    route_residue_separates_repair curQ predM γ η h⟩
  intro Q' q' href hdesc
  exact memory_repair_coarsest curQ predM q' href hdesc

end SixBirdsMetaMath.FoundationsIV.Transport.HolonomyMemoryRepair
