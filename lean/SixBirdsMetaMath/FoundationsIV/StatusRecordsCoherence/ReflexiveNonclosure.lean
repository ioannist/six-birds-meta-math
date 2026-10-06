/-!
F21 Reflexive Nonclosure.

Scoped lower-level audit can be accepted, but complete same-layer
self-certification cannot be accepted without a level shift.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ReflexiveNonclosure

/-- Statuses for reflexive audit claims. -/
inductive ReflexiveAuditStatus where
  | accepted
  | outsideScope
  | undefinedCircular
  | objectLevelAudit
  | metaLayerCertified
  | blocked
deriving DecidableEq

/-- A same-layer audit policy with the source qualification preserved:
`ScopedLowerAudit` claims are ordinary lower-scope audits, not complete
self-soundness claims. -/
structure SameLayerAuditPolicy (Claim : Type) where
  InScope : Claim → Prop
  CompleteSelfSoundness : Claim → Prop
  ScopedLowerAudit : Claim → Prop
  SameLayerCycle : Claim → Prop
  StatusOf : Claim → ReflexiveAuditStatus
  scoped_lower_not_complete :
    ∀ claim : Claim, ScopedLowerAudit claim → ¬ CompleteSelfSoundness claim
  outside_scope_rule :
    ∀ claim : Claim, ¬ InScope claim → StatusOf claim = ReflexiveAuditStatus.outsideScope
  circular_rule :
    ∀ claim : Claim,
      InScope claim → SameLayerCycle claim →
        StatusOf claim = ReflexiveAuditStatus.undefinedCircular
  complete_self_cycle :
    ∀ claim : Claim,
      CompleteSelfSoundness claim → InScope claim → SameLayerCycle claim

/-- A same-layer complete soundness claim is accepted. This is the forbidden
case for complete self-audit. -/
def SameLayerSelfCertification {Claim : Type} (policy : SameLayerAuditPolicy Claim)
    (claim : Claim) : Prop :=
  policy.CompleteSelfSoundness claim ∧
    policy.StatusOf claim = ReflexiveAuditStatus.accepted

/-- The complete self-soundness claim is blocked at the same layer. -/
def SelfCertificationBlocked {Claim : Type} (policy : SameLayerAuditPolicy Claim)
    (claim : Claim) : Prop :=
  policy.CompleteSelfSoundness claim →
    policy.StatusOf claim ≠ ReflexiveAuditStatus.accepted

/-- The qualified allowed case: a scoped lower-level audit that is accepted as
an object/lower-scope claim. -/
def AcceptedScopedLowerAudit {Claim : Type} (policy : SameLayerAuditPolicy Claim)
    (claim : Claim) : Prop :=
  policy.ScopedLowerAudit claim ∧
    policy.StatusOf claim = ReflexiveAuditStatus.accepted

/-- A claim is marked outside scope by the same-layer classifier. -/
def OutsideScopeVerdict {Claim : Type} (policy : SameLayerAuditPolicy Claim)
    (claim : Claim) : Prop :=
  ¬ policy.InScope claim ∧
    policy.StatusOf claim = ReflexiveAuditStatus.outsideScope

/-- A claim is marked undefined/circular by the same-layer classifier. -/
def UndefinedCircularVerdict {Claim : Type} (policy : SameLayerAuditPolicy Claim)
    (claim : Claim) : Prop :=
  policy.InScope claim ∧ policy.SameLayerCycle claim ∧
    policy.StatusOf claim = ReflexiveAuditStatus.undefinedCircular

/-- A higher audit layer may certify a lower claim without certifying itself. -/
structure MetaLayerAudit (LowerClaim MetaClaim : Type) where
  audits : MetaClaim → LowerClaim → Prop
  acceptedByMeta : MetaClaim → Prop
  metaSelfSoundness : MetaClaim → Prop
  meta_does_not_self_certify :
    ∀ metaClaim : MetaClaim, metaSelfSoundness metaClaim → ¬ acceptedByMeta metaClaim

/-- A lower claim has a meta-layer certificate. -/
def HasMetaLayerCertificate {LowerClaim MetaClaim : Type}
    (metaAudit : MetaLayerAudit LowerClaim MetaClaim) (claim : LowerClaim) : Prop :=
  ∃ metaClaim : MetaClaim,
    metaAudit.audits metaClaim claim ∧ metaAudit.acceptedByMeta metaClaim

/-- Same-layer self-audit dependency defect. -/
def SameLayerCycleDefect {Claim : Type} (policy : SameLayerAuditPolicy Claim) :
    Claim → Prop :=
  fun claim => policy.CompleteSelfSoundness claim ∧
    policy.InScope claim ∧ policy.SameLayerCycle claim

/-- No same-layer cycle defect for a claim. -/
def SameLayerCycleDefectAbsent {Claim : Type} (policy : SameLayerAuditPolicy Claim)
    (claim : Claim) : Prop :=
  ¬ SameLayerCycleDefect policy claim

/-- Broader F21 status vocabulary. -/
inductive ReflexiveNonclosureStatus where
  | scopedLowerAuditAccepted
  | outsideScope
  | undefinedCircular
  | metaLayerCertified
  | finiteRotatingAudit
  | finalSelfCertificationBlocked
  | reflexiveOverread
deriving DecidableEq

/-- Meaning assignment for the F21 status vocabulary. -/
def ReflexiveNonclosureStatusHolds (scopedStatus outside circular metaStatus finite blocked
    overread : Prop) : ReflexiveNonclosureStatus → Prop
  | ReflexiveNonclosureStatus.scopedLowerAuditAccepted => scopedStatus
  | ReflexiveNonclosureStatus.outsideScope => outside
  | ReflexiveNonclosureStatus.undefinedCircular => circular
  | ReflexiveNonclosureStatus.metaLayerCertified => metaStatus
  | ReflexiveNonclosureStatus.finiteRotatingAudit => finite
  | ReflexiveNonclosureStatus.finalSelfCertificationBlocked => blocked
  | ReflexiveNonclosureStatus.reflexiveOverread => overread

/-- If a complete self-soundness claim is out of scope, it is not accepted. -/
theorem out_of_scope_self_soundness_not_accepted {Claim : Type}
    (policy : SameLayerAuditPolicy Claim) (claim : Claim) :
    policy.CompleteSelfSoundness claim →
      ¬ policy.InScope claim →
        policy.StatusOf claim ≠ ReflexiveAuditStatus.accepted := by
  intro _hself hout haccepted
  have hstatus : policy.StatusOf claim = ReflexiveAuditStatus.outsideScope :=
    policy.outside_scope_rule claim hout
  rw [haccepted] at hstatus
  cases hstatus

/-- If a complete self-soundness claim is in scope, it has a same-layer cycle
and is therefore not accepted. -/
theorem in_scope_self_soundness_circular_not_accepted {Claim : Type}
    (policy : SameLayerAuditPolicy Claim) (claim : Claim) :
    policy.CompleteSelfSoundness claim →
      policy.InScope claim →
        policy.StatusOf claim ≠ ReflexiveAuditStatus.accepted := by
  intro hself hin haccepted
  have hcycle : policy.SameLayerCycle claim :=
    policy.complete_self_cycle claim hself hin
  have hstatus : policy.StatusOf claim = ReflexiveAuditStatus.undefinedCircular :=
    policy.circular_rule claim hin hcycle
  rw [haccepted] at hstatus
  cases hstatus

/-- The allowed qualification: accepted scoped lower-level audit is not a
complete self-soundness certification. -/
theorem accepted_scoped_lower_audit_not_complete {Claim : Type}
    (policy : SameLayerAuditPolicy Claim) (claim : Claim) :
    AcceptedScopedLowerAudit policy claim →
      ¬ policy.CompleteSelfSoundness claim := by
  intro hscoped
  exact policy.scoped_lower_not_complete claim hscoped.1

/-- Meta-layer certificates do not imply the meta layer certifies its own
complete soundness. -/
theorem meta_certificate_not_meta_self_certification {LowerClaim MetaClaim : Type}
    (metaAudit : MetaLayerAudit LowerClaim MetaClaim) (claim : LowerClaim) :
    HasMetaLayerCertificate metaAudit claim →
      ∃ metaClaim : MetaClaim,
        metaAudit.audits metaClaim claim ∧ metaAudit.acceptedByMeta metaClaim ∧
          ¬ metaAudit.metaSelfSoundness metaClaim := by
  intro hcert
  rcases hcert with ⟨metaClaim, haudits, haccepted⟩
  refine ⟨metaClaim, haudits, haccepted, ?_⟩
  intro hself
  exact metaAudit.meta_does_not_self_certify metaClaim hself haccepted

/--
Reflexive Nonclosure Normal Form. A complete same-layer self-soundness claim is
never accepted: if out of scope it receives `outsideScope`, and if in scope it
is `undefinedCircular` by the same-layer cycle rule. The important
qualification is preserved: scoped lower-level audits may be accepted, but they
are not complete same-layer self-certifications. Meta-layer certificates audit
lower claims without certifying the meta layer itself.
-/
theorem reflexive_nonclosure {Claim MetaClaim : Type}
    (policy : SameLayerAuditPolicy Claim)
    (metaAudit : MetaLayerAudit Claim MetaClaim) :
    (∀ claim : Claim, SelfCertificationBlocked policy claim) ∧
      (∀ claim : Claim,
        AcceptedScopedLowerAudit policy claim →
          ¬ policy.CompleteSelfSoundness claim) ∧
        (∀ claim : Claim,
          HasMetaLayerCertificate metaAudit claim →
            ∃ metaClaim : MetaClaim,
              metaAudit.audits metaClaim claim ∧ metaAudit.acceptedByMeta metaClaim ∧
                ¬ metaAudit.metaSelfSoundness metaClaim) ∧
          (∀ claim : Claim,
            policy.CompleteSelfSoundness claim →
              OutsideScopeVerdict policy claim ∨
                UndefinedCircularVerdict policy claim) := by
  constructor
  · intro claim hself
    classical
    by_cases hin : policy.InScope claim
    · exact in_scope_self_soundness_circular_not_accepted policy claim hself hin
    · exact out_of_scope_self_soundness_not_accepted policy claim hself hin
  · constructor
    · intro claim hscoped
      exact accepted_scoped_lower_audit_not_complete policy claim hscoped
    · constructor
      · intro claim hcert
        exact meta_certificate_not_meta_self_certification metaAudit claim hcert
      · intro claim hself
        classical
        by_cases hin : policy.InScope claim
        · right
          have hcycle : policy.SameLayerCycle claim :=
            policy.complete_self_cycle claim hself hin
          exact ⟨hin, hcycle, policy.circular_rule claim hin hcycle⟩
        · left
          exact ⟨hin, policy.outside_scope_rule claim hin⟩

/-- Paper F21 with the three audit verdicts explicitly declared pairwise
distinct. The inductive status type already ensures these inequalities. -/
theorem reflexive_nonclosure_distinct {Claim MetaClaim : Type}
    (policy : SameLayerAuditPolicy Claim)
    (metaAudit : MetaLayerAudit Claim MetaClaim)
    (_hdistinct :
      ReflexiveAuditStatus.accepted ≠ ReflexiveAuditStatus.outsideScope ∧
      ReflexiveAuditStatus.accepted ≠ ReflexiveAuditStatus.undefinedCircular ∧
      ReflexiveAuditStatus.outsideScope ≠ ReflexiveAuditStatus.undefinedCircular) :
    (∀ claim : Claim, SelfCertificationBlocked policy claim) ∧
    (∀ claim : Claim,
      AcceptedScopedLowerAudit policy claim →
        ¬ policy.CompleteSelfSoundness claim) ∧
    (∀ claim : Claim,
      HasMetaLayerCertificate metaAudit claim →
        ∃ metaClaim : MetaClaim,
          metaAudit.audits metaClaim claim ∧ metaAudit.acceptedByMeta metaClaim ∧
            ¬ metaAudit.metaSelfSoundness metaClaim) ∧
    (∀ claim : Claim,
      policy.CompleteSelfSoundness claim →
        OutsideScopeVerdict policy claim ∨
          UndefinedCircularVerdict policy claim) :=
  reflexive_nonclosure policy metaAudit

/-- Paper F21 with the four same-layer rules and the meta-layer rule stated
as hypotheses, rather than stored in policy records. -/
theorem paper_reflexive_nonclosure_explicit_rules
    {Claim MetaClaim Status : Type}
    (inScope complete lowerAudit cycle : Claim → Prop)
    (status : Claim → Status)
    (accepted outsideScope undefinedCircular : Status)
    (audits : MetaClaim → Claim → Prop)
    (acceptedMeta metaSelfSound : MetaClaim → Prop)
    (hdistinct : accepted ≠ outsideScope ∧
      accepted ≠ undefinedCircular ∧ outsideScope ≠ undefinedCircular)
    (h1 : ∀ c, lowerAudit c → ¬ complete c)
    (h2 : ∀ c, ¬ inScope c → status c = outsideScope)
    (h3 : ∀ c, inScope c → cycle c → status c = undefinedCircular)
    (h4 : ∀ c, complete c → inScope c → cycle c)
    (hmeta : ∀ m, metaSelfSound m → ¬ acceptedMeta m) :
    (accepted ≠ outsideScope ∧
      accepted ≠ undefinedCircular ∧ outsideScope ≠ undefinedCircular) ∧
    (∀ c, complete c → status c ≠ accepted) ∧
    (∀ c, lowerAudit c ∧ status c = accepted → ¬ complete c) ∧
    (∀ c, (∃ m, audits m c ∧ acceptedMeta m) →
      ∃ m, audits m c ∧ acceptedMeta m ∧ ¬ metaSelfSound m) ∧
    (∀ c, complete c →
      (¬ inScope c ∧ status c = outsideScope) ∨
      (inScope c ∧ cycle c ∧ status c = undefinedCircular)) := by
  refine ⟨hdistinct, ?_, ?_, ?_, ?_⟩
  · intro c hcomplete haccepted
    by_cases hin : inScope c
    · have hcycle := h4 c hcomplete hin
      have hcircular := h3 c hin hcycle
      exact hdistinct.2.1 (haccepted.symm.trans hcircular)
    · have houtside := h2 c hin
      exact hdistinct.1 (haccepted.symm.trans houtside)
  · intro c hscoped
    exact h1 c hscoped.1
  · rintro c ⟨m, haudit, haccepted⟩
    refine ⟨m, haudit, haccepted, ?_⟩
    intro hself
    exact hmeta m hself haccepted
  · intro c hcomplete
    by_cases hin : inScope c
    · exact Or.inr ⟨hin, h4 c hcomplete hin,
        h3 c hin (h4 c hcomplete hin)⟩
    · exact Or.inl ⟨hin, h2 c hin⟩

/-- Two claims show that the complete-self-cycle rule is needed to block
same-layer self-certification. -/
theorem reflexive_nonclosure_rule_four_sharp :
    ∃ (inScope complete lowerAudit cycle : Bool → Prop)
      (status : Bool → ReflexiveAuditStatus),
      (∀ c, lowerAudit c → ¬ complete c) ∧
      (∀ c, ¬ inScope c → status c = .outsideScope) ∧
      (∀ c, inScope c → cycle c → status c = .undefinedCircular) ∧
      ¬ (∀ c, complete c → inScope c → cycle c) ∧
      ¬ (∀ c, complete c → status c ≠ .accepted) := by
  refine ⟨(fun _ => True), (fun c => c = true), (fun c => c = false),
    (fun _ => False), (fun _ => .accepted), ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc hcomplete
    cases c <;> simp_all
  · intro c h
    exact False.elim (h trivial)
  · intro c _ h
    exact False.elim h
  · intro h
    exact h true rfl trivial
  · intro h
    exact h true rfl rfl

/-- The direct F21 conclusion and a two-claim sharpness witness for rule four. -/
theorem paper_reflexive_nonclosure_with_sharpness
    {Claim MetaClaim Status : Type}
    (inScope complete lowerAudit cycle : Claim → Prop)
    (status : Claim → Status)
    (accepted outsideScope undefinedCircular : Status)
    (audits : MetaClaim → Claim → Prop)
    (acceptedMeta metaSelfSound : MetaClaim → Prop)
    (hdistinct : accepted ≠ outsideScope ∧
      accepted ≠ undefinedCircular ∧ outsideScope ≠ undefinedCircular)
    (h1 : ∀ c, lowerAudit c → ¬ complete c)
    (h2 : ∀ c, ¬ inScope c → status c = outsideScope)
    (h3 : ∀ c, inScope c → cycle c → status c = undefinedCircular)
    (h4 : ∀ c, complete c → inScope c → cycle c)
    (hmeta : ∀ m, metaSelfSound m → ¬ acceptedMeta m) :
    ((accepted ≠ outsideScope ∧
      accepted ≠ undefinedCircular ∧ outsideScope ≠ undefinedCircular) ∧
    (∀ c, complete c → status c ≠ accepted) ∧
    (∀ c, lowerAudit c ∧ status c = accepted → ¬ complete c) ∧
    (∀ c, (∃ m, audits m c ∧ acceptedMeta m) →
      ∃ m, audits m c ∧ acceptedMeta m ∧ ¬ metaSelfSound m) ∧
    (∀ c, complete c →
      (¬ inScope c ∧ status c = outsideScope) ∨
      (inScope c ∧ cycle c ∧ status c = undefinedCircular))) ∧
    (∃ (scope full lower loop : Bool → Prop)
      (st : Bool → ReflexiveAuditStatus),
      (∀ c, lower c → ¬ full c) ∧
      (∀ c, ¬ scope c → st c = .outsideScope) ∧
      (∀ c, scope c → loop c → st c = .undefinedCircular) ∧
      ¬ (∀ c, full c → scope c → loop c) ∧
      ¬ (∀ c, full c → st c ≠ .accepted)) := by
  exact ⟨paper_reflexive_nonclosure_explicit_rules inScope complete lowerAudit
    cycle status accepted outsideScope undefinedCircular audits acceptedMeta
    metaSelfSound hdistinct h1 h2 h3 h4 hmeta,
    reflexive_nonclosure_rule_four_sharp⟩

/-- A one-claim policy shows that rule two is needed: a complete
self-soundness claim outside scope can otherwise be accepted, even while
rules one, three, and four hold. -/
theorem reflexive_nonclosure_rule_two_sharp :
    ∃ (scope full lower loop : Unit → Prop)
      (st : Unit → ReflexiveAuditStatus),
      (∀ c, lower c → ¬ full c) ∧
      ¬ (∀ c, ¬ scope c → st c = .outsideScope) ∧
      (∀ c, scope c → loop c → st c = .undefinedCircular) ∧
      (∀ c, full c → scope c → loop c) ∧
      (∃ c, full c ∧ ¬ scope c ∧ st c = .accepted) ∧
      ¬ (∀ c, full c → st c ≠ .accepted) := by
  refine ⟨(fun _ => False), (fun _ => True), (fun _ => False),
    (fun _ => False), (fun _ => .accepted), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c h
    exact False.elim h
  · intro h
    have hstatus := h () (by trivial)
    cases hstatus
  · intro c h
    exact False.elim h
  · intro c _ h
    exact False.elim h
  · exact ⟨(), trivial, (by trivial), rfl⟩
  · intro h
    exact h () trivial rfl

/-- F21 with the direct audit conclusion and finite sharpness witnesses for
both the outside-scope rule and the complete-self-cycle rule. -/
theorem paper_reflexive_nonclosure_with_sharpness_rules_2_4
    {Claim MetaClaim Status : Type}
    (inScope complete lowerAudit cycle : Claim → Prop)
    (status : Claim → Status)
    (accepted outsideScope undefinedCircular : Status)
    (audits : MetaClaim → Claim → Prop)
    (acceptedMeta metaSelfSound : MetaClaim → Prop)
    (hdistinct : accepted ≠ outsideScope ∧
      accepted ≠ undefinedCircular ∧ outsideScope ≠ undefinedCircular)
    (h1 : ∀ c, lowerAudit c → ¬ complete c)
    (h2 : ∀ c, ¬ inScope c → status c = outsideScope)
    (h3 : ∀ c, inScope c → cycle c → status c = undefinedCircular)
    (h4 : ∀ c, complete c → inScope c → cycle c)
    (hmeta : ∀ m, metaSelfSound m → ¬ acceptedMeta m) :
    (((accepted ≠ outsideScope ∧
      accepted ≠ undefinedCircular ∧ outsideScope ≠ undefinedCircular) ∧
    (∀ c, complete c → status c ≠ accepted) ∧
    (∀ c, lowerAudit c ∧ status c = accepted → ¬ complete c) ∧
    (∀ c, (∃ m, audits m c ∧ acceptedMeta m) →
      ∃ m, audits m c ∧ acceptedMeta m ∧ ¬ metaSelfSound m) ∧
    (∀ c, complete c →
      (¬ inScope c ∧ status c = outsideScope) ∨
      (inScope c ∧ cycle c ∧ status c = undefinedCircular))) ∧
    (∃ (scope full lower loop : Bool → Prop)
      (st : Bool → ReflexiveAuditStatus),
      (∀ c, lower c → ¬ full c) ∧
      (∀ c, ¬ scope c → st c = .outsideScope) ∧
      (∀ c, scope c → loop c → st c = .undefinedCircular) ∧
      ¬ (∀ c, full c → scope c → loop c) ∧
      ¬ (∀ c, full c → st c ≠ .accepted))) ∧
    (∃ (scope full lower loop : Unit → Prop)
      (st : Unit → ReflexiveAuditStatus),
      (∀ c, lower c → ¬ full c) ∧
      ¬ (∀ c, ¬ scope c → st c = .outsideScope) ∧
      (∀ c, scope c → loop c → st c = .undefinedCircular) ∧
      (∀ c, full c → scope c → loop c) ∧
      (∃ c, full c ∧ ¬ scope c ∧ st c = .accepted) ∧
      ¬ (∀ c, full c → st c ≠ .accepted)) := by
  exact ⟨paper_reflexive_nonclosure_with_sharpness inScope complete lowerAudit
    cycle status accepted outsideScope undefinedCircular audits acceptedMeta
    metaSelfSound hdistinct h1 h2 h3 h4 hmeta,
    reflexive_nonclosure_rule_two_sharp⟩

/-- A one-claim policy shows that rule three is needed even when the claim is
in scope and the other three rules hold. -/
theorem reflexive_nonclosure_rule_three_sharp :
    ∃ (scope full lower loop : Unit → Prop)
      (st : Unit → ReflexiveAuditStatus),
      (∀ c, lower c → ¬ full c) ∧
      (∀ c, ¬ scope c → st c = .outsideScope) ∧
      ¬ (∀ c, scope c → loop c → st c = .undefinedCircular) ∧
      (∀ c, full c → scope c → loop c) ∧
      (∃ c, full c ∧ scope c ∧ loop c ∧ st c = .accepted) ∧
      ¬ (∀ c, full c → st c ≠ .accepted) := by
  refine ⟨(fun _ => True), (fun _ => True), (fun _ => False),
    (fun _ => True), (fun _ => .accepted), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c h
    exact False.elim h
  · intro c h
    exact False.elim (h trivial)
  · intro h
    have hs := h () trivial trivial
    cases hs
  · intro c _ _
    trivial
  · exact ⟨(), trivial, trivial, trivial, rfl⟩
  · intro h
    exact h () trivial rfl

/-- F21 with finite sharpness witnesses for rules two, three, and four. -/
theorem paper_reflexive_nonclosure_with_sharpness_rules_2_3_4
    {Claim MetaClaim Status : Type}
    (inScope complete lowerAudit cycle : Claim → Prop)
    (status : Claim → Status)
    (accepted outsideScope undefinedCircular : Status)
    (audits : MetaClaim → Claim → Prop)
    (acceptedMeta metaSelfSound : MetaClaim → Prop)
    (hdistinct : accepted ≠ outsideScope ∧
      accepted ≠ undefinedCircular ∧ outsideScope ≠ undefinedCircular)
    (h1 : ∀ c, lowerAudit c → ¬ complete c)
    (h2 : ∀ c, ¬ inScope c → status c = outsideScope)
    (h3 : ∀ c, inScope c → cycle c → status c = undefinedCircular)
    (h4 : ∀ c, complete c → inScope c → cycle c)
    (hmeta : ∀ m, metaSelfSound m → ¬ acceptedMeta m) :
    ((((accepted ≠ outsideScope ∧
      accepted ≠ undefinedCircular ∧ outsideScope ≠ undefinedCircular) ∧
    (∀ c, complete c → status c ≠ accepted) ∧
    (∀ c, lowerAudit c ∧ status c = accepted → ¬ complete c) ∧
    (∀ c, (∃ m, audits m c ∧ acceptedMeta m) →
      ∃ m, audits m c ∧ acceptedMeta m ∧ ¬ metaSelfSound m) ∧
    (∀ c, complete c →
      (¬ inScope c ∧ status c = outsideScope) ∨
      (inScope c ∧ cycle c ∧ status c = undefinedCircular))) ∧
    (∃ (scope full lower loop : Bool → Prop)
      (st : Bool → ReflexiveAuditStatus),
      (∀ c, lower c → ¬ full c) ∧
      (∀ c, ¬ scope c → st c = .outsideScope) ∧
      (∀ c, scope c → loop c → st c = .undefinedCircular) ∧
      ¬ (∀ c, full c → scope c → loop c) ∧
      ¬ (∀ c, full c → st c ≠ .accepted))) ∧
    (∃ (scope full lower loop : Unit → Prop)
      (st : Unit → ReflexiveAuditStatus),
      (∀ c, lower c → ¬ full c) ∧
      ¬ (∀ c, ¬ scope c → st c = .outsideScope) ∧
      (∀ c, scope c → loop c → st c = .undefinedCircular) ∧
      (∀ c, full c → scope c → loop c) ∧
      (∃ c, full c ∧ ¬ scope c ∧ st c = .accepted) ∧
      ¬ (∀ c, full c → st c ≠ .accepted))) ∧
    (∃ (scope full lower loop : Unit → Prop)
      (st : Unit → ReflexiveAuditStatus),
      (∀ c, lower c → ¬ full c) ∧
      (∀ c, ¬ scope c → st c = .outsideScope) ∧
      ¬ (∀ c, scope c → loop c → st c = .undefinedCircular) ∧
      (∀ c, full c → scope c → loop c) ∧
      (∃ c, full c ∧ scope c ∧ loop c ∧ st c = .accepted) ∧
      ¬ (∀ c, full c → st c ≠ .accepted)) := by
  exact ⟨paper_reflexive_nonclosure_with_sharpness_rules_2_4 inScope complete
    lowerAudit cycle status accepted outsideScope undefinedCircular audits
    acceptedMeta metaSelfSound hdistinct h1 h2 h3 h4 hmeta,
    reflexive_nonclosure_rule_three_sharp⟩

/-- Rules two through four already block complete claims, including any
accepted lower audit, so the full F21 bundle does not require rule one. -/
theorem paper_reflexive_nonclosure_with_sharpness_rules_2_3_4_without_rule_1
    {Claim MetaClaim Status : Type}
    (inScope complete lowerAudit cycle : Claim → Prop)
    (status : Claim → Status)
    (accepted outsideScope undefinedCircular : Status)
    (audits : MetaClaim → Claim → Prop)
    (acceptedMeta metaSelfSound : MetaClaim → Prop)
    (hdistinct : accepted ≠ outsideScope ∧
      accepted ≠ undefinedCircular ∧ outsideScope ≠ undefinedCircular)
    (h2 : ∀ c, ¬ inScope c → status c = outsideScope)
    (h3 : ∀ c, inScope c → cycle c → status c = undefinedCircular)
    (h4 : ∀ c, complete c → inScope c → cycle c)
    (hmeta : ∀ m, metaSelfSound m → ¬ acceptedMeta m) :
    ((((accepted ≠ outsideScope ∧
      accepted ≠ undefinedCircular ∧ outsideScope ≠ undefinedCircular) ∧
    (∀ c, complete c → status c ≠ accepted) ∧
    (∀ c, lowerAudit c ∧ status c = accepted → ¬ complete c) ∧
    (∀ c, (∃ m, audits m c ∧ acceptedMeta m) →
      ∃ m, audits m c ∧ acceptedMeta m ∧ ¬ metaSelfSound m) ∧
    (∀ c, complete c →
      (¬ inScope c ∧ status c = outsideScope) ∨
      (inScope c ∧ cycle c ∧ status c = undefinedCircular))) ∧
    (∃ (scope full lower loop : Bool → Prop)
      (st : Bool → ReflexiveAuditStatus),
      (∀ c, lower c → ¬ full c) ∧
      (∀ c, ¬ scope c → st c = .outsideScope) ∧
      (∀ c, scope c → loop c → st c = .undefinedCircular) ∧
      ¬ (∀ c, full c → scope c → loop c) ∧
      ¬ (∀ c, full c → st c ≠ .accepted))) ∧
    (∃ (scope full lower loop : Unit → Prop)
      (st : Unit → ReflexiveAuditStatus),
      (∀ c, lower c → ¬ full c) ∧
      ¬ (∀ c, ¬ scope c → st c = .outsideScope) ∧
      (∀ c, scope c → loop c → st c = .undefinedCircular) ∧
      (∀ c, full c → scope c → loop c) ∧
      (∃ c, full c ∧ ¬ scope c ∧ st c = .accepted) ∧
      ¬ (∀ c, full c → st c ≠ .accepted))) ∧
    (∃ (scope full lower loop : Unit → Prop)
      (st : Unit → ReflexiveAuditStatus),
      (∀ c, lower c → ¬ full c) ∧
      (∀ c, ¬ scope c → st c = .outsideScope) ∧
      ¬ (∀ c, scope c → loop c → st c = .undefinedCircular) ∧
      (∀ c, full c → scope c → loop c) ∧
      (∃ c, full c ∧ scope c ∧ loop c ∧ st c = .accepted) ∧
      ¬ (∀ c, full c → st c ≠ .accepted)) := by
  have hblocked : ∀ c, complete c → status c ≠ accepted := by
    intro c hcomplete haccepted
    by_cases hin : inScope c
    · exact hdistinct.2.1 (haccepted.symm.trans (h3 c hin (h4 c hcomplete hin)))
    · exact hdistinct.1 (haccepted.symm.trans (h2 c hin))
  refine ⟨⟨⟨⟨hdistinct, hblocked, ?_, ?_, ?_⟩,
    reflexive_nonclosure_rule_four_sharp⟩,
    reflexive_nonclosure_rule_two_sharp⟩,
    reflexive_nonclosure_rule_three_sharp⟩
  · intro c hscoped hcomplete
    exact hblocked c hcomplete hscoped.2
  · rintro c ⟨m, haudit, haccepted⟩
    exact ⟨m, haudit, haccepted, fun hself => hmeta m hself haccepted⟩
  · intro c hcomplete
    by_cases hin : inScope c
    · exact Or.inr ⟨hin, h4 c hcomplete hin,
        h3 c hin (h4 c hcomplete hin)⟩
    · exact Or.inl ⟨hin, h2 c hin⟩

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ReflexiveNonclosure
