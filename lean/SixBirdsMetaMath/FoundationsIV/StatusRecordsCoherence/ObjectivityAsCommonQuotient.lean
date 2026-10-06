import SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-!
F17 Objectivity as Common Quotient.

Objectivity is common quotient visibility: a proposed object is shared across
an access family exactly when it descends through each access quotient, and
equivalently through the declared common quotient.
-/

namespace SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ObjectivityAsCommonQuotient

open SixBirdsMetaMath.FoundationsIV.Transport.DescentRepair

/-- A proposed object/readout is visible to one access quotient. -/
def AccessVisible {H Q R : Type} (q : H → Q) (r : H → R) : Prop :=
  Descends q (fun h : H => h) r

/-- The access-specific objectivity defect: an access fiber split by `r`. -/
def AccessObjectivityDefect {H Q R : Type} (q : H → Q) (r : H → R) :
    (H × H) → Prop :=
  splitPairObstruction q (fun h : H => h) r

/-- No access-specific objectivity defect is present. -/
def AccessObjectivityDefectEmpty {H Q R : Type} (q : H → Q) (r : H → R) :
    Prop :=
  ObstructionEmpty (AccessObjectivityDefect q r)

/-- A proposed object/readout is common across every access in the family. -/
def CommonAcrossAccesses {I H R : Type} {Q : I → Type}
    (q : (i : I) → H → Q i) (r : H → R) : Prop :=
  ∀ i : I, AccessVisible (q i) r

/-- A declared common quotient is visible to every participating access. -/
def CommonQuotientVisible {I H P : Type} {Q : I → Type}
    (q : (i : I) → H → Q i) (p : H → P) : Prop :=
  CommonAcrossAccesses q p

/-- Universal property of the declared common quotient: exactly the readouts
common to every access are those factoring through `p`. -/
def CommonQuotientUniversal {I H P : Type} {Q : I → Type}
    (q : (i : I) → H → Q i) (p : H → P) : Prop :=
  ∀ {R : Type} (r : H → R), CommonAcrossAccesses q r ↔
    Descends p (fun h : H => h) r

/-- The public/common quotient is split by a proposed object. -/
def PublicToObjectDefect {H P R : Type} (p : H → P) (r : H → R) :
    (H × H) → Prop :=
  splitPairObstruction p (fun h : H => h) r

/-- The proposed object forgets a distinction of the public/common quotient. -/
def ObjectToPublicDefect {H P R : Type} (r : H → R) (p : H → P) :
    (H × H) → Prop :=
  splitPairObstruction r (fun h : H => h) p

/-- The proposed object descends through the public/common quotient. -/
def PublicDeterminesObject {H P R : Type} (p : H → P) (r : H → R) : Prop :=
  Descends p (fun h : H => h) r

/-- The proposed object determines the public/common quotient. -/
def ObjectDeterminesPublic {H P R : Type} (r : H → R) (p : H → P) : Prop :=
  Descends r (fun h : H => h) p

/-- Pooled access is a new joint instrument, not the public common quotient. -/
def pooledAccess {H QA QB : Type} (qA : H → QA) (qB : H → QB) :
    H → QA × QB :=
  fun h => (qA h, qB h)

/-- Canonical strict-extension style repair that carries both public quotient
and proposed object. -/
def objectiveExtension {H P R : Type} (p : H → P) (r : H → R) : H → P × R :=
  fun h => (p h, r h)

/-- The extension retains the public/common quotient. -/
def RetainsPublicQuotient {H P R : Type} (p : H → P) (extension : H → R) :
    Prop :=
  Descends extension (fun h : H => h) p

/-- The extension carries the proposed object. -/
def CarriesObject {H E R : Type} (extension : H → E) (r : H → R) : Prop :=
  Descends extension (fun h : H => h) r

/-- Four quotient-comparison statuses for a proposed object against the public
common quotient. -/
inductive ObjectivityStatus where
  | exactCommonQuotient
  | coarseObjectiveObject
  | privateOverrefinement
  | incomparableObjectClaim
deriving DecidableEq

/-- Meaning of each objectivity status. -/
def ObjectivityStatusHolds {H P R : Type} (p : H → P) (r : H → R) :
    ObjectivityStatus → Prop
  | ObjectivityStatus.exactCommonQuotient =>
      PublicDeterminesObject p r ∧ ObjectDeterminesPublic r p
  | ObjectivityStatus.coarseObjectiveObject =>
      PublicDeterminesObject p r ∧ ¬ ObjectDeterminesPublic r p
  | ObjectivityStatus.privateOverrefinement =>
      ¬ PublicDeterminesObject p r ∧ ObjectDeterminesPublic r p
  | ObjectivityStatus.incomparableObjectClaim =>
      ¬ PublicDeterminesObject p r ∧ ¬ ObjectDeterminesPublic r p

/-- Exactly one public/object comparison status applies. -/
def ExactlyOneObjectivityStatus {H P R : Type} (p : H → P) (r : H → R) :
    Prop :=
  ∃ status : ObjectivityStatus,
    ObjectivityStatusHolds p r status ∧
      ∀ other : ObjectivityStatus,
        ObjectivityStatusHolds p r other → other = status

/-- Dynamic objectivity: continuation descends between common quotients. -/
def DynamicallyObjective {H H' P P' : Type} (p : H → P) (p' : H' → P')
    (T : H → H') : Prop :=
  Descends p T p'

/-- The dynamic objectivity transport defect. -/
def DynamicObjectivityDefect {H H' P P' : Type} (p : H → P) (p' : H' → P')
    (T : H → H') : (H × H) → Prop :=
  splitPairObstruction p T p'

/-- Access visibility is equivalent to absence of the access objectivity defect. -/
theorem access_visible_iff_no_defect {H Q R : Type} (q : H → Q) (r : H → R)
    (hq : Function.Surjective q) :
    AccessVisible q r ↔ AccessObjectivityDefectEmpty q r :=
  descent_repair_normal_form q (fun h : H => h) r hq

/-- Public determination of the object is equivalent to no public-to-object
defect. -/
theorem public_determines_object_iff_no_defect {H P R : Type} (p : H → P)
    (r : H → R) (hp : Function.Surjective p) :
    PublicDeterminesObject p r ↔ ObstructionEmpty (PublicToObjectDefect p r) :=
  descent_repair_normal_form p (fun h : H => h) r hp

/-- Object determination of the public quotient is equivalent to no
object-to-public defect. -/
theorem object_determines_public_iff_no_defect {H P R : Type} (r : H → R)
    (p : H → P) (hr : Function.Surjective r) :
    ObjectDeterminesPublic r p ↔ ObstructionEmpty (ObjectToPublicDefect r p) :=
  descent_repair_normal_form r (fun h : H => h) p hr

/-- The declared common quotient is visible to every access. -/
theorem common_quotient_visible {I H P : Type} {Q : I → Type}
    (q : (i : I) → H → Q i) (p : H → P) :
    CommonQuotientUniversal q p → CommonQuotientVisible q p := by
  intro huniversal
  have hp_descends : Descends p (fun h : H => h) p := by
    refine ⟨id, ?_⟩
    funext h
    rfl
  exact (huniversal p).2 hp_descends

/-- Common objectivity is equivalent to all access-specific defects being empty. -/
theorem common_across_iff_all_access_defects_empty {I H R : Type} {Q : I → Type}
    (q : (i : I) → H → Q i) (r : H → R)
    (hq : ∀ i : I, Function.Surjective (q i)) :
    CommonAcrossAccesses q r ↔
      ∀ i : I, AccessObjectivityDefectEmpty (q i) r := by
  constructor
  · intro hcommon i
    exact (access_visible_iff_no_defect (q i) r (hq i)).1 (hcommon i)
  · intro hdefects i
    exact (access_visible_iff_no_defect (q i) r (hq i)).2 (hdefects i)

/-- The canonical public/object extension retains the public quotient. -/
theorem objective_extension_retains_public {H P R : Type} (p : H → P)
    (r : H → R) :
    RetainsPublicQuotient p (objectiveExtension p r) := by
  refine ⟨Prod.fst, ?_⟩
  funext h
  rfl

/-- The canonical public/object extension carries the proposed object. -/
theorem objective_extension_carries_object {H P R : Type} (p : H → P)
    (r : H → R) :
    CarriesObject (objectiveExtension p r) r := by
  refine ⟨Prod.snd, ?_⟩
  funext h
  rfl

/-- Dynamic objectivity is exactly absence of its transport defect. -/
theorem dynamic_objectivity_iff_no_defect {H H' P P' : Type} (p : H → P)
    (p' : H' → P') (T : H → H') (hp : Function.Surjective p) :
    DynamicallyObjective p p' T ↔ ObstructionEmpty (DynamicObjectivityDefect p p' T) :=
  descent_repair_normal_form p T p' hp

/-- The two public/object factorization bits classify a proposed object. -/
theorem objectivity_status_partition {H P R : Type} (p : H → P) (r : H → R) :
    ExactlyOneObjectivityStatus p r := by
  classical
  by_cases hpub : PublicDeterminesObject p r
  · by_cases hobj : ObjectDeterminesPublic r p
    · refine ⟨ObjectivityStatus.exactCommonQuotient, ⟨hpub, hobj⟩, ?_⟩
      intro other hother
      cases other with
      | exactCommonQuotient => rfl
      | coarseObjectiveObject => exact False.elim (hother.2 hobj)
      | privateOverrefinement => exact False.elim (hother.1 hpub)
      | incomparableObjectClaim => exact False.elim (hother.1 hpub)
    · refine ⟨ObjectivityStatus.coarseObjectiveObject, ⟨hpub, hobj⟩, ?_⟩
      intro other hother
      cases other with
      | exactCommonQuotient => exact False.elim (hobj hother.2)
      | coarseObjectiveObject => rfl
      | privateOverrefinement => exact False.elim (hother.1 hpub)
      | incomparableObjectClaim => exact False.elim (hother.1 hpub)
  · by_cases hobj : ObjectDeterminesPublic r p
    · refine ⟨ObjectivityStatus.privateOverrefinement, ⟨hpub, hobj⟩, ?_⟩
      intro other hother
      cases other with
      | exactCommonQuotient => exact False.elim (hpub hother.1)
      | coarseObjectiveObject => exact False.elim (hpub hother.1)
      | privateOverrefinement => rfl
      | incomparableObjectClaim => exact False.elim (hother.2 hobj)
    · refine ⟨ObjectivityStatus.incomparableObjectClaim, ⟨hpub, hobj⟩, ?_⟩
      intro other hother
      cases other with
      | exactCommonQuotient => exact False.elim (hpub hother.1)
      | coarseObjectiveObject => exact False.elim (hpub hother.1)
      | privateOverrefinement => exact False.elim (hobj hother.2)
      | incomparableObjectClaim => rfl

/--
Objectivity as Common Quotient Normal Form. Given a declared common quotient
`p` satisfying the common-quotient universal property, a readout `r` is
objective across the access family iff it factors through `p`, equivalently iff
all access-specific split-pair defects are empty. The proposed object also has
exactly one public/object quotient-comparison status, and transport persistence
is governed by the same descent obstruction.
-/
theorem objectivity_as_common_quotient {I H R P : Type} {Q : I → Type}
    (q : (i : I) → H → Q i) (p : H → P) (r : H → R)
    (hq : ∀ i : I, Function.Surjective (q i))
    (hp : Function.Surjective p)
    (huniversal : CommonQuotientUniversal q p) :
    (CommonAcrossAccesses q r ↔ PublicDeterminesObject p r) ∧
      (CommonAcrossAccesses q r ↔
        ∀ i : I, AccessObjectivityDefectEmpty (q i) r) ∧
        (PublicDeterminesObject p r ↔
          ObstructionEmpty (PublicToObjectDefect p r)) ∧
          CommonQuotientVisible q p ∧
            RetainsPublicQuotient p (objectiveExtension p r) ∧
              CarriesObject (objectiveExtension p r) r ∧
                ExactlyOneObjectivityStatus p r := by
  exact ⟨huniversal r,
    common_across_iff_all_access_defects_empty q r hq,
    public_determines_object_iff_no_defect p r hp,
    common_quotient_visible q p huniversal,
    objective_extension_retains_public p r,
    objective_extension_carries_object p r,
    objectivity_status_partition p r⟩

/-- Paper-facing F17, proved from the universal property and quotient lemmas
without an audit record containing the conclusions as fields. -/
theorem paper_objectivity_from_common_quotient_universal
    {I H R P : Type} {Q : I → Type}
    (q : (i : I) → H → Q i) (p : H → P) (r : H → R)
    (hq : ∀ i : I, Function.Surjective (q i))
    (hp : Function.Surjective p)
    (huniversal : CommonQuotientUniversal q p) :
    (CommonAcrossAccesses q r ↔ PublicDeterminesObject p r) ∧
      (CommonAcrossAccesses q r ↔
        ∀ i : I, AccessObjectivityDefectEmpty (q i) r) ∧
        (PublicDeterminesObject p r ↔
          ObstructionEmpty (PublicToObjectDefect p r)) ∧
          CommonQuotientVisible q p ∧
            RetainsPublicQuotient p (objectiveExtension p r) ∧
              CarriesObject (objectiveExtension p r) r ∧
                ExactlyOneObjectivityStatus p r := by
  exact ⟨huniversal r,
    common_across_iff_all_access_defects_empty q r hq,
    public_determines_object_iff_no_defect p r hp,
    common_quotient_visible q p huniversal,
    objective_extension_retains_public p r,
    objective_extension_carries_object p r,
    objectivity_status_partition p r⟩

/-- The two factorization clauses in F17 yield the common-quotient universal
property. The quantified readout codomain ranges over `Type`. -/
theorem common_quotient_universal_of_factorization_minimality
    {I H P : Type} {Q : I → Type}
    (q : (i : I) → H → Q i) (p : H → P)
    (hfac : ∀ i, Descends (q i) (fun h : H => h) p)
    (hmin : ∀ {S : Type} (s : H → S),
      (∀ i, Descends (q i) (fun h : H => h) s) →
        Descends p (fun h : H => h) s) :
    CommonQuotientUniversal q p := by
  intro S s
  constructor
  · exact hmin s
  · rintro ⟨sbar, hs⟩ i
    rcases hfac i with ⟨pbar, hp⟩
    refine ⟨sbar ∘ pbar, ?_⟩
    funext h
    calc
      (sbar ∘ pbar) ((q i) h) = sbar (p h) :=
        congrArg sbar (congrFun hp h)
      _ = s h := congrFun hs h

/-- F17 from the factorization and minimality hypotheses stated in the paper. -/
theorem paper_objectivity_from_factorization_minimality
    {I H R P : Type} {Q : I → Type}
    (q : (i : I) → H → Q i) (p : H → P) (r : H → R)
    (hq : ∀ i : I, Function.Surjective (q i))
    (hp : Function.Surjective p)
    (hfac : ∀ i, Descends (q i) (fun h : H => h) p)
    (hmin : ∀ {S : Type} (s : H → S),
      (∀ i, Descends (q i) (fun h : H => h) s) →
        Descends p (fun h : H => h) s) :
    (CommonAcrossAccesses q r ↔ PublicDeterminesObject p r) ∧
      (CommonAcrossAccesses q r ↔
        ∀ i : I, AccessObjectivityDefectEmpty (q i) r) ∧
        (PublicDeterminesObject p r ↔
          ObstructionEmpty (PublicToObjectDefect p r)) ∧
          CommonQuotientVisible q p ∧
            RetainsPublicQuotient p (objectiveExtension p r) ∧
              CarriesObject (objectiveExtension p r) r ∧
                ExactlyOneObjectivityStatus p r := by
  exact paper_objectivity_from_common_quotient_universal q p r hq hp
    (common_quotient_universal_of_factorization_minimality q p hfac hmin)

end SixBirdsMetaMath.FoundationsIV.StatusRecordsCoherence.ObjectivityAsCommonQuotient
