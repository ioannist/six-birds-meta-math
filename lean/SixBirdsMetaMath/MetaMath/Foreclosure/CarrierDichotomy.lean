import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.Main.LegalQuotient
import SixBirdsMetaMath.Xi.AdequacyResidual

open SixBirdsMetaMath.Main.LegalQuotient
open SixBirdsMetaMath.Xi.AdequacyResidual

namespace SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy

/-!
T1 Carrier Dichotomy.

This module states the T1 dichotomy against the existing finite-matrix
`adequacyResidual` surface from the Xi axis. Classification is supplied
as an explicit schema hypothesis; this module asserts no project axiom.
-/

/-- Claim codes are not identified merely because their interpretations agree. -/
structure ClaimLanguage where
  Claim : Type u
  interp : Claim → Prop

/--
A typed primary carrier `C = (E, L, D, C)` aimed at a target conjecture.

The abstract carrier space `E` is represented by the finite dimension `e`;
`L` and `D` are the native-probe and dissolving readout matrices, and
`audit` is the carrier audit energy.  The residual `Xi_C(D | L)` is supplied
by the canonical Xi-axis `adequacyResidual` definition.
-/
structure TypedPrimaryCarrier (language : ClaimLanguage.{u}) where
  e : Nat
  y : Nat
  z : Nat
  audit : Mat e e
  nativeProbes : Mat y e
  dissolvingReadout : Mat z e
  KLLdagger : Mat y y
  aimedAt : language.Claim → Prop
  typedContextDiscipline : Prop
  sameLevelAuditStatus : SixBirdsMetaMath.F3ClaimStatus
  noAcceptedBridgeToTarget : language.Claim → Prop
  structurallyBridgeIncompatible : language.Claim → Prop
  cascadeReducesToMatrixFamily : Prop
  inheritedRecordsDecideMatrixFamily : Prop
  matrixFamilyDecisionEquivalentToTarget : language.Claim → Prop

variable {language : ClaimLanguage.{u}}

/-- The carrier's adequacy residual `Xi_C(D | L)`. -/
def carrierResidual (C : TypedPrimaryCarrier language) : Mat C.z C.z :=
  adequacyResidual C.audit C.nativeProbes C.dissolvingReadout C.KLLdagger

/-- Closure of the carrier residual, written in the paper as `Xi_C = 0`. -/
def residualClosureZero (C : TypedPrimaryCarrier language) : Prop :=
  carrierResidual C = zeroMat C.z C.z

/-- Closure of `Xi_C` is logically equivalent to a conjecture. -/
def residualClosureEquivalent (C : TypedPrimaryCarrier language) (X : language.Claim) : Prop :=
  residualClosureZero C ↔ language.interp X

/-- `X`-equivalence: closure of `Xi_C` is logically equivalent to `X`. -/
def xEquivalent (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop :=
  residualClosureEquivalent C X

/--
State 1: non-`X`-equivalent.

There is a distinct conjecture `X'` such that closure of `Xi_C` is logically
equivalent to `X'`, with `X' ≠ X`.
-/
def nonXEquivalent (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop :=
  ∃ X' : language.Claim, residualClosureEquivalent C X' ∧ X' ≠ X

/-- Native closure is open-pending exactly when `X'` is not in the accepted-imports base. -/
def openPending (acceptedImportsBase : language.Claim → Prop) (X' : language.Claim) : Prop :=
  ¬ acceptedImportsBase X'

/--
The non-`X` branch's native-closure verdict: either `X'` is in the accepted
imports base and `Xi_C = 0` closes natively, or `X'` is open-pending.
-/
def NativeClosureOutcome
    (acceptedImportsBase : language.Claim → Prop) (C : TypedPrimaryCarrier language) (X' : language.Claim) : Prop :=
  (acceptedImportsBase X' ∧ residualClosureZero C) ∨
    openPending acceptedImportsBase X'

/-- Foundations III same-level self-audit returns the two T1 target-equivalence statuses. -/
def sameLevelSelfAuditFailure (C : TypedPrimaryCarrier language) : Prop :=
  C.sameLevelAuditStatus = SixBirdsIII.ClaimStatus.outsideScope ∨
    C.sameLevelAuditStatus = SixBirdsIII.ClaimStatus.undefinedCircular

/--
State 2: CRE-TE.  The residual closure is `X` itself and the carrier-level
same-level audit returns `outsideScope` or `undefinedCircular`.
-/
def creTE (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop :=
  xEquivalent X C ∧ sameLevelSelfAuditFailure C

/--
State 3: CRE-BF.  The carrier has no accepted audited bridge to the target
primary carrier, either ledger-relatively or by structural type mismatch.
-/
def creBF (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop :=
  C.noAcceptedBridgeToTarget X ∨ C.structurallyBridgeIncompatible X

/--
State 4: CRE-CTMT.  The cascade terminates at a carrier-native
matrix-element family not decided by inherited records and not equivalent
to the target conjecture.
-/
def creCTMT (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop :=
  C.cascadeReducesToMatrixFamily ∧
    ¬ C.inheritedRecordsDecideMatrixFamily ∧
      ¬ C.matrixFamilyDecisionEquivalentToTarget X

/-- Exactly one of three foreclosure modes holds. -/
def ExactlyOneOfThree (A B C : Prop) : Prop :=
  (A ∧ ¬ B ∧ ¬ C) ∨ (B ∧ ¬ A ∧ ¬ C) ∨ (C ∧ ¬ A ∧ ¬ B)

/-- Coverage guards are supplied interpretations, never fixed opaque constants. -/
def CoverageContext
    (guard : language.Claim → TypedPrimaryCarrier language → Prop)
    (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop :=
  guard X C

/-- Per-instance classification schema; its content is supplied explicitly. -/
def CarrierClassificationSchema
    (X : language.Claim) (C : TypedPrimaryCarrier language) : Prop :=
  xEquivalent X C →
    ExactlyOneOfThree (creTE X C) (creBF X C) (creCTMT X C)

/-- Conditional dichotomy. Aim, discipline and coverage guards are omitted:
the proof uses only import soundness and the classification instance. -/
theorem carrier_dichotomy
    (acceptedImportsBase : language.Claim → Prop)
    (h_imports_sound : ∀ c, acceptedImportsBase c → language.interp c)
    (X : language.Claim) (C : TypedPrimaryCarrier language)
    (hclassification : CarrierClassificationSchema X C) :
    (nonXEquivalent X C →
      ∃ X' : language.Claim,
        residualClosureEquivalent C X' ∧ X' ≠ X ∧
          NativeClosureOutcome acceptedImportsBase C X') ∧
    (xEquivalent X C →
      ExactlyOneOfThree (creTE X C) (creBF X C) (creCTMT X C)) := by
  refine ⟨?_, hclassification⟩
  intro hnon
  rcases hnon with ⟨X', hclosureEquiv, hdistinct⟩
  refine ⟨X', hclosureEquiv, hdistinct, ?_⟩
  classical
  by_cases hbase : acceptedImportsBase X'
  · exact Or.inl ⟨hbase, hclosureEquiv.mpr (h_imports_sound X' hbase)⟩
  · exact Or.inr hbase

/-- Two distinct codes with the same true interpretation. -/
def twoTrueClaims : ClaimLanguage.{0} := ⟨Bool, fun _ => True⟩

/-- This sound base accepts exactly the false code, not the true code. -/
def selectiveTrueBase : twoTrueClaims.Claim → Prop := fun c => c = false

/-- A sound code-indexed base can distinguish two true claims. -/
theorem sound_base_noncollapse :
    (∀ c, selectiveTrueBase c → twoTrueClaims.interp c) ∧
    twoTrueClaims.interp false ∧ twoTrueClaims.interp true ∧
    selectiveTrueBase false ∧ ¬ selectiveTrueBase true := by
  refine ⟨fun _ _ => True.intro, True.intro, True.intro, rfl, ?_⟩
  intro h
  cases h

/-- A concrete one-dimensional zero-residual carrier for the two-code language. -/
def closedTwoClaimCarrier : TypedPrimaryCarrier twoTrueClaims where
  e := 1
  y := 1
  z := 1
  audit := zeroMat 1 1
  nativeProbes := zeroMat 1 1
  dissolvingReadout := zeroMat 1 1
  KLLdagger := zeroMat 1 1
  aimedAt := fun _ => True
  typedContextDiscipline := True
  sameLevelAuditStatus := SixBirdsIII.ClaimStatus.outsideScope
  noAcceptedBridgeToTarget := fun _ => False
  structurallyBridgeIncompatible := fun _ => False
  cascadeReducesToMatrixFamily := False
  inheritedRecordsDecideMatrixFamily := False
  matrixFamilyDecisionEquivalentToTarget := fun _ => False

/-- The witness uses the actual finite-matrix residual definition. -/
theorem closedTwoClaimCarrier_zero : residualClosureZero closedTwoClaimCarrier := by
  simp [residualClosureZero, carrierResidual, closedTwoClaimCarrier,
    adequacyResidual, blockCurrencyDD, blockCurrencyDL, blockCurrencyLD,
    matMul_zero_left, matSub_self_eq_zero]

/-- The concrete carrier satisfies the classification schema for either code. -/
theorem closedTwoClaimCarrier_classification (X : twoTrueClaims.Claim) :
    CarrierClassificationSchema X closedTwoClaimCarrier := by
  intro hx
  refine Or.inl ⟨⟨hx, Or.inl rfl⟩, ?_, ?_⟩
  · intro hbf
    cases hbf with
    | inl h => exact h
    | inr h => exact h
  · intro hctmt
    exact hctmt.1

/-- Code non-equivalence and interpreted X-equivalence can hold simultaneously. -/
theorem nonXEquivalent_and_xEquivalent :
    nonXEquivalent true closedTwoClaimCarrier ∧
      xEquivalent true closedTwoClaimCarrier := by
  have hzero := closedTwoClaimCarrier_zero
  have heq (c : twoTrueClaims.Claim) : residualClosureEquivalent closedTwoClaimCarrier c :=
    ⟨fun _ => True.intro, fun _ => hzero⟩
  refine ⟨⟨false, heq false, ?_⟩, heq true⟩
  intro h
  cases h

end SixBirdsMetaMath.MetaMath.Foreclosure.CarrierDichotomy
