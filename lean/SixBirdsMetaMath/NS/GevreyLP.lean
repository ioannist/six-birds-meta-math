import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.NS.Carrier
import SixBirdsMetaMath.NS.PDEImports
import SixBirdsMetaMath.Xi.AdequacyResidual

open SixBirdsMetaMath.Main.LegalQuotient

namespace SixBirdsMetaMath.NS.GevreyLP

/-!
NS paper §6 "Gevrey radius-window branch and LP-transport rescue".

- `def:ns:gevrey-probes` — Gevrey-normalized derivative probes
  `M̃_{m,J,t} = (ρ^m / (C_G^m m!)) ∇^m P_{J(t)}`. Note `C_G` is the
  Gevrey constant, **distinct** from the legal-quotient `C_0` of the
  Main paper (see `paper/notation_and_terminology.md` §4.3).
- `def:ns:lp-transport` — LP-transport stage operator
  `S_j : L²(P_j) → H^{-s}` with `‖S_j‖² ≃ 2^{-2sj}`.
- `thm:ns:gevrey-dominance` (T6) — dominance constant
  `A_m^G = λ_J^{q-ε} m!/σ_J^m`, optimized
  `inf_m A_m^G ≲ λ_J^{q-ε}√(1+σ_J) e^{-cσ_J}`. Status:
  `schema_theorem` / `narrowed_surrogate` (uses `inf`, `sqrt`, `exp`,
  `log`, asymptotic `≲` — kept under elevated hypotheses since the
  needles Lean infrastructure is rational-finite-matrix).
- `thm:ns:lp-transport-rescue` (T8) — transported budget
  `B̃_j(s) ≃ C_B 2^{2(p-s)j}(1+μ√L_j)e^{-2cμ√L_j}`; `s ≥ p` gives
  eventual contraction. Status: `partial` / `projection_packaged`.
- `thm:ns:smooth-data-half-log-transfer` (T9) — transfer of half-log
  analyticity to BG-compatible stages via the Sobolev/Besov embedding
  import. Status: `partial` / `projection_packaged`.
-/

/--
Gevrey-normalized derivative probes.

The record carries the family
`M_tilde m = (rho^m / (C_G^m m!)) * derivativeWindow m`, indexed by
`m >= 0`, together with the half-log/R7 legality certificate making
each member a lawful native probe on the BG-windowed carrier.
-/
structure gevreyProbes (e y : Nat) where
  rho : Rat
  gevreyConstant : Rat
  gevreyConstant_positive : 0 < gevreyConstant
  derivativeWindow : Nat → Mat y e
  M_tilde : Nat → Mat y e
  factorialWeight : Nat → Rat
  lawfulNativeProbe : Nat → Prop
  normalized_formula :
    ∀ m,
      M_tilde m =
        matScale
          (rho ^ m / (gevreyConstant ^ m * factorialWeight m))
          (derivativeWindow m)
  lawful_under_R7 : ∀ m, lawfulNativeProbe m

/--
Littlewood--Paley transport stage operator.

The record carries the stage map `LPtr : L^2(P_j) -> H^{-s}`, the
condition `s >= q - eps`, a norm-bound constant, and the BG-compatible
doubling-sequence/norm-bound certificates.
-/
structure lpTransport (domainDim responseDim : Nat) where
  stage : Nat
  LPtr : Mat responseDim domainDim
  s : Rat
  q : Rat
  eps : Rat
  normBoundConstant : Rat
  s_ge_q_minus_eps : q - eps ≤ s
  normBoundConstant_positive : 0 < normBoundConstant
  bgCompatibleDoublingSequence : Prop
  normSquaredAsymptotic : Prop
  bgCompatibleDoublingSequence_holds : bgCompatibleDoublingSequence
  normSquaredAsymptotic_holds : normSquaredAsymptotic

/--
Gevrey dominance formula.

The exact closed form is recorded with `lambdaPower_q_minus_eps`
standing for `lambda_J(t)^(q-eps)`.  The optimized bound and the
radius-window gate are exposed as analytic certificates consumed by
the theorem.
-/
theorem gevreyDominance
    (lambdaPower_q_minus_eps sigmaJ c : Rat)
    (A_m_G factorialWeight : Nat → Rat)
    (optimizedBound radiusWindowGate : Prop)
    (c_positive : 0 < c)
    (closedForm :
      ∀ m, A_m_G m =
        lambdaPower_q_minus_eps * factorialWeight m / (sigmaJ ^ m))
    (optimization :
      (∀ m, A_m_G m =
        lambdaPower_q_minus_eps * factorialWeight m / (sigmaJ ^ m)) →
        0 < c → optimizedBound)
    (gate :
      optimizedBound → radiusWindowGate) :
    (∀ m, A_m_G m =
        lambdaPower_q_minus_eps * factorialWeight m / (sigmaJ ^ m)) ∧
      optimizedBound ∧ radiusWindowGate := by
  have hOptimized : optimizedBound := optimization closedForm c_positive
  exact ⟨closedForm, hOptimized, gate hOptimized⟩

/--
LP-transport rescue.

Under the R6 transport record and the exponent condition `s >= p`, the
transported staged-budget formula, ratio contraction, divergent
contraction ledger, and summability are returned as the rescue package.
-/
theorem lpTransportRescue {domainDim responseDim : Nat}
    (R6 : lpTransport domainDim responseDim)
    (p : Rat)
    (transportedBudgetFormula ratioContraction etaSumDiverges transportedResidualSummable : Prop)
    (p_eq_q_minus_eps : p = R6.q - R6.eps)
    (formula_holds : transportedBudgetFormula)
    (ratio_from_transport :
      R6.s ≥ p → transportedBudgetFormula → ratioContraction)
    (eta_from_ratio :
      ratioContraction → etaSumDiverges)
    (summable_from_eta :
      ratioContraction → etaSumDiverges → transportedResidualSummable) :
    transportedBudgetFormula ∧ ratioContraction ∧
      etaSumDiverges ∧ transportedResidualSummable := by
  have hSgeP : R6.s ≥ p := by
    rw [p_eq_q_minus_eps]
    exact R6.s_ge_q_minus_eps
  have hRatio : ratioContraction := ratio_from_transport hSgeP formula_holds
  have hEta : etaSumDiverges := eta_from_ratio hRatio
  exact ⟨formula_holds, hRatio, hEta, summable_from_eta hRatio hEta⟩

/--
Smooth-data half-log transfer.

The Sobolev/Besov embedding import lifts smooth restart data into the
joint hypothesis space required by the half-log analyticity import; the
Wang/Foias--Temam/Herbst--Skibsted record then supplies the radius
bound on BG-compatible stages.
-/
theorem smoothDataHalfLogTransfer {RestartData JointRegularity Stage : Type}
    (embedding : SixBirdsMetaMath.NS.PDEImports.sobolevBesovEmbeddingImport
      RestartData JointRegularity)
    (halfLog : SixBirdsMetaMath.NS.PDEImports.wangHalfLogImport
      JointRegularity Stage)
    (restart : RestartData) (stage : Stage)
    (hSmooth : embedding.smoothSobolevRestart restart)
    (hJointSobolev :
      halfLog.inSobolevGamma0 (embedding.lift restart hSmooth))
    (hJointBesov :
      halfLog.inBesovMinusEps (embedding.lift restart hSmooth))
    (hBGStage :
      halfLog.bgCompatibleStage (embedding.lift restart hSmooth) stage)
    (allSixAudited : Prop)
    (hAllSixAudited : allSixAudited) :
    embedding.jointBesovCompatibleRegularity restart (embedding.lift restart hSmooth) ∧
      halfLog.halfLogLowerBound (embedding.lift restart hSmooth) stage ∧
        allSixAudited := by
  refine ⟨embedding.lift_regularity restart hSmooth, ?_, hAllSixAudited⟩
  exact halfLog.radius_bound (embedding.lift restart hSmooth) stage
    hJointSobolev hJointBesov hBGStage

end SixBirdsMetaMath.NS.GevreyLP
