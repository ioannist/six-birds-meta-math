import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.NS.Carrier

namespace SixBirdsMetaMath.NS.PDEImports

/-!
NS paper §2 "Literature imports".

This module hosts the proof-carrying `structure` realizations of the
paper-grounded PDE imports:
- `def:ns:bkm-import`   — Beale--Kato--Majda continuation criterion
- `def:ns:bg-import`    — Bradshaw--Grujić frequency-window criterion
- `def:ns:kato-import`  — Kato local well-posedness for `H^{γ_0}` data with `γ_0 > 5/2`
- `def:ns:wang-halflog-import` — half-log analyticity radius (Foias--Temam / Herbst--Skibsted / Wang)
- `def:ns:lp-bcd-import` — Littlewood--Paley / Bony--Chemin--Danchin calculus
- `def:ns:sobolev-besov-embedding-import` — `H^{γ_0} ↪ Ḃ^{-ε}_{∞,∞}` embedding chain

Per `paper/notation_and_terminology.md` §4.6 and §8, each import is
realized as a `structure` whose fields capture the result's conclusion
under its named hypotheses. **No project-local `axiom`, no `opaque`,
no `sorry`**: the structures have constructors that consume the
hypotheses and expose the conclusion as fields. Downstream NS theorems
take these structures as hypotheses.
-/

/--
Beale--Kato--Majda continuation import.

The record packages the BKM continuation criterion as data: for a
three-dimensional incompressible NS strong solution `u`, smooth-data
regularity and Leray--Hopf background hypotheses, finite vorticity
integral up to `T`, and `T` lying before the maximal lifespan imply
that the solution continues beyond `T`.
-/
structure bkmImport (Solution : Type) where
  strongSolution : Solution → Prop
  smoothDataRegularity : Solution → Prop
  lerayHopfBackground : Solution → Prop
  lifespanInOpenFiniteInfinity : Solution → Prop
  beforeMaximalLifespan : Solution → Rat → Prop
  vorticityIntegralFinite : Solution → Rat → Prop
  continuesBeyond : Solution → Rat → Prop
  continuation :
    ∀ u T,
      strongSolution u →
        smoothDataRegularity u →
          lerayHopfBackground u →
            lifespanInOpenFiniteInfinity u →
              beforeMaximalLifespan u T →
                vorticityIntegralFinite u T →
                  continuesBeyond u T

/--
Bradshaw--Grujic frequency-window regularity import.

The record packages the BG criterion as data: under named hypotheses on
the BG package `Γ_j`, a uniform bound for `D^{BG}_{J,t}` on a doubling
sequence of stages with `lambda_{j+1} = 2 lambda_j` yields the global
lifespan conclusion `T_max = infinity`.
-/
structure bgImport
    (Solution : Type) (stageDim packageDim : Nat → Nat)
    (lambda : Nat → Rat)
    (admissibleBGWindow preservesDivergenceFree exactEnergy exactResponse :
      (j : Nat) →
        SixBirdsMetaMath.Main.LegalQuotient.Mat (stageDim j) (packageDim j) → Prop) where
  Gamma_j :
    SixBirdsMetaMath.NS.Carrier.bgPackage stageDim packageDim lambda
      admissibleBGWindow preservesDivergenceFree exactEnergy exactResponse
  strongSolution : Solution → Prop
  bgPackageHypotheses : Prop
  dbgUniformlyBoundedOnDoublingStages : Solution → Prop
  TmaxInfinity : Solution → Prop
  regularity :
    ∀ u,
      strongSolution u →
        bgPackageHypotheses →
          dbgUniformlyBoundedOnDoublingStages u →
            TmaxInfinity u

/--
Kato local well-posedness import.

For each divergence-free datum `u0` in `H^{gamma0}` with
`gamma0 > 5/2`, the record provides `Tmax u0`, a strong solution on
`[0,Tmax)`, continuity into `H^{gamma0}`, and uniqueness of that strong
solution.
-/
structure katoImport (InitialData Solution Lifespan : Type) where
  sobolevExponent : Rat
  sobolevExponent_gt_five_halves : 5 < 2 * sobolevExponent
  divergenceFree : InitialData → Prop
  inSobolevGamma0 : InitialData → Prop
  lifespanInOpenFiniteInfinity : Lifespan → Prop
  Tmax : InitialData → Lifespan
  strongSolutionOn : InitialData → Lifespan → Solution → Prop
  continuousIntoSobolev : InitialData → Lifespan → Solution → Prop
  solution :
    ∀ u0,
      divergenceFree u0 → inSobolevGamma0 u0 → Solution
  Tmax_valid :
    ∀ u0 (_hDiv : divergenceFree u0) (_hSob : inSobolevGamma0 u0),
      lifespanInOpenFiniteInfinity (Tmax u0)
  solution_regular :
    ∀ u0 (hDiv : divergenceFree u0) (hSob : inSobolevGamma0 u0),
      strongSolutionOn u0 (Tmax u0) (solution u0 hDiv hSob) ∧
        continuousIntoSobolev u0 (Tmax u0) (solution u0 hDiv hSob)
  uniqueness :
    ∀ u0 (hDiv : divergenceFree u0) (hSob : inSobolevGamma0 u0) v,
      strongSolutionOn u0 (Tmax u0) v →
        continuousIntoSobolev u0 (Tmax u0) v →
          v = solution u0 hDiv hSob

/--
Half-log analyticity import.

For restart data in `H^{gamma0} ∩ B^{-eps}_{infty,infty}` with
`gamma0 > 3/2 - eps`, the record carries the BG-compatible stage
radius condition as an arbitrary supplied predicate `halfLogLowerBound`.
This retained record contains no radius inequality or logarithm definition.
The maintained Needles record distinguishes the squared half-log condition
from the stronger full-log gate.
-/
structure wangHalfLogImport (RestartData Stage : Type) where
  sobolevExponent : Rat
  eps : Rat
  exponentCondition : 3 < 2 * (sobolevExponent + eps)
  inSobolevGamma0 : RestartData → Prop
  inBesovMinusEps : RestartData → Prop
  bgCompatibleStage : RestartData → Stage → Prop
  lambdaJ : RestartData → Stage → Rat
  rho : RestartData → Stage → Rat
  halfLogLowerBound : RestartData → Stage → Prop
  radius_bound :
    ∀ restart stage,
      inSobolevGamma0 restart →
        inBesovMinusEps restart →
          bgCompatibleStage restart stage →
            halfLogLowerBound restart stage

/--
Littlewood--Paley / Bony--Chemin--Danchin calculus import.

The record carries the operator-norm bounds, commutator estimates, and
shell-orthogonality identities used by the LP transport map and
half-log staged residuals.
-/
structure lpBcdImport (Stage Operator Shell : Type) where
  lpTransportMap : Stage → Operator
  halfLogResidualOperator : Stage → Operator
  operatorNormBound : Operator → Prop
  commutatorEstimate : Operator → Prop
  shellOrthogonality : Shell → Shell → Prop
  lpTransportNorm :
    ∀ stage, operatorNormBound (lpTransportMap stage)
  lpTransportCommutator :
    ∀ stage, commutatorEstimate (lpTransportMap stage)
  halfLogResidualNorm :
    ∀ stage, operatorNormBound (halfLogResidualOperator stage)
  halfLogResidualCommutator :
    ∀ stage, commutatorEstimate (halfLogResidualOperator stage)
  shellOrthogonalityRecord :
    ∀ shell₁ shell₂, shellOrthogonality shell₁ shell₂

/--
Sobolev/Besov embedding chain import.

For admissible `eps > 0` and `gamma0 > 3/2`, the record lifts smooth
`H^{gamma0}` restart data into the joint Sobolev/Besov hypothesis space
used by the half-log analyticity import.
-/
structure sobolevBesovEmbeddingImport (RestartData JointRegularity : Type) where
  sobolevExponent : Rat
  eps : Rat
  sobolevExponent_gt_three_halves : 3 < 2 * sobolevExponent
  eps_admissible : 0 < eps
  smoothSobolevRestart : RestartData → Prop
  jointBesovCompatibleRegularity : RestartData → JointRegularity → Prop
  lift :
    ∀ restart, smoothSobolevRestart restart → JointRegularity
  lift_regularity :
    ∀ restart (hSmooth : smoothSobolevRestart restart),
      jointBesovCompatibleRegularity restart (lift restart hSmooth)

end SixBirdsMetaMath.NS.PDEImports
