import SixBirdsMetaMath.RHNavierPvNP.ConstantProbeComparison

/-!
A limited obstruction to promoting the shared constant probe into an
RH-to-SAT state transport. It rules out a map that both preserves that
probe on every state and sends a reflection-symmetric RH displacement
to a satisfiable SAT indicator. It does not rule out other transports,
other probes, or a shared sourced closure theorem.
-/

noncomputable section
open scoped InnerProductSpace
namespace SixBirdsMetaMath.RHNavierPvNP.ProbePreservingTransportNoGo

open SixBirdsMetaMath.RHNavierPvNP.ConstantProbeComparison
open SixBirdsMetaMath.RHNavierPvNP.SATXiCurrency
open SixBirdsDualityConfinement.RH.ClassicalZeroLedger
open SixBirdsDualityConfinement.RH.FiniteZeroWindows
open SixBirdsDualityConfinement.RH.ActualInvolution
open SixBirdsHiddenness.PvNP.CNFSemantics

/-- A satisfiable SAT indicator cannot be the image of a reflected RH
displacement under a map that preserves the shared constant-probe
readout. No linearity or continuity assumption is needed for this
specific obstruction. -/
theorem no_probe_preserving_transport_to_sat
    (m : NontrivialZero → ℕ)
    (hm : ∀ ρ, m (J_zero ρ) = m ρ)
    (W : Finset NontrivialZero) (hW : JReflectedWindow W)
    {n : Nat} (φ : Formula n)
    (hSAT : (SixBirdsHiddenness.PvNP.StandardSATBridge.toExternalFormula φ).encode ∈
      SAT.L_SAT) :
    ¬ ∃ F : EuclideanSpace ℝ {ρ // ρ ∈ W} →
          EuclideanSpace ℝ (Assignment n),
        (∀ v, finiteConstantProbe (Assignment n) (F v) =
          finiteConstantProbe {ρ // ρ ∈ W} v) ∧
        F (displacementVector m W) = satState φ := by
  rintro ⟨F, hprobe, himage⟩
  have hread := rh_sat_constant_probe_readouts m hm W hW φ
  have hpositive := hread.2.mpr hSAT
  have hzero : finiteConstantProbe (Assignment n) (satState φ) = 0 := by
    rw [← himage, hprobe]
    exact hread.1
  exact (ne_of_gt hpositive) hzero

end SixBirdsMetaMath.RHNavierPvNP.ProbePreservingTransportNoGo
