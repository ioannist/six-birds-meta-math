import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.NS.Carrier
import SixBirdsMetaMath.NS.PDEImports
import SixBirdsMetaMath.Xi.AdequacyResidual

open SixBirdsMetaMath.Main.LegalQuotient
open SixBirdsMetaMath.Xi.AdequacyResidual

namespace SixBirdsMetaMath.NS.Cascade

/-!
NS paper §4 "The physical-native adequacy cascade".

- `def:ns:source-admission-ledger` — `Ω_src = Ω_tr + Ω_pr + Ω_visc + Ω_tail + Ω_str`
  as a `structure` carrying the five positive components on the
  dissolving response space `Z_J`.
- `thm:ns:source-admission-recurrence` (T4) — the Loewner-inequality
  recurrence
  `Ξ_{t+h} ≼ C_old · 𝒯_h · Ξ_t · 𝒯_h^* + Ω_tr + Ω_pr + Ω_visc + Ω_tail + Ω_str`,
  conditional on records `R_3` (null-mode legality) and `R_4`
  (source-admission acceptance). Status: `partial` /
  `mechanized-fragment` under elevated PDE hypotheses.
-/

/--
Source-admission ledger.

The total source record `Ω_src` is decomposed into five declared
positive operators on the dissolving response space `Z_J`: transport,
pressure, viscosity, high-frequency tail, and vortex stretching.  The
`*_paid` fields are placeholders for the imported PDE record or
downstream no-go that pays each component.
-/
structure sourceAdmissionLedger (z : Nat) where
  Omega_src : Mat z z
  Omega_tr : Mat z z
  Omega_pr : Mat z z
  Omega_visc : Mat z z
  Omega_tail : Mat z z
  Omega_str : Mat z z
  source_decomposition :
    Omega_src =
      matAdd (matAdd (matAdd (matAdd Omega_tr Omega_pr) Omega_visc) Omega_tail) Omega_str
  Omega_tr_positive : PositiveSemidefinite Omega_tr
  Omega_pr_positive : PositiveSemidefinite Omega_pr
  Omega_visc_positive : PositiveSemidefinite Omega_visc
  Omega_tail_positive : PositiveSemidefinite Omega_tail
  Omega_str_positive : PositiveSemidefinite Omega_str
  transport_paid : Prop
  pressure_paid : Prop
  viscosity_paid : Prop
  tail_paid : Prop
  stretching_paid : Prop
  transport_paid_holds : transport_paid
  pressure_paid_holds : pressure_paid
  viscosity_paid_holds : viscosity_paid
  tail_paid_holds : tail_paid
  stretching_paid_holds : stretching_paid

/--
Source-admission recurrence.

Under R3 null-mode legality and R4 source-admission acceptance, the
next BG-window residual is Loewner-dominated by the transported old
residual plus the five source-admission ledger components.
-/
theorem sourceAdmissionRecurrence {e e_next y z : Nat}
    (C_J_t : Mat e e) (C_J_t_h : Mat e_next e_next)
    (D_BG_J_t : Mat z e) (D_BG_J_t_h : Mat z e_next)
    (Lphys_J_t : Mat y e) (Lphys_J_t_h : Mat y e_next)
    (KLL_t : Mat y y) (KLL_t_h : Mat y y)
    (T_h : Mat z z) (C_old h : Rat)
    (ledger : sourceAdmissionLedger z)
    (_h_step_positive : 0 < h)
    (_h_C_old_nonneg : 0 ≤ C_old)
    (_R3_current : NullLegal C_J_t Lphys_J_t ∧ NullLegal C_J_t D_BG_J_t)
    (_R3_next : NullLegal C_J_t_h Lphys_J_t_h ∧ NullLegal C_J_t_h D_BG_J_t_h)
    (R4_acceptance :
      loewnerLE
        (adequacyResidual C_J_t_h Lphys_J_t_h D_BG_J_t_h KLL_t_h)
        (matAdd
          (matScale C_old
            (matMul
              (matMul T_h (adequacyResidual C_J_t Lphys_J_t D_BG_J_t KLL_t))
              (transpose T_h)))
          ledger.Omega_src)) :
    loewnerLE
      (adequacyResidual C_J_t_h Lphys_J_t_h D_BG_J_t_h KLL_t_h)
      (matAdd
        (matScale C_old
          (matMul
            (matMul T_h (adequacyResidual C_J_t Lphys_J_t D_BG_J_t KLL_t))
            (transpose T_h)))
        (matAdd
          (matAdd (matAdd (matAdd ledger.Omega_tr ledger.Omega_pr) ledger.Omega_visc)
            ledger.Omega_tail)
          ledger.Omega_str)) := by
  have hAccepted := R4_acceptance
  rw [ledger.source_decomposition] at hAccepted
  exact hAccepted

end SixBirdsMetaMath.NS.Cascade
