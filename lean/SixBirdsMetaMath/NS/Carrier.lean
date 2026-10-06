import SixBirdsMetaMath.Terminology
import SixBirdsMetaMath.Main.LegalQuotient
import SixBirdsMetaMath.Xi.AdequacyResidual

open SixBirdsMetaMath.Main.LegalQuotient
open SixBirdsMetaMath.Xi.AdequacyResidual

namespace SixBirdsMetaMath.NS.Carrier

/-!
NS paper §1 "The Navier--Stokes carrier and the BG/BKM dissolving readout".

This module hosts the NS-specific carrier data and probe families:
- `def:ns:bg-readout`   — Bradshaw--Grujić dissolving readout `D^{BG}`
- `def:ns:physical-native-probes` — linear Fourier/Sobolev probes `L^{phys}`
- `def:ns:bg-package`   — BG-windowed exact package `Γ_j`
- `def:ns:null-mode-legal-ns` — null-mode legality on the NS carrier

Each declaration is paper-grounded against `paper/ns/needles_ns.tex`
§1 statements; the audit energy `C_{J,t}` and frequency-window data are
declared as `structure` fields, not as project-local axioms.
Per `paper/notation_and_terminology.md` §4.1, `D^{BG}` and `L^{phys}`
are explicit NS-instantiations of the abstract `D` and `L` from the
Xi paper; the Lean naming uses `bgReadout`, `physicalNativeProbes`,
etc., to make the NS instantiation explicit while preserving the
abstract-side decl names in the Xi modules.
-/

/--
Bradshaw--Grujic frequency-window dissolving readout `D^{BG}`.

For every BG stage `J` and time `t`, the carrier has dimension
`carrierDim J t`, audit `C_J_t J t`, and response space dimension
`responseDim J` at window scale `lambdaJ J t`.  The chosen readout is a
fixed matrix family `E_{J,t} -> Z_J` whose rows only see the BG window
`P_{J(t)}`; algebraically this is the right-support condition
`D^{BG}_{J,t} = D^{BG}_{J,t} P_{J(t)}`.
-/
def bgReadout
    (carrierDim : Nat → Nat → Nat) (responseDim : Nat → Nat)
    (_C_J_t : (J t : Nat) → Mat (carrierDim J t) (carrierDim J t))
    (_lambdaJ : Nat → Nat → Rat)
    (bgWindow : (J t : Nat) → Mat (carrierDim J t) (carrierDim J t)) : Type :=
  { D_BG : (J t : Nat) → Mat (responseDim J) (carrierDim J t) //
      ∀ J t, D_BG J t = matMul (D_BG J t) (bgWindow J t) }

/--
Physical-native probe family `L^{phys}`.

The data are a finite matrix family `E_{J,t} -> Y_{J,t}`.  Each output
component is tagged as either a Littlewood--Paley shell probe or a
Sobolev/Bessel-potential component probe, and its native currency
recovers the stage energy and enstrophy budgets at BG-window resolution.
-/
def physicalNativeProbes
    (carrierDim nativeDim : Nat → Nat → Nat)
    (C_J_t : (J t : Nat) → Mat (carrierDim J t) (carrierDim J t))
    (lpShellProbe besselPotentialProbe :
      (J t : Nat) → Fin (nativeDim J t) → Prop)
    (energyBudget enstrophyBudget :
      (J t : Nat) → Mat (nativeDim J t) (nativeDim J t)) : Type :=
  { Lphys : (J t : Nat) → Mat (nativeDim J t) (carrierDim J t) //
      (∀ J t k, lpShellProbe J t k ∨ besselPotentialProbe J t k) ∧
        (∀ J t,
          blockCurrencyLL (C_J_t J t) (Lphys J t) =
            matAdd (energyBudget J t) (enstrophyBudget J t)) }

/--
BG-windowed exact package `Γ_j`.

The package selects admissible BG-window probes, preserves the
divergence-free carrier structure, preserves the audited energy and
response information, and carries the frequency-doubling staging
`lambda_{j+1} = 2 lambda_j`.
-/
def bgPackage
    (stageDim packageDim : Nat → Nat) (lambda : Nat → Rat)
    (admissibleBGWindow preservesDivergenceFree exactEnergy exactResponse :
      (j : Nat) → Mat (stageDim j) (packageDim j) → Prop) : Type :=
  { Gamma_j : (j : Nat) → Mat (stageDim j) (packageDim j) //
      (∀ j, admissibleBGWindow j (Gamma_j j)) ∧
        (∀ j, preservesDivergenceFree j (Gamma_j j)) ∧
          (∀ j, exactEnergy j (Gamma_j j) ∧ exactResponse j (Gamma_j j)) ∧
            (∀ j, lambda (j + 1) = 2 * lambda j) }

/--
Null-mode legality on the NS carrier.

At every stage and time, both the physical-native family `L^{phys}` and
the BG dissolving family `D^{BG}` vanish on the kernel of the audit
`C_{J,t}`.  This is the concrete finite-dimensional form of clean
descent to the legal energy quotient `E_{J,t} / Ker C_{J,t}`.
-/
def nullModeLegalNS
    (carrierDim nativeDim : Nat → Nat → Nat) (responseDim : Nat → Nat)
    (C_J_t : (J t : Nat) → Mat (carrierDim J t) (carrierDim J t))
    (Lphys : (J t : Nat) → Mat (nativeDim J t) (carrierDim J t))
    (D_BG : (J t : Nat) → Mat (responseDim J) (carrierDim J t)) : Prop :=
  ∀ J t,
    NullLegal (C_J_t J t) (Lphys J t) ∧
      NullLegal (C_J_t J t) (D_BG J t)

end SixBirdsMetaMath.NS.Carrier
