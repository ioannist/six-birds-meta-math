import SixBirdsMetaMath.Main.LayerDissolving

/-!
F6 No-Needles Stability.

This Foundations IV stability law is anchored to the inherited Paper 4
layer-dissolving endpoint theorem. The F-IV statement keeps the structural
spine: native budget plus residual budget plus transported endpoint budget
implies the dissolving endpoint budget, hence no unpriced layer-dissolving
critical pair at the formed stability package.
-/

namespace SixBirdsMetaMath.FoundationsIV.Stability.NoNeedles

open SixBirdsMetaMath.Main.LegalQuotient
open SixBirdsMetaMath.Main.XiInterface
open SixBirdsMetaMath.Xi.AdequacyResidual

/--
No-Needles Stability, anchored to
`SixBirdsMetaMath.Main.LayerDissolving.layerDissolvingMaster`.

The conclusion is the endpoint Loewner budget
`S K^D S^* <= ThetaD`; because `loewnerLE` is defined as absence of a
positive critical-pair witness, this is the formal no-needles endpoint.
-/
theorem no_needles_stability {e y z d : Nat}
    (C : Mat e e) (L : Mat y e) (D : Mat z e)
    (KLLdagger : Mat y y)
    (ThetaY : Mat y y) (OmegaZ : Mat z z) (ThetaD : Mat d d)
    (S : Mat d z)
    (hKLDsym : transpose (blockCurrencyDL C L D) = blockCurrencyLD C L D)
    (hKLLdaggerSym : transpose KLLdagger = KLLdagger)
    (hMPLLD : matMul (matMul (blockCurrencyLL C L) KLLdagger)
      (blockCurrencyLD C L D) = blockCurrencyLD C L D)
    (hKLbound : loewnerLE (blockCurrencyLL C L) ThetaY)
    (hXibound : loewnerLE (adequacyResidual C L D KLLdagger) OmegaZ)
    (hTransport :
      loewnerLE
        (matMul
          (matMul S
            (matAdd
              (matMul
                (matMul (optimalNativeExplanation C L D KLLdagger) ThetaY)
                (transpose (optimalNativeExplanation C L D KLLdagger)))
              OmegaZ))
          (transpose S))
        ThetaD) :
    loewnerLE
      (matMul (matMul S (blockCurrencyDD C D)) (transpose S))
      ThetaD :=
  SixBirdsMetaMath.Main.LayerDissolving.layerDissolvingMaster
    C L D KLLdagger ThetaY OmegaZ ThetaD S
    hKLDsym hKLLdaggerSym hMPLLD hKLbound hXibound hTransport

/-- Schur residual for arbitrary rational currency blocks. -/
def generalBlockResidual {y z : Nat}
    (KLD : Mat y z) (KDL : Mat z y) (KDD : Mat z z)
    (KLLdagger : Mat y y) : Mat z z :=
  matSub KDD (matMul (matMul KDL KLLdagger) KLD)

/-- The native explanation associated with arbitrary currency blocks. -/
def generalBlockNativeExplanation {y z : Nat}
    (KDL : Mat z y) (KLLdagger : Mat y y) : Mat z y :=
  matMul KDL KLLdagger

/-- The block projection and symmetry identities give the Schur decomposition
without any diagonal hypothesis on the underlying currency matrix. -/
theorem general_block_schur_identity {y z : Nat}
    (KLL : Mat y y) (KLD : Mat y z) (KDL : Mat z y)
    (KDD : Mat z z) (KLLdagger : Mat y y)
    (hKLDsym : transpose KDL = KLD)
    (hKLLdaggerSym : transpose KLLdagger = KLLdagger)
    (hMPLLD : matMul (matMul KLL KLLdagger) KLD = KLD) :
    KDD = matAdd
      (matMul (matMul (generalBlockNativeExplanation KDL KLLdagger) KLL)
        (transpose (generalBlockNativeExplanation KDL KLLdagger)))
      (generalBlockResidual KLD KDL KDD KLLdagger) := by
  let Astar := generalBlockNativeExplanation KDL KLLdagger
  let schurTerm := matMul (matMul KDL KLLdagger) KLD
  have hSchur : matMul (matMul Astar KLL) (transpose Astar) = schurTerm := by
    calc
      matMul (matMul Astar KLL) (transpose Astar) =
          matMul (matMul (matMul KDL KLLdagger) KLL)
            (transpose (matMul KDL KLLdagger)) := rfl
      _ = matMul (matMul (matMul KDL KLLdagger) KLL)
            (matMul (transpose KLLdagger) (transpose KDL)) := by
              rw [transpose_matMul]
      _ = matMul (matMul (matMul KDL KLLdagger) KLL)
            (matMul KLLdagger KLD) := by rw [hKLLdaggerSym, hKLDsym]
      _ = matMul (matMul KDL KLLdagger)
            (matMul (matMul KLL KLLdagger) KLD) := by
              rw [matMul_assoc (matMul KDL KLLdagger) KLL
                (matMul KLLdagger KLD), ← matMul_assoc KLL KLLdagger KLD]
      _ = schurTerm := by rw [hMPLLD]
  symm
  calc
    matAdd (matMul (matMul Astar KLL) (transpose Astar))
        (generalBlockResidual KLD KDL KDD KLLdagger) =
        matAdd schurTerm (matSub KDD schurTerm) := by
          rw [hSchur]
          rfl
    _ = KDD := matAdd_sub_cancel KDD schurTerm

/-- No-Needles endpoint for arbitrary rational blocks satisfying only the
displayed symmetry, projection, residual, and budget identities. -/
theorem no_needles_stability_general_blocks {y z d : Nat}
    (KLL : Mat y y) (KLD : Mat y z) (KDL : Mat z y)
    (KDD : Mat z z) (KLLdagger : Mat y y)
    (ThetaY : Mat y y) (OmegaZ : Mat z z) (ThetaD : Mat d d)
    (S : Mat d z)
    (hKLDsym : transpose KDL = KLD)
    (hKLLdaggerSym : transpose KLLdagger = KLLdagger)
    (hMPLLD : matMul (matMul KLL KLLdagger) KLD = KLD)
    (hKLbound : loewnerLE KLL ThetaY)
    (hXibound : loewnerLE (generalBlockResidual KLD KDL KDD KLLdagger) OmegaZ)
    (hTransport : loewnerLE
      (matMul (matMul S
        (matAdd
          (matMul (matMul (generalBlockNativeExplanation KDL KLLdagger) ThetaY)
            (transpose (generalBlockNativeExplanation KDL KLLdagger)))
          OmegaZ)) (transpose S)) ThetaD) :
    loewnerLE (matMul (matMul S KDD) (transpose S)) ThetaD := by
  let Astar := generalBlockNativeExplanation KDL KLLdagger
  have hSchur := general_block_schur_identity KLL KLD KDL KDD KLLdagger
    hKLDsym hKLLdaggerSym hMPLLD
  have hNative : loewnerLE
      (matMul (matMul Astar KLL) (transpose Astar))
      (matMul (matMul Astar ThetaY) (transpose Astar)) :=
    loewnerLE_conjugate Astar KLL ThetaY hKLbound
  have hSchurBound : loewnerLE KDD
      (matAdd (matMul (matMul Astar ThetaY) (transpose Astar)) OmegaZ) := by
    rw [hSchur]
    exact loewnerLE_add_mono _ _ _ _ hNative hXibound
  have hTransportSource : loewnerLE
      (matMul (matMul S KDD) (transpose S))
      (matMul (matMul S
        (matAdd (matMul (matMul Astar ThetaY) (transpose Astar)) OmegaZ))
        (transpose S)) :=
    loewnerLE_conjugate S KDD _ hSchurBound
  exact loewnerLE_trans _ _ _ hTransportSource hTransport

/-- Currency blocks formed using a supplied pseudoinverse, with no diagonal
construction imposed on it. -/
def suppliedCurrencyLL {e y : Nat} (Cplus : Mat e e) (L : Mat y e) : Mat y y :=
  matMul (matMul L Cplus) (transpose L)

def suppliedCurrencyLD {e y z : Nat} (Cplus : Mat e e)
    (L : Mat y e) (D : Mat z e) : Mat y z :=
  matMul (matMul L Cplus) (transpose D)

def suppliedCurrencyDL {e y z : Nat} (Cplus : Mat e e)
    (L : Mat y e) (D : Mat z e) : Mat z y :=
  matMul (matMul D Cplus) (transpose L)

def suppliedCurrencyDD {e z : Nat} (Cplus : Mat e e) (D : Mat z e) : Mat z z :=
  matMul (matMul D Cplus) (transpose D)

/-- Symmetry of the supplied pseudoinverse gives the cross-block symmetry
needed by the general endpoint theorem. -/
theorem supplied_currency_cross_symmetry {e y z : Nat}
    (Cplus : Mat e e) (L : Mat y e) (D : Mat z e)
    (hCplusSym : transpose Cplus = Cplus) :
    transpose (suppliedCurrencyDL Cplus L D) =
      suppliedCurrencyLD Cplus L D := by
  unfold suppliedCurrencyDL suppliedCurrencyLD
  rw [transpose_matMul, transpose_transpose, transpose_matMul, hCplusSym]
  exact (matMul_assoc L Cplus (transpose D)).symm

/-- C-form of No-Needles for any declared currency matrix and a supplied
symmetric pseudoinverse satisfying the block projection and budget equations. -/
theorem no_needles_stability_supplied_pseudoinverse {e y z d : Nat}
    (_C Cplus : Mat e e) (L : Mat y e) (D : Mat z e)
    (KLLdagger : Mat y y)
    (ThetaY : Mat y y) (OmegaZ : Mat z z) (ThetaD : Mat d d)
    (S : Mat d z)
    (hCplusSym : transpose Cplus = Cplus)
    (hKLLdaggerSym : transpose KLLdagger = KLLdagger)
    (hMPLLD : matMul
      (matMul (suppliedCurrencyLL Cplus L) KLLdagger)
      (suppliedCurrencyLD Cplus L D) = suppliedCurrencyLD Cplus L D)
    (hKLbound : loewnerLE (suppliedCurrencyLL Cplus L) ThetaY)
    (hXibound : loewnerLE
      (generalBlockResidual (suppliedCurrencyLD Cplus L D)
        (suppliedCurrencyDL Cplus L D) (suppliedCurrencyDD Cplus D)
        KLLdagger) OmegaZ)
    (hTransport : loewnerLE
      (matMul (matMul S
        (matAdd
          (matMul (matMul
            (generalBlockNativeExplanation (suppliedCurrencyDL Cplus L D)
              KLLdagger) ThetaY)
            (transpose (generalBlockNativeExplanation
              (suppliedCurrencyDL Cplus L D) KLLdagger)))
          OmegaZ)) (transpose S)) ThetaD) :
    loewnerLE
      (matMul (matMul S (suppliedCurrencyDD Cplus D)) (transpose S))
      ThetaD := by
  exact no_needles_stability_general_blocks
    (suppliedCurrencyLL Cplus L) (suppliedCurrencyLD Cplus L D)
    (suppliedCurrencyDL Cplus L D) (suppliedCurrencyDD Cplus D)
    KLLdagger ThetaY OmegaZ ThetaD S
    (supplied_currency_cross_symmetry Cplus L D hCplusSym)
    hKLLdaggerSym hMPLLD hKLbound hXibound hTransport

end SixBirdsMetaMath.FoundationsIV.Stability.NoNeedles
