import DeepWiki.SymbolicIntegration.LrtGeneralDerivation
import DeepWiki.SymbolicIntegration.Computable.SubresultantSpec
import DeepWiki.SymbolicIntegration.Computable.MonomialDeriv

/-! # Connecting the computable parametric LRT subresultant to the abstract theory (G4c)

`cSubresultantParam Dstar A Dd n m j` is the engine's parametric LRT log argument `Sⱼ(z,t)`: its `k`-th
entry is the `z`-polynomial coefficient of `tᵏ`, computed by interpolation in `z` of the coefficient of
`cSubresultantG Dstar (A − z·Dd) n m j`. This file connects it to the general-derivation abstract
subresultant `subresultant (toPolyG Dstar) (toPolyG A − C z · B) n m j` (`B = toPolyG Dd`), building on
the L4b subresultant certification `toPolyG_cSubresultantG`. See `docs/generalize-lrt-derivation.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **Per-value subresultant agreement.** The `k`-th `t`-coefficient of the computable subresultant
`cSubresultantG Dstar (A − c·Dd) n m j`, read through `toK`, equals the `k`-th `t`-coefficient of the
abstract subresultant of `(Dstar, A − c·B)` (`B = toPolyG Dd`), for any value `c`. Immediate from the L4b
certification `toPolyG_cSubresultantG` plus the `csubG`/`cscaleG` bridges — no interpolation needed (this is
the per-node fact the interpolation extends to all residues). -/
theorem toK_cSubresultantG_getD_eq_coeff (Dstar A Dd : CPolyG α) (c : α) (n m j k : ℕ) :
    CFieldSpec.toK
        (((cSubresultantG Dstar (csubG A (cscaleG c Dd)) n m j : CPolyG α) : List α).getD k
          CField.zero)
      = (subresultant (toPolyG Dstar)
          (toPolyG A - C (CFieldSpec.toK c) * toPolyG Dd) n m j).coeff k := by
  rw [← toPolyG_coeff, toPolyG_cSubresultantG, toPolyG_csubG, toPolyG_cscaleG]

variable [CDiffField α] [CDiffFieldSpec α]

/-- The per-value subresultant agreement with the **tower derivation** `Dd = cmonomialDeriv Dt Dstar`, so
`B = implicitDeriv (toPolyG Dt) (toPolyG Dstar)` — the form used by `cLrtLogArgG`. -/
theorem toK_cSubresultantG_getD_eq_coeff_monomial (Dt Dstar A : CPolyG α) (c : α) (n m j k : ℕ) :
    CFieldSpec.toK
        (((cSubresultantG Dstar (csubG A (cscaleG c (cmonomialDeriv Dt Dstar))) n m j : CPolyG α) :
            List α).getD k CField.zero)
      = (subresultant (toPolyG Dstar)
          (toPolyG A - C (CFieldSpec.toK c)
            * Differential.implicitDeriv (toPolyG Dt) (toPolyG Dstar)) n m j).coeff k := by
  rw [toK_cSubresultantG_getD_eq_coeff, toPolyG_cmonomialDeriv]

end DeepWiki.SymbolicIntegration
