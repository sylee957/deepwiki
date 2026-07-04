import DeepWiki.SymbolicIntegration.LrtGeneralDerivation
import DeepWiki.SymbolicIntegration.Computable.LogPartTowerSoundness

/-! # Connecting the computable tower residue resultant to the general-derivation abstract theory (G4b)

`cResidueResultantTowerGWf Dt a d` interpolates the resultant samples `res_t(d, a − zₖ·Dd)` (`Dd =
cmonomialDeriv Dt d`). This file certifies it against the general-derivation abstract residue resultant
`rtResultantGen (toPolyG a) (toPolyG d) B` with `B = implicitDeriv (toPolyG Dt) (toPolyG d)` (G1–G3), for
the **primitive** reduced case (`Dt` constant, `Dstar` monic). Sample agreement is the core; the full
interpolation certification (`toPolyG … = rtResultantGen …`) follows by interpolation uniqueness. See
`docs/generalize-lrt-derivation.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- **Sample agreement.** `toK (cresultantWf d (cAmcDdG Dt a d c))` equals the general-derivation abstract
residue resultant `rtResultantGen (toPolyG a) (toPolyG d) B` (`B = implicitDeriv (toPolyG Dt) (toPolyG d)`)
evaluated at `toK c`, for **monic** `d`, **constant** `Dt`, and proper `a` (`deg a < deg d`). The engine
computes the resultant at the *actual* degree `deg(a − c·Dd)`; the abstract `rtResultantGen` uses the formal
degree `deg d − 1`; `Polynomial.resultant_add_right_deg` reconciles them (`lc d = 1` from monic). -/
theorem toK_cresultantWf_cAmcDdG_eq_eval (Dt a d : CPolyG α) (c : α)
    (hDmonic : (toPolyG d).Monic) (hDt0 : (toPolyG Dt).natDegree = 0)
    (hAD : (toPolyG a).natDegree < (toPolyG d).natDegree) :
    CFieldSpec.toK (cresultantWf d (cAmcDdG Dt a d c))
      = (rtResultantGen (toPolyG a) (toPolyG d)
          (Differential.implicitDeriv (toPolyG Dt) (toPolyG d))).eval (CFieldSpec.toK c) := by
  set B := Differential.implicitDeriv (toPolyG Dt) (toPolyG d) with hBdef
  have hBdeg : B.natDegree ≤ (toPolyG d).natDegree - 1 :=
    natDegree_implicitDeriv_le_of_monic (toPolyG Dt) (toPolyG d) hDmonic hDt0
  have htE : toPolyG (cAmcDdG Dt a d c) = toPolyG a - C (CFieldSpec.toK c) * B :=
    toPolyG_cAmcDdG Dt a d c
  have hEdeg : (toPolyG a - C (CFieldSpec.toK c) * B).natDegree ≤ (toPolyG d).natDegree - 1 := by
    refine (natDegree_sub_le _ _).trans (max_le (by omega) ?_)
    exact (natDegree_C_mul_le _ _).trans hBdeg
  rw [toPolyG_cresultantWf, rtResultantGen_eval, cdegG_eq_natDegree d,
    cdegG_eq_natDegree (cAmcDdG Dt a d c), htE]
  obtain ⟨k, hk⟩ :
      ∃ k, (toPolyG d).natDegree - 1 = (toPolyG a - C (CFieldSpec.toK c) * B).natDegree + k :=
    ⟨(toPolyG d).natDegree - 1 - (toPolyG a - C (CFieldSpec.toK c) * B).natDegree, by omega⟩
  rw [hk, Polynomial.resultant_add_right_deg (toPolyG d) (toPolyG a - C (CFieldSpec.toK c) * B)
      (toPolyG d).natDegree (toPolyG a - C (CFieldSpec.toK c) * B).natDegree k le_rfl,
    show (toPolyG d).coeff (toPolyG d).natDegree = (toPolyG d).leadingCoeff from rfl,
    hDmonic.leadingCoeff, one_pow, one_mul]

end DeepWiki.SymbolicIntegration
