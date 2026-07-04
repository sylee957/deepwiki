import DeepWiki.SymbolicIntegration.Computable.HermiteReduction
import DeepWiki.SymbolicIntegration.Computable.HermiteValuationTower

/-! # Realization (Stage 2): `cHermiteReduceTowerGWf` is a lawful Hermite reduction

The single `LawfulHermiteReduction` realization theorem for the tower Hermite reducer. The cleared
field identity comes from the pole-cancellation capstone (`cHermiteReduceTowerGWf_field_identity` +
`toPolyG_hNum'_eq_2_1`); **`Dstar` squarefreeness is consumed from the squarefree-decomposition
interface** (`cSqfreeYunFFGWf_lawfulSquarefreeDecomposition`, via `prod_squarefree`), NOT re-derived from
the Yun loop; the leftover properness is the deg-`Dt`-≤1 contract, threaded. See
`docs/risch-two-stage-discipline.md`. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α]

/-- **Realization: `cHermiteReduceTowerGWf` is a lawful Hermite reduction of `a/d`.** `field_identity` from
the pole-cancellation capstone; `squarefree` consumed from `LawfulSquarefreeDecomposition`; `proper` the
deg-`Dt`-≤1 leftover-properness contract. Under the differential-normality precondition `hcopgcd`. -/
theorem cHermiteReduceTowerGWf_lawfulHermiteReduction [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).degree
      < (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).degree) :
    LawfulHermiteReduction Dt a d (cHermiteReduceTowerGWf Dt a d).1.1
      (cHermiteReduceTowerGWf Dt a d).1.2 (cHermiteReduceTowerGWf Dt a d).2.1
      (cHermiteReduceTowerGWf Dt a d).2.2 where
  field_identity := by
    have hcap := cHermiteReduceTowerGWf_field_identity hgcd Dt a d hd0 hpp hcopgcd
    rwa [toPolyG_hNum'_eq_2_1 hgcd Dt a d hd0 hpp hcopgcd] at hcap
  squarefree := by
    rw [show toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 = ((cSqfreeYunFFGWf d).map toPolyG).prod from by
      rw [cHermiteReduceTowerGWf]
      simp only [toPolyG_cnormG, toPolyG_foldl_cmulG_plainList, toPolyG_one_singleton, one_mul]]
    exact (cSqfreeYunFFGWf_lawfulSquarefreeDecomposition hgcd d hd0 hpp).prod_squarefree
  proper := hproper

end DeepWiki.SymbolicIntegration
