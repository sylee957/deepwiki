import DeepWiki.SymbolicIntegration.Engine.Hermite.Reduction
import DeepWiki.SymbolicIntegration.Engine.Hermite.ValuationTower

/-! # Tower Hermite reduction realization

The tower Hermite reducer realizes the `LawfulHermiteReduction` interface: the field identity,
squarefree leftover denominator, and properness clauses are assembled from the corresponding tower
and squarefree-decomposition facts. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α]

/-- `cHermiteReduceTowerGWf` is a lawful Hermite reduction of `a/d` under differential normality. -/
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
      simp only [denote]
      simp]
    exact (cSqfreeYunFFGWf_lawfulSquarefreeDecomposition hgcd d hd0 hpp).prod_squarefree
  proper := hproper

end DeepWiki.SymbolicIntegration
