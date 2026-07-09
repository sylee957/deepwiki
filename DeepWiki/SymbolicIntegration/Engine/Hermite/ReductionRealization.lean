import DeepWiki.SymbolicIntegration.Engine.Hermite.Reduction
import DeepWiki.SymbolicIntegration.Engine.Hermite.ValuationTower

/-! # Tower Hermite reduction realization

The tower Hermite reducer realizes the `LawfulHermiteReduction` interface: the field identity,
squarefree leftover denominator, and properness clauses are assembled from the corresponding tower
and squarefree-decomposition facts. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α]

/-- `cHermiteReduceTowerG` is a lawful Hermite reduction of `a/d` under differential normality. -/
theorem cHermiteReduceTowerG_lawfulHermiteReduction [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPoly α) (hd0 : toPolyG d ≠ 0)
    (hpp : (toPolyG d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFFG d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPolyG (cHermiteReduceTowerG Dt a d).2.1).degree
      < (toPolyG (cHermiteReduceTowerG Dt a d).2.2).degree) :
    LawfulHermiteReduction Dt a d (cHermiteReduceTowerG Dt a d).1.1
      (cHermiteReduceTowerG Dt a d).1.2 (cHermiteReduceTowerG Dt a d).2.1
      (cHermiteReduceTowerG Dt a d).2.2 where
  field_identity := by
    have hcap := cHermiteReduceTowerG_field_identity hgcd Dt a d hd0 hpp hcopgcd
    rwa [toPolyG_hNum'_eq_2_1 hgcd Dt a d hd0 hpp hcopgcd] at hcap
  squarefree := by
    rw [show toPolyG (cHermiteReduceTowerG Dt a d).2.2 = ((cSqfreeYunFFG d).map toPolyG).prod from by
      rw [cHermiteReduceTowerG]
      simp only [denote]
      simp]
    exact (cSqfreeYunFFG_lawfulSquarefreeDecomposition hgcd d hd0 hpp).prod_squarefree
  proper := hproper

end DeepWiki.SymbolicIntegration
