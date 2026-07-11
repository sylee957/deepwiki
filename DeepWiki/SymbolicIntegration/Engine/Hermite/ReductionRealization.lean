import DeepWiki.SymbolicIntegration.Engine.Hermite.Reduction
import DeepWiki.SymbolicIntegration.Engine.Hermite.ValuationTower

/-! # Tower Hermite reduction realization

The tower Hermite reducer realizes the `LawfulHermiteReduction` interface: the field identity,
squarefree leftover denominator, and properness clauses are assembled from the corresponding tower
and squarefree-decomposition facts. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α]

/-- `cHermiteReduceTower` is a lawful Hermite reduction of `a/d` under differential normality. -/
theorem cHermiteReduceTowerG_lawfulHermiteReduction [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hproper : (toPoly (cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (cHermiteReduceTower Dt a d).2.2).degree) :
    LawfulHermiteReduction Dt a d (cHermiteReduceTower Dt a d).1.1
      (cHermiteReduceTower Dt a d).1.2 (cHermiteReduceTower Dt a d).2.1
      (cHermiteReduceTower Dt a d).2.2 where
  field_identity := by
    have hcap := cHermiteReduceTowerG_field_identity hgcd Dt a d hd0 hpp hcopgcd
    rwa [toPolyG_hNum'_eq_2_1 hgcd Dt a d hd0 hpp hcopgcd] at hcap
  squarefree := by
    rw [show toPoly (cHermiteReduceTower Dt a d).2.2 = ((cSqfreeYunFF d).map toPoly).prod from by
      rw [cHermiteReduceTower]
      simp only [denote]
      simp]
    have hmap : (cSqfreeYunFF d).map CPoly.toPoly =
        (cSqfreeYunFF d).map DensePoly.toPoly := by
      apply List.map_congr_left
      intro p _
      exact toPoly_list_eq p
    rw [← hmap]
    exact (cSqfreeYunFFG_lawfulSquarefreeDecomposition hgcd d hd0 hpp).prod_squarefree
  proper := hproper

end DeepWiki.SymbolicIntegration
