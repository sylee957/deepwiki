import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Polynomial matrix degree bounds

Degree estimates for determinants of matrices over polynomial rings.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- If column `j` of a polynomial matrix has degree at most `b j`, its determinant has degree at most `∑ j, b j`. -/
theorem natDegree_det_le_sum_col {K : Type*} [Field K]
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (M : Matrix ι ι K[X]) (b : ι → ℕ) (hb : ∀ i j, (M i j).natDegree ≤ b j) :
    (M.det).natDegree ≤ ∑ j, b j := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro σ _
  rw [Function.comp_apply]
  refine (natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  exact Finset.sum_le_sum (fun i _ => hb (σ i) i)

end DeepWiki.SymbolicIntegration
