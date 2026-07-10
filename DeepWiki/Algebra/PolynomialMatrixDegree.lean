import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Polynomial matrix degree bounds

Degree estimates for parameter-linear polynomial expressions and determinants over polynomial rings.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- Every coefficient of `A.map C - C X * B.map C` has parameter degree at most one. -/
theorem natDegree_coeff_map_sub_C_X_mul_map_le_one {K : Type*} [Field K]
    (A B : K[X]) (k : ℕ) :
    ((A.map (C : K →+* K[X]) - C Polynomial.X * B.map (C : K →+* K[X])).coeff k).natDegree ≤ 1 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_C]
    exact Nat.zero_le 1
  · refine (Polynomial.natDegree_mul_le (p := (Polynomial.X : K[X]))
      (q := Polynomial.C (B.coeff k))).trans ?_
    rw [Polynomial.natDegree_X, Polynomial.natDegree_C]

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
