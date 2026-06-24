import DeepWiki.SymbolicIntegration.SubresultantCorrectness
import DeepWiki.SymbolicIntegration.LrtMonicLogs
import Mathlib.LinearAlgebra.Lagrange

/-! # Correctness of the computable Rothstein–Trager resultant (`rtResultantCompute ↔ rtResultant`)
The computable `rtResultantCompute` (`RtResultantCompute`) recovers the bivariate Rothstein–Trager
resultant `R(t) = res_x(D, A − t·D')` by **evaluation + Lagrange interpolation** on `CPoly = List ℚ`.
This file proves it realizes the noncomputable `rtResultant` (`RationalIntegrationAlgorithms`) through
the `toPoly` bridge, on all inputs:

* `cinterpolate` correctness: `toPoly (cinterpolate pts)` evaluates to `yₖ` at `xₖ` and has degree
  `< #pts` (`toPoly_cinterpolate_eval`, `natDegree_toPoly_cinterpolate_lt`), via the Lagrange-basis
  numerator `clagNum`.
* point-agreement: `cresultant fuel D (A − aₖ·D')` is the specialization of `rtResultant` at `aₖ`
  (`cresultant_eq` + `rtResultant_eval`, `cresultant_sample_eq_eval`).
* `toPoly_rtResultantCompute_eq_rtResultant`: the two polynomials agree (degree `< deg D + 1`, equal at
  `deg D + 1` nodes, hence equal by `Lagrange.eq_of_degrees_lt_of_eval_index_eq`).

It then discharges the single remaining hypothesis `hLne` of Example 2.4.1's LRT closure, via the honest
`ℚ[t]` equation `rtResultant (toPoly cA241)(toPoly cD241) = 45796·(4t²+1)³` and the multiplicity-3
regularity of the LRT subresultant at the residue `α = i/2`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### `clagNum`: the Lagrange-basis numerator `∏ (x − xⱼ)` -/

/-- **`clagNum` realizes `∏ (X − C xⱼ)`**: `toPoly (clagNum xs) = ∏_{x ∈ xs} (X − C x)`. -/
theorem toPoly_clagNum (xs : List ℚ) :
    toPoly (clagNum xs) = (xs.map (fun x => Polynomial.X - Polynomial.C x)).prod := by
  induction xs with
  | nil => simp [clagNum, toPoly_cons]
  | cons x xs ih =>
    rw [clagNum, toPoly_cmul, ih, List.map_cons, List.prod_cons]
    have : toPoly [(-x), 1] = Polynomial.X - Polynomial.C x := by
      rw [toPoly_cons, toPoly_cons, toPoly_nil, map_neg, map_one]; ring
    rw [this]

/-- **`toPoly` of the `cinterpolate` accumulator fold** is the running sum: folding `cadd acc (f p)`
over `pts` maps under `toPoly` to `toPoly init + ∑ p, toPoly (f p)`. -/
theorem toPoly_foldl_cadd (f : ℚ × ℚ → CPoly) (pts : List (ℚ × ℚ)) (init : CPoly) :
    toPoly (pts.foldl (fun acc p => cadd acc (f p)) init)
      = toPoly init + (pts.map (fun p => toPoly (f p))).sum := by
  induction pts generalizing init with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih, toPoly_cadd, List.map_cons, List.sum_cons]
    ring

/-- The `cinterpolate` denominator fold `∏ acc·(xk − xⱼ)` equals the list product `∏ (xk − xⱼ)`,
threaded through an arbitrary starting accumulator. -/
theorem foldl_mul_sub_eq_prod' (xk : ℚ) (others : List ℚ) (init : ℚ) :
    others.foldl (fun acc xj => acc * (xk - xj)) init
      = init * (others.map (fun xj => xk - xj)).prod := by
  induction others generalizing init with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons]; ring

/-- The `cinterpolate` denominator fold `∏ acc·(xk − xⱼ)` equals the list product `∏ (xk − xⱼ)`. -/
theorem foldl_mul_sub_eq_prod (xk : ℚ) (others : List ℚ) :
    others.foldl (fun acc xj => acc * (xk - xj)) 1
      = (others.map (fun xj => xk - xj)).prod := by
  rw [foldl_mul_sub_eq_prod', one_mul]

/-- The product `∏_{xⱼ ∈ others} (xk − xⱼ)` is nonzero when every `xⱼ ≠ xk`. -/
theorem prod_sub_ne_zero {xk : ℚ} {others : List ℚ} (hne : ∀ xj ∈ others, xj ≠ xk) :
    (others.map (fun xj => xk - xj)).prod ≠ 0 := by
  rw [Ne, List.prod_eq_zero_iff]
  intro hy
  rw [List.mem_map] at hy
  obtain ⟨xj, hxj, hxeq⟩ := hy
  exact hne xj hxj (sub_eq_zero.mp hxeq).symm

/-- **Eval of a Lagrange term polynomial at a node** `x`: `(C (yk/denom) · ∏(X − C xⱼ)).eval x =
(yk/denom)·∏(x − xⱼ)`. -/
theorem eval_term_poly (xk yk x : ℚ) (others : List ℚ) :
    (toPoly (cscale (yk / (others.foldl (fun acc xj => acc * (xk - xj)) 1))
        (clagNum others))).eval x
      = (yk / (others.map (fun xj => xk - xj)).prod)
        * (others.map (fun xj => x - xj)).prod := by
  rw [toPoly_cscale, toPoly_clagNum, eval_mul, eval_C, foldl_mul_sub_eq_prod]
  congr 1
  rw [eval_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro xj _
  simp [Function.comp, eval_sub, eval_X, eval_C]

/-- **Eval of a Lagrange term at its own node**: the `cinterpolate` term for `(xk, yk)`, with
`others` the abscissas distinct from `xk`, evaluates to `yk` at `xk` (the denominator is the same
product, and is nonzero since each `xⱼ ≠ xk`). -/
theorem eval_term_at_self (xk yk : ℚ) (others : List ℚ) (hne : ∀ xj ∈ others, xj ≠ xk) :
    (toPoly (cscale (yk / (others.foldl (fun acc xj => acc * (xk - xj)) 1))
        (clagNum others))).eval xk = yk := by
  rw [eval_term_poly, div_mul_cancel₀]
  exact prod_sub_ne_zero hne

end DeepWiki.SymbolicIntegration.Compute
