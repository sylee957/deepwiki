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

end DeepWiki.SymbolicIntegration.Compute
