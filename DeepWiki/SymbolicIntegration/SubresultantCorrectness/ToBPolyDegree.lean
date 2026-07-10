import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.SubresultantPRS
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! # `GBPolyCore.toGBCoeffPoly` degree and leading-coefficient bridge

`GBPolyCore.gbdegCore` and `GBPolyCore.gblcCore` are the honest `x`-`natDegree` and `leadingCoeff` of `GBPolyCore.toGBCoeffPoly p`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-- The `i`-th `x`-coefficient of `GBPolyCore.toGBCoeffPoly p` is `toPoly` of the `i`-th list entry (`[]` past the end). -/
theorem toBPoly_coeff (p : GBPolyCore ℚ) (i : ℕ) : (GBPolyCore.toGBCoeffPoly p).coeff i = toPoly (p.getD i []) := by
  induction p generalizing i with
  | nil => simp
  | cons a as ih =>
    rw [GBPolyCore.toGBCoeffPoly_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

/-- `natDegree (GBPolyCore.toGBCoeffPoly p) ≤ (GBPolyCore.gbnormCore p).length − 1`. -/
theorem natDegree_toBPoly_le (p : GBPolyCore ℚ) : (GBPolyCore.toGBCoeffPoly p).natDegree ≤ (GBPolyCore.gbnormCore p).length - 1 := by
  rw [← GBPolyCore.toGBCoeffPoly_gbnormCore]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [toBPoly_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- `GBPolyCore.gbnormCore` has no trailing zero `x`-coefficient: its `getLast?` never `toPoly`-vanishes. -/
theorem bnorm_getLast?_toPoly_ne_zero (p : GBPolyCore ℚ) {v : DensePoly ℚ}
    (h : (GBPolyCore.gbnormCore p).getLast? = some v) : toPoly v ≠ 0 := by
  induction p with
  | nil => simp at h
  | cons a as ih =>
    rw [GBPolyCore.gbnormCore_cons_eq] at h
    cases hr : GBPolyCore.gbnormCore as with
    | nil =>
      rw [hr] at h
      by_cases ha : cisZero (cnorm a)
      · simp [ha] at h
      · simp only [ha, Bool.false_eq_true, if_false] at h
        rw [List.getLast?_singleton, Option.some.injEq] at h
        subst h
        rw [DensePoly.toPolyG_cnormG]
        intro hz
        exact ha (by simp [cisZero, (DensePoly.cnormG_eq_nil_iff a).mpr hz])
    | cons b bs =>
      rw [hr] at h
      rw [List.getLast?_cons_cons] at h
      exact ih (by rw [hr]; exact h)

/-- `toPoly (GBPolyCore.gblcCore p) = (GBPolyCore.toGBCoeffPoly p).coeff (GBPolyCore.gbdegCore p)`: `GBPolyCore.gblcCore` is the top-index `x`-coefficient. -/
theorem toPoly_blc_eq_coeff (p : GBPolyCore ℚ) : toPoly (GBPolyCore.gblcCore p) = (GBPolyCore.toGBCoeffPoly p).coeff (GBPolyCore.gbdegCore p) := by
  rw [GBPolyCore.gblcCore, GBPolyCore.gbdegCore, ← GBPolyCore.toGBCoeffPoly_gbnormCore, toBPoly_coeff, List.getD_eq_getElem?_getD,
    ← List.getLast?_eq_getElem?]

/-- `toPoly (GBPolyCore.gblcCore p) ≠ 0` when `¬ GBPolyCore.gbisZeroCore p`. -/
theorem toPoly_blc_ne_zero (p : GBPolyCore ℚ) (h : ¬ GBPolyCore.gbisZeroCore p = true) : toPoly (GBPolyCore.gblcCore p) ≠ 0 := by
  have hbne : GBPolyCore.gbnormCore p ≠ [] := by
    intro hb
    exact h (by rw [GBPolyCore.gbisZeroCore, List.isEmpty_iff, hb])
  rw [GBPolyCore.gblcCore]
  rcases hg : (GBPolyCore.gbnormCore p).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hg) hbne
  · simp only [Option.getD_some]
    exact bnorm_getLast?_toPoly_ne_zero p hg

/-- `GBPolyCore.gbdegCore p = (GBPolyCore.toGBCoeffPoly p).natDegree`. -/
theorem bdeg_eq_natDegree (p : GBPolyCore ℚ) : GBPolyCore.gbdegCore p = (GBPolyCore.toGBCoeffPoly p).natDegree := by
  by_cases h : GBPolyCore.gbisZeroCore p = true
  · have hz : GBPolyCore.toGBCoeffPoly p = 0 := (GBPolyCore.gbisZeroCore_iff_toGBCoeffPoly p).mp h
    have hb : GBPolyCore.gbnormCore p = [] := by simpa [GBPolyCore.gbisZeroCore] using h
    rw [GBPolyCore.gbdegCore, hb, hz]; simp
  · refine le_antisymm ?_ ?_
    · -- GBPolyCore.gbdegCore ≤ natDegree via the leading coeff being nonzero at index GBPolyCore.gbdegCore
      apply Polynomial.le_natDegree_of_ne_zero
      rw [← toPoly_blc_eq_coeff]
      exact toPoly_blc_ne_zero p h
    · -- natDegree ≤ GBPolyCore.gbdegCore via natDegree_toBPoly_le and the length count
      have hbne : GBPolyCore.gbnormCore p ≠ [] := by
        intro hb
        exact h (by rw [GBPolyCore.gbisZeroCore, List.isEmpty_iff, hb])
      have hpos : 1 ≤ (GBPolyCore.gbnormCore p).length := List.length_pos_iff.mpr hbne
      have hle := natDegree_toBPoly_le p
      rw [GBPolyCore.gbdegCore]; omega

/-- For nonzero `p`, `(GBPolyCore.gbnormCore p).length = (GBPolyCore.toGBCoeffPoly p).natDegree + 1`. -/
theorem length_bnorm_of_ne (p : GBPolyCore ℚ) (h : ¬ GBPolyCore.gbisZeroCore p = true) :
    (GBPolyCore.gbnormCore p).length = (GBPolyCore.toGBCoeffPoly p).natDegree + 1 := by
  have hbne : GBPolyCore.gbnormCore p ≠ [] := by
    intro hb
    exact h (by rw [GBPolyCore.gbisZeroCore, List.isEmpty_iff, hb])
  have hd := bdeg_eq_natDegree p
  rw [GBPolyCore.gbdegCore] at hd
  have hpos : 1 ≤ (GBPolyCore.gbnormCore p).length := List.length_pos_iff.mpr hbne
  omega

/-- `toPoly (GBPolyCore.gblcCore p) = (GBPolyCore.toGBCoeffPoly p).leadingCoeff`. -/
theorem toPoly_blc_eq_leadingCoeff (p : GBPolyCore ℚ) : toPoly (GBPolyCore.gblcCore p) = (GBPolyCore.toGBCoeffPoly p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← bdeg_eq_natDegree, ← toPoly_blc_eq_coeff]

/-- `Sⱼ(A, C c · B) = c^(n−j) · Sⱼ(A, B)` (`j ≤ m`, `j ≤ n`): subresultant scaled in the second argument. -/
theorem subresultant_C_mul_right {R : Type*} [CommRing R] (c : R) (A B : R[X]) (n m j : ℕ)
    (hjm : j ≤ m) (hjn : j ≤ n) :
    subresultant A (C c * B) n m j = C (c ^ (n - j)) * subresultant A B n m j := by
  have h := subresultant_C_mul 1 c A B n m j hjm hjn
  rw [map_one, one_mul, one_pow, one_mul] at h
  rw [h]

end DeepWiki.SymbolicIntegration.Compute
