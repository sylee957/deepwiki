import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.SubresultantPRS
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! # `toBPoly` degree and leading-coefficient bridge

`bdeg` and `blc` are the honest `x`-`natDegree` and `leadingCoeff` of `toBPoly p`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-- The `i`-th `x`-coefficient of `toBPoly p` is `toPoly` of the `i`-th list entry (`[]` past the end). -/
theorem toBPoly_coeff (p : BPoly) (i : ℕ) : (toBPoly p).coeff i = toPoly (p.getD i []) := by
  induction p generalizing i with
  | nil => simp
  | cons a as ih =>
    rw [toBPoly_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

/-- `natDegree (toBPoly p) ≤ (bnorm p).length − 1`. -/
theorem natDegree_toBPoly_le (p : BPoly) : (toBPoly p).natDegree ≤ (bnorm p).length - 1 := by
  rw [← toBPoly_bnorm]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [toBPoly_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- `bnorm` has no trailing zero `x`-coefficient: its `getLast?` never `toPoly`-vanishes. -/
theorem bnorm_getLast?_toPoly_ne_zero (p : BPoly) {v : CPoly ℚ}
    (h : (bnorm p).getLast? = some v) : toPoly v ≠ 0 := by
  induction p with
  | nil => simp at h
  | cons a as ih =>
    rw [bnorm_cons_eq] at h
    cases hr : bnorm as with
    | nil =>
      rw [hr] at h
      by_cases ha : cisZero (cnorm a)
      · simp [ha] at h
      · simp only [ha, Bool.false_eq_true, if_false] at h
        rw [List.getLast?_singleton, Option.some.injEq] at h
        subst h
        rw [toPoly_cnorm]
        intro hz
        exact ha (by simp [cisZero, (cnorm_eq_nil_iff a).mpr hz])
    | cons b bs =>
      rw [hr] at h
      rw [List.getLast?_cons_cons] at h
      exact ih (by rw [hr]; exact h)

/-- `toPoly (blc p) = (toBPoly p).coeff (bdeg p)`: `blc` is the top-index `x`-coefficient. -/
theorem toPoly_blc_eq_coeff (p : BPoly) : toPoly (blc p) = (toBPoly p).coeff (bdeg p) := by
  rw [blc, bdeg, ← toBPoly_bnorm, toBPoly_coeff, List.getD_eq_getElem?_getD,
    ← List.getLast?_eq_getElem?]

/-- `bisZero p = true ↔ toBPoly p = 0`. -/
theorem bisZero_iff_toBPoly_eq_zero (p : BPoly) : bisZero p = true ↔ toBPoly p = 0 := by
  rw [bisZero, beq_iff_eq]
  constructor
  · intro h; rw [← toBPoly_bnorm, h, toBPoly_nil]
  · intro h
    rcases hb : bnorm p with _ | ⟨c, cs⟩
    · rfl
    · exfalso
      have hlast : ((c :: cs).getLast?) ≠ none := by simp
      rcases hg : (c :: cs).getLast? with _ | v
      · exact hlast hg
      · have hv := bnorm_getLast?_toPoly_ne_zero p (by rw [hb]; exact hg)
        have : (toBPoly p).coeff (bdeg p) = 0 := by rw [h]; simp
        rw [← toPoly_blc_eq_coeff] at this
        rw [blc, hb] at this
        rw [hg] at this
        simp only [Option.getD_some] at this
        exact hv this

/-- `toPoly (blc p) ≠ 0` when `¬ bisZero p`. -/
theorem toPoly_blc_ne_zero (p : BPoly) (h : ¬ bisZero p = true) : toPoly (blc p) ≠ 0 := by
  have hbne : bnorm p ≠ [] := by
    intro hb
    exact h (by rw [bisZero, beq_iff_eq, hb])
  rw [blc]
  rcases hg : (bnorm p).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hg) hbne
  · simp only [Option.getD_some]
    exact bnorm_getLast?_toPoly_ne_zero p hg

/-- `bdeg p = (toBPoly p).natDegree`. -/
theorem bdeg_eq_natDegree (p : BPoly) : bdeg p = (toBPoly p).natDegree := by
  by_cases h : bisZero p = true
  · have hz : toBPoly p = 0 := (bisZero_iff_toBPoly_eq_zero p).mp h
    have hb : bnorm p = [] := by simpa [bisZero] using h
    rw [bdeg, hb, hz]; simp
  · refine le_antisymm ?_ ?_
    · -- bdeg ≤ natDegree via the leading coeff being nonzero at index bdeg
      apply Polynomial.le_natDegree_of_ne_zero
      rw [← toPoly_blc_eq_coeff]
      exact toPoly_blc_ne_zero p h
    · -- natDegree ≤ bdeg via natDegree_toBPoly_le and the length count
      have hbne : bnorm p ≠ [] := by
        intro hb
        exact h (by rw [bisZero, beq_iff_eq, hb])
      have hpos : 1 ≤ (bnorm p).length := List.length_pos_iff.mpr hbne
      have hle := natDegree_toBPoly_le p
      rw [bdeg]; omega

/-- For nonzero `p`, `(bnorm p).length = (toBPoly p).natDegree + 1`. -/
theorem length_bnorm_of_ne (p : BPoly) (h : ¬ bisZero p = true) :
    (bnorm p).length = (toBPoly p).natDegree + 1 := by
  have hbne : bnorm p ≠ [] := by
    intro hb
    exact h (by rw [bisZero, beq_iff_eq, hb])
  have hd := bdeg_eq_natDegree p
  rw [bdeg] at hd
  have hpos : 1 ≤ (bnorm p).length := List.length_pos_iff.mpr hbne
  omega

/-- `toPoly (blc p) = (toBPoly p).leadingCoeff`. -/
theorem toPoly_blc_eq_leadingCoeff (p : BPoly) : toPoly (blc p) = (toBPoly p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← bdeg_eq_natDegree, ← toPoly_blc_eq_coeff]

/-- `Sⱼ(A, C c · B) = c^(n−j) · Sⱼ(A, B)` (`j ≤ m`, `j ≤ n`): subresultant scaled in the second argument. -/
theorem subresultant_C_mul_right {R : Type*} [CommRing R] (c : R) (A B : R[X]) (n m j : ℕ)
    (hjm : j ≤ m) (hjn : j ≤ n) :
    subresultant A (C c * B) n m j = C (c ^ (n - j)) * subresultant A B n m j := by
  have h := subresultant_C_mul 1 c A B n m j hjm hjn
  rw [map_one, one_mul, one_pow, one_mul] at h
  rw [h]

end DeepWiki.SymbolicIntegration.Compute
