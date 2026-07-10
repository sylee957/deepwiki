import DeepWiki.SymbolicIntegration.Compute.Hermite
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCorrect
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Correctness of the computable engine
Through `DensePoly.toPoly`, the concrete bivariate, rational-function, and resultant operations
realize the corresponding `ℚ[X]` operations. Polynomial division and gcd correctness come directly
from the representation-independent and well-founded dense APIs. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-- `cnorm` on a cons cell, unfolded to its defining `match`. -/
theorem cnorm_cons_eq (a : ℚ) (as : DensePoly ℚ) :
    cnorm (a :: as)
      = (match cnorm as with | [] => if a = 0 then [] else [a] | r => a :: r) := by
  show DensePoly.cnorm (a :: as)
      = (match DensePoly.cnorm as with | [] => if a = 0 then [] else [a] | r => a :: r)
  rw [DensePoly.cnormG_cons_eq]
  cases DensePoly.cnorm as with
  | nil => show (if (decide (a = 0) = true) then _ else _) = _; by_cases ha : a = 0 <;> simp [ha]
  | cons b bs => rfl

/-- Rational-function read of a `QFun` into `RatFunc ℚ`: `(num, den) ↦ toPoly num / toPoly den`. -/
noncomputable def toQFun (x : QFun ℚ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (toPoly x.1) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly x.2)

/-- `QFun.qadd` realizes rational-function addition (for nonzero denominators):
`toQFun (QFun.qadd x y) = toQFun x + toQFun y`. -/
theorem toQFun_qadd (x y : QFun ℚ) (hb : toPoly x.2 ≠ 0) (hd : toPoly y.2 ≠ 0) :
    toQFun (QFun.qadd x y) = toQFun x + toQFun y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  have hinj := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have hb' : algebraMap ℚ[X] (RatFunc ℚ) (toPoly b) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hb
  have hd' : algebraMap ℚ[X] (RatFunc ℚ) (toPoly d) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hd
  simp only [toPoly_eq_dense] at hb' hd'
  simp only [toQFun, QFun.qadd, toPoly_eq_dense, DensePoly.toPolyG_caddG,
    DensePoly.toPolyG_cmulG, map_add, map_mul]
  rw [div_add_div _ _ hb' hd']
  ring

/-- `toQFun QFun.qzero = 0`. -/
theorem toQFun_qzero : toQFun QFun.qzero = 0 := by
  simp [toQFun, QFun.qzero, DensePoly.toPolyG_nil]

/-- `QFun.qadd x y` has nonzero denominator when both `x` and `y` do. -/
theorem toPoly_qadd_den_ne_zero {x y : QFun ℚ} (hx : toPoly x.2 ≠ 0) (hy : toPoly y.2 ≠ 0) :
    toPoly (QFun.qadd x y).2 ≠ 0 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  show toPoly (cmul b d) ≠ 0
  rw [toPoly_eq_dense, DensePoly.toPolyG_cmulG]
  exact mul_ne_zero hx hy

/-- A `QFun.qadd` fold denotes the seed plus the sum of the entries. -/
theorem toQFun_foldl_qadd (gs : List (QFun ℚ)) (init : QFun ℚ) (hinit : toPoly init.2 ≠ 0)
    (hgs : ∀ g ∈ gs, toPoly g.2 ≠ 0) :
    toQFun (gs.foldl QFun.qadd init) = toQFun init + (gs.map toQFun).sum := by
  induction gs generalizing init with
  | nil => simp
  | cons hd tl ih =>
    have hhd : toPoly hd.2 ≠ 0 := hgs hd (List.mem_cons_self ..)
    have htl : ∀ g ∈ tl, toPoly g.2 ≠ 0 := fun g hg => hgs g (List.mem_cons_of_mem hd hg)
    have hnew : toPoly (QFun.qadd init hd).2 ≠ 0 := toPoly_qadd_den_ne_zero hinit hhd
    rw [List.foldl_cons, ih (QFun.qadd init hd) hnew htl, toQFun_qadd init hd hinit hhd,
      List.map_cons, List.sum_cons]
    ring

/-! ### Degree / leading coefficient bridge
`(toPoly p).coeff i = p.getD i 0`, from which `cdeg`/`clead` are the `natDegree`/`leadingCoeff`. -/

/-- Coefficient read: `(toPoly p).coeff i = p.getD i 0`. -/
theorem toPoly_coeff (p : DensePoly ℚ) (i : ℕ) : (toPoly p).coeff i = p.getD i 0 := by
  induction p generalizing i with
  | nil => simp
  | cons a as ih =>
    simp only [toPoly_eq_dense] at ih
    rw [toPoly_eq_dense, DensePoly.toPolyG_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

/-- Degree bound: `natDegree (toPoly p) ≤ (cnorm p).length − 1`. -/
theorem natDegree_toPoly_le (p : DensePoly ℚ) : (toPoly p).natDegree ≤ (cnorm p).length - 1 := by
  rw [toPoly_eq_dense, ← DensePoly.toPolyG_cnormG]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [DensePoly.toPolyG_coeff, toR_eq_toK, CFieldSpec.toK_rat,
    List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- `cnorm` has no trailing zero: `(cnorm p).getLast? ≠ some 0`. -/
theorem cnorm_getLast?_ne_some_zero (p : DensePoly ℚ) : (cnorm p).getLast? ≠ some 0 := by
  induction p with
  | nil => simp
  | cons a as ih =>
    rw [cnorm_cons_eq]
    cases h : cnorm as with
    | nil =>
      by_cases ha : a = 0 <;> simp [ha]
    | cons b bs =>
      rw [h] at ih
      rw [List.getLast?_cons_cons]
      exact ih

/-- For a normalized nonzero `DensePoly ℚ`, the leading coefficient `clead` is nonzero. -/
theorem clead_ne_zero {p : DensePoly ℚ} (h : cnorm p ≠ []) : clead p ≠ 0 := by
  show DensePoly.clead p ≠ 0
  rcases hl : (DensePoly.cnorm p).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hl) h
  · simp only [DensePoly.clead, hl, Option.getD_some]
    rintro rfl
    exact cnorm_getLast?_ne_some_zero p hl

/-- `clead p = (toPoly p).coeff (cdeg p)`: the leading coefficient sits at the top index. -/
theorem clead_eq_coeff (p : DensePoly ℚ) : clead p = (toPoly p).coeff (cdeg p) := by
  show DensePoly.clead p = _
  rw [DensePoly.clead, cdeg, toPoly_eq_dense, ← DensePoly.toPolyG_cnormG,
    DensePoly.toPolyG_coeff, toR_eq_toK, CFieldSpec.toK_rat,
    List.getD_eq_getElem?_getD,
    ← List.getLast?_eq_getElem?]

/-- `cdeg p = (toPoly p).natDegree`: `cdeg` is the honest `natDegree`. -/
theorem cdeg_eq_natDegree (p : DensePoly ℚ) : cdeg p = (toPoly p).natDegree := by
  rcases eq_or_ne (cnorm p) [] with h | h
  · have h0 : toPoly p = 0 := by
      rw [toPoly_eq_dense, ← DensePoly.toPolyG_cnormG, h, DensePoly.toPolyG_nil]
    rw [cdeg, h, h0]; simp
  · refine le_antisymm ?_ (natDegree_toPoly_le p)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [← clead_eq_coeff]
    exact clead_ne_zero h

/-- `clead p = (toPoly p).leadingCoeff`: `clead` is the honest `leadingCoeff`. -/
theorem clead_eq_leadingCoeff (p : DensePoly ℚ) : clead p = (toPoly p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← cdeg_eq_natDegree, ← clead_eq_coeff]

/-- `cnorm p = []` iff `toPoly p = 0` (the list normalizes to empty exactly for the zero polynomial). -/
theorem cnorm_eq_nil_iff (p : DensePoly ℚ) : cnorm p = [] ↔ toPoly p = 0 := by
  constructor
  · intro h; rw [toPoly_eq_dense, ← DensePoly.toPolyG_cnormG, h, DensePoly.toPolyG_nil]
  · intro h
    by_contra hne
    have hcl := clead_ne_zero hne
    rw [clead_eq_leadingCoeff, h, Polynomial.leadingCoeff_zero] at hcl
    exact hcl rfl

/-- For a nonzero polynomial, the normalized list length is `natDegree + 1`. -/
theorem length_cnorm_of_ne (p : DensePoly ℚ) (h : cnorm p ≠ []) :
    (cnorm p).length = (toPoly p).natDegree + 1 := by
  have hd := cdeg_eq_natDegree p
  rw [cdeg] at hd
  have hlen : 1 ≤ (cnorm p).length := List.length_pos_iff.mpr h
  omega

end DeepWiki.SymbolicIntegration.Compute
