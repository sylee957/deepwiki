import DeepWiki.SymbolicIntegration.Compute.Hermite
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCorrect
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Correctness of concrete rational-function accumulation

The legacy `QFun ℚ` addition and fold operations agree with their `RatFunc ℚ` denotation.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

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
  simp only [toQFun, QFun.qadd, DensePoly.toPolyG_caddG,
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
  rw [DensePoly.toPolyG_cmulG]
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

end DeepWiki.SymbolicIntegration.Compute
