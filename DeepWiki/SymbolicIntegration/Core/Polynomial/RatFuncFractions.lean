import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic
import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncEmbedding

/-! # Rational-function fraction arithmetic

Small arithmetic lemmas for `RatFunc.mk` representatives.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- Fraction addition for `RatFunc.mk`: `p/q + r/s = (p*s + r*q)/(q*s)`. -/
theorem ratFunc_mk_add_mk (p r : K[X]) {q s : K[X]} (hq : q ≠ 0) (hs : s ≠ 0) :
    RatFunc.mk p q + RatFunc.mk r s = RatFunc.mk (p * s + r * q) (q * s) := by
  rw [RatFunc.mk_eq_div, RatFunc.mk_eq_div, RatFunc.mk_eq_div,
    div_add_div _ _ (ratFunc_algebraMap_ne_zero hq) (ratFunc_algebraMap_ne_zero hs),
    map_add, map_mul, map_mul, map_mul]
  ring

/-- Fraction multiplication for `RatFunc.mk`: `(p/q) * (r/s) = (p*r)/(q*s)`. -/
theorem ratFunc_mk_mul_mk (p q r s : K[X]) :
    RatFunc.mk p q * RatFunc.mk r s = RatFunc.mk (p * r) (q * s) := by
  rw [RatFunc.mk_eq_div, RatFunc.mk_eq_div, RatFunc.mk_eq_div, div_mul_div_comm, map_mul, map_mul]

/-- A list sum of polynomial numerators over a common denominator collapses to one fraction. -/
theorem ratFunc_list_sum_algebraMap_div_const {α : Type*} (L : List α) (f : α → K[X])
    (d : RatFunc K) :
    (L.map (fun k => algebraMap K[X] (RatFunc K) (f k) / d)).sum
      = algebraMap K[X] (RatFunc K) ((L.map f).sum) / d := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, map_add, add_div]

end DeepWiki.SymbolicIntegration
