import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic

/-! # Rational-function fraction arithmetic

Small arithmetic lemmas for `RatFunc.mk` representatives.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- The polynomial embedding into `RatFunc K` preserves nonzero polynomials. -/
theorem ratFunc_algebraMap_ne_zero {q : K[X]} (hq : q ≠ 0) :
    algebraMap K[X] (RatFunc K) q ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hq

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

end DeepWiki.SymbolicIntegration
