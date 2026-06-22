import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Derivation.DifferentialRing

/-! # The derivative `d/dx` on rational functions `K(x)` (Bronstein §2, the differential field `K(x)`)
Mathlib has no derivation on a field of fractions, so we build `d/dx` on `RatFunc K` directly by the
quotient rule `(p/q)' = (p'q − pq')/q²`. Well-definedness on `RatFunc.liftOn'` is clean: replacing
`(p, q)` by `(a·p, a·q)` multiplies numerator and denominator both by `a²` (the `a'` cross-terms
cancel), so the value is unchanged. This is the substrate for stating the integral correctness
(`∫f = g + ∫h`) of the rational-integration algorithms (Hermite, Rothstein–Trager, …). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- The quotient-rule numerator/denominator pair `(p'q − pq', q²)` as a rational function. -/
private noncomputable def ratFuncDerivAux (p q : K[X]) : RatFunc K :=
  RatFunc.mk (derivative p * q - p * derivative q) (q ^ 2)

private theorem ratFuncDerivAux_wd {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0) :
    ratFuncDerivAux (a * p) (a * q) = ratFuncDerivAux p q := by
  unfold ratFuncDerivAux
  rw [RatFunc.mk_eq_mk (pow_ne_zero 2 (mul_ne_zero ha hq)) (pow_ne_zero 2 hq)]
  simp only [derivative_mul]; ring

private theorem ratFuncDerivAux_zero (p : K[X]) :
    ratFuncDerivAux p 0 = ratFuncDerivAux 0 1 := by
  unfold ratFuncDerivAux
  rw [show (0 : K[X]) ^ 2 = 0 by ring, RatFunc.mk_zero]
  simp [RatFunc.mk_eq_div]

/-- **`d/dx` on `K(x)`**: the rational-function derivative `(p/q)' = (p'q − pq')/q²`, defined via
`RatFunc.liftOn'` (well-defined by `ratFuncDerivAux_wd`). -/
noncomputable def ratFuncDeriv (x : RatFunc K) : RatFunc K :=
  x.liftOn' ratFuncDerivAux fun {_ _ _} hq ha => ratFuncDerivAux_wd hq ha

/-- **Quotient rule** for `ratFuncDeriv`: `(mk p q)' = (p'q − pq')/q²`. -/
theorem ratFuncDeriv_mk (p q : K[X]) :
    ratFuncDeriv (RatFunc.mk p q)
      = RatFunc.mk (derivative p * q - p * derivative q) (q ^ 2) :=
  RatFunc.liftOn'_mk p q ratFuncDerivAux ratFuncDerivAux_zero
    (fun {_ _ _} hq ha => ratFuncDerivAux_wd hq ha)

/-- **`ratFuncDeriv` extends `Polynomial.derivative`**: on a polynomial (as a rational function),
`d/dx` is the polynomial derivative. -/
theorem ratFuncDeriv_algebraMap (p : K[X]) :
    ratFuncDeriv (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (derivative p) := by
  rw [← RatFunc.mk_one p, ratFuncDeriv_mk]
  simp

private theorem algebraMap_ne_zero {q : K[X]} (hq : q ≠ 0) :
    algebraMap K[X] (RatFunc K) q ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hq

/-- Fraction addition for `RatFunc.mk`: `p/q + r/s = (ps + rq)/(qs)`. -/
private theorem mk_add_mk (p r : K[X]) {q s : K[X]} (hq : q ≠ 0) (hs : s ≠ 0) :
    RatFunc.mk p q + RatFunc.mk r s = RatFunc.mk (p * s + r * q) (q * s) := by
  rw [RatFunc.mk_eq_div, RatFunc.mk_eq_div, RatFunc.mk_eq_div,
    div_add_div _ _ (algebraMap_ne_zero hq) (algebraMap_ne_zero hs), map_add, map_mul, map_mul,
    map_mul]
  ring

/-- **Additivity of `d/dx`** on `K(x)`: `(x + y)' = x' + y'`. -/
theorem ratFuncDeriv_add (x y : RatFunc K) :
    ratFuncDeriv (x + y) = ratFuncDeriv x + ratFuncDeriv y := by
  induction x using RatFunc.induction_on' with | _ p q hq =>
  induction y using RatFunc.induction_on' with | _ r s hs =>
  rw [mk_add_mk p r hq hs, ratFuncDeriv_mk, ratFuncDeriv_mk, ratFuncDeriv_mk,
    mk_add_mk _ _ (pow_ne_zero 2 hq) (pow_ne_zero 2 hs),
    RatFunc.mk_eq_mk (pow_ne_zero 2 (mul_ne_zero hq hs)) (mul_ne_zero (pow_ne_zero 2 hq)
      (pow_ne_zero 2 hs))]
  simp only [derivative_add, derivative_mul]; ring

/-- Fraction multiplication for `RatFunc.mk`: `(p/q)·(r/s) = (pr)/(qs)`. -/
private theorem mk_mul_mk (p q r s : K[X]) :
    RatFunc.mk p q * RatFunc.mk r s = RatFunc.mk (p * r) (q * s) := by
  rw [RatFunc.mk_eq_div, RatFunc.mk_eq_div, RatFunc.mk_eq_div, div_mul_div_comm, map_mul, map_mul]

/-- **Leibniz rule for `d/dx`** on `K(x)`: `(x·y)' = x'·y + x·y'`. -/
theorem ratFuncDeriv_mul (x y : RatFunc K) :
    ratFuncDeriv (x * y) = ratFuncDeriv x * y + x * ratFuncDeriv y := by
  induction x using RatFunc.induction_on' with | _ p q hq =>
  induction y using RatFunc.induction_on' with | _ r s hs =>
  rw [mk_mul_mk p q r s, ratFuncDeriv_mk, ratFuncDeriv_mk, ratFuncDeriv_mk,
    mk_mul_mk (derivative p * q - p * derivative q) (q ^ 2) r s,
    mk_mul_mk p q (derivative r * s - r * derivative s) (s ^ 2),
    mk_add_mk _ _ (mul_ne_zero (pow_ne_zero 2 hq) hs) (mul_ne_zero hq (pow_ne_zero 2 hs)),
    RatFunc.mk_eq_mk (pow_ne_zero 2 (mul_ne_zero hq hs))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq) hs) (mul_ne_zero hq (pow_ne_zero 2 hs)))]
  simp only [derivative_mul]; ring

/-- `d/dx` annihilates `0`. -/
theorem ratFuncDeriv_zero : ratFuncDeriv (0 : RatFunc K) = 0 := by
  have h := ratFuncDeriv_algebraMap (0 : K[X]); simpa using h

/-- `d/dx` as an additive homomorphism on `K(x)` (additivity + `0 ↦ 0`). -/
noncomputable def ratFuncDerivHom : RatFunc K →+ RatFunc K where
  toFun := ratFuncDeriv
  map_zero' := ratFuncDeriv_zero
  map_add' := ratFuncDeriv_add

end DeepWiki.SymbolicIntegration
