import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Derivative

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

end DeepWiki.SymbolicIntegration
