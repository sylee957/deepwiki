import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Derivation.DifferentialRing
import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncFractions
import DeepWiki.SymbolicIntegration.DifferentialAlgebra

/-! # The derivative `d/dx` on rational functions `K(x)`
Builds `d/dx` on `RatFunc K` via the quotient rule `(p/q)' = (p'q − pq')/q²`, proves its derivation
laws, and makes `RatFunc K` a `Differential` field. -/

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

/-- **Additivity of `d/dx`** on `K(x)`: `(x + y)' = x' + y'`. -/
theorem ratFuncDeriv_add (x y : RatFunc K) :
    ratFuncDeriv (x + y) = ratFuncDeriv x + ratFuncDeriv y := by
  induction x using RatFunc.induction_on' with | _ p q hq =>
  induction y using RatFunc.induction_on' with | _ r s hs =>
  rw [ratFunc_mk_add_mk p r hq hs, ratFuncDeriv_mk, ratFuncDeriv_mk, ratFuncDeriv_mk,
    ratFunc_mk_add_mk _ _ (pow_ne_zero 2 hq) (pow_ne_zero 2 hs),
    RatFunc.mk_eq_mk (pow_ne_zero 2 (mul_ne_zero hq hs)) (mul_ne_zero (pow_ne_zero 2 hq)
      (pow_ne_zero 2 hs))]
  simp only [derivative_add, derivative_mul]; ring

/-- **Leibniz rule for `d/dx`** on `K(x)`: `(x·y)' = x'·y + x·y'`. -/
theorem ratFuncDeriv_mul (x y : RatFunc K) :
    ratFuncDeriv (x * y) = ratFuncDeriv x * y + x * ratFuncDeriv y := by
  induction x using RatFunc.induction_on' with | _ p q hq =>
  induction y using RatFunc.induction_on' with | _ r s hs =>
  rw [ratFunc_mk_mul_mk p q r s, ratFuncDeriv_mk, ratFuncDeriv_mk, ratFuncDeriv_mk,
    ratFunc_mk_mul_mk (derivative p * q - p * derivative q) (q ^ 2) r s,
    ratFunc_mk_mul_mk p q (derivative r * s - r * derivative s) (s ^ 2),
    ratFunc_mk_add_mk _ _ (mul_ne_zero (pow_ne_zero 2 hq) hs) (mul_ne_zero hq (pow_ne_zero 2 hs)),
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

/-- `d/dx` kills constants `C c` (`c : K`): `(C c)' = 0`. -/
theorem ratFuncDeriv_C_eq_zero (c : K) : ratFuncDeriv (RatFunc.C c) = 0 := by
  rw [← RatFunc.algebraMap_C, ratFuncDeriv_algebraMap, derivative_C, map_zero]

/-- **`K`-linearity of `d/dx`** on `K(x)`: `(c • x)' = c • x'` for a constant `c : K`. -/
theorem ratFuncDeriv_smul (c : K) (x : RatFunc K) :
    ratFuncDeriv (c • x) = c • ratFuncDeriv x := by
  rw [RatFunc.smul_eq_C_mul, ratFuncDeriv_mul, ratFuncDeriv_C_eq_zero, zero_mul, zero_add,
    ← RatFunc.smul_eq_C_mul]

/-- `d/dx` as a `K`-derivation on `K(x)` (the `Algebra K (RatFunc K)` is unambiguous, so no diamond). -/
noncomputable def ratFuncKDeriv : Derivation K (RatFunc K) (RatFunc K) :=
  Derivation.mk'
    { toFun := ratFuncDeriv, map_add' := ratFuncDeriv_add,
      map_smul' := fun c x => by simpa using ratFuncDeriv_smul c x }
    fun a b => by simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]; rw [ratFuncDeriv_mul]; ring

/-- `K(x)` is a differential field with derivation `d/dx`. -/
noncomputable instance : Differential (RatFunc K) :=
  letI : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
  ⟨ratFuncKDeriv.restrictScalars ℤ⟩

open scoped Differential in
/-- `x`-constants have derivative zero: `(algebraMap (C c))′ = 0` in `K(x)`. -/
theorem deriv_algebraMap_C (c : K) :
    (algebraMap K[X] (RatFunc K) (C c))′ = 0 := by
  rw [show (algebraMap K[X] (RatFunc K) (C c))′
      = ratFuncDeriv (algebraMap K[X] (RatFunc K) (C c)) from rfl,
    ratFuncDeriv_algebraMap, derivative_C, map_zero]

open scoped Differential in
/-- `logDeriv` kills a nonzero `x`-constant factor: for a nonzero constant `c ∈ K` (a `C`-constant, hence
`x`-derivative `0`) and a nonzero polynomial `f ∈ K[x]`, `logDeriv (algebraMap (C c · f)) = logDeriv (algebraMap f)`
over `K(x)`. General identity (associate-invariance of `logDeriv` under constant scaling); the `log(c)` term is
`x`-constant so it drops. -/
theorem logDeriv_algebraMap_C_mul_eq (c : K) (hc : c ≠ 0) (f : K[X]) (hf : f ≠ 0) :
    Differential.logDeriv (algebraMap K[X] (RatFunc K) (C c * f))
      = Differential.logDeriv (algebraMap K[X] (RatFunc K) f) := by
  have hcne : algebraMap K[X] (RatFunc K) (C c) ≠ 0 := by
    simpa [map_eq_zero_iff _ (RatFunc.algebraMap_injective K), C_eq_zero] using hc
  have hfne : algebraMap K[X] (RatFunc K) f ≠ 0 := by
    simpa [map_eq_zero_iff _ (RatFunc.algebraMap_injective K)] using hf
  have hlogc : Differential.logDeriv (algebraMap K[X] (RatFunc K) (C c)) = 0 := by
    rw [Differential.logDeriv_eq_zero,
      show (algebraMap K[X] (RatFunc K) (C c))′ = ratFuncDeriv (algebraMap K[X] (RatFunc K) (C c))
        from rfl, ratFuncDeriv_algebraMap, derivative_C, map_zero]
  rw [map_mul, Differential.logDeriv_mul _ _ hcne hfne, hlogc, zero_add]

end DeepWiki.SymbolicIntegration
