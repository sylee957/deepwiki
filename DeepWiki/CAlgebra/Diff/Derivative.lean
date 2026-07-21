import DeepWiki.CAlgebra.Poly.Operations
import DeepWiki.CAlgebra.Diff.Basic

/-! # Formal derivative of dense polynomials

The computable formal derivative of `DensePoly R` (`coeff k = (k+1)·coeff (k+1)`), exposed
**only** through Mathlib's differential-algebra interface: a computable `Derivation ℤ`
packaged as a **scoped** `Differential (DensePoly R)` instance (`open scoped FormalDiff`),
with the `′`-satellites and the bridge into `Polynomial.derivative`. The raw recursion is
private — `p′` is the public spelling, and it computes. The instance is scoped because the
formal derivative (constant coefficients) is only one derivation on `DensePoly R`: a
differential coefficient ring will induce an extension derivation in its own scope. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

namespace DensePoly

/-- The formal derivative: `∑ aₙ xⁿ ↦ ∑ (n+1)·a₍ₙ₊₁₎ xⁿ` (implementation; use `p′`). -/
private def deriv (p : DensePoly R) : DensePoly R :=
  ofList ((List.range p.size).map (fun k => ((k + 1 : ℕ) : R) * p.coeff (k + 1)))

/-- The `n`th coefficient of the derivative is `(n+1)·(coeff (n+1))`. -/
private theorem coeff_deriv (p : DensePoly R) (n : Nat) :
    (deriv p).coeff n = ((n + 1 : ℕ) : R) * p.coeff (n + 1) := by
  rw [deriv, coeff_ofList_map_range]
  by_cases h : n < p.size
  · rw [if_pos h]
  · rw [if_neg h, coeff_eq_zero_of_size_le p (by omega), mul_zero]

private theorem toPolynomial_deriv_impl (p : DensePoly R) :
    toPolynomial (deriv p) = (toPolynomial p).derivative := by
  ext n
  rw [coeff_toPolynomial, coeff_deriv, Polynomial.coeff_derivative, coeff_toPolynomial]
  push_cast
  ring

private theorem deriv_add_impl (p q : DensePoly R) : deriv (p + q) = deriv p + deriv q := by
  apply toPolynomial_injective
  simp only [toPolynomial_deriv_impl, toPolynomial_add, Polynomial.derivative_add]

private theorem deriv_mul_impl (p q : DensePoly R) :
    deriv (p * q) = deriv p * q + p * deriv q := by
  apply toPolynomial_injective
  simp only [toPolynomial_deriv_impl, toPolynomial_mul, toPolynomial_add,
    Polynomial.derivative_mul]

/-- The formal derivative as a computable `ℤ`-derivation on `DensePoly R`. -/
def densePolyDerivation : Derivation ℤ (DensePoly R) (DensePoly R) where
  toLinearMap := (AddMonoidHom.mk' deriv deriv_add_impl).toIntLinearMap
  map_one_eq_zero' := by
    apply toPolynomial_injective
    show toPolynomial (deriv 1) = toPolynomial 0
    simp only [toPolynomial_deriv_impl, toPolynomial_one, Polynomial.derivative_one,
      toPolynomial_zero]
  leibniz' a b := by
    show deriv (a * b) = a • deriv b + b • deriv a
    rw [deriv_mul_impl, smul_eq_mul, smul_eq_mul]; ring

end DensePoly

end DeepWiki.CAlgebra

namespace FormalDiff

/-- The formal derivative as the differential structure of `DensePoly R` (scoped: coefficients
are treated as constants — open `FormalDiff` to use it; `p′` computes). -/
scoped instance {R : Type u} [CommRing R] [DecidableEq R] :
    Differential (DeepWiki.CAlgebra.DensePoly R) :=
  ⟨DeepWiki.CAlgebra.DensePoly.densePolyDerivation⟩

end FormalDiff

namespace DeepWiki.CAlgebra

variable {R : Type u} [CommRing R] [DecidableEq R]

namespace DensePoly

open scoped Differential FormalDiff

/-- The derivative loses at least one stored coefficient. -/
theorem size_deriv_le (p : DensePoly R) : (p′).size ≤ p.size - 1 :=
  size_le_of_coeff_zero fun j hj => by
    show (deriv p).coeff j = 0
    rw [coeff_deriv, coeff_eq_zero_of_size_le p (by omega), mul_zero]

/-- The derivative is additive. -/
@[simp] theorem deriv_add (p q : DensePoly R) : (p + q)′ = p′ + q′ := deriv_add_impl p q

/-- Leibniz rule: `(p*q)′ = p′*q + p*q′`. -/
theorem deriv_mul (p q : DensePoly R) : (p * q)′ = p′ * q + p * q′ := deriv_mul_impl p q

end DensePoly

open scoped Differential FormalDiff

/-- `toPolynomial` carries the dense derivative to `Polynomial.derivative`. -/
@[simp] theorem toPolynomial_deriv (p : DensePoly R) :
    toPolynomial (p′) = (toPolynomial p).derivative :=
  DensePoly.toPolynomial_deriv_impl p

/-- `toPolynomial` is a differential-ring morphism for the scoped `′` on both sides. -/
theorem toPolynomial_differential (p : DensePoly R) :
    toPolynomial (p′) = (toPolynomial p)′ := toPolynomial_deriv p

namespace DensePoly

/-- The derivative of the zero polynomial is zero. -/
@[simp] theorem deriv_zero : (0 : DensePoly R)′ = 0 := by
  apply toPolynomial_injective
  simp only [toPolynomial_deriv, toPolynomial_zero, Polynomial.derivative_zero]

/-- The derivative commutes with negation. -/
@[simp] theorem deriv_neg (p : DensePoly R) : (-p)′ = -p′ := by
  apply toPolynomial_injective
  simp only [toPolynomial_deriv, toPolynomial_neg, Polynomial.derivative_neg]

/-- The derivative of the constant `1` is zero. -/
@[simp] theorem deriv_one : (1 : DensePoly R)′ = 0 := by
  apply toPolynomial_injective
  simp only [toPolynomial_deriv, toPolynomial_one, Polynomial.derivative_one, toPolynomial_zero]

/-- Constant multiples pass through the derivative. -/
theorem deriv_C_mul (a : R) (p : DensePoly R) : (C a * p)′ = C a * p′ := by
  apply toPolynomial_injective
  simp

/-- The power rule, successor form (subtraction-free exponents). -/
theorem deriv_pow_succ (p : DensePoly R) (n : ℕ) :
    (p ^ (n + 1))′ = C ((n + 1 : ℕ) : R) * p ^ n * p′ := by
  apply toPolynomial_injective
  have hpow : ∀ k, toPolynomial (p ^ k) = toPolynomial p ^ k := fun k => by
    simpa using map_pow (equiv (R := R)) p k
  simp only [toPolynomial_deriv, toPolynomial_mul, toPolynomial_C, hpow,
    Polynomial.derivative_pow_succ, Nat.cast_add, Nat.cast_one]

end DensePoly

namespace DensePoly

section Field

variable {K : Type u} [Field K] [DecidableEq K] [CharZero K]

/-- The polynomial antiderivative with zero constant term (characteristic zero):
`∑ aₖ xᵏ ↦ ∑ aₖ/(k+1) · xᵏ⁺¹`. -/
def polyIntegrate (p : DensePoly K) : DensePoly K :=
  ofList ((List.range (p.size + 1)).map fun k =>
    if k = 0 then 0 else p.coeff (k - 1) / ((k : ℕ) : K))

/-- `polyIntegrate` is a right inverse of the derivative. -/
@[simp] theorem polyIntegrate_deriv (p : DensePoly K) : (polyIntegrate p)′ = p := by
  apply toPolynomial_injective
  rw [toPolynomial_deriv]
  ext n
  rw [Polynomial.coeff_derivative, coeff_toPolynomial, coeff_toPolynomial, polyIntegrate,
    coeff_ofList_map_range]
  by_cases h : n < p.size
  · rw [if_pos (by omega : n + 1 < p.size + 1), if_neg (by omega : ¬ n + 1 = 0)]
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [div_mul_cancel₀]
    exact_mod_cast Nat.succ_ne_zero n
  · rw [if_neg (by omega : ¬ n + 1 < p.size + 1), zero_mul,
      coeff_eq_zero_of_size_le p (by omega)]

end Field

end DensePoly

/-- Validation: `′` computes through the bridge and is Leibniz. -/
example (p q : DensePoly R) :
    toPolynomial (p′) = (toPolynomial p).derivative ∧ (p * q)′ = p′ * q + p * q′ :=
  ⟨toPolynomial_deriv p, DensePoly.deriv_mul p q⟩

end DeepWiki.CAlgebra
