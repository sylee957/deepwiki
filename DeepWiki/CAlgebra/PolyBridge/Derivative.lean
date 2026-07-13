import DeepWiki.CAlgebra.Poly.Derivative
import DeepWiki.CAlgebra.PolyBridge.Ring
import Mathlib.Algebra.Polynomial.Derivative

/-! # Mathlib bridge for the formal derivative

`toPolynomial` intertwines the computable `deriv` with `Polynomial.derivative`, and the derivation
laws (additivity, Leibniz, …) are proved by transport through that bridge. Kept out of the
`Poly/Derivative.lean` core so it stays Mathlib-correspondence-free. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- `toPolynomial` intertwines the formal derivative with Mathlib's `Polynomial.derivative`. -/
@[simp] theorem toPolynomial_deriv (p : DensePoly R) :
    toPolynomial (DensePoly.deriv p) = (toPolynomial p).derivative := by
  ext n
  rw [coeff_toPolynomial, DensePoly.coeff_deriv, Polynomial.coeff_derivative, coeff_toPolynomial]
  push_cast
  ring

namespace DensePoly

/-- The derivative is additive. -/
@[simp] theorem deriv_add (p q : DensePoly R) : deriv (p + q) = deriv p + deriv q := by
  apply toPolynomial_injective
  simp only [toPolynomial_deriv, toPolynomial_add, Polynomial.derivative_add]

/-- Leibniz rule: `deriv (p*q) = deriv p * q + p * deriv q`. -/
theorem deriv_mul (p q : DensePoly R) : deriv (p * q) = deriv p * q + p * deriv q := by
  apply toPolynomial_injective
  simp only [toPolynomial_deriv, toPolynomial_mul, toPolynomial_add, Polynomial.derivative_mul]

/-- The derivative of the zero polynomial is zero. -/
@[simp] theorem deriv_zero : deriv (0 : DensePoly R) = 0 := by
  apply toPolynomial_injective
  simp only [toPolynomial_deriv, toPolynomial_zero, Polynomial.derivative_zero]

/-- The derivative commutes with negation. -/
@[simp] theorem deriv_neg (p : DensePoly R) : deriv (-p) = -deriv p := by
  apply toPolynomial_injective
  simp only [toPolynomial_deriv, toPolynomial_neg, Polynomial.derivative_neg]

/-- The derivative of the constant `1` is zero. -/
@[simp] theorem deriv_one : deriv (1 : DensePoly R) = 0 := by
  apply toPolynomial_injective
  simp only [toPolynomial_deriv, toPolynomial_one, Polynomial.derivative_one, toPolynomial_zero]

end DensePoly

/-- Validation: the dense derivative matches Mathlib's polynomial derivative through the bridge,
and satisfies the Leibniz rule. -/
example (p q : DensePoly R) :
    toPolynomial (DensePoly.deriv p) = (toPolynomial p).derivative ∧
    DensePoly.deriv (p * q) = DensePoly.deriv p * q + p * DensePoly.deriv q :=
  ⟨toPolynomial_deriv p, DensePoly.deriv_mul p q⟩

end DeepWiki.CAlgebra
