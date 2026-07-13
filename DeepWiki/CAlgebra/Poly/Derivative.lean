import DeepWiki.CAlgebra.PolyBridge.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-! # Formal derivative of dense polynomials

`deriv p` is the computable formal derivative (`coeff k = (k+1)·coeff (k+1)`), bridging to Mathlib's
`Polynomial.derivative` via `toPolynomial`. Derivations are the core operation the Risch engine is
built on. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

namespace DensePoly

/-- The formal derivative: `∑ aₙ xⁿ ↦ ∑ (n+1)·a₍ₙ₊₁₎ xⁿ`. -/
def deriv (p : DensePoly R) : DensePoly R :=
  ofList ((List.range p.size).map (fun k => ((k + 1 : ℕ) : R) * p.coeff (k + 1)))

/-- The `n`th coefficient of the derivative is `(n+1)·(coeff (n+1))`. -/
@[simp] theorem coeff_deriv (p : DensePoly R) (n : Nat) :
    (deriv p).coeff n = ((n + 1 : ℕ) : R) * p.coeff (n + 1) := by
  rw [deriv, coeff_ofList_map_range]
  by_cases h : n < p.size
  · rw [if_pos h]
  · rw [if_neg h, coeff_eq_zero_of_size_le p (by omega), mul_zero]

end DensePoly

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

/-- The derivative of a constant is zero. -/
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
