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

/-- Validation: the dense derivative matches Mathlib's polynomial derivative through the bridge. -/
example (p : DensePoly R) : toPolynomial (DensePoly.deriv p) = (toPolynomial p).derivative :=
  toPolynomial_deriv p

end DeepWiki.CAlgebra
