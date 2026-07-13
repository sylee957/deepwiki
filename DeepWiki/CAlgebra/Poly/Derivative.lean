import DeepWiki.CAlgebra.Poly.Operations

/-! # Formal derivative of dense polynomials — carrier

`deriv p` is the computable formal derivative (`coeff k = (k+1)·coeff (k+1)`). Its Mathlib
correspondence (`toPolynomial_deriv` into `Polynomial.derivative`) and the derivation laws proved by
transport live in `PolyBridge/Derivative.lean`, keeping this core module correspondence-free. -/

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

end DeepWiki.CAlgebra
