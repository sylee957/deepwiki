import Mathlib.Algebra.Polynomial.Derivative
import DeepWiki.SymbolicIntegration.Core.Polynomial.SquarefreeParts

/-! # Polynomial squarefree-part derivatives

Derivative formulas for multiplicity-indexed squarefree-factorization parts.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

section SquarefreePartDerivatives
open UniqueFactorizationMonoid
variable {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D]

open Classical in
/-- The derivative of a deflation in factored form:
`d(A⁻ᵏ)/dx = ∑ₐ (∏_{b ≠ a} Aᵦ^(b−k)) · (a−k)·Aₐ^(a−k−1)·dAₐ/dx`. -/
theorem derivative_deflation (A : D[X]) (k : ℕ) :
    derivative (deflation A k)
      = ∑ a ∈ (normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P),
        (∏ b ∈ ((normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P)).erase a, (sqfreeFactPart A b) ^ (b - k))
        * (C ((a - k : ℕ) : D) * (sqfreeFactPart A a) ^ (a - k - 1)
          * derivative (sqfreeFactPart A a)) := by
  rw [deflation_eq_prod_sqfreeFactPart A k, derivative_prod_finset]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [derivative_pow]

end SquarefreePartDerivatives

end DeepWiki.SymbolicIntegration
