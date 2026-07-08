import DeepWiki.SymbolicIntegration.LaurentCoefficients.Cofactors.Basic

/-! # Laurent cofactor root evaluation

Root-evaluation consequences of the Laurent Bezout cofactor congruences.
-/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- `(P %ₘ Dᵢ).eval α = P.eval α` at a root `α` of a monic `Dᵢ`: the `%ₘ` reduction is invisible there. -/
theorem eval_modByMonic_of_root {P Di : K[X]} {α : K} (_hDi : Di.Monic) (hα : Di.eval α = 0) :
    (P %ₘ Di).eval α = P.eval α := by
  conv_rhs => rw [← modByMonic_add_div P Di]
  rw [Polynomial.eval_add, Polynomial.eval_mul, hα, zero_mul, add_zero]

/-- `Bᵢ(α)·Eᵢ(α) = 1` at a root `α` of the monic `Dᵢ` (so `Bᵢ(α) = 1/Eᵢ(α)`). -/
theorem bezoutE_mul_laurentE_eval {D Di : K[X]} {α : K} (i : ℕ) (hDi : Di.Monic)
    (hα : Di.eval α = 0) (hcop : IsCoprime (laurentE D Di i) Di) :
    (bezoutE D Di i).eval α * (laurentE D Di i).eval α = 1 := by
  have h := bezoutE_mul_laurentE_modByMonic D Di i hDi hcop
  have := congrArg (fun p => p.eval α) h
  simpa [eval_modByMonic_of_root hDi hα, Polynomial.eval_mul] using this

/-- `Cᵢ(α)·Dᵢ'(α) = 1` at a root `α` of the monic `Dᵢ` (so `Cᵢ(α) = 1/Dᵢ'(α)`). -/
theorem bezoutDeriv_mul_derivative_eval {Di : K[X]} {α : K} (hDi : Di.Monic)
    (hα : Di.eval α = 0) (hcop : IsCoprime (derivative Di) Di) :
    (bezoutDeriv Di).eval α * (derivative Di).eval α = 1 := by
  have h := bezoutDeriv_mul_derivative_modByMonic Di hDi hcop
  have := congrArg (fun p => p.eval α) h
  simpa [eval_modByMonic_of_root hDi hα, Polynomial.eval_mul] using this

end DeepWiki.SymbolicIntegration
