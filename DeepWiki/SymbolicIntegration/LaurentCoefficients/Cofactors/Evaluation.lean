import DeepWiki.SymbolicIntegration.Core.Polynomial.RootEvaluation
import DeepWiki.SymbolicIntegration.Core.Polynomial.Diophantine
import DeepWiki.SymbolicIntegration.LaurentCoefficients.Cofactors.Basic

/-! # Laurent cofactor root evaluation

Root-evaluation consequences of the Laurent Bezout cofactor congruences.
-/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- `Bᵢ(α)·Eᵢ(α) = 1` at a root `α` of the monic `Dᵢ` (so `Bᵢ(α) = 1/Eᵢ(α)`). -/
theorem bezoutE_mul_laurentE_eval {D Di : K[X]} {α : K} (i : ℕ) (hDi : Di.Monic)
    (hα : Di.eval α = 0) (hcop : IsCoprime (laurentE D Di i) Di) :
    (bezoutE D Di i).eval α * (laurentE D Di i).eval α = 1 := by
  have h := bezoutE_mul_laurentE_modByMonic D Di i hDi hcop
  have := congrArg (fun p => p.eval α) h
  simpa [eval_modByMonic_of_root hDi hα, Polynomial.eval_mul] using this

end DeepWiki.SymbolicIntegration
