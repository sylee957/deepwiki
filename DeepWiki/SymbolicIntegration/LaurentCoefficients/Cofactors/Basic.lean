import DeepWiki.SymbolicIntegration.Core.Polynomial.Diophantine
import DeepWiki.SymbolicIntegration.Core.Polynomial.Basic

/-! # Laurent cofactor data

Complementary denominator factors and Bezout cofactors for Laurent coefficients.
-/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- The cofactor `Eᵢ = D /ₘ Dᵢ^i`: the part of `D` complementary to the prime power `Dᵢ^i`. -/
noncomputable def laurentE (D Di : K[X]) (i : ℕ) : K[X] := D /ₘ Di ^ i

/-- `laurentE D Di 1 = D /ₘ Di`: the cofactor `E₁` at multiplicity one. -/
theorem laurentE_one (D Di : K[X]) : laurentE D Di 1 = D /ₘ Di := by
  rw [laurentE, pow_one]

/-- The Bézout cofactor `Bᵢ` of `Eᵢ` in `Eᵢ·Bᵢ + Dᵢ·(…) = 1`, so `Bᵢ·Eᵢ ≡ 1 (mod Dᵢ)`. -/
noncomputable def bezoutE (D Di : K[X]) (i : ℕ) : K[X] :=
  (diophantineSolve (laurentE D Di i) Di 1).1

/-- The `Bᵢ` congruence: for `IsCoprime Eᵢ Dᵢ`, `(bezoutE D Di i * laurentE D Di i) %ₘ Di = 1 %ₘ Di`. -/
theorem bezoutE_mul_laurentE_modByMonic (D Di : K[X]) (i : ℕ) (hDi : Di.Monic)
    (hcop : IsCoprime (laurentE D Di i) Di) :
    (bezoutE D Di i * laurentE D Di i) %ₘ Di = (1 : K[X]) %ₘ Di := by
  have hspec := diophantineSolve_spec hcop (1 : K[X])
  -- `Eᵢ·Bᵢ + Dᵢ·s = 1`, so `Bᵢ·Eᵢ = 1 − Dᵢ·s`, and `Dᵢ·s ≡ 0 (mod Dᵢ)`
  have hkey : bezoutE D Di i * laurentE D Di i
      = (1 : K[X]) - Di * (diophantineSolve (laurentE D Di i) Di 1).2 := by
    rw [bezoutE]; linear_combination hspec
  rw [hkey, sub_modByMonic, self_mul_modByMonic hDi, sub_zero]

/-- `Bᵢ(α)·Eᵢ(α) = 1` at a root `α` of the monic `Dᵢ` (so `Bᵢ(α) = 1/Eᵢ(α)`). -/
theorem bezoutE_mul_laurentE_eval {D Di : K[X]} {α : K} (i : ℕ) (hDi : Di.Monic)
    (hα : Di.eval α = 0) (hcop : IsCoprime (laurentE D Di i) Di) :
    (bezoutE D Di i).eval α * (laurentE D Di i).eval α = 1 := by
  have h := bezoutE_mul_laurentE_modByMonic D Di i hDi hcop
  have := congrArg (fun p => p.eval α) h
  simpa [eval_modByMonic_of_root hDi hα, Polynomial.eval_mul] using this

end DeepWiki.SymbolicIntegration
