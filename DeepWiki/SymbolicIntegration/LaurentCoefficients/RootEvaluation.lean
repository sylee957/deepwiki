import DeepWiki.SymbolicIntegration.LaurentCoefficients.RootSubstitution

/-! # Laurent root evaluation

Root-evaluation bridges for the Laurent-coefficient engine output `Hᵢⱼ`. -/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## The `i=1` residue: `H₁₁(α) = A(α)/D'(α)` -/

/-- `laurentE D Di 1 = D /ₘ Di`: the cofactor `E₁` at multiplicity one. -/
theorem laurentE_one (D Di : K[X]) : laurentE D Di 1 = D /ₘ Di := by
  rw [laurentE, pow_one]

open scoped Classical in
/-- `laurentH A D Di 1 1 = (A · bezoutE D Di 1 · bezoutDeriv Di) %ₘ Di`: the `i=1` engine output. -/
theorem laurentH_one_one (A D Di : K[X]) :
    laurentH A D Di 1 1 = (A * bezoutE D Di 1 * bezoutDeriv Di) %ₘ Di := by
  rw [laurentH, laurentQ_one_one]
  norm_num

/-- The general engine-output evaluation
`(laurentH A D Di i j).eval α = Qᵢⱼ(α)·(1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}` at a root `α` of the monic
`Dᵢ`, using `Bᵢ(α) = 1/Eᵢ(α)`, `Cᵢ(α) = 1/Dᵢ'(α)`. -/
theorem eval_laurentH {A D Di : K[X]} {α : K} (i j : ℕ) (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di) :
    (laurentH A D Di i j).eval α
      = (laurentQ A D Di i j).eval α * (1 / (laurentE D Di i).eval α) ^ (i - j + 1)
          * (1 / (derivative Di).eval α) ^ (2 * i - j) := by
  rw [laurentH, eval_modByMonic_of_root hDi hα, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_pow]
  have hB : (bezoutE D Di i).eval α = 1 / (laurentE D Di i).eval α :=
    eq_one_div_of_mul_eq_one_left (bezoutE_mul_laurentE_eval i hDi hα hcopE)
  have hC : (bezoutDeriv Di).eval α = 1 / (derivative Di).eval α :=
    eq_one_div_of_mul_eq_one_left (bezoutDeriv_mul_derivative_eval hDi hα hcopD)
  rw [hB, hC]

/-- `(laurentH A D Di 1 1).eval α = A(α)/(E₁(α)·D₁'(α))` at a root `α` of the monic `Di`
(with `E₁(α), D₁'(α) ≠ 0`). -/
theorem eval_laurentH_one_one {A D Di : K[X]} {α : K} (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hcopE : IsCoprime (laurentE D Di 1) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hE : (laurentE D Di 1).eval α ≠ 0) (hD' : (derivative Di).eval α ≠ 0) :
    (laurentH A D Di 1 1).eval α
      = A.eval α / ((laurentE D Di 1).eval α * (derivative Di).eval α) := by
  rw [laurentH_one_one, eval_modByMonic_of_root hDi hα, Polynomial.eval_mul, Polynomial.eval_mul]
  have hB : (bezoutE D Di 1).eval α = 1 / (laurentE D Di 1).eval α :=
    eq_one_div_of_mul_eq_one_left (bezoutE_mul_laurentE_eval 1 hDi hα hcopE)
  have hC : (bezoutDeriv Di).eval α = 1 / (derivative Di).eval α :=
    eq_one_div_of_mul_eq_one_left (bezoutDeriv_mul_derivative_eval hDi hα hcopD)
  rw [hB, hC]
  field_simp

/-- `(laurentH A D Di 1 1).eval α = A(α)/D'(α)` for `D = Di·E₁` and `α` a root of the monic `Di`: the
residue of `A/D` at the simple root `α`. -/
theorem eval_laurentH_one_one_eq_residue {A D Di : K[X]} {α : K} (hDi : Di.Monic)
    (hα : Di.eval α = 0) (hfac : D = Di * laurentE D Di 1) (hcopE : IsCoprime (laurentE D Di 1) Di)
    (hcopD : IsCoprime (derivative Di) Di) (hE : (laurentE D Di 1).eval α ≠ 0)
    (hD' : (derivative Di).eval α ≠ 0) :
    (laurentH A D Di 1 1).eval α = A.eval α / (derivative D).eval α := by
  rw [eval_laurentH_one_one hDi hα hcopE hcopD hE hD']
  congr 1
  -- `D'(α) = D₁'(α)·E₁(α)`: differentiate `D = D₁·E₁`, the `D₁·E₁'` term vanishes at the root `α`
  conv_rhs => rw [hfac, derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_mul, hα, zero_mul, add_zero]
  rw [mul_comm]

/-- The engine output from the genuine `hᵢ,α`-numerator: for `Dᵢ = (x−α)·Dᵢ,α`,
`(laurentH A D Di i j).eval α = (diffSubst Diα (laurentNum …)).eval α · (1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}`. -/
theorem eval_laurentH_eq_diffSubst_laurentNum [CharZero K] {A D Di Diα : K[X]} {α : K} (i j : ℕ)
    (hDi : Di.Monic) (hα : Di.eval α = 0) (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di) :
    (laurentH A D Di i j).eval α
      = Polynomial.eval α (diffSubst Diα (laurentNum A (laurentE D Di i) i (i - j)))
        * (1 / (laurentE D Di i).eval α) ^ (i - j + 1)
        * (1 / (derivative Di).eval α) ^ (2 * i - j) := by
  rw [eval_laurentH i j hDi hα hcopE hcopD]
  congr 2
  rw [laurentQ, eval_aeval_diffPoly, eval_diffSubst]
  have hf : (fun v => Polynomial.eval α (laurentSubst Di v)) = substEvalAt Diα α := by
    funext v
    cases v with
    | none => simp [laurentSubst, substEvalAt]
    | some k => subst hfac; rw [eval_laurentSubst_some]; simp [substEvalAt]
  rw [hf]

end DeepWiki.SymbolicIntegration
