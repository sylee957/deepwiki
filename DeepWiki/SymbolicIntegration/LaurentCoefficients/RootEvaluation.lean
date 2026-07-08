import DeepWiki.SymbolicIntegration.Core.Differential.PolynomialDerivatives
import DeepWiki.SymbolicIntegration.LaurentCoefficients.Engine
import DeepWiki.SymbolicIntegration.LaurentCoefficients.RootInvariant

/-! # Laurent root evaluation

Root-evaluation bridges for the Laurent-coefficient engine output. -/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## The root-evaluation `Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), …)` -/

/-- `(laurentSubst ((x−α)·Diα) (some k)).eval α = (derivative^[k] Diα).eval α`: the substitution's root
value. -/
theorem eval_laurentSubst_some [CharZero K] (Diα : K[X]) (α : K) (k : ℕ) :
    (laurentSubst ((Polynomial.X - Polynomial.C α) * Diα) (some k)).eval α
      = (derivative^[k] Diα).eval α := by
  unfold laurentSubst
  rw [Polynomial.eval_mul, Polynomial.eval_C, eval_iterate_derivative_X_sub_C_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_add_one_ne_zero (R := K) k), one_mul]

/-- `Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), …)`: at a root `α` of `Dᵢ = (x−α)·Dᵢ,α`, the `Qᵢⱼ` substitution evaluates
to `aeval (substEvalAt Diα α) (laurentNum …)`. -/
theorem laurentQ_eval_at_root [CharZero K] (A D Diα : K[X]) (α : K) (i j : ℕ) :
    (laurentQ A D ((Polynomial.X - Polynomial.C α) * Diα) i j).eval α
      = MvPolynomial.aeval (substEvalAt Diα α)
          (laurentNum A (laurentE D ((Polynomial.X - Polynomial.C α) * Diα) i) i (i - j)) := by
  unfold laurentQ
  rw [eval_aeval_diffPoly]
  have hfg : (fun v => (laurentSubst ((Polynomial.X - Polynomial.C α) * Diα) v).eval α) = substEvalAt Diα α := by
    funext v
    cases v with
    | none => simp [laurentSubst, substEvalAt]
    | some k => rw [eval_laurentSubst_some]; rfl
  rw [hfg]

/-! ## The root-value bridge `σα(Pᵢ,d)(α) = Qᵢⱼ(α)` -/

/-- The bridge `(σα(laurentNum …)).eval α = (laurentQ …).eval α`: both are
`aeval (substEvalAt Diα α) (laurentNum …)`. -/
theorem eval_diffSubst_laurentNum_eq_laurentQ_eval [CharZero K] (A D Diα : K[X]) (α : K) (i j : ℕ) :
    Polynomial.eval α
        (diffSubst Diα (laurentNum A (laurentE D ((Polynomial.X - Polynomial.C α) * Diα) i) i (i - j)))
      = (laurentQ A D ((Polynomial.X - Polynomial.C α) * Diα) i j).eval α := by
  rw [eval_diffSubst, laurentQ_eval_at_root]

/-! ## The `i=1` residue: `H₁₁(α) = A(α)/D'(α)` -/

/-- `aeval (laurentSubst Di) (dpEmbed p) = p`: the `Qᵢⱼ` substitution undoes `dpEmbed` on a pure-`x`
polynomial. -/
theorem aeval_laurentSubst_dpEmbed (Di p : K[X]) :
    aeval (laurentSubst Di) (dpEmbed p) = p := by
  have h : ((aeval (laurentSubst Di) : DiffPoly K →ₐ[K] K[X]).toRingHom.comp dpEmbed)
      = RingHom.id K[X] := by
    apply Polynomial.ringHom_ext
    · intro c; simp [dpEmbed]
    · simp [dpEmbed, laurentSubst]
  exact congrArg (fun f : K[X] →+* K[X] => f p) h

/-- `Q₁₁ = A`: at `i=j=1` the derivative count is `0`, so `laurentQ A D Di 1 1 = A`. -/
theorem laurentQ_one_one (A D Di : K[X]) : laurentQ A D Di 1 1 = A := by
  rw [laurentQ, Nat.sub_self, laurentNum_zero, aeval_laurentSubst_dpEmbed]

/-- `laurentE D Di 1 = D /ₘ Di`: the cofactor `E₁` at multiplicity one. -/
theorem laurentE_one (D Di : K[X]) : laurentE D Di 1 = D /ₘ Di := by
  rw [laurentE, pow_one]

open scoped Classical in
/-- `laurentH A D Di 1 1 = (A · bezoutE D Di 1 · bezoutDeriv Di) %ₘ Di`: the `i=1` engine output. -/
theorem laurentH_one_one (A D Di : K[X]) :
    laurentH A D Di 1 1 = (A * bezoutE D Di 1 * bezoutDeriv Di) %ₘ Di := by
  rw [laurentH, laurentQ_one_one]
  norm_num

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
