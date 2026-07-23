import DeepWiki.SymbolicIntegration.DifferentialAlgebra.PolynomialDerivative
import DeepWiki.SymbolicIntegration.LaurentCoefficients.Engine
import DeepWiki.SymbolicIntegration.LaurentCoefficients.RootInvariant

/-! # Laurent root substitution

Root-evaluation bridges for the `Qᵢⱼ` substitution in the Laurent-coefficient engine.
-/

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

/-! ## The `i=1` specialization of `Qᵢⱼ` -/

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

end DeepWiki.SymbolicIntegration
