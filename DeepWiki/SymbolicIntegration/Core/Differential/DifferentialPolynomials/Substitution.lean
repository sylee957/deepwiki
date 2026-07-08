import DeepWiki.SymbolicIntegration.Core.Differential.DifferentialPolynomials.Base

/-! # Differential polynomial substitution

Substitution and point-evaluation API for differential polynomials. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial MvPolynomial

variable {K : Type*} [Field K]

/-- The differential substitution hom `DiffPoly K →ₐ[K] K[x]` sending `x` to `X` and `u^(k)` to `Diα^(k)`. -/
noncomputable def diffSubst (Diα : K[X]) : DiffPoly K →ₐ[K] K[X] :=
  MvPolynomial.aeval fun v => match v with
    | none => Polynomial.X
    | some k => derivative^[k] Diα

/-- `diffSubst` sends the base variable to `X`. -/
@[simp] theorem diffSubst_X_none (Diα : K[X]) :
    diffSubst Diα (X none : DiffPoly K) = Polynomial.X := by
  simp [diffSubst]

/-- `diffSubst` sends `u^(k)` to the `k`-th derivative of `Diα`. -/
@[simp] theorem diffSubst_X_some (Diα : K[X]) (k : ℕ) :
    diffSubst Diα (X (some k) : DiffPoly K) = derivative^[k] Diα := by
  simp [diffSubst]

/-- `diffSubst` sends constants to constant polynomials. -/
@[simp] theorem diffSubst_C (Diα : K[X]) (a : K) :
    diffSubst Diα (MvPolynomial.C a : DiffPoly K) = Polynomial.C a := by
  simp [diffSubst]

/-- `diffSubst` undoes `dpEmbed` on pure `x`-polynomials. -/
@[simp] theorem diffSubst_dpEmbed (Diα p : K[X]) : diffSubst Diα (dpEmbed p) = p := by
  have h : ((diffSubst Diα : DiffPoly K →ₐ[K] K[X]).toRingHom.comp dpEmbed) = RingHom.id K[X] := by
    apply Polynomial.ringHom_ext
    · intro c; simp [dpEmbed]
    · simp [dpEmbed]
  exact congrArg (fun f : K[X] →+* K[X] => f p) h

/-- `dpEmbed p ≠ 0` for `p ≠ 0`. -/
theorem dpEmbed_ne_zero {p : K[X]} (hp : p ≠ 0) : dpEmbed p ≠ (0 : DiffPoly K) := by
  intro h
  apply hp
  have := congrArg (diffSubst (0 : K[X])) h
  rwa [diffSubst_dpEmbed, map_zero] at this

/-- `diffSubst Diα` carries `ddx` to the polynomial derivative. -/
theorem diffSubst_ddx (Diα : K[X]) (p : DiffPoly K) :
    diffSubst Diα (ddx p) = derivative (diffSubst Diα p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [← MvPolynomial.algebraMap_eq, (ddx (K := K)).map_algebraMap, map_zero,
      AlgHom.commutes, Polynomial.algebraMap_eq, derivative_C]
  | add p q hp hq => rw [map_add, map_add, map_add, derivative_add, hp, hq]
  | mul_X p v hp =>
      have hbase : diffSubst Diα (ddx (X v : DiffPoly K)) = derivative (diffSubst Diα (X v)) := by
        cases v with
        | none => rw [ddx_x, map_one, diffSubst_X_none, derivative_X]
        | some k =>
            rw [show ddx (X (some k) : DiffPoly K) = X (some (k + 1)) from ddx_u k,
              diffSubst_X_some, diffSubst_X_some, ← Function.iterate_succ_apply' derivative k Diα]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp, hbase,
        map_mul, derivative_mul]
      ring

/-- `(aeval f P).eval α = aeval (fun v => (f v).eval α) P`. -/
theorem eval_aeval_diffPoly (f : Option ℕ → K[X]) (α : K) (P : DiffPoly K) :
    Polynomial.eval α (MvPolynomial.aeval f P) = MvPolynomial.aeval (fun v => (f v).eval α) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

/-- The point substitution `x ↦ α`, `u^(k) ↦ (Diα^(k)).eval α`. -/
noncomputable def substEvalAt (Diα : K[X]) (α : K) : Option ℕ → K := fun v =>
  match v with
  | none => α
  | some k => (derivative^[k] Diα).eval α

/-- `(diffSubst Diα P).eval α = aeval (substEvalAt Diα α) P`. -/
theorem eval_diffSubst (Diα : K[X]) (α : K) (P : DiffPoly K) :
    Polynomial.eval α (diffSubst Diα P) = MvPolynomial.aeval (substEvalAt Diα α) P := by
  rw [diffSubst, eval_aeval_diffPoly]
  have hfun : (fun v => Polynomial.eval α
        (match v with | (none : Option ℕ) => Polynomial.X | some k => derivative^[k] Diα))
      = substEvalAt Diα α := by
    funext v
    cases v with
    | none => simp [substEvalAt]
    | some k => simp [substEvalAt]
  exact congrArg (fun f => MvPolynomial.aeval f P) hfun

end DeepWiki.SymbolicIntegration
