import DeepWiki.SymbolicIntegration.LaurentCoefficients.Assembly.Core

/-! # Laurent coefficient assembly examples

Restatement examples for the engine-form Laurent coefficient assembly API. -/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## Restatement examples -/

/-- The `Bᵢ` congruence `Bᵢ·Eᵢ ≡ 1 (mod Dᵢ)`. -/
example (D Di : K[X]) (i : ℕ) (hDi : Di.Monic) (hcop : IsCoprime (laurentE D Di i) Di) :
    (bezoutE D Di i * laurentE D Di i) %ₘ Di = (1 : K[X]) %ₘ Di :=
  bezoutE_mul_laurentE_modByMonic D Di i hDi hcop

/-- The `Cᵢ` congruence `Cᵢ·Dᵢ' ≡ 1 (mod Dᵢ)`. -/
example (Di : K[X]) (hDi : Di.Monic) (hcop : IsCoprime (derivative Di) Di) :
    (bezoutDeriv Di * derivative Di) %ₘ Di = (1 : K[X]) %ₘ Di :=
  bezoutDeriv_mul_derivative_modByMonic Di hDi hcop

/-- The engine `Hᵢⱼ = Qᵢⱼ·Bᵢ^(i−j+1)·Cᵢ^(2i−j) (mod Dᵢ)`. -/
example (A D Di : K[X]) (i j : ℕ) :
    laurentH A D Di i j
      = (laurentQ A D Di i j * bezoutE D Di i ^ (i - j + 1) * bezoutDeriv Di ^ (2 * i - j)) %ₘ Di :=
  laurentH_def A D Di i j

/-- The `i=1` residue `H₁₁(α) = A(α)/D'(α)` at a simple root `α` of `D`. -/
example {A D Di : K[X]} {α : K} (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : D = Di * laurentE D Di 1) (hcopE : IsCoprime (laurentE D Di 1) Di)
    (hcopD : IsCoprime (derivative Di) Di)
    (hE : (laurentE D Di 1).eval α ≠ 0) (hD' : (derivative Di).eval α ≠ 0) :
    (laurentH A D Di 1 1).eval α = A.eval α / (derivative D).eval α :=
  eval_laurentH_one_one_eq_residue hDi hα hfac hcopE hcopD hE hD'

/-- The recursion as a fraction-field invariant: `(d/dx)^[d] hᵢ = d! · Pᵢ,d/(u^(i+d)·Eᵢ^(d+1))` in
`K(x)⟨u⟩`. -/
example [CharZero K] (A Ei : K[X]) (i : ℕ) (hi : 0 < i) (hEi : Ei ≠ 0) (d : ℕ) :
    (fracKDeriv^[d]) (hFrac A Ei i) = (d.factorial : K) • lFrac A Ei i d := by
  rw [iterate_fracKDeriv_hFrac A Ei i hi hEi d, laurentScale_eq_factorial]

/-- `laurentNum A E₂ 2 1 = A'·u·E₂ − A·(2·u'·E₂ + u·E₂')`: the `i=2, d=1` numerator. -/
example (A E2 : K[X]) :
    laurentNum A E2 2 1
      = ddx (dpEmbed A) * X (some 0) * dpEmbed E2
        - dpEmbed A * ((2 : DiffPoly K) * X (some 1) * dpEmbed E2
                        + (1 : DiffPoly K) * X (some 0) * dpEmbed (derivative E2)) := by
  rw [laurentNum_succ, laurentNum_zero, laurentNumStep]
  norm_num

/-- The root-evaluation step: at a root `α` of `Dᵢ = (x−α)·Dᵢ,α`, `Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), …)`. -/
example [CharZero K] (A D Diα : K[X]) (α : K) (i j : ℕ) :
    (laurentQ A D ((Polynomial.X - Polynomial.C α) * Diα) i j).eval α
      = MvPolynomial.aeval (substEvalAt Diα α)
          (laurentNum A (laurentE D ((Polynomial.X - Polynomial.C α) * Diα) i) i (i - j)) :=
  laurentQ_eval_at_root A D Diα α i j

/-- `σα` is a differential hom: `σα (ddx p) = derivative (σα p)`. -/
example (Diα : K[X]) (p : DiffPoly K) :
    diffSubst Diα (ddx p) = derivative (diffSubst Diα p) :=
  diffSubst_ddx Diα p

/-- The specialized recursion invariant in `K(x)`: `(d/dx)^[d] hᵢ,α = d!·σα(Pᵢ,d)/(Dᵢ,α^{i+d}·Eᵢ^{d+1})`. -/
example [CharZero K] (A Ei Diα : K[X]) (i : ℕ) (hi : 0 < i) (hEi : Ei ≠ 0) (hDiα : Diα ≠ 0) (d : ℕ) :
    (ratFuncKDeriv^[d]) (hFracα A Ei Diα i)
      = (d.factorial : K) • (algebraMap K[X] (RatFunc K) (diffSubst Diα (laurentNum A Ei i d)) /
          algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d)) :=
  iterate_ratFuncKDeriv_hFracα A Ei Diα i hi hEi hDiα d

/-- `hᵢ,α = (A/D)·(x−α)ⁱ` shown at `α = 0`: `hFracα·((x·Dᵢ,α)ⁱ·Eᵢ) = A·xⁱ`. -/
example (A Ei Diα : K[X]) (i : ℕ) (hEi : Ei ≠ 0) (hDiα : Diα ≠ 0) :
    hFracα A Ei Diα i * algebraMap K[X] (RatFunc K) (((Polynomial.X - Polynomial.C (0 : K)) * Diα) ^ i * Ei)
      = algebraMap K[X] (RatFunc K) (A * (Polynomial.X - Polynomial.C (0 : K)) ^ i) := by
  rw [hFracα, lDenomα, Nat.add_zero, Nat.zero_add, pow_one, div_mul_eq_mul_div,
    div_eq_iff (RatFunc.algebraMap_ne_zero (mul_ne_zero (pow_ne_zero _ hDiα) hEi)),
    ← map_mul, ← map_mul]
  congr 1
  rw [mul_pow]; ring

/-- The root-value bridge `σα(Pᵢ,i−j)(α) = Qᵢⱼ(α)`. -/
example [CharZero K] (A D Diα : K[X]) (α : K) (i j : ℕ) :
    Polynomial.eval α
        (diffSubst Diα (laurentNum A (laurentE D ((Polynomial.X - Polynomial.C α) * Diα) i) i (i - j)))
      = (laurentQ A D ((Polynomial.X - Polynomial.C α) * Diα) i j).eval α :=
  eval_diffSubst_laurentNum_eq_laurentQ_eval A D Diα α i j

/-- The engine-output evaluation `Hᵢⱼ(α) = Qᵢⱼ(α)·(1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}`. -/
example {A D Di : K[X]} {α : K} (i j : ℕ) (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di) :
    (laurentH A D Di i j).eval α
      = (laurentQ A D Di i j).eval α * (1 / (laurentE D Di i).eval α) ^ (i - j + 1)
          * (1 / (derivative Di).eval α) ^ (2 * i - j) :=
  eval_laurentH i j hDi hα hcopE hcopD

/-- The cofactor identity at a simple root: `Dᵢ'(α) = Dᵢ,α(α)`. -/
example {Di Diα : K[X]} {α : K} (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα) :
    (derivative Di).eval α = Diα.eval α :=
  eval_derivative_of_X_sub_C_mul hfac

/-- The specialized invariant evaluated at the root:
`(d/dx)^[d] hᵢ,α (α) = d!·σα(Pᵢ,d)(α)/(Dᵢ,α(α)^{i+d}·Eᵢ(α)^{d+1})`. -/
example [CharZero K] {A Ei Diα : K[X]} {α : K} (i : ℕ) (hi : 0 < i) (hEi0 : Ei ≠ 0)
    (hDiα0 : Diα ≠ 0) (hEi : Ei.eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) (d : ℕ) :
    RatFunc.eval (RingHom.id K) α ((ratFuncKDeriv^[d]) (hFracα A Ei Diα i))
      = (d.factorial : K) * (diffSubst Diα (laurentNum A Ei i d)).eval α
          / (lDenomα Ei Diα i d).eval α :=
  eval_ratFuncKDeriv_iterate_hFracα_at_root i hi hEi0 hDiα0 hEi hDiα d

/-- `Hᵢⱼ(α)` is the order-`(i−j)` Taylor coefficient `(1/(i−j)!)·(d/dx)^[i−j] hᵢ,α (α)` of
`hᵢ,α = (A/D)(x−α)ⁱ`. -/
example [CharZero K] {A D Di Diα : K[X]} {α : K} (i j : ℕ) (hi : 0 < i) (hji : j ≤ i)
    (hDi : Di.Monic) (hα : Di.eval α = 0) (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di i).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    (laurentH A D Di i j).eval α
      = (((i - j).factorial : K))⁻¹
          * RatFunc.eval (RingHom.id K) α
              ((ratFuncKDeriv^[i - j]) (hFracα A (laurentE D Di i) Diα i)) :=
  eval_laurentH_eq_taylor_coeff i j hi hji ⟨hDi, hα, hfac, hcopE, hcopD, hEi, hDiα⟩

/-- The `i=j=1` instance: `H₁₁(α) = h₁,α(α)`, the order-`0` Taylor coefficient (function value at `α`). -/
example [CharZero K] {A D Di Diα : K[X]} {α : K} (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di 1) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di 1).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    (laurentH A D Di 1 1).eval α
      = RatFunc.eval (RingHom.id K) α (hFracα A (laurentE D Di 1) Diα 1) := by
  have h := eval_laurentH_eq_taylor_coeff (A := A) (D := D) (Di := Di) (Diα := Diα) (α := α) 1 1
    one_pos le_rfl ⟨hDi, hα, hfac, hcopE, hcopD, hEi, hDiα⟩
  simpa using h

/-! ## Principal parts: subtracting the local term removes the pole -/

/-- `M·W ≡ A (mod (X−α)^i)`: `(X−α)^i ∣ A − M·(localApprox A M α i)`. -/
example (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    (Polynomial.X - Polynomial.C α) ^ i ∣ A - M * localApprox A M α i :=
  localApprox_spec A M i hM

/-- Subtracting the principal part removes the pole: `A/D − localPrincipalPart A M α i = (localRemainder A M α i)/M`,
regular at `α`. -/
example (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    algebraMap K[X] (RatFunc K) A
        / (algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ i * M))
      - localPrincipalPart A M α i
      = algebraMap K[X] (RatFunc K) (localRemainder A M α i)
          / algebraMap K[X] (RatFunc K) M :=
  subtract_localPrincipalPart_eq A M i hM

/-! ## Engine-form assembly examples -/

example [CharZero K] (A M : K[X]) {α : K} (i d : ℕ) (hM : M.eval α ≠ 0) (hd : d < i) :
    localCoeff A M α i d
      = (((d.factorial : K))⁻¹)
          * RatFunc.eval (RingHom.id K) α
              ((ratFuncKDeriv^[d])
                (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) M)) :=
  localCoeff_eq_taylor_coeff A M i d hM hd

example [CharZero K] (A D Di Diα : K[X]) {α : K} (i d : ℕ) (hi : 0 < i) (hd : d < i)
    (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di i).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    localCoeff A (lDenomα (laurentE D Di i) Diα i 0) α i d
      = (laurentH A D Di i (i - d)).eval α :=
  localCoeff_eq_laurentH A D Di Diα i d hi hd
    ⟨hDi, hα, hfac, hcopE, hcopD, hEi, hDiα⟩

example {N M : K[X]} (hM : M.natDegree = 0) (hM0 : M ≠ 0) (hdeg : N.degree < M.degree) :
    algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M = 0 :=
  properRatFunc_const_denom_eq_zero hM hM0 hdeg

example (M₀ A : K[X]) (mult : K → ℕ) (R : Finset K) (hpf : ∀ α ∈ R, M₀.eval α ≠ 0) :
    ∃ (PP : K → RatFunc K) (Rem : K[X]),
      algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀)
        = (∑ α ∈ R, PP α) + algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) M₀ :=
  exists_sum_localPrincipalPart M₀ mult R hpf A

example (A : K[X]) (mult : K → ℕ) (R : Finset K) {c : K} (hc : c ≠ 0) :
    ∃ (P : K[X]) (PP : K → RatFunc K),
      algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) (rootProd R mult * Polynomial.C c)
        = algebraMap K[X] (RatFunc K) P + ∑ α ∈ R, PP α :=
  completePartialFraction_over_closure A mult R hc

example {A₁ M₁ A₂ M₂ N₁ N₂ Md₁ Md₂ : K[X]} {α : K} (i : ℕ) (hMd₁ : Md₁.eval α ≠ 0)
    (hMd₂ : Md₂.eval α ≠ 0)
    (heq : localPrincipalPart A₁ M₁ α i
            + algebraMap K[X] (RatFunc K) N₁ / algebraMap K[X] (RatFunc K) Md₁
          = localPrincipalPart A₂ M₂ α i
            + algebraMap K[X] (RatFunc K) N₂ / algebraMap K[X] (RatFunc K) Md₂) :
    localPrincipalPart A₁ M₁ α i = localPrincipalPart A₂ M₂ α i :=
  principalPart_unique i hMd₁ hMd₂ heq

example [CharZero K] (A D Di Diα : K[X]) {α : K} (i : ℕ) (hi : 0 < i) (hDi : Di.Monic)
    (hα : Di.eval α = 0) (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di i).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    localPrincipalPart A (lDenomα (laurentE D Di i) Diα i 0) α i
      = ∑ j ∈ Finset.Icc 1 i,
          algebraMap K[X] (RatFunc K) (Polynomial.C ((laurentH A D Di i j).eval α))
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j :=
  localPrincipalPart_eq_engineSum A D Di Diα i hi
    ⟨hDi, hα, hfac, hcopE, hcopD, hEi, hDiα⟩

example [CharZero K] (A : K[X]) (mult : K → ℕ) (R : Finset K) {c : K} (hc : c ≠ 0)
    (Di Diα : K → K[X])
    (pole : ∀ α ∈ R, 0 < mult α ∧ (Di α).Monic ∧ (Di α).eval α = 0
      ∧ Di α = (Polynomial.X - Polynomial.C α) * Diα α
      ∧ IsCoprime (laurentE (rootProd R mult * Polynomial.C c) (Di α) (mult α)) (Di α)
      ∧ IsCoprime (derivative (Di α)) (Di α)
      ∧ (laurentE (rootProd R mult * Polynomial.C c) (Di α) (mult α)).eval α ≠ 0
      ∧ (Diα α).eval α ≠ 0
      ∧ rootProd R mult * Polynomial.C c
          = (Polynomial.X - Polynomial.C α) ^ mult α
            * lDenomα (laurentE (rootProd R mult * Polynomial.C c) (Di α) (mult α)) (Diα α) (mult α) 0) :
    ∃ (P : K[X]),
      algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) (rootProd R mult * Polynomial.C c)
        = algebraMap K[X] (RatFunc K) P
          + ∑ α ∈ R, ∑ j ∈ Finset.Icc 1 (mult α),
              algebraMap K[X] (RatFunc K)
                  (Polynomial.C ((laurentH A (rootProd R mult * Polynomial.C c) (Di α) (mult α) j).eval α))
                / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j :=
  completePartialFraction_engineForm A mult R hc Di Diα pole

end DeepWiki.SymbolicIntegration
