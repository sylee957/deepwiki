import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor
import DeepWiki.SymbolicIntegration.Core.Differential.DiffPolyFractionDeriv
import DeepWiki.SymbolicIntegration.Core.Differential.PolynomialDerivatives
import DeepWiki.SymbolicIntegration.Core.Polynomial.LinearFactors
import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalAssembly
import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalParts
import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalDerivatives
import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalUniqueness
import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalRegularity
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.RecognizingLogDeriv
import DeepWiki.SymbolicIntegration.CompletePartialFraction

/-! # Rational Laurent coefficients of a partial-fraction decomposition

For `A, D ∈ K[x]` with a squarefree factorization `D = ∏ᵢ Dᵢ^i`, computes the partial-fraction Laurent
coefficients `Hᵢⱼ ∈ K[x]` by rational operations over `K` (no factoring of `Dᵢ`), via a differential
polynomial ring `K(x)⟨u⟩` and its `d/dx` derivation, and proves `A/D = P + ∑ᵢ ∑_α ∑ⱼ Hᵢⱼ(α)/(x−α)ʲ`. -/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## The differential polynomial ring `K⟨u⟩` and its `d/dx` derivation -/

/-! ## The extended-Euclidean Bézout cofactors `Bᵢ`, `Cᵢ` -/

/-- The cofactor `Eᵢ = D /ₘ Dᵢ^i`: the part of `D` complementary to the prime power `Dᵢ^i`. -/
noncomputable def laurentE (D Di : K[X]) (i : ℕ) : K[X] := D /ₘ Di ^ i

/-- The Bézout cofactor `Bᵢ` of `Eᵢ` in `Eᵢ·Bᵢ + Dᵢ·(…) = 1`, so `Bᵢ·Eᵢ ≡ 1 (mod Dᵢ)`. -/
noncomputable def bezoutE (D Di : K[X]) (i : ℕ) : K[X] :=
  (diophantineSolve (laurentE D Di i) Di 1).1

/-- The Bézout cofactor `Cᵢ` of `Dᵢ'` in `Dᵢ'·Cᵢ + Dᵢ·(…) = 1`, so `Cᵢ·Dᵢ' ≡ 1 (mod Dᵢ)`. -/
noncomputable def bezoutDeriv (Di : K[X]) : K[X] :=
  (diophantineSolve (derivative Di) Di 1).1

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

/-- The `Cᵢ` congruence: for `IsCoprime Dᵢ' Dᵢ`, `(bezoutDeriv Di * derivative Di) %ₘ Di = 1 %ₘ Di`. -/
theorem bezoutDeriv_mul_derivative_modByMonic (Di : K[X]) (hDi : Di.Monic)
    (hcop : IsCoprime (derivative Di) Di) :
    (bezoutDeriv Di * derivative Di) %ₘ Di = (1 : K[X]) %ₘ Di := by
  have hspec := diophantineSolve_spec hcop (1 : K[X])
  have hkey : bezoutDeriv Di * derivative Di
      = (1 : K[X]) - Di * (diophantineSolve (derivative Di) Di 1).2 := by
    rw [bezoutDeriv]; linear_combination hspec
  rw [hkey, sub_modByMonic, self_mul_modByMonic hDi, sub_zero]

/-! ## The `Pᵢⱼ` numerator recursion -/

/-- The numerator-recursion step: from the numerator `P` of `hᵢ^d/d! = P/(u^a·Eᵢ^b)` (`a = i+d`, `b = d+1`),
`(1/b)·(ddx P·u·Eᵢ − P·(a·u'·Eᵢ + b·u·Eᵢ'))` is the numerator of `hᵢ^(d+1)/(d+1)!`. -/
noncomputable def laurentNumStep (Ei : K[X]) (a b : ℕ) (P : DiffPoly K) : DiffPoly K :=
  MvPolynomial.C ((b : K)⁻¹) *
    (ddx P * X (some 0) * dpEmbed Ei
      - P * ((a : DiffPoly K) * X (some 1) * dpEmbed Ei
              + (b : DiffPoly K) * X (some 0) * dpEmbed (derivative Ei)))

/-- The Laurent numerator `Pᵢⱼ` (`j = i − d`), the numerator of `hᵢ^d/d! = Pᵢⱼ/(u^(i+d)·Eᵢ^(d+1))`:
`laurentNum A Ei i 0 = dpEmbed A` (numerator of `hᵢ = A/(uⁱ·Eᵢ)`), stepped by `laurentNumStep`. -/
noncomputable def laurentNum (A Ei : K[X]) (i : ℕ) : ℕ → DiffPoly K
  | 0 => dpEmbed A
  | d + 1 => laurentNumStep Ei (i + d) (d + 1) (laurentNum A Ei i d)

@[simp] theorem laurentNum_zero (A Ei : K[X]) (i : ℕ) :
    laurentNum A Ei i 0 = dpEmbed A := rfl

theorem laurentNum_succ (A Ei : K[X]) (i d : ℕ) :
    laurentNum A Ei i (d + 1)
      = laurentNumStep Ei (i + d) (d + 1) (laurentNum A Ei i d) := rfl

/-- The denominator-free (characteristic-`0`) recursion identity
`(d+1)·Pᵢ,d₊₁ = ddx Pᵢ,d·u·Eᵢ − Pᵢ,d·((i+d)·u'·Eᵢ + (d+1)·u·Eᵢ')` in `DiffPoly K`. -/
theorem laurentNum_cleared_step [CharZero K] (A Ei : K[X]) (i d : ℕ) :
    MvPolynomial.C ((d : K) + 1) * laurentNum A Ei i (d + 1)
      = ddx (laurentNum A Ei i d) * X (some 0) * dpEmbed Ei
        - laurentNum A Ei i d
            * ((i + d : DiffPoly K) * X (some 1) * dpEmbed Ei
                + (d + 1 : DiffPoly K) * X (some 0) * dpEmbed (derivative Ei)) := by
  rw [laurentNum_succ, laurentNumStep, ← mul_assoc, ← MvPolynomial.C_mul]
  have hne : ((d : ℕ) : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  rw [show ((d : K) + 1) = (((d + 1 : ℕ)) : K) by push_cast; ring,
      mul_inv_cancel₀ (by exact_mod_cast hne), MvPolynomial.C_1, one_mul]
  push_cast; ring

/-! ## The engine: `Qᵢⱼ` substitution and `Hᵢⱼ` -/

/-- The `Qᵢⱼ` substitution `Option ℕ → K[x]`: `x ↦ X`, `u^(k) ↦ Dᵢ^(k+1)/(k+1)`. -/
noncomputable def laurentSubst (Di : K[X]) : Option ℕ → K[X] := fun v =>
  match v with
  | none => Polynomial.X
  | some k => Polynomial.C ((k + 1 : K)⁻¹) * (derivative^[k + 1] Di)

/-- The polynomial `Qᵢⱼ = aeval (laurentSubst Dᵢ) Pᵢⱼ ∈ K[x]`, substituting the scaled derivatives of `Dᵢ`
into the numerator `Pᵢⱼ = laurentNum A Eᵢ i (i−j)` (`Eᵢ = laurentE D Dᵢ i`). -/
noncomputable def laurentQ (A D Di : K[X]) (i j : ℕ) : K[X] :=
  aeval (laurentSubst Di) (laurentNum A (laurentE D Di i) i (i - j))

/-- The Laurent coefficient `Hᵢⱼ = Qᵢⱼ·Bᵢ^(i−j+1)·Cᵢ^(2i−j) (mod Dᵢ) ∈ K[x]`: `Hᵢⱼ(α)` is the
`1/(x−α)^j` coefficient at a root `α` of `Dᵢ`. -/
noncomputable def laurentH (A D Di : K[X]) (i j : ℕ) : K[X] :=
  (laurentQ A D Di i j * bezoutE D Di i ^ (i - j + 1) * bezoutDeriv Di ^ (2 * i - j)) %ₘ Di

theorem laurentH_def (A D Di : K[X]) (i j : ℕ) :
    laurentH A D Di i j
      = (laurentQ A D Di i j * bezoutE D Di i ^ (i - j + 1) * bezoutDeriv Di ^ (2 * i - j)) %ₘ Di :=
  rfl

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

end DeepWiki.SymbolicIntegration
