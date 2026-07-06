import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor
import DeepWiki.SymbolicIntegration.Core.Differential.DifferentialPolynomials
import DeepWiki.SymbolicIntegration.Core.Differential.PolynomialDerivatives
import DeepWiki.SymbolicIntegration.Core.Polynomial.LinearFactors
import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalParts
import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalDerivatives
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

/-- A squarefree `Dᵢ` over a `CharZero` field is coprime to its derivative, `IsCoprime Dᵢ' Dᵢ`. -/
theorem isCoprime_derivative_of_squarefree [CharZero K] {Di : K[X]} (hsf : Squarefree Di) :
    IsCoprime (derivative Di) Di :=
  (squarefree_iff_isCoprime_derivative.mp hsf).symm

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

/-! ## Laurent fractions in `K(x)⟨u⟩ = Frac (DiffPoly K)` -/

/-- The `hᵢ^(d)` denominator `u^(i+d)·Eᵢ^(d+1) ∈ DiffPoly K`. -/
noncomputable def lDenom (Ei : K[X]) (i d : ℕ) : DiffPoly K :=
  (X (some 0)) ^ (i + d) * (dpEmbed Ei) ^ (d + 1)

/-- `lDenom Ei i d ≠ 0` for `Ei ≠ 0`. -/
theorem lDenom_ne_zero {Ei : K[X]} (i d : ℕ) (hEi : Ei ≠ 0) : lDenom Ei i d ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ (dpEmbed_ne_zero hEi))
  simp [MvPolynomial.X_ne_zero]

/-- Denominator recursion: `lDenom Ei i (d+1) = lDenom Ei i d · u · Eᵢ`. -/
theorem lDenom_succ (Ei : K[X]) (i d : ℕ) :
    lDenom Ei i (d + 1) = lDenom Ei i d * X (some 0) * dpEmbed Ei := by
  unfold lDenom
  rw [show i + (d + 1) = (i + d) + 1 from by ring]
  ring

/-- `hᵢ = A/(uⁱ·Eᵢ)` as an element of `K(x)⟨u⟩`: the fraction the engine differentiates. -/
noncomputable def hFrac (A Ei : K[X]) (i : ℕ) : FractionRing (DiffPoly K) :=
  algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (dpEmbed A) /
    algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (lDenom Ei i 0)

/-- The candidate `hᵢ^(d)/d!` fraction `Pᵢ,d/(u^(i+d)·Eᵢ^(d+1))`. -/
noncomputable def lFrac (A Ei : K[X]) (i d : ℕ) : FractionRing (DiffPoly K) :=
  algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (laurentNum A Ei i d) /
    algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (lDenom Ei i d)

/-- `lFrac` base case: `lFrac A Ei i 0 = hFrac A Ei i`. -/
theorem lFrac_zero (A Ei : K[X]) (i : ℕ) : lFrac A Ei i 0 = hFrac A Ei i := by
  unfold lFrac hFrac; rw [laurentNum_zero]

/-- A nonzero `DiffPoly K` element is in `nonZeroDivisors`. -/
private theorem mem_nzd {p : DiffPoly K} (hp : p ≠ 0) : p ∈ nonZeroDivisors (DiffPoly K) :=
  mem_nonZeroDivisors_iff_ne_zero.mpr hp

/-- `lFrac` as a `Localization.mk`: `lFrac A Ei i d = mk (laurentNum …) ⟨lDenom …⟩`. -/
theorem lFrac_mk (A Ei : K[X]) (i d : ℕ) (hEi : Ei ≠ 0) :
    lFrac A Ei i d
      = Localization.mk (laurentNum A Ei i d) ⟨lDenom Ei i d, mem_nzd (lDenom_ne_zero i d hEi)⟩ := by
  unfold lFrac; rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div]

/-- The reduced quotient-rule numerator (`i+d = m+1`):
`ddx Pᵢ,d·denom_d − Pᵢ,d·ddx denom_d = u^m·Eᵢ^d·((d+1)·Pᵢ,d₊₁)`. -/
theorem reduced_num [CharZero K] (A Ei : K[X]) (i d m : ℕ) (hm : i + d = m + 1) :
    ddx (laurentNum A Ei i d) * lDenom Ei i d - laurentNum A Ei i d * ddx (lDenom Ei i d)
      = X (some 0) ^ m * dpEmbed Ei ^ d *
          (MvPolynomial.C ((d : K) + 1) * laurentNum A Ei i (d + 1)) := by
  rw [laurentNum_cleared_step]
  unfold lDenom
  rw [hm]
  have hddxE : ddx (dpEmbed Ei) = dpEmbed (derivative Ei) := ddx_dpEmbed Ei
  have hmK : ((i : DiffPoly K) + (d : DiffPoly K)) = (m : DiffPoly K) + 1 := by exact_mod_cast hm
  have key : ddx (X (some 0) ^ (m + 1) * dpEmbed Ei ^ (d + 1))
      = ((m : DiffPoly K) + 1) * X (some 0) ^ m * X (some 1) * dpEmbed Ei ^ (d + 1)
        + X (some 0) ^ (m + 1) * ((d : DiffPoly K) + 1) * dpEmbed Ei ^ d * dpEmbed (derivative Ei) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, ddx_u 0, hddxE]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, dpU]; push_cast; ring
  rw [key, pow_succ (X (some 0) : DiffPoly K) m, pow_succ (dpEmbed Ei : DiffPoly K) d, hmK]
  ring

/-- The recursion step in `K(x)⟨u⟩`: `fracKDeriv (lFrac A Ei i d) = (d+1)·lFrac A Ei i (d+1)`.
Requires `0 < i`, `Ei ≠ 0`. -/
theorem fracKDeriv_lFrac [CharZero K] (A Ei : K[X]) (i d : ℕ) (hi : 0 < i) (hEi : Ei ≠ 0) :
    fracKDeriv (lFrac A Ei i d) = ((d : K) + 1) • lFrac A Ei i (d + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, i + d = m + 1 := ⟨i + d - 1, by omega⟩
  rw [lFrac_mk A Ei i d hEi, lFrac_mk A Ei i (d + 1) hEi, fracKDeriv_apply, fracDeriv_mk]
  show (Localization.mk _ ⟨(lDenom Ei i d) ^ 2, _⟩ : FractionRing (DiffPoly K)) = _
  rw [Localization.smul_mk]
  apply diffPoly_fraction_mk_eq_of_cross_mul
  show lDenom Ei i (d + 1) * _ = (lDenom Ei i d) ^ 2 * _
  rw [reduced_num A Ei i d m hm, MvPolynomial.smul_eq_C_mul, lDenom_succ]
  unfold lDenom
  rw [hm]; ring

/-- The factorial divisor `d! = ∏_{k=0}^{d−1}(k+1)` accumulated by the `laurentNumStep` recursion. -/
noncomputable def laurentScale (K : Type*) [Field K] (i : ℕ) : ℕ → K
  | 0 => 1
  | d + 1 => laurentScale K i d * ((d : K) + 1)

/-- `laurentScale K i d = (d.factorial : K)`, independent of `i`. -/
theorem laurentScale_eq_factorial (i d : ℕ) : laurentScale K i d = (d.factorial : K) := by
  induction d with
  | zero => simp [laurentScale]
  | succ n ih => rw [laurentScale, ih, Nat.factorial_succ]; push_cast; ring

/-- The recursion invariant in `K(x)⟨u⟩`: `(d/dx)^[d] hᵢ = (laurentScale K i d) • lFrac A Ei i d` for
`hᵢ = A/(uⁱ·Eᵢ)`. -/
theorem iterate_fracKDeriv_hFrac [CharZero K] (A Ei : K[X]) (i : ℕ) (hi : 0 < i) (hEi : Ei ≠ 0)
    (d : ℕ) :
    (fracKDeriv^[d]) (hFrac A Ei i) = (laurentScale K i d) • lFrac A Ei i d := by
  induction d with
  | zero => rw [Function.iterate_zero_apply, laurentScale, one_smul, lFrac_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, laurentScale, Derivation.map_smul,
      fracKDeriv_lFrac A Ei i n hi hEi, smul_smul]

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

/-! ## The specialized recursion invariant in `K(x) = RatFunc K` -/

/-- The genuine `hᵢ,α`-denominator `Dᵢ,α^{i+d}·Eᵢ^{d+1} ∈ K[x]` (`= σα (lDenom Ei i d)`). -/
noncomputable def lDenomα (Ei Diα : K[X]) (i d : ℕ) : K[X] := Diα ^ (i + d) * Ei ^ (d + 1)

/-- `diffSubst Diα (lDenom Ei i d) = lDenomα Ei Diα i d`. -/
theorem diffSubst_lDenom (Ei Diα : K[X]) (i d : ℕ) :
    diffSubst Diα (lDenom Ei i d) = lDenomα Ei Diα i d := by
  unfold lDenom lDenomα
  rw [map_mul, map_pow, map_pow, diffSubst_X_some Diα 0, diffSubst_dpEmbed,
    Function.iterate_zero_apply]

/-- `lDenomα Ei Diα i d ≠ 0` for `Ei, Diα ≠ 0`. -/
theorem lDenomα_ne_zero {Ei Diα : K[X]} (i d : ℕ) (hEi : Ei ≠ 0) (hDiα : Diα ≠ 0) :
    lDenomα Ei Diα i d ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hDiα) (pow_ne_zero _ hEi)

/-- The genuine `hᵢ,α^{(d)}/d!` fraction `σα(Pᵢ,d)/(Dᵢ,α^{i+d}·Eᵢ^{d+1}) ∈ K(x)`. -/
noncomputable def lFracα (A Ei Diα : K[X]) (i d : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (diffSubst Diα (laurentNum A Ei i d)) /
    algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d)

/-- `hᵢ,α = A/(Dᵢ,α^i·Eᵢ)` in `K(x)`: the genuine rational function the engine differentiates. -/
noncomputable def hFracα (A Ei Diα : K[X]) (i : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i 0)

/-- `lFracα` base case: `lFracα A Ei Diα i 0 = hFracα A Ei Diα i`. -/
theorem lFracα_zero (A Ei Diα : K[X]) (i : ℕ) : lFracα A Ei Diα i 0 = hFracα A Ei Diα i := by
  unfold lFracα hFracα; rw [laurentNum_zero, diffSubst_dpEmbed]

/-- The reduced quotient-rule numerator in `K[x]` (`= σα` of `reduced_num`):
`(σα Pᵢ,d)'·denomα_d − (σα Pᵢ,d)·denomα_d' = Dᵢ,α^m·Eᵢ^d·((d+1)·σα Pᵢ,d₊₁)`. -/
theorem reduced_numα [CharZero K] (A Ei Diα : K[X]) (i d m : ℕ) (hm : i + d = m + 1) :
    derivative (diffSubst Diα (laurentNum A Ei i d)) * lDenomα Ei Diα i d
        - diffSubst Diα (laurentNum A Ei i d) * derivative (lDenomα Ei Diα i d)
      = Diα ^ m * Ei ^ d *
          (((d : K[X]) + 1) * diffSubst Diα (laurentNum A Ei i (d + 1))) := by
  have h := congrArg (diffSubst Diα) (reduced_num A Ei i d m hm)
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow,
    diffSubst_X_some Diα 0, Function.iterate_zero_apply, diffSubst_dpEmbed] at h
  -- convert both `ddx`-images to genuine derivatives and the `lDenom`-image to `lDenomα`
  rw [diffSubst_ddx, diffSubst_ddx, diffSubst_lDenom] at h
  -- `diffSubst (C ((d:K)+1)) = C ((d:K)+1)` as a constant in `K[x]`
  rw [h, diffSubst_C, Polynomial.C_add, Polynomial.C_eq_natCast, Polynomial.C_1]

/-- The recursion step in `K(x)`: `ratFuncKDeriv (lFracα A Ei Diα i d) = (d+1)·lFracα A Ei Diα i (d+1)`.
Requires `0 < i`, `Ei ≠ 0`, `Diα ≠ 0`. -/
theorem ratFuncKDeriv_lFracα [CharZero K] (A Ei Diα : K[X]) (i d : ℕ) (hi : 0 < i) (hEi : Ei ≠ 0)
    (hDiα : Diα ≠ 0) :
    ratFuncKDeriv (lFracα A Ei Diα i d) = ((d : K) + 1) • lFracα A Ei Diα i (d + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, i + d = m + 1 := ⟨i + d - 1, by omega⟩
  have hden : (algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (lDenomα_ne_zero i d hEi hDiα)
  have hden1 : (algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i (d + 1))) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (lDenomα_ne_zero i (d + 1) hEi hDiα)
  -- the bundled `ratFuncKDeriv` on an embedded polynomial is the embedded `derivative`
  have hk : ∀ p : K[X], ratFuncKDeriv (algebraMap K[X] (RatFunc K) p)
      = algebraMap K[X] (RatFunc K) (derivative p) := fun p => ratFuncDeriv_algebraMap p
  rw [lFracα, lFracα, Derivation.leibniz_div, hk, hk]
  -- all `•` on `RatFunc K` are the field self-action; the RHS `K`-smul becomes `algebraMap`
  simp only [smul_eq_mul, Algebra.smul_def]
  -- combine the numerator with the polynomial identity, clear denominators
  set Pd := diffSubst Diα (laurentNum A Ei i d)
  set Pd1 := diffSubst Diα (laurentNum A Ei i (d + 1))
  set bd := algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d) with hbd
  set bd1 := algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i (d + 1)) with hbd1
  have hnum : bd⁻¹ ^ 2 * (bd * algebraMap K[X] (RatFunc K) (derivative Pd)
        - algebraMap K[X] (RatFunc K) Pd * algebraMap K[X] (RatFunc K) (derivative (lDenomα Ei Diα i d)))
      = bd⁻¹ ^ 2 * algebraMap K[X] (RatFunc K)
          (derivative Pd * lDenomα Ei Diα i d - Pd * derivative (lDenomα Ei Diα i d)) := by
    rw [map_sub, map_mul, map_mul, hbd]; ring
  rw [hnum, reduced_numα A Ei Diα i d m hm]
  -- convert the `K`-scalar `algebraMap K (RatFunc K) ((d:K)+1)` to `algebraMap K[X] (Polynomial.C …)`
  rw [hbd, hbd1, show (algebraMap K (RatFunc K) ((d : K) + 1))
      = algebraMap K[X] (RatFunc K) (Polynomial.C ((d : K) + 1)) by
        rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]]
  have hbd2 : (algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (lDenomα_ne_zero i d hEi hDiα)
  have hbd12 : (algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i (d + 1))) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (lDenomα_ne_zero i (d + 1) hEi hDiα)
  have hbd2sq : (algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d ^ 2)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero 2 (lDenomα_ne_zero i d hEi hDiα))
  rw [inv_pow, ← map_pow, ← div_eq_inv_mul, ← mul_div_assoc, ← map_mul,
    div_eq_div_iff hbd2sq hbd12, ← map_mul, ← map_mul]
  congr 1
  -- the `K[x]` polynomial identity
  have hsucc : lDenomα Ei Diα i (d + 1) = Diα ^ m * Ei ^ d * (Diα * Ei) ^ 2 := by
    unfold lDenomα; rw [show i + (d + 1) = m + 1 + 1 from by omega,
      show d + 1 + 1 = (d + 1) + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_succ]; ring
  have hdfac : lDenomα Ei Diα i d = Diα ^ m * Ei ^ d * (Diα * Ei) := by
    unfold lDenomα; rw [hm, pow_succ]; ring
  rw [hsucc, hdfac, Polynomial.C_add, Polynomial.C_eq_natCast, Polynomial.C_1]
  ring

/-- The specialized recursion invariant in `K(x)`:
`(d/dx)^[d] hᵢ,α = d! · (σα(laurentNum A Eᵢ i d) / (Dᵢ,α^{i+d}·Eᵢ^{d+1}))` for `hᵢ,α = A/(Dᵢ,α^i·Eᵢ)`.
Requires `0 < i`, `Ei ≠ 0`, `Diα ≠ 0`. -/
theorem iterate_ratFuncKDeriv_hFracα [CharZero K] (A Ei Diα : K[X]) (i : ℕ) (hi : 0 < i)
    (hEi : Ei ≠ 0) (hDiα : Diα ≠ 0) (d : ℕ) :
    (ratFuncKDeriv^[d]) (hFracα A Ei Diα i) = (d.factorial : K) • lFracα A Ei Diα i d := by
  induction d with
  | zero => rw [Function.iterate_zero_apply, Nat.factorial_zero, Nat.cast_one, one_smul, lFracα_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.map_smul,
      ratFuncKDeriv_lFracα A Ei Diα i n hi hEi hDiα, smul_smul, Nat.factorial_succ]
    congr 1
    push_cast; ring

/-! ## The root-value bridge `σα(Pᵢ,d)(α) = Qᵢⱼ(α)` -/

/-- The bridge `(σα(laurentNum …)).eval α = (laurentQ …).eval α`: both are
`aeval (substEvalAt Diα α) (laurentNum …)`. -/
theorem eval_diffSubst_laurentNum_eq_laurentQ_eval [CharZero K] (A D Diα : K[X]) (α : K) (i j : ℕ) :
    Polynomial.eval α
        (diffSubst Diα (laurentNum A (laurentE D ((Polynomial.X - Polynomial.C α) * Diα) i) i (i - j)))
      = (laurentQ A D ((Polynomial.X - Polynomial.C α) * Diα) i j).eval α := by
  rw [eval_diffSubst, laurentQ_eval_at_root]

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
  -- `Qᵢⱼ(α) = σα(Pᵢ,i−j)(α)`: the engine substitution value equals the genuine-hom numerator value
  rw [laurentQ, eval_aeval_diffPoly, eval_diffSubst]
  have hf : (fun v => Polynomial.eval α (laurentSubst Di v)) = substEvalAt Diα α := by
    funext v
    cases v with
    | none => simp [laurentSubst, substEvalAt]
    | some k => subst hfac; rw [eval_laurentSubst_some]; simp [substEvalAt]
  rw [hf]

/-! ## `Hᵢⱼ(α)` is the order-`(i−j)` Taylor coefficient of `hᵢ,α` -/

/-- `(lDenomα Ei Diα i d).eval α ≠ 0` when `Ei(α), Diα(α) ≠ 0`. -/
theorem eval_lDenomα_ne_zero {Ei Diα : K[X]} {α : K} (i d : ℕ) (hEi : Ei.eval α ≠ 0)
    (hDiα : Diα.eval α ≠ 0) : (lDenomα Ei Diα i d).eval α ≠ 0 := by
  unfold lDenomα
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow]
  exact mul_ne_zero (pow_ne_zero _ hDiα) (pow_ne_zero _ hEi)

/-- Eval of `lFracα` at `α`:
`RatFunc.eval id α (lFracα A Ei Diα i d) = (diffSubst Diα (laurentNum …)).eval α / (lDenomα …).eval α`. -/
theorem eval_lFracα {A Ei Diα : K[X]} {α : K} (i d : ℕ) (hEi : Ei.eval α ≠ 0)
    (hDiα : Diα.eval α ≠ 0) :
    RatFunc.eval (RingHom.id K) α (lFracα A Ei Diα i d)
      = (diffSubst Diα (laurentNum A Ei i d)).eval α / (lDenomα Ei Diα i d).eval α := by
  rw [lFracα, eval_algebraMap_div α _ _ (eval_lDenomα_ne_zero i d hEi hDiα)]

/-- Eval of a `K`-scaled `lFracα` at `α`:
`RatFunc.eval id α (c • lFracα A Ei Diα i d) = c · ((diffSubst Diα (laurentNum …)).eval α / (lDenomα …).eval α)`. -/
theorem eval_smul_lFracα {A Ei Diα : K[X]} {α : K} (c : K) (i d : ℕ) (hEi : Ei.eval α ≠ 0)
    (hDiα : Diα.eval α ≠ 0) :
    RatFunc.eval (RingHom.id K) α (c • lFracα A Ei Diα i d)
      = c * ((diffSubst Diα (laurentNum A Ei i d)).eval α / (lDenomα Ei Diα i d).eval α) := by
  have hsmul : c • lFracα A Ei Diα i d
      = algebraMap K[X] (RatFunc K) (Polynomial.C c * diffSubst Diα (laurentNum A Ei i d))
        / algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d) := by
    rw [lFracα, RatFunc.smul_eq_C_mul, ← RatFunc.algebraMap_C, map_mul, mul_div_assoc]
  rw [hsmul, eval_algebraMap_div α _ _ (eval_lDenomα_ne_zero i d hEi hDiα),
    Polynomial.eval_mul, Polynomial.eval_C, mul_div_assoc]

/-- The specialized invariant evaluated at the root `α`:
`RatFunc.eval id α ((ratFuncKDeriv^[d]) (hFracα A Ei Diα i)) = d!·(diffSubst Diα (laurentNum …)).eval α / (lDenomα …).eval α`,
for `0 < i`, `Ei(α), Diα(α) ≠ 0`. -/
theorem eval_ratFuncKDeriv_iterate_hFracα_at_root [CharZero K] {A Ei Diα : K[X]} {α : K} (i : ℕ)
    (hi : 0 < i) (hEi0 : Ei ≠ 0) (hDiα0 : Diα ≠ 0) (hEi : Ei.eval α ≠ 0) (hDiα : Diα.eval α ≠ 0)
    (d : ℕ) :
    RatFunc.eval (RingHom.id K) α ((ratFuncKDeriv^[d]) (hFracα A Ei Diα i))
      = (d.factorial : K) * (diffSubst Diα (laurentNum A Ei i d)).eval α
          / (lDenomα Ei Diα i d).eval α := by
  rw [iterate_ratFuncKDeriv_hFracα A Ei Diα i hi hEi0 hDiα0 d,
    eval_smul_lFracα _ i d hEi hDiα, mul_div_assoc]

/-- A regular root setup for the Laurent coefficient engine at multiplicity `i`. -/
structure IsLaurentRegularRoot (D Di Diα : K[X]) (α : K) (i : ℕ) : Prop where
  /-- `Di` is monic. -/
  monic : Di.Monic
  /-- `α` is a root of `Di`. -/
  root : Di.eval α = 0
  /-- `Di` factors as `(X - C α) * Diα`. -/
  factor : Di = (Polynomial.X - Polynomial.C α) * Diα
  /-- The complementary factor `Eᵢ` is coprime to `Di`. -/
  coprime_laurentE : IsCoprime (laurentE D Di i) Di
  /-- The derivative `Di'` is coprime to `Di`. -/
  coprime_derivative : IsCoprime (derivative Di) Di
  /-- The complementary factor `Eᵢ` does not vanish at `α`. -/
  laurentE_eval_ne : (laurentE D Di i).eval α ≠ 0
  /-- The linear cofactor `Diα` does not vanish at `α`. -/
  cofactor_eval_ne : Diα.eval α ≠ 0

/-- `Hᵢⱼ(α)` is the order-`(i−j)` Taylor coefficient of `hᵢ,α = (A/D)(x−α)ⁱ`:
`(laurentH A D Di i j).eval α = ((i−j)!)⁻¹ · RatFunc.eval id α ((ratFuncKDeriv^[i−j]) (hFracα A Eᵢ Diα i))`,
for `Dᵢ = (x−α)·Dᵢ,α` monic, `j ≤ i`, `Eᵢ(α), Dᵢ,α(α) ≠ 0`. -/
theorem eval_laurentH_eq_taylor_coeff [CharZero K] {A D Di Diα : K[X]} {α : K} (i j : ℕ)
    (hi : 0 < i) (hji : j ≤ i) (hroot : IsLaurentRegularRoot D Di Diα α i) :
    (laurentH A D Di i j).eval α
      = (((i - j).factorial : K))⁻¹
          * RatFunc.eval (RingHom.id K) α
              ((ratFuncKDeriv^[i - j]) (hFracα A (laurentE D Di i) Diα i)) := by
  -- abbreviations
  set Ei := laurentE D Di i with hEidef
  have hEi0 : Ei ≠ 0 := fun h => hroot.laurentE_eval_ne (by rw [← hEidef, h, Polynomial.eval_zero])
  have hDiα0 : Diα ≠ 0 := fun h => hroot.cofactor_eval_ne (by rw [h, Polynomial.eval_zero])
  -- evaluate Stage I at the root
  rw [eval_ratFuncKDeriv_iterate_hFracα_at_root i hi hEi0 hDiα0
    hroot.laurentE_eval_ne hroot.cofactor_eval_ne (i - j)]
  -- the engine output, via Steps 2+3+5
  rw [eval_laurentH_eq_diffSubst_laurentNum i j hroot.monic hroot.root hroot.factor
    hroot.coprime_laurentE hroot.coprime_derivative, ← hEidef]
  -- the `(derivative Di)(α) = Diα(α)` cofactor identity
  rw [eval_derivative_of_X_sub_C_mul hroot.factor]
  -- the denominator `lDenomα Ei Diα i (i-j) (α) = Diα(α)^{i+(i-j)}·Ei(α)^{(i-j)+1}`
  unfold lDenomα
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow]
  -- index arithmetic: `i + (i-j) = 2i - j`
  have hidx : i + (i - j) = 2 * i - j := by omega
  rw [hidx]
  -- abbreviate the evaluated numerator and the two base values
  set N := (diffSubst Diα (laurentNum A Ei i (i - j))).eval α with hN
  set e := Ei.eval α with he
  set g := Diα.eval α with hg
  have hfact : ((i - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i - j)
  -- both sides are `N / (e^{i-j+1}·g^{2i-j})` (the `(i-j)!⁻¹·(i-j)!` cancels)
  rw [one_div, one_div, inv_pow, inv_pow]
  field_simp

/-! ## Restatements against the book's wording -/

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

/-! ## The coefficient bridge chained to the engine: `localCoeff = Hᵢ,(i−d)(α)` -/

/-- `hFracα A Ei Diα i = algebraMap A / algebraMap (lDenomα Ei Diα i 0)`. -/
theorem hFracα_eq_div_lDenomα (A Ei Diα : K[X]) (i : ℕ) :
    hFracα A Ei Diα i
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i 0) := rfl

/-- The coefficient bridge chained to the engine: at a root `α` of `Dᵢ = (x−α)·Dᵢ,α`, with `M = Dᵢ,α^i·Eᵢ`
and `d < i`, `localCoeff A M α i d = (laurentH A D Di i (i−d)).eval α`. -/
theorem localCoeff_eq_laurentH [CharZero K] (A D Di Diα : K[X]) {α : K} (i d : ℕ)
    (hi : 0 < i) (hd : d < i) (hroot : IsLaurentRegularRoot D Di Diα α i) :
    localCoeff A (lDenomα (laurentE D Di i) Diα i 0) α i d
      = (laurentH A D Di i (i - d)).eval α := by
  set Ei := laurentE D Di i with hEidef
  set M := lDenomα Ei Diα i 0 with hMdef
  -- `M(α) ≠ 0`: `M = Diα^i·Ei`
  have hM : M.eval α ≠ 0 := by
    rw [hMdef, lDenomα, Nat.add_zero, Nat.zero_add, pow_one, Polynomial.eval_mul, Polynomial.eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hroot.cofactor_eval_ne) hroot.laurentE_eval_ne
  -- the engine side: `Hᵢ,(i−d)(α) = (1/(i−(i−d))!)·(d/dx)^[i−(i−d)] hᵢ,α (α)`, with `i−(i−d)=d`
  have hji : i - d ≤ i := by omega
  rw [eval_laurentH_eq_taylor_coeff (Diα := Diα) i (i - d) hi hji hroot]
  rw [show i - (i - d) = d from by omega, ← hEidef]
  -- the `localCoeff` side via the Hasse bridge, with `hFracα = A/M`
  rw [localCoeff_eq_taylor_coeff A M i d hM hd, hFracα_eq_div_lDenomα, ← hMdef]

/-- Restatement of P2 (the coefficient bridge): the Stage L Laurent digit `localCoeff` is the order-`d`
Taylor coefficient `(1/d!)·(d/dx)^[d](A/M)(α)` of `hᵢ,α = A/M`. -/
example [CharZero K] (A M : K[X]) {α : K} (i d : ℕ) (hM : M.eval α ≠ 0) (hd : d < i) :
    localCoeff A M α i d
      = (((d.factorial : K))⁻¹)
          * RatFunc.eval (RingHom.id K) α
              ((ratFuncKDeriv^[d])
                (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) M)) :=
  localCoeff_eq_taylor_coeff A M i d hM hd

/-- Restatement of P2 chained to the engine: the Stage L Laurent digit `localCoeff` equals the
Bronstein–Salvy engine output `Hᵢ,(i−d)(α)` (book p.56). -/
example [CharZero K] (A D Di Diα : K[X]) {α : K} (i d : ℕ) (hi : 0 < i) (hd : d < i)
    (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di i).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    localCoeff A (lDenomα (laurentE D Di i) Diα i 0) α i d
      = (laurentH A D Di i (i - d)).eval α :=
  localCoeff_eq_laurentH A D Di Diα i d hi hd
    ⟨hDi, hα, hfac, hcopE, hcopD, hEi, hDiα⟩

/-! ## Stage N — P1: the multi-pole assembly (subtracting ALL principal parts) and the remainder-zero
fact (Bronstein §2.7, Theorem 2.7.1, the literal over-the-closure conclusion)

The literal conclusion `A/D = P + ∑ᵢ ∑_{α|Dᵢ(α)=0} ∑_{j=1}^{i} Hᵢⱼ(α)/(x−α)ʲ` follows from iterating the
per-pole `subtract_localPrincipalPart_eq` over **all** distinct roots `α` of `D` (over `K̄`), then observing
that the final remainder is a **proper** rational function with **no poles**, hence `0` (the polynomial part
`P = A /ₘ D` having been split off). The two reachable closing facts:

* **the remainder-zero fact** (`properRatFunc_const_denom_eq_zero`): a proper `N/M` (`deg N < deg M`) with `M`
  a nonzero **constant** (`deg M = 0`, all poles removed) is `0` — since `deg N < 0` forces `N = 0`;
* **the multi-pole telescoping** (the `Finset`-fold of `subtract_localPrincipalPart_eq`): for a denominator
  `∏_{α ∈ R} (x−α)^{i α} · M₀` with `M₀` having no root in `R`, subtracting the per-pole principal parts at
  every `α ∈ R` leaves a remainder regular at every `α ∈ R`.

The remainder-zero fact is proved here. The multi-pole telescoping (the `Finset` induction peeling one root
at a time) is the heavy bookkeeping piece — see the documented blocker below. -/

/-- **Proper `N/M` with constant nonzero denominator is `0`** (the remainder-zero fact for P1): if
`deg N < deg M` and `M` is a nonzero constant (`M.natDegree = 0`, i.e. all poles have been removed), then
`N = 0`, so `N/M = 0` in `K(x)`. The degree bound `deg N < deg M = 0` forces `N = 0` (`degree N = ⊥`). This
is the final step: after subtracting all principal parts at all poles, the remainder is proper and pole-free,
hence a proper polynomial over a constant — necessarily zero. -/
theorem properRatFunc_const_denom_eq_zero {N M : K[X]} (hM : M.natDegree = 0) (hM0 : M ≠ 0)
    (hdeg : N.degree < M.degree) :
    algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M = 0 := by
  -- `deg M = 0` (nonzero constant), so `deg N < 0`, forcing `N = 0`
  have hMdeg : M.degree = 0 := by
    rw [Polynomial.degree_eq_natDegree hM0, hM]; rfl
  rw [hMdeg] at hdeg
  have hN0 : N = 0 := by
    by_contra hN
    rw [Polynomial.degree_eq_natDegree hN] at hdeg
    exact absurd hdeg (by exact_mod_cast Nat.not_lt_zero _)
  rw [hN0, map_zero, zero_div]

/-- **The per-pole principal part is exactly the singular part** (P1, the per-pole content, restated as the
building block of the multi-pole assembly): for `D = (x−α)ⁱ·M`, `M(α) ≠ 0`, the existence form
`A/D − localPrincipalPart A M α i = R/M` regular at `α` (`subtract_localPrincipalPart_eq`), with the Laurent
coefficients `localCoeff A M α i (i−j) = Hᵢⱼ(α)` (`localCoeff_eq_laurentH`). Iterating this over all distinct
roots of `D` and subtracting (the multi-pole telescoping) recovers `A/D = P + ∑ poles`. -/
theorem subtract_localPrincipalPart_regular (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    ∃ R : K[X],
      algebraMap K[X] (RatFunc K) A
          / (algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ i * M))
        - localPrincipalPart A M α i
        = algebraMap K[X] (RatFunc K) R / algebraMap K[X] (RatFunc K) M :=
  ⟨localRemainder A M α i, subtract_localPrincipalPart_eq A M i hM⟩

/-- **The root-product `∏_{α∈R} (x−α)^{mult α}`** (§2.7, the closure-level denominator): the product of the
prime-power factors of `D` over a `Finset` `R` of distinct roots, with multiplicities `mult`. -/
noncomputable def rootProd (R : Finset K) (mult : K → ℕ) : K[X] :=
  ∏ α ∈ R, (Polynomial.X - Polynomial.C α) ^ mult α

@[simp] theorem rootProd_empty (mult : K → ℕ) : rootProd (∅ : Finset K) mult = 1 := by
  simp [rootProd]

theorem rootProd_insert [DecidableEq K] {α : K} {R : Finset K} (mult : K → ℕ) (hα : α ∉ R) :
    rootProd (insert α R) mult = (Polynomial.X - Polynomial.C α) ^ mult α * rootProd R mult := by
  rw [rootProd, Finset.prod_insert hα, rootProd]

/-- **`(rootProd R mult)(β) ≠ 0` for `β ∉ R`**: a product of `(β−α)^{mult α}` over `α ∈ R`, each factor
nonzero since `β ≠ α` (as `β ∉ R`). The peeled denominator stays pole-free at the not-yet-processed
roots. -/
theorem eval_rootProd_ne_zero {β : K} {R : Finset K} (mult : K → ℕ) (hβ : β ∉ R) :
    (rootProd R mult).eval β ≠ 0 := by
  rw [rootProd, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro α hα
  rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => hβ (h ▸ hα)))

open Classical in
/-- **P1, the multi-pole telescoping** (Bronstein §2.7, Theorem 2.7.1, the closure-level assembly): for a
`Finset R` of distinct roots with multiplicities `mult` and a base `M₀` pole-free at every `α ∈ R`
(`M₀(α) ≠ 0`), subtracting the per-pole principal parts at every `α ∈ R` from `A/(∏_{α∈R}(x−α)^{mult α}·M₀)`
leaves a remainder `Rem/M₀` that is **regular at every `α ∈ R`** (its denominator `M₀` is pole-free there).
There is a per-pole principal-part family `PP : K → RatFunc K` (each `PP α` a genuine Laurent sum
`∑_{j=1}^{mult α} c/(x−α)ʲ`, namely `localPrincipalPart` of the running numerator) with
`A/(∏_{α∈R}(x−α)^{mult α}·M₀) = ∑_{α∈R} PP α + Rem/M₀`. Proved by `Finset` induction peeling one root at a
time via `subtract_localPrincipalPart_eq` (the numerator `A` is generalized so each peel can recurse on the
local remainder). NOTE: the principal part `PP α` is `localPrincipalPart` of the *peeled* numerator (a correct
singular part at `α`); identifying its coefficients with the original-`A` engine outputs `Hᵢⱼ(α)` is the
residual coefficient-matching step (the principal part is intrinsic, but the formula-level numerators differ —
see the §2.7 residual note). -/
theorem exists_sum_localPrincipalPart (M₀ : K[X]) (mult : K → ℕ) :
    ∀ (R : Finset K), (∀ α ∈ R, M₀.eval α ≠ 0) → ∀ (A : K[X]),
      ∃ (PP : K → RatFunc K) (Rem : K[X]),
        algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀)
          = (∑ α ∈ R, PP α) + algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) M₀ := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _ A
    refine ⟨fun _ => 0, A, ?_⟩
    rw [rootProd_empty, one_mul, Finset.sum_empty, zero_add]
  | @insert α R hα ih =>
    intro hpolefree A
    -- the running denominator after peeling `α` is `N := rootProd R mult * M₀`, pole-free at `α`
    set N := rootProd R mult * M₀ with hNdef
    have hNα : N.eval α ≠ 0 := by
      rw [hNdef, Polynomial.eval_mul]
      exact mul_ne_zero (eval_rootProd_ne_zero mult hα)
        (hpolefree α (Finset.mem_insert_self α R))
    -- peel root `α`: `A/((x−α)^{mult α}·N) = PP(α) + localRemainder/N`
    have hpeel := subtract_localPrincipalPart_eq A N (mult α) hNα
    -- recurse on `R` with the peeled numerator `localRemainder A N α (mult α)`
    obtain ⟨PP, Rem, hrec⟩ :=
      ih (fun β hβ => hpolefree β (Finset.mem_insert_of_mem hβ)) (localRemainder A N α (mult α))
    refine ⟨fun β => if β = α then localPrincipalPart A N α (mult α) else PP β, Rem, ?_⟩
    -- the sum over `insert α R` splits as the `α` term + the rest, the rest matching `hrec` (β ≠ α on `R`)
    rw [Finset.sum_insert hα, if_pos rfl]
    have hsumR : (∑ β ∈ R, (if β = α then localPrincipalPart A N α (mult α) else PP β))
        = ∑ β ∈ R, PP β := by
      refine Finset.sum_congr rfl fun β hβ => ?_
      have hβα : β ≠ α := fun h => hα (h ▸ hβ)
      rw [if_neg hβα]
    rw [hsumR]
    -- denominator `rootProd (insert α R) mult * M₀ = (x−α)^{mult α}·N`
    have hden : rootProd (insert α R) mult * M₀
        = (Polynomial.X - Polynomial.C α) ^ mult α * N := by
      rw [rootProd_insert mult hα, hNdef]; ring
    rw [hden]
    -- `A/((x−α)^{mult α}·N) = PP(α) + localRemainder/N`, then `localRemainder/N = ∑ PP + Rem/M₀` (hrec)
    have hsplit : algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ mult α * N)
        = localPrincipalPart A N α (mult α)
          + algebraMap K[X] (RatFunc K) (localRemainder A N α (mult α))
              / algebraMap K[X] (RatFunc K) N := by
      have := hpeel
      rw [sub_eq_iff_eq_add] at this
      rw [this]; ring
    rw [hsplit, hrec]
    ring

/-- **`Rem/(C c) = algebraMap (c⁻¹ • Rem)`** for a nonzero constant `c`: a quotient by a nonzero scalar is
itself a polynomial (the polynomial part), no division left. Used to close the multi-pole assembly when the
base `M₀ = C c` is a constant (all roots extracted over `K̄`). -/
theorem div_C_eq_algebraMap {Rem : K[X]} {c : K} (hc : c ≠ 0) :
    algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) (Polynomial.C c)
      = algebraMap K[X] (RatFunc K) (Polynomial.C c⁻¹ * Rem) := by
  have hCc : algebraMap K[X] (RatFunc K) (Polynomial.C c) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (by simpa using hc)
  rw [map_mul, div_eq_iff hCc, ← map_mul, ← map_mul]
  congr 1
  rw [mul_right_comm, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1, one_mul]

open Classical in
/-- **P1 capstone — Theorem 2.7.1, the over-the-closure partial fraction with constant base** (Bronstein §2.7,
the literal closure-level conclusion when `D` splits completely): for `D = (∏_{α∈R}(x−α)^{mult α})·C c` with `c`
a nonzero constant (so `R` is the full root set of `D` over `K̄`), there is a polynomial part `P` and a per-pole
principal-part family `PP` (each `PP α = ∑_{j=1}^{mult α} c_{α,j}/(x−α)ʲ` a genuine Laurent sum) with
`A/D = P + ∑_{α∈R} PP α` — the complete partial-fraction decomposition. The constant base `M₀ = C c` makes the
telescoping remainder `Rem/(C c)` a pure polynomial (`div_C_eq_algebraMap`), the polynomial part `P`. The
principal-part coefficients are the engine outputs `Hᵢⱼ(α)` per `localCoeff_eq_laurentH` (up to the residual
peeled-vs-original numerator matching). -/
theorem completePartialFraction_over_closure (A : K[X]) (mult : K → ℕ) (R : Finset K) {c : K}
    (hc : c ≠ 0) :
    ∃ (P : K[X]) (PP : K → RatFunc K),
      algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) (rootProd R mult * Polynomial.C c)
        = algebraMap K[X] (RatFunc K) P + ∑ α ∈ R, PP α := by
  have hpolefree : ∀ α ∈ R, (Polynomial.C c).eval α ≠ 0 := fun α _ => by
    rw [Polynomial.eval_C]; exact hc
  obtain ⟨PP, Rem, hdecomp⟩ := exists_sum_localPrincipalPart (Polynomial.C c) mult R hpolefree A
  refine ⟨Polynomial.C c⁻¹ * Rem, PP, ?_⟩
  rw [hdecomp, div_C_eq_algebraMap hc, add_comm]

/-- Restatement of the P1 remainder-zero fact: a proper `N/M` over a nonzero constant `M` is `0`. -/
example {N M : K[X]} (hM : M.natDegree = 0) (hM0 : M ≠ 0) (hdeg : N.degree < M.degree) :
    algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M = 0 :=
  properRatFunc_const_denom_eq_zero hM hM0 hdeg

/-- Restatement of P1, the multi-pole telescoping (book p.56): subtracting the per-pole principal parts at
every root in `R` leaves a remainder `Rem/M₀` regular at every `α ∈ R`. -/
example (M₀ A : K[X]) (mult : K → ℕ) (R : Finset K) (hpf : ∀ α ∈ R, M₀.eval α ≠ 0) :
    ∃ (PP : K → RatFunc K) (Rem : K[X]),
      algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀)
        = (∑ α ∈ R, PP α) + algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) M₀ :=
  exists_sum_localPrincipalPart M₀ mult R hpf A

/-- Restatement of the P1 capstone (book p.56, the over-the-closure conclusion with split denominator):
`A/D = P + ∑_{α∈R} PP α` for `D = (∏_{α∈R}(x−α)^{mult α})·C c`, `c ≠ 0` (all roots of `D` over `K̄`). -/
example (A : K[X]) (mult : K → ℕ) (R : Finset K) {c : K} (hc : c ≠ 0) :
    ∃ (P : K[X]) (PP : K → RatFunc K),
      algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) (rootProd R mult * Polynomial.C c)
        = algebraMap K[X] (RatFunc K) P + ∑ α ∈ R, PP α :=
  completePartialFraction_over_closure A mult R hc

/-! ## Stage O — principal-part intrinsicity (uniqueness of the principal part at `α`) and the literal
Theorem 2.7.1 conclusion (Bronstein §2.7, the final closing step)

The telescoping `exists_sum_localPrincipalPart` produces, at each pole `α`, the principal part
`PP α = localPrincipalPart A' N α i` of the **running (peeled) numerator** `A'` over the running cofactor
`N` — a correct singular part of `A/D` at `α`, but with numerators differing from the original-`A` engine
form. Principal-part **intrinsicity** closes this gap: the principal part of a rational function at `α` is
**unique** (independent of how the rest is split off), so `PP α` coincides with `localPrincipalPart A Mα α i`
for the original cofactor `Mα = D /ₘ (X−α)^i`, whose coefficients ARE the engine outputs `Hᵢⱼ(α)`
(`localCoeff_eq_laurentH`).

The mechanism: a principal part at `α` of order `i` consolidates (over the common denominator `(X−α)^i`) to
`W/(X−α)^i` with `deg W < i` (`localPrincipalPart_eq_div`, `degree_modByMonic_lt`). If such a `W/(X−α)^i`
equals a function `N/M` **regular at `α`** (`M(α) ≠ 0`), then cross-multiplying gives `(X−α)^i ∣ W·M`;
coprimality of `(X−α)^i` to `M` forces `(X−α)^i ∣ W`, and `deg W < i` forces `W = 0`. Hence two principal
parts at `α` whose difference is regular at `α` are equal (`principalPart_unique`). -/

/-- **A bounded-degree principal part `W/(X−α)^i` equal to a function regular at `α` is `0`** (§2.7, the
intrinsicity core): if `algebraMap W / (algebraMap (X−α))^i = algebraMap N / algebraMap M` with `M(α) ≠ 0`
and `deg W < i`, then `W = 0`. Cross-multiplying gives the polynomial identity `W·M = N·(X−α)^i`, so
`(X−α)^i ∣ W·M`; since `(X−α)^i` is coprime to `M` (`M(α) ≠ 0`), `(X−α)^i ∣ W`, and `deg W < i = deg (X−α)^i`
forces `W = 0` (`eq_zero_of_dvd_of_degree_lt`). -/
theorem eq_zero_of_div_pow_eq_regular {W N M : K[X]} {α : K} (i : ℕ) (hM : M.eval α ≠ 0)
    (hW : W.degree < ((Polynomial.X - Polynomial.C α) ^ i).degree)
    (heq : algebraMap K[X] (RatFunc K) W
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i
          = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M) :
    W = 0 := by
  have hX0 : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hM0 : algebraMap K[X] (RatFunc K) M ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hM (by rw [h, Polynomial.eval_zero]))
  -- cross-multiply the `RatFunc` identity to a polynomial identity `W·M = N·(X−α)^i`
  rw [div_eq_div_iff (pow_ne_zero i hX0) hM0, ← map_pow, ← map_mul, ← map_mul] at heq
  have hpoly : W * M = N * (Polynomial.X - Polynomial.C α) ^ i :=
    RatFunc.algebraMap_injective K heq
  -- `(X−α)^i ∣ W·M`, coprime to `M`, so `(X−α)^i ∣ W`; then `deg W < i` forces `W = 0`
  have hdvd : (Polynomial.X - Polynomial.C α) ^ i ∣ W * M := ⟨N, by rw [hpoly]; ring⟩
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C α) ^ i) M :=
    (isCoprime_M_X_sub_C_pow i hM).symm
  exact eq_zero_of_dvd_of_degree_lt (hcop.dvd_of_dvd_mul_right hdvd) hW

/-- **Principal-part intrinsicity / uniqueness at `α`** (§2.7, the closing step): two principal parts at `α`
of order `i` whose difference is regular at `α` are equal. Concretely, if
`localPrincipalPart A₁ M₁ α i + r₁ = localPrincipalPart A₂ M₂ α i + r₂` where `r₁, r₂` are functions regular
at `α` (here both `Nₖ/Mₖ` with `Mₖ(α) ≠ 0`), then `localPrincipalPart A₁ M₁ α i = localPrincipalPart A₂ M₂ α i`.
Consolidating both principal parts to `Wₖ/(X−α)^i` (`localPrincipalPart_eq_div`, `deg Wₖ < i`), their
difference `(W₁−W₂)/(X−α)^i` equals the regular `r₂ − r₁` (a single quotient `N/M`, `M(α) ≠ 0`), so
`W₁ − W₂ = 0` (`eq_zero_of_div_pow_eq_regular`); hence `W₁ = W₂` and the principal parts agree. -/
theorem principalPart_unique {A₁ M₁ A₂ M₂ N₁ N₂ Md₁ Md₂ : K[X]} {α : K} (i : ℕ)
    (hMd₁ : Md₁.eval α ≠ 0) (hMd₂ : Md₂.eval α ≠ 0)
    (heq : localPrincipalPart A₁ M₁ α i
            + algebraMap K[X] (RatFunc K) N₁ / algebraMap K[X] (RatFunc K) Md₁
          = localPrincipalPart A₂ M₂ α i
            + algebraMap K[X] (RatFunc K) N₂ / algebraMap K[X] (RatFunc K) Md₂) :
    localPrincipalPart A₁ M₁ α i = localPrincipalPart A₂ M₂ α i := by
  set W₁ := localApprox A₁ M₁ α i with hW₁
  set W₂ := localApprox A₂ M₂ α i with hW₂
  have hX0 : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hMd₁0 : algebraMap K[X] (RatFunc K) Md₁ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hMd₁ (by rw [h, Polynomial.eval_zero]))
  have hMd₂0 : algebraMap K[X] (RatFunc K) Md₂ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hMd₂ (by rw [h, Polynomial.eval_zero]))
  have hDp0 : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i ≠ 0 :=
    pow_ne_zero i hX0
  have hMd₁₂0 : algebraMap K[X] (RatFunc K) (Md₁ * Md₂) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hMd₁0 hMd₂0
  -- consolidate both principal parts to the common `(X−α)^i` denominator
  rw [localPrincipalPart_eq_div, localPrincipalPart_eq_div, ← hW₁, ← hW₂] at heq
  -- the polynomial cross-identity `(W₁ − W₂)·(Md₁·Md₂) = (N₂·Md₁ − N₁·Md₂)·(X−α)^i`, from `heq`
  -- rearrange `heq` so the shared `D^i` denominator combines on one side
  have heqsub : algebraMap K[X] (RatFunc K) (W₁ - W₂)
        / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i
      = algebraMap K[X] (RatFunc K) N₂ / algebraMap K[X] (RatFunc K) Md₂
        - algebraMap K[X] (RatFunc K) N₁ / algebraMap K[X] (RatFunc K) Md₁ := by
    rw [map_sub, sub_div]
    linear_combination heq
  have hpolyid : (W₁ - W₂) * (Md₁ * Md₂)
      = (N₂ * Md₁ - N₁ * Md₂) * (Polynomial.X - Polynomial.C α) ^ i := by
    apply RatFunc.algebraMap_injective K
    rw [div_sub_div _ _ hMd₂0 hMd₁0,
      div_eq_div_iff hDp0 (mul_ne_zero hMd₂0 hMd₁0)] at heqsub
    simp only [map_mul, map_sub, map_pow] at heqsub ⊢
    ring_nf
    ring_nf at heqsub
    linear_combination heqsub
  -- `(W₁−W₂)/(X−α)^i = (N₂·Md₁ − N₁·Md₂)/(Md₁·Md₂)`, regular at `α`
  have hdiff : algebraMap K[X] (RatFunc K) (W₁ - W₂)
        / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i
      = algebraMap K[X] (RatFunc K) (N₂ * Md₁ - N₁ * Md₂)
        / algebraMap K[X] (RatFunc K) (Md₁ * Md₂) := by
    rw [div_eq_div_iff hDp0 hMd₁₂0, ← map_pow, ← map_mul, ← map_mul, hpolyid]
  -- the difference numerator has degree `< i` (each `Wₖ` is a `%ₘ (X−α)^i`)
  have hdeg : (W₁ - W₂).degree < ((Polynomial.X - Polynomial.C α) ^ i).degree := by
    have hmonic : ((Polynomial.X - Polynomial.C α) ^ i).Monic := (monic_X_sub_C α).pow i
    have h1 : W₁.degree < ((Polynomial.X - Polynomial.C α) ^ i).degree := by
      rw [hW₁, localApprox]; exact degree_modByMonic_lt _ hmonic
    have h2 : W₂.degree < ((Polynomial.X - Polynomial.C α) ^ i).degree := by
      rw [hW₂, localApprox]; exact degree_modByMonic_lt _ hmonic
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt h1 h2)
  -- `W₁ − W₂ = 0` by the intrinsicity core, so the principal parts agree
  have hMM : (Md₁ * Md₂).eval α ≠ 0 := by
    rw [Polynomial.eval_mul]; exact mul_ne_zero hMd₁ hMd₂
  have hWeq : W₁ - W₂ = 0 := eq_zero_of_div_pow_eq_regular i hMM hdeg hdiff
  rw [localPrincipalPart_eq_div, localPrincipalPart_eq_div, ← hW₁, ← hW₂,
    sub_eq_zero.mp hWeq]

/-- **The principal part in engine form `∑_{j=1}^{i} Hᵢⱼ(α)/(x−α)ʲ`** (§2.7, Theorem 2.7.1, the literal
per-pole conclusion): at a root `α` of the monic `Dᵢ = (x−α)·Dᵢ,α`, the principal part of `A/D` at `α`
(`localPrincipalPart A M α i`, `M = Dᵢ,α^i·Eᵢ` the original cofactor with `D = (x−α)ⁱ·M`) is **literally** the
Bronstein–Salvy engine sum `∑_{j=1}^{i} (laurentH A D Dᵢ i j)(α)/(x−α)ʲ`. Each Laurent coefficient
`localCoeff A M α i (i−j)` is the engine output `Hᵢⱼ(α)` (`localCoeff_eq_laurentH`, with `i−(i−j)=j` for
`1 ≤ j ≤ i`, so the `i−j < i` hypothesis holds). This is the precise sense in which the engine `Hᵢⱼ` are the
partial-fraction Laurent coefficients of `A/D`. -/
theorem localPrincipalPart_eq_engineSum [CharZero K] (A D Di Diα : K[X]) {α : K} (i : ℕ)
    (hi : 0 < i) (hroot : IsLaurentRegularRoot D Di Diα α i) :
    localPrincipalPart A (lDenomα (laurentE D Di i) Diα i 0) α i
      = ∑ j ∈ Finset.Icc 1 i,
          algebraMap K[X] (RatFunc K) (Polynomial.C ((laurentH A D Di i j).eval α))
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j := by
  rw [localPrincipalPart]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_Icc] at hj
  -- the `j`-th Laurent coefficient `localCoeff A M α i (i−j) = Hᵢⱼ(α)`
  rw [localCoeff_eq_laurentH A D Di Diα i (i - j) hi (by omega) hroot,
    show i - (i - j) = j from by omega]

/-! ## Stage P — the literal Theorem 2.7.1 conclusion over the algebraic closure (engine form) -/

open Classical in
/-- **Theorem 2.7.1, the literal partial fraction `A/D = P + ∑ᵢ ∑_α ∑_{j=1}^{i} Hᵢⱼ(α)/(x−α)ʲ`** (Bronstein
§2.7, the closure-level conclusion, engine form): for `D = (∏_{α∈R}(x−α)^{mult α})·C c` split over `K̄`
(`c ≠ 0`), there is a polynomial part `P` and a per-pole principal-part family `PP` with
`A/D = P + ∑_{α∈R} PP α`, where each `PP α` is a genuine Laurent sum `∑_{j=1}^{mult α} c_{α,j}/(x−α)ʲ` (the
principal part of `A/D` at `α`). By `localPrincipalPart_eq_engineSum`, each such per-pole principal part is the
engine sum `∑_{j=1}^{mult α} Hᵢⱼ(α)/(x−α)ʲ` once `PP α` is identified (via principal-part intrinsicity,
`principalPart_unique`) with `localPrincipalPart` of the original numerator. This is the over-the-closure
`completePartialFraction_over_closure` packaged as the book conclusion. -/
theorem completePartialFraction_thm_2_7_1 (A : K[X]) (mult : K → ℕ) (R : Finset K) {c : K}
    (hc : c ≠ 0) :
    ∃ (P : K[X]) (PP : K → RatFunc K),
      algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) (rootProd R mult * Polynomial.C c)
        = algebraMap K[X] (RatFunc K) P + ∑ α ∈ R, PP α :=
  completePartialFraction_over_closure A mult R hc

/-- **Per-pole intrinsic identification of any principal part with the engine sum** (§2.7, the bridge from
the telescoping's per-pole `PP α` to the literal engine form): at a root `α` of the monic
`Dᵢ = (x−α)·Dᵢ,α`, with `D = (x−α)ⁱ·M`, `M = Dᵢ,α^i·Eᵢ` (`Eᵢ = laurentE D Dᵢ i`) the original cofactor, IF a
candidate Laurent sum `q` (a principal part at `α`, given as `localPrincipalPart A' M' α i` for some peeled
data `A', M'`) has the property that `A/D − q` is **regular at `α`** (`= N/Md`, `Md(α) ≠ 0`), then `q` is
**literally** the engine sum `∑_{j=1}^{i} (laurentH A D Dᵢ i j)(α)/(x−α)ʲ`. By principal-part intrinsicity
(`principalPart_unique`, since `A/D − q` and `A/D − localPrincipalPart A M α i` are both regular at `α`),
`q = localPrincipalPart A M α i`, which is the engine sum by `localPrincipalPart_eq_engineSum`. This closes
the peeled-vs-original numerator matching: the intrinsic principal part is the original-`A` engine sum
regardless of how it was computed. -/
theorem principalPart_eq_engineSum_of_regular [CharZero K] {A A' M' N Md D Di Diα : K[X]} {α : K}
    (i : ℕ) (hi : 0 < i) (hroot : IsLaurentRegularRoot D Di Diα α i) (hMd : Md.eval α ≠ 0)
    (hreg : algebraMap K[X] (RatFunc K) A
              / algebraMap K[X] (RatFunc K)
                  ((Polynomial.X - Polynomial.C α) ^ i * lDenomα (laurentE D Di i) Diα i 0)
            - localPrincipalPart A' M' α i
          = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) Md) :
    localPrincipalPart A' M' α i
      = ∑ j ∈ Finset.Icc 1 i,
          algebraMap K[X] (RatFunc K) (Polynomial.C ((laurentH A D Di i j).eval α))
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j := by
  set M := lDenomα (laurentE D Di i) Diα i 0 with hMdef
  have hM : M.eval α ≠ 0 := by
    rw [hMdef, lDenomα, Nat.add_zero, Nat.zero_add, pow_one, Polynomial.eval_mul, Polynomial.eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hroot.cofactor_eval_ne) hroot.laurentE_eval_ne
  -- `q` and `localPrincipalPart A M α i` are both principal parts of `A/D` at `α`, rest regular at `α`
  have hcanon := subtract_localPrincipalPart_eq A M i hM
  -- `q + N/Md = localPrincipalPart A M α i + R/M` (both equal `A/D`)
  have heq : localPrincipalPart A' M' α i
        + algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) Md
      = localPrincipalPart A M α i
        + algebraMap K[X] (RatFunc K) (localRemainder A M α i) / algebraMap K[X] (RatFunc K) M := by
    -- both sides equal `A/D = A/((x−α)^i·M)`: `hreg` gives the LHS, `hcanon` the RHS
    linear_combination hcanon - hreg
  -- uniqueness: `q = localPrincipalPart A M α i`, then engine form
  rw [principalPart_unique i hMd hM heq,
    localPrincipalPart_eq_engineSum A D Di Diα i hi hroot]

/-! ## Stage Q — regularity at `α` and the fully-assembled engine-form capstone -/

open Classical in
/-- **P1, the multi-pole telescoping with per-pole regularity certificate** (§2.7, the strengthened
assembly): like `exists_sum_localPrincipalPart`, but additionally certifies that for **each** pole `α ∈ R`,
subtracting *only* its own principal part `PP α` from the whole fraction leaves a function **regular at `α`**
(`RegularAt α (A/(∏·M₀) − PP α)`). This is the hypothesis `principalPart_eq_engineSum_of_regular` needs to
upgrade each peeled `PP α` to the original-`A` engine sum. Proof: at each peel `α₀`, the whole minus its own
principal part is exactly the local remainder `localRemainder/N` (regular at `α₀` since `N(α₀) ≠ 0`); for the
already-processed `γ ≠ α₀`, the peeled `α₀`-principal part is regular at `γ` (`RegularAt.localPrincipalPart`)
and the recursive certificate gives the rest, so their sum is regular at `γ` (`RegularAt.add`). -/
theorem exists_sum_localPrincipalPart_regular (M₀ : K[X]) (mult : K → ℕ) :
    ∀ (R : Finset K), (∀ α ∈ R, M₀.eval α ≠ 0) → ∀ (A : K[X]),
      ∃ (PP : K → RatFunc K) (Rem : K[X]),
        algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀)
          = (∑ α ∈ R, PP α) + algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) M₀
        ∧ (∀ α ∈ R, RegularAt α
            (algebraMap K[X] (RatFunc K) A
                / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀) - PP α))
        ∧ ∀ α ∈ R, ∃ (A' M' : K[X]), PP α = localPrincipalPart A' M' α (mult α) := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _ A
    exact ⟨fun _ => 0, A, by rw [rootProd_empty, one_mul, Finset.sum_empty, zero_add],
      (fun α hα => by simp at hα), fun α hα => by simp at hα⟩
  | @insert α₀ R hα₀ ih =>
    intro hpolefree A
    set N := rootProd R mult * M₀ with hNdef
    have hNα₀ : N.eval α₀ ≠ 0 := by
      rw [hNdef, Polynomial.eval_mul]
      exact mul_ne_zero (eval_rootProd_ne_zero mult hα₀)
        (hpolefree α₀ (Finset.mem_insert_self α₀ R))
    have hpeel := subtract_localPrincipalPart_eq A N (mult α₀) hNα₀
    obtain ⟨PP, Rem, hrec, hregrec, hstructrec⟩ :=
      ih (fun β hβ => hpolefree β (Finset.mem_insert_of_mem hβ)) (localRemainder A N α₀ (mult α₀))
    refine ⟨fun β => if β = α₀ then localPrincipalPart A N α₀ (mult α₀) else PP β, Rem, ?_, ?_, ?_⟩
    · -- the decomposition equation (as in `exists_sum_localPrincipalPart`)
      simp only [Finset.sum_insert hα₀, if_pos]
      have hsumR : (∑ β ∈ R, (if β = α₀ then localPrincipalPart A N α₀ (mult α₀) else PP β))
          = ∑ β ∈ R, PP β :=
        Finset.sum_congr rfl fun β hβ => if_neg (show β ≠ α₀ from fun h => hα₀ (h ▸ hβ))
      rw [hsumR]
      have hden : rootProd (insert α₀ R) mult * M₀
          = (Polynomial.X - Polynomial.C α₀) ^ mult α₀ * N := by
        rw [rootProd_insert mult hα₀, hNdef]; ring
      rw [hden]
      have hsplit : algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α₀) ^ mult α₀ * N)
          = localPrincipalPart A N α₀ (mult α₀)
            + algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                / algebraMap K[X] (RatFunc K) N := by
        rw [sub_eq_iff_eq_add] at hpeel; rw [hpeel]; ring
      rw [hsplit, hrec]; ring
    · -- the per-pole regularity certificate
      intro γ hγ
      -- the whole fraction over `insert α₀ R`
      have hden : rootProd (insert α₀ R) mult * M₀
          = (Polynomial.X - Polynomial.C α₀) ^ mult α₀ * N := by
        rw [rootProd_insert mult hα₀, hNdef]; ring
      -- whole = PP(α₀) + localRemainder/N  (the peel)
      have hwhole : algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) (rootProd (insert α₀ R) mult * M₀)
          = localPrincipalPart A N α₀ (mult α₀)
            + algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                / algebraMap K[X] (RatFunc K) N := by
        rw [sub_eq_iff_eq_add] at hpeel; rw [hden, hpeel]; ring
      rw [hwhole]
      simp only []  -- beta-reduce the `PP'` lambda applied to `γ`
      rcases eq_or_ne γ α₀ with hγα₀ | hγα₀
      · -- γ = α₀: whole − PP(α₀) = localRemainder/N, regular at α₀ (`N(α₀) ≠ 0`)
        subst hγα₀
        rw [if_pos rfl, add_sub_cancel_left]
        exact ⟨localRemainder A N γ (mult γ), N, hNα₀, rfl⟩
      · -- γ ≠ α₀: whole − PP(γ) = PP(α₀) + (localRemainder/N − PP(γ)); both summands regular at γ
        rw [if_neg hγα₀]
        have hmemR : γ ∈ R := Finset.mem_of_mem_insert_of_ne hγ hγα₀
        have h1 : RegularAt γ (localPrincipalPart A N α₀ (mult α₀)) :=
          RegularAt.localPrincipalPart hγα₀ A N (mult α₀)
        have h2 : RegularAt γ
            (algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                / algebraMap K[X] (RatFunc K) N - PP γ) := hregrec γ hmemR
        have hrw : localPrincipalPart A N α₀ (mult α₀)
              + algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                  / algebraMap K[X] (RatFunc K) N - PP γ
            = localPrincipalPart A N α₀ (mult α₀)
              + (algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                  / algebraMap K[X] (RatFunc K) N - PP γ) := by ring
        rw [hrw]
        exact h1.add h2
    · -- each `PP α` is a `localPrincipalPart` (explicitly for `α₀`, by IH for `α ∈ R`)
      intro γ hγ
      simp only []
      rcases eq_or_ne γ α₀ with hγα₀ | hγα₀
      · subst hγα₀; exact ⟨A, N, by rw [if_pos rfl]⟩
      · rw [if_neg hγα₀]
        exact hstructrec γ (Finset.mem_of_mem_insert_of_ne hγ hγα₀)

open Classical in
/-- **Theorem 2.7.1, the LITERAL engine-form partial fraction `A/D = P + ∑_α ∑_{j=1}^{mult α} Hᵢⱼ(α)/(x−α)ʲ`**
(Bronstein §2.7, the full closure-level conclusion): for `D = (∏_{α∈R}(x−α)^{mult α})·C c` split over `K̄`
(`c ≠ 0`), GIVEN per-pole squarefree-factorization data `pole α` (a monic `Dᵢ = (x−α)·Dᵢ,α` with `α` its root,
the cofactor coprimalities, the base-value nonvanishing, `0 < mult α`, and the original factorization
`D = (x−α)^{mult α}·(Dᵢ,α^{mult α}·Eᵢ)`), there is a polynomial part `P` with
`A/D = P + ∑_{α∈R} ∑_{j=1}^{mult α} (laurentH A D Dᵢ (mult α) j)(α)/(x−α)ʲ` — the engine outputs `Hᵢⱼ(α)` ARE
the partial-fraction Laurent coefficients. Each per-pole principal part from the telescoping
(`exists_sum_localPrincipalPart_regular`) is identified with the original-`A` engine sum by principal-part
intrinsicity (`principalPart_eq_engineSum_of_regular`), the per-pole `RegularAt α (A/D − PP α)` certificate
supplying the needed regularity. This is the complete, literal Theorem 2.7.1 over the algebraic closure. -/
theorem completePartialFraction_engineForm [CharZero K] (A : K[X]) (mult : K → ℕ) (R : Finset K)
    {c : K} (hc : c ≠ 0)
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
                / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j := by
  set D := rootProd R mult * Polynomial.C c with hDdef
  have hpolefree : ∀ α ∈ R, (Polynomial.C c).eval α ≠ 0 := fun α _ => by
    rw [Polynomial.eval_C]; exact hc
  obtain ⟨PP, Rem, hdecomp, hreg, hstruct⟩ :=
    exists_sum_localPrincipalPart_regular (Polynomial.C c) mult R hpolefree A
  refine ⟨Polynomial.C c⁻¹ * Rem, ?_⟩
  -- each `PP α` equals its engine sum, by intrinsicity
  have hPPeng : ∀ α ∈ R, PP α
      = ∑ j ∈ Finset.Icc 1 (mult α),
          algebraMap K[X] (RatFunc K) (Polynomial.C ((laurentH A D (Di α) (mult α) j).eval α))
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j := by
    intro α hα
    obtain ⟨hi, hDimonic, hDiα0root, hfac, hcopE, hcopD, hEi, hDiαα, hDfac⟩ := pole α hα
    obtain ⟨A', M', hPPeq⟩ := hstruct α hα
    obtain ⟨N, Md, hMd, hregdiv⟩ := (hreg α hα).exists_div
    rw [hPPeq]
    -- assemble the `hreg`-certificate into the input shape of `principalPart_eq_engineSum_of_regular`
    apply principalPart_eq_engineSum_of_regular (D := D) (mult α) hi
      ⟨hDimonic, hDiα0root, hfac, hcopE, hcopD, hEi, hDiαα⟩ hMd
    -- the goal denominator `(x−α)^{mult α}·lDenomα… = D` (`hDfac`); rest is `hreg`'s certificate
    rw [← hDfac, ← hPPeq]
    exact hregdiv
  -- rewrite the sum and fold the constant remainder into the polynomial part
  rw [hdecomp, div_C_eq_algebraMap hc, add_comm]
  congr 1
  exact Finset.sum_congr rfl hPPeng

/-- Restatement of the principal-part intrinsicity / uniqueness (book §2.7, the closing fact): two principal
parts at `α` of order `i` whose difference is regular at `α` are equal. -/
example {A₁ M₁ A₂ M₂ N₁ N₂ Md₁ Md₂ : K[X]} {α : K} (i : ℕ) (hMd₁ : Md₁.eval α ≠ 0)
    (hMd₂ : Md₂.eval α ≠ 0)
    (heq : localPrincipalPart A₁ M₁ α i
            + algebraMap K[X] (RatFunc K) N₁ / algebraMap K[X] (RatFunc K) Md₁
          = localPrincipalPart A₂ M₂ α i
            + algebraMap K[X] (RatFunc K) N₂ / algebraMap K[X] (RatFunc K) Md₂) :
    localPrincipalPart A₁ M₁ α i = localPrincipalPart A₂ M₂ α i :=
  principalPart_unique i hMd₁ hMd₂ heq

/-- Restatement of the literal per-pole engine form (book p.56): the principal part of `A/D` at a root `α` of
`Dᵢ` is `∑_{j=1}^{i} Hᵢⱼ(α)/(x−α)ʲ`, the Bronstein–Salvy engine sum. -/
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

/-- Restatement of the literal Theorem 2.7.1 over `K̄` (book p.55–56), engine form:
`A/D = P + ∑ᵢ ∑_{α|Dᵢ(α)=0} (Hᵢᵢ(α)/(x−α)ⁱ + ⋯ + Hᵢ₁(α)/(x−α))`, the engine outputs `Hᵢⱼ(α)` being the
partial-fraction Laurent coefficients of `A/D`. -/
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
