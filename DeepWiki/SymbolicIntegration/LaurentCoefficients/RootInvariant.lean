import DeepWiki.SymbolicIntegration.LaurentCoefficients.FractionInvariant
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionDerivative

/-! # Laurent root rational invariant

Specialized rational-function invariants after substituting a linear root factor. -/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

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
  rw [diffSubst_ddx, diffSubst_ddx, diffSubst_lDenom] at h
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
  have hk : ∀ p : K[X], ratFuncKDeriv (algebraMap K[X] (RatFunc K) p)
      = algebraMap K[X] (RatFunc K) (derivative p) := fun p => ratFuncDeriv_algebraMap p
  rw [lFracα, lFracα, Derivation.leibniz_div, hk, hk]
  simp only [smul_eq_mul, Algebra.smul_def]
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

end DeepWiki.SymbolicIntegration
