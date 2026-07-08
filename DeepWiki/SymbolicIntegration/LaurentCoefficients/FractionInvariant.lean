import DeepWiki.SymbolicIntegration.Core.Differential.DiffPolyFractionDeriv
import DeepWiki.SymbolicIntegration.LaurentCoefficients.Base

/-! # Laurent fraction invariants

Fraction-field denominator and derivative invariants for the Laurent-coefficient recursion. -/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

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

end DeepWiki.SymbolicIntegration
