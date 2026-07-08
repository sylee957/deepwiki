import DeepWiki.SymbolicIntegration.Core.Differential.DifferentialPolynomials
import DeepWiki.SymbolicIntegration.LaurentCoefficients.Cofactors

/-! # Laurent numerator recursion

Differential-polynomial numerator recurrence for Laurent coefficients. -/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

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

/-- `laurentNum A Ei i 0 = dpEmbed A`. -/
@[simp] theorem laurentNum_zero (A Ei : K[X]) (i : ℕ) :
    laurentNum A Ei i 0 = dpEmbed A := rfl

/-- One step of the Laurent numerator recurrence. -/
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

end DeepWiki.SymbolicIntegration
