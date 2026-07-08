import DeepWiki.SymbolicIntegration.DifferentialFields

/-! # Rational-integration identities
Differential-field identities for rational-function integration: Hermite lowering, one-shot
Horowitz reduction, elementary powers, quadratic terms, logarithm-to-arctangent conversion,
and worked rational-integration traces. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {F : Type*} [Field F] [Differential F]

/-- If `Q = -(m+1) * (B * V′ + C * V)`, then `Q / V^(m+2)` lowers to a derivative plus denominator `V^(m+1)`. -/
theorem hermite_reduction_step (B C V : F) (hV : V ≠ 0) (m : ℕ) :
    (-((m : F) + 1) * (B * V′ + C * V)) / V ^ (m + 2)
      = (B / V ^ (m + 1))′ + (-((m : F) + 1) * C - B′) / V ^ (m + 1) := by
  rw [deriv_div, deriv_pow]
  simp only [Nat.add_sub_cancel]
  field_simp
  push_cast
  ring

/-- If `E * Dminus = Dminus′ * Dstar`, then `(B′ * Dstar - B * E + C * Dminus) / (Dminus * Dstar)` splits as `(B / Dminus)′ + C / Dstar`. -/
theorem horowitz_reduction_step (B C Dminus Dstar E : F) (hDm : Dminus ≠ 0) (hDs : Dstar ≠ 0)
    (hE : E * Dminus = Dminus′ * Dstar) :
    (B′ * Dstar - B * E + C * Dminus) / (Dminus * Dstar)
      = (B / Dminus)′ + C / Dstar := by
  rw [deriv_div]
  field_simp
  linear_combination -B * hE

/-- When `t′ = 1` and `n` is nonzero in the field, `(t ^ n / n)′ = t ^ (n - 1)`. -/
theorem deriv_zpow_div_self {t : F} (ht : t′ = 1) {n : ℤ} (hn : (n : F) ≠ 0) :
    (t ^ n / (n : F))′ = t ^ (n - 1) := by
  have hn0 : ((n : F))′ = 0 := by simp
  rw [Differential.deriv.leibniz_div_const (t ^ n) (n : F) hn0,
    smul_eq_mul, deriv_zpow, ht, mul_one, inv_mul_cancel_left₀ hn]

/-- If `t′ = 1`, then `logDeriv t = t⁻¹`. -/
theorem logDeriv_eq_inv {t : F} (ht : t′ = 1) : Differential.logDeriv t = t⁻¹ := by
  rw [Differential.logDeriv, ht, one_div]

/-- Given logarithm and arctangent derivative laws for a quadratic, their weighted sum has derivative `(B * t + C) / (t ^ 2 + b * t + c)`. -/
theorem deriv_logArctan_eq_quadratic [CharZero F] {t : F}
    {B C b c s L Θ : F} (hB : B′ = 0) (hC : C′ = 0) (hb : b′ = 0) (hs : s′ = 0)
    (hs2 : s ^ 2 = 4 * c - b ^ 2) (hsne : s ≠ 0)
    (hL : L′ = (2 * t + b) / (t ^ 2 + b * t + c))
    (hΘ : Θ′ = (2 / s) / (1 + ((2 * t + b) / s) ^ 2)) :
    ((B / 2) * L + ((2 * C - b * B) / s) * Θ)′ = (B * t + C) / (t ^ 2 + b * t + c) := by
  have h2 : (2 : F)′ = 0 := mem_constants.mp (by norm_num)
  have hβ : (B / 2)′ = 0 := by rw [deriv_div, hB, h2]; ring
  have hnum : (2 * C - b * B)′ = 0 := by
    rw [map_sub, deriv_const_mul _ h2, deriv_const_mul _ hb, hC, hB]; ring
  have hγ : ((2 * C - b * B) / s)′ = 0 := by rw [deriv_div, hnum, hs]; ring
  have hu2 : 1 + ((2 * t + b) / s) ^ 2 = 4 * (t ^ 2 + b * t + c) / s ^ 2 := by
    rw [div_pow]; field_simp; linear_combination hs2
  have hΘ' : Θ′ = s / (2 * (t ^ 2 + b * t + c)) := by
    rw [hΘ, hu2]; field_simp; ring
  rw [map_add, deriv_const_mul _ hβ, deriv_const_mul _ hγ, hL, hΘ']
  field_simp
  ring

/-- The numerator balance for reducing powers of a quadratic denominator. -/
theorem quadraticPow_reduce_core {R : Type*} [CommRing R] (t B C b c : R) :
    2 * (2 * C - b * B) * (t ^ 2 + b * t + c)
        - (2 * t + b) * ((2 * C - b * B) * t + (b * C - 2 * c * B))
      = (B * t + C) * (4 * c - b ^ 2) := by ring

/-- The derivative of the quadratic-power reduction term plus its residual equals `(B * t + C) / q^(m+2)`. -/
theorem deriv_quadraticPow_reduce [CharZero F] {t : F}
    (ht : t′ = 1) {B C b c : F} (hB : B′ = 0) (hC : C′ = 0) (hb : b′ = 0) (hc : c′ = 0)
    (hR : 4 * c - b ^ 2 ≠ 0) (hq : t ^ 2 + b * t + c ≠ 0) (m : ℕ) :
    (((2 * C - b * B) * t + (b * C - 2 * c * B))
        / (((m : F) + 1) * (4 * c - b ^ 2) * (t ^ 2 + b * t + c) ^ (m + 1)))′
      + ((2 * (m : F) + 1) * (2 * C - b * B))
        / (((m : F) + 1) * (4 * c - b ^ 2) * (t ^ 2 + b * t + c) ^ (m + 1))
      = (B * t + C) / (t ^ 2 + b * t + c) ^ (m + 2) := by
  have h2 : (2 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h4 : (4 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h1' : (1 : F)′ = 0 := mem_constants.mp (by norm_num)
  have hmc : ((m : F))′ = 0 := by simp
  have hq' : (t ^ 2 + b * t + c)′ = 2 * t + b := by
    rw [map_add, map_add, deriv_pow, deriv_const_mul _ hb, hc, ht]; ring
  have hcoef1 : (2 * C - b * B)′ = 0 := by
    rw [map_sub, deriv_const_mul _ h2, deriv_const_mul _ hb, hC, hB]; ring
  have h2c : (2 * c)′ = 0 := by rw [deriv_const_mul _ h2, hc]; ring
  have hcoef2 : (b * C - 2 * c * B)′ = 0 := by
    rw [map_sub, deriv_const_mul _ hb, deriv_const_mul _ h2c, hC, hB]; ring
  have hP' : ((2 * C - b * B) * t + (b * C - 2 * c * B))′ = 2 * C - b * B := by
    rw [map_add, deriv_const_mul _ hcoef1, hcoef2, ht]; ring
  have hKconst : (((m : F) + 1))′ = 0 := by rw [map_add, hmc, h1']; ring
  have h4cb : (4 * c - b ^ 2)′ = 0 := by
    rw [map_sub, deriv_const_mul _ h4, hc, deriv_pow, hb]; ring
  have hK : (((m : F) + 1) * (4 * c - b ^ 2))′ = 0 := by
    rw [deriv_const_mul _ hKconst, h4cb]; ring
  have hcore := quadraticPow_reduce_core t B C b c
  have hRatDeriv : (((2 * C - b * B) * t + (b * C - 2 * c * B))
        / (((m : F) + 1) * (4 * c - b ^ 2) * (t ^ 2 + b * t + c) ^ (m + 1)))′
      = ((t ^ 2 + b * t + c) * (2 * C - b * B)
          - ((m : F) + 1) * (2 * t + b) * ((2 * C - b * B) * t + (b * C - 2 * c * B)))
        / (((m : F) + 1) * (4 * c - b ^ 2) * (t ^ 2 + b * t + c) ^ (m + 2)) := by
    rw [deriv_div, hP', deriv_const_mul _ hK, deriv_pow, hq']
    simp only [Nat.add_sub_cancel]
    set q := t ^ 2 + b * t + c
    clear_value q
    field_simp
    push_cast
    ring
  rw [hRatDeriv]
  set q := t ^ 2 + b * t + c with hqdef
  clear_value q
  set R := 4 * c - b ^ 2 with hRdef
  clear_value R
  have hpow : q ^ (m + 2) = q ^ (m + 1) * q := pow_succ q (m + 1)
  simp only [hpow]
  have hQne : q ^ (m + 1) ≠ 0 := pow_ne_zero _ hq
  set Q := q ^ (m + 1) with hQdef
  clear_value Q
  field_simp
  linear_combination ((m : F) + 1) * hcore

/-- If `i ^ 2 = -1` and `i` is constant, then `i * logDeriv ((u + i) / (u - i)) = 2 * (u′ / (1 + u ^ 2))`. -/
theorem logDeriv_imagQuot_eq_arctanDeriv {i u : F} (hi : i ^ 2 = -1)
    (hi' : i′ = 0) (h1 : u + i ≠ 0) (h2 : u - i ≠ 0) :
    i * Differential.logDeriv ((u + i) / (u - i)) = 2 * (u′ / (1 + u ^ 2)) := by
  have hq : (1 + u ^ 2 : F) = (u + i) * (u - i) := by linear_combination hi
  rw [Differential.logDeriv, deriv_div, map_add, map_sub, hi', hq]
  field_simp
  linear_combination (-2 * u′) * hi

/-! ## Worked rational-integration examples -/

/-- `1/(t³+t) = 1/t − (1/2)/(t+i) − (1/2)/(t−i)` when `i² = −1`. -/
theorem inv_cubic_partialFraction {F : Type*} [Field F] [CharZero F] (t i : F) (hi : i ^ 2 = -1)
    (ht : t ≠ 0) (h1 : t + i ≠ 0) (h2 : t - i ≠ 0) :
    1 / (t ^ 3 + t) = 1 / t - (1 / 2) / (t + i) - (1 / 2) / (t - i) := by
  have hfac : t ^ 3 + t = t * (t + i) * (t - i) := by linear_combination t * hi
  have key : (1 : F) / t - (1 / 2) / (t + i) - (1 / 2) / (t - i) = -(i ^ 2) / (t ^ 3 + t) := by
    rw [hfac]; field_simp; ring
  rw [key, hi]; norm_num

/-- Rothstein-Trager residue-gcd cofactorizations of `D` and `A−aD'` for `4a²+1 = 0`. -/
theorem rothsteinTrager_gcd_example {F : Type*} [Field F] (a : F) (ha : 4 * a ^ 2 + 1 = 0) :
    ((X : F[X]) ^ 6 - 5 * X ^ 4 + 5 * X ^ 2 + 4
        = (X ^ 3 + 2 * C a * X ^ 2 - 3 * X - 4 * C a) * (X ^ 3 - 2 * C a * X ^ 2 - 3 * X + 4 * C a))
      ∧ ((X : F[X]) ^ 4 - 3 * X ^ 2 + 6 - C a * (6 * X ^ 5 - 20 * X ^ 3 + 10 * X)
        = (X ^ 3 + 2 * C a * X ^ 2 - 3 * X - 4 * C a) * (-6 * C a * X ^ 2 - 2 * X + 6 * C a)) := by
  have hb : 4 * (C a) ^ 2 + 1 = (0 : F[X]) := by
    have h := congrArg (C : F →+* F[X]) ha
    simpa [map_ofNat] using h
  refine ⟨?_, ?_⟩
  · linear_combination ((X : F[X]) ^ 2 - 2) ^ 2 * hb
  · linear_combination (3 * ((X : F[X]) ^ 2 - 1) * (X ^ 2 - 2)) * hb

/-- Hermite reduction of `(t⁷−24t⁴−4t²+8t−8)/(t⁸+6t⁶+12t⁴+8t²)`: rational part plus `1/t`. -/
theorem hermiteReduce_octic_example {F : Type*} [Field F] [Differential F] {t : F} (ht : t′ = 1)
    (ht0 : t ≠ 0) (ht2 : t ^ 2 + 2 ≠ 0) :
    ((3 * t ^ 3 + 8 * t ^ 2 + 6 * t + 4) / (t ^ 5 + 4 * t ^ 3 + 4 * t))′ + t⁻¹
      = (t ^ 7 - 24 * t ^ 4 - 4 * t ^ 2 + 8 * t - 8) / (t ^ 8 + 6 * t ^ 6 + 12 * t ^ 4 + 8 * t ^ 2) := by
  have hQ : (t ^ 5 + 4 * t ^ 3 + 4 * t : F) ≠ 0 := by
    have h : (t ^ 5 + 4 * t ^ 3 + 4 * t : F) = t * (t ^ 2 + 2) ^ 2 := by ring
    rw [h]; exact mul_ne_zero ht0 (pow_ne_zero _ ht2)
  have hD : (t ^ 8 + 6 * t ^ 6 + 12 * t ^ 4 + 8 * t ^ 2 : F) ≠ 0 := by
    have h : (t ^ 8 + 6 * t ^ 6 + 12 * t ^ 4 + 8 * t ^ 2 : F) = t ^ 2 * (t ^ 2 + 2) ^ 3 := by ring
    rw [h]; exact mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ ht2)
  have h3 : (3 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h4 : (4 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h6 : (6 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h8 : (8 : F)′ = 0 := mem_constants.mp (by norm_num)
  rw [deriv_div]
  simp only [map_add, deriv_const_mul _ h3, deriv_const_mul _ h4, deriv_const_mul _ h6,
    deriv_const_mul _ h8, h4, deriv_pow, ht, mul_one]
  rw [show (t⁻¹ : F) = 1 / t from (one_div t).symm,
    div_add_div _ _ (pow_ne_zero 2 hQ) ht0,
    div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hQ) ht0) hD]
  ring

/-- Hermite reduction of `(t⁵−t⁴+4t³+t²−t+5)/(t²−t+2)²`: rational part plus `(7t+3)/(7(t²−t+2))`. -/
theorem hermiteReduce_quartic_example {F : Type*} [Field F] [CharZero F] [Differential F] {t : F}
    (ht : t′ = 1)
    (hV : t ^ 2 - t + 2 ≠ 0) :
    ((7 * t ^ 4 + 7 * t ^ 3 + 20 * t + 18) / (14 * (t ^ 2 - t + 2)))′
        + (7 * t + 3) / (7 * (t ^ 2 - t + 2))
      = (t ^ 5 - t ^ 4 + 4 * t ^ 3 + t ^ 2 - t + 5) / ((t ^ 2 - t + 2) ^ 2) := by
  have h2 : (2 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h7 : (7 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h14 : (14 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h18 : (18 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h20 : (20 : F)′ = 0 := mem_constants.mp (by norm_num)
  have hV14 : (14 * (t ^ 2 - t + 2) : F) ≠ 0 := mul_ne_zero (by norm_num) hV
  have hV7 : (7 * (t ^ 2 - t + 2) : F) ≠ 0 := mul_ne_zero (by norm_num) hV
  have hV2 : ((t ^ 2 - t + 2) ^ 2 : F) ≠ 0 := pow_ne_zero _ hV
  rw [deriv_div]
  simp only [map_add, map_sub, deriv_const_mul _ h7, deriv_const_mul _ h14,
    deriv_const_mul _ h20, deriv_pow, ht, mul_one, h18, h2]
  rw [div_add_div _ _ (pow_ne_zero 2 hV14) hV7, div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hV14) hV7) hV2]
  ring

/-- Basic Hermite-reduction step trace for `(x⁷−24x⁴−4x²+8x−8)/(x²·(x²+2)³)`. -/
theorem hermiteBasic_trace_octic {F : Type*} [CommRing F] :
    -- x-part, step (2,1) j=1: V=x, A=x−1, B=1, C=−1
    ((1 : F[X]) * 1 + X * (-1) = -(X - 1))
      ∧ ((1 : F[X]) = -(-1) - 0)
    -- (x²+2)-part, step (3,2) j=2 (scaled by 2, Ĉ = 2C = −x²+6x−4)
    ∧ (2 * ((2 * X) * (6 * X)) + (X ^ 2 + 2) * (-X ^ 2 + 6 * X - 4)
        = -(X ^ 4 - 6 * X ^ 3 - 18 * X ^ 2 - 12 * X + 8 : F[X]))
      ∧ ((X ^ 2 - 6 * X - 2 : F[X]) = -(-X ^ 2 + 6 * X - 4) - 6)
    -- step (3,1) j=1: V=x²+2, A=x²−6x−2, B=−x+3, C=1
    ∧ ((2 * X) * (-X + 3) + (X ^ 2 + 2) * 1 = -(X ^ 2 - 6 * X - 2 : F[X]))
      ∧ ((0 : F[X]) = -(1 : F[X]) - (-1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- Quadratic Hermite-reduction step trace for `(x⁷−24x⁴−4x²+8x−8)/(x²·(x²+2)³)`. -/
theorem hermiteQuadratic_trace_octic {F : Type*} [CommRing F] :
    -- step (2,1), j=1:  U₂·V₂'·B + V₂·C₁ = −A₀,   A₁ = −1·C₁ − U₂·B'
    ((X ^ 2 + 2) ^ 3 * (1 : F[X]) + X * (-X ^ 6 - X ^ 5 + 18 * X ^ 3 - 8 * X - 8)
        = -(X ^ 7 - 24 * X ^ 4 - 4 * X ^ 2 + 8 * X - 8))
      ∧ ((X ^ 6 + X ^ 5 - 18 * X ^ 3 + 8 * X + 8 : F[X])
        = -(-X ^ 6 - X ^ 5 + 18 * X ^ 3 - 8 * X - 8))
    -- step (3,2), j=2 (scaled by 2):  2·(U₃·V₃'·B) + V₃·Ĉ₂ = −A₁,   A₂ = −Ĉ₂ − U₃·B'
    ∧ (2 * (X * (2 * X) * (6 * X)) + (X ^ 2 + 2) * (-X ^ 4 - X ^ 3 + 2 * X ^ 2 - 4 * X - 4)
        = -(X ^ 6 + X ^ 5 - 18 * X ^ 3 + 8 * X + 8 : F[X]))
      ∧ ((X ^ 4 + X ^ 3 - 2 * X ^ 2 - 2 * X + 4 : F[X])
        = -(-X ^ 4 - X ^ 3 + 2 * X ^ 2 - 4 * X - 4) - 6 * X)
    -- step (3,1), j=1:  U₃·V₃'·B + V₃·C₃ = −A₂,   A₃ = −1·C₃ − U₃·B'
    ∧ (X * (2 * X) * (-X + 3) + (X ^ 2 + 2) * (-X ^ 2 + X - 2)
        = -(X ^ 4 + X ^ 3 - 2 * X ^ 2 - 2 * X + 4 : F[X]))
      ∧ ((X ^ 2 + 2 : F[X]) = -(-X ^ 2 + X - 2) - X * (-1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- Mack's linear Hermite-reduction step trace for `(x⁷−24x⁴−4x²+8x−8)/(x²·(x²+2)³)`. -/
theorem hermiteMack_trace_octic {F : Type*} [CommRing F] :
    -- denominator split D = D*·D⁻, and the polynomial cofactor for −D*·D⁻'/D⁻ = −(5x²+2)
    ((X ^ 8 + 6 * X ^ 6 + 12 * X ^ 4 + 8 * X ^ 2 : F[X]) = (X ^ 3 + 2 * X) * (X ^ 5 + 4 * X ^ 3 + 4 * X))
      ∧ ((X ^ 5 + 4 * X ^ 3 + 4 * X) * (5 * X ^ 2 + 2)
        = (X ^ 3 + 2 * X) * (5 * X ^ 4 + 12 * X ^ 2 + 4 : F[X]))
    -- step 1 Bézout (−5x²−2)·B + D⁻*·C = A₀, with D⁻* = x³+2x; update A₁ = C − B'·(D*/D⁻*=1)
    ∧ ((-5 * X ^ 2 - 2) * (8 * X ^ 2 + 4) + (X ^ 3 + 2 * X) * (X ^ 4 - 2 * X ^ 2 + 16 * X + 4)
        = (X ^ 7 - 24 * X ^ 4 - 4 * X ^ 2 + 8 * X - 8 : F[X]))
      ∧ ((X ^ 4 - 2 * X ^ 2 + 4 : F[X]) = (X ^ 4 - 2 * X ^ 2 + 16 * X + 4) - 16 * X * 1)
    -- step 2: D⁻ = x²+2, cofactor for −D*·D⁻'/D⁻ = −2x²; Bézout (−2x²)·B + D⁻*·C = A₁; update A₂ = C
    ∧ ((X ^ 2 + 2) * (2 * X ^ 2) = (X ^ 3 + 2 * X) * (2 * X : F[X]))
      ∧ ((-2 * X ^ 2) * 3 + (X ^ 2 + 2) * (X ^ 2 + 2) = (X ^ 4 - 2 * X ^ 2 + 4 : F[X]))
    -- final remainder A₂/D* = (x²+2)/(x³+2x) = 1/x  (since (x²+2)·x = x³+2x)
    ∧ ((X ^ 2 + 2) * X = (X ^ 3 + 2 * X : F[X])) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- The degree-3 Lazard-Rioboo-Trager subresultant is `−214a` times the residue gcd `Gₐ`, for `4a²+1 = 0`. -/
theorem lazardRiobooTrager_example {F : Type*} [Field F] (a : F) (ha : 4 * a ^ 2 + 1 = 0) :
    (-214 * C a * (X : F[X]) ^ 3 + 107 * X ^ 2 + 642 * C a * X - 214
      = -214 * C a * (X ^ 3 + 2 * C a * X ^ 2 - 3 * X - 4 * C a)) := by
  have hb : 4 * (C a) ^ 2 + 1 = (0 : F[X]) := by
    have h := congrArg (C : F →+* F[X]) ha
    simpa [map_ofNat] using h
  linear_combination (107 * ((X : F[X]) ^ 2 - 2)) * hb

/-- Hermite reduction of `36/(x²−1)²(x−2)`: rational part `(12t+6)/(t²−1)` plus `12/(t²−t−2)`. -/
theorem hermiteReduce_quintic_example {F : Type*} [Field F] [Differential F] {t : F} (ht : t′ = 1)
    (h1 : t ^ 2 - 1 ≠ 0) (h2 : t ^ 2 - t - 2 ≠ 0) :
    ((12 * t + 6) / (t ^ 2 - 1))′ + 12 / (t ^ 2 - t - 2)
      = 36 / (t ^ 5 - 2 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 + t - 2) := by
  have ht2 : (t - 2 : F) ≠ 0 := by
    intro h; apply h2; rw [sub_eq_zero.mp h]; norm_num
  have hD : (t ^ 5 - 2 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 + t - 2 : F) ≠ 0 := by
    have h : (t ^ 5 - 2 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 + t - 2 : F) = (t ^ 2 - 1) ^ 2 * (t - 2) := by
      ring
    rw [h]; exact mul_ne_zero (pow_ne_zero 2 h1) ht2
  have h12 : (12 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h6 : (6 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h1' : (1 : F)′ = 0 := mem_constants.mp (by norm_num)
  rw [deriv_div]
  simp only [map_add, map_sub, deriv_const_mul _ h12, h6, h1', deriv_pow, ht, mul_one, sub_zero,
    add_zero]
  rw [div_add_div _ _ (pow_ne_zero 2 h1) h2, div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 h1) h2) hD]
  ring

/-- Full partial fraction `36/(t−1)²(t+1)²(t−2) = −9/(t−1)² − 3/(t+1)² − 4/(t+1) + 4/(t−2)`. -/
theorem fullPartialFraction_example {F : Type*} [Field F] (t : F) (h1 : t - 1 ≠ 0) (h2 : t + 1 ≠ 0)
    (h3 : t - 2 ≠ 0) :
    36 / (t ^ 5 - 2 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 + t - 2)
      = -9 / (t - 1) ^ 2 - 3 / (t + 1) ^ 2 - 4 / (t + 1) + 4 / (t - 2) := by
  have hD : t ^ 5 - 2 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 + t - 2 = (t - 1) ^ 2 * (t + 1) ^ 2 * (t - 2) := by
    ring
  rw [hD]; field_simp; ring

/-- Integral of `36/(t−1)²(t+1)²(t−2)`: rational part `9/(t−1)+3/(t+1)` plus log integrand. -/
theorem integrateRational_example {F : Type*} [Field F] [Differential F] {t : F} (ht : t′ = 1)
    (h1 : t - 1 ≠ 0) (h2 : t + 1 ≠ 0) (h3 : t - 2 ≠ 0) :
    (9 / (t - 1) + 3 / (t + 1))′ + (4 / (t - 2) - 4 / (t + 1))
      = 36 / (t ^ 5 - 2 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 + t - 2) := by
  have hD : (t ^ 5 - 2 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 + t - 2 : F)
      = (t - 1) ^ 2 * ((t + 1) ^ 2 * (t - 2)) := by ring
  have h9 : (9 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h3' : (3 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h1' : (1 : F)′ = 0 := mem_constants.mp (by norm_num)
  rw [map_add, deriv_div, deriv_div]
  simp only [map_add, map_sub, h9, h3', h1', ht]
  rw [hD]; field_simp; ring

end DeepWiki.SymbolicIntegration
