import DeepWiki.SymbolicIntegration.RationalIntegration

/-! # Worked examples of the rational-function integration algorithms (Bronstein §2.1–§2.8)
Concrete instances demonstrating the Bernoulli, Hermite, Rothstein–Trager, Lazard–Rioboo–Trager,
Czichowski and full-partial-fraction procedures. Stated over a general field (book-number-free);
the per-book §/page citations live in the `Sources/` catalog. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

/-- **Bernoulli partial fraction of `1/(x³+x)` over `ℚ(√−1)`**: factoring `x³+x = x(x+i)(x−i)`
(`i² = −1`) gives `1/(x³+x) = 1/x − (1/2)/(x+i) − (1/2)/(x−i)` (numerator collapses to `−i² = 1`). -/
theorem inv_cubic_partialFraction {F : Type*} [Field F] [CharZero F] (t i : F) (hi : i ^ 2 = -1)
    (ht : t ≠ 0) (h1 : t + i ≠ 0) (h2 : t - i ≠ 0) :
    1 / (t ^ 3 + t) = 1 / t - (1 / 2) / (t + i) - (1 / 2) / (t - i) := by
  have hfac : t ^ 3 + t = t * (t + i) * (t - i) := by linear_combination t * hi
  have key : (1 : F) / t - (1 / 2) / (t + i) - (1 / 2) / (t - i) = -(i ^ 2) / (t ^ 3 + t) := by
    rw [hfac]; field_simp; ring
  rw [key, hi]; norm_num

/-- **Rothstein–Trager residue gcd for `(x⁴−3x²+6)/(x⁶−5x⁴+5x²+4)`**: for `4a²+1 = 0` the residue gcd
`Gₐ = x³+2ax²−3x−4a` divides both `D = x⁶−5x⁴+5x²+4` and `A−aD' = (x⁴−3x²+6) − a(6x⁵−20x³+10x)`,
via the cofactorizations `D = Gₐ·(x³−2ax²−3x+4a)` and `A−aD' = Gₐ·(−6ax²−2x+6a)`. -/
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

/-- **Hermite reduction of `(t⁷−24t⁴−4t²+8t−8)/(t⁸+6t⁶+12t⁴+8t²)`**: the rational part is
`(3t³+8t²+6t+4)/(t⁵+4t³+4t)` and the remaining integrand reduces to `1/t`, i.e.
`((3t³+8t²+6t+4)/(t⁵+4t³+4t))′ + t⁻¹ = the integrand` (denominators `t·(t²+2)²`, `t²·(t²+2)³`). -/
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

/-- **Exercise 2.1** (§2.2/§2.4, Hermite reduction of `(t⁵−t⁴+4t³+t²−t+5)/(t⁴−2t³+5t²−4t+4)`): the
denominator is `(t²−t+2)²`, so Hermite reduction gives rational part `(7t⁴+7t³+20t+18)/(14(t²−t+2))` and
remaining integrand `(7t+3)/(7(t²−t+2))` (squarefree denominator, the logarithmic part), i.e.
`((7t⁴+7t³+20t+18)/(14(t²−t+2)))′ + (7t+3)/(7(t²−t+2))` is the integrand. -/
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

/-- **Example 2.2.1** (§2.2, the original Hermite reduction trace) for
`∫(x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)` (denominator `x²·(x²+2)³`). After the partial fraction
`f = (x−1)/x² + (x⁴−6x³−18x²−12x+8)/(x²+2)³`, `HermiteReduce` (original version) runs the steps
`(i,j) = (2,1),(3,2),(3,1)` with `V = x` then `V = x²+2`: each verifies the extended-Euclidean relation
`V'·B + V·C = −Aᵢ/j` (no `U` factor — partial fractions already separated the prime powers) and the update
`Aᵢ ← −jC − B'`. The `x`-part reduces to `1` (giving `∫dx/x`); the `(x²+2)`-part reduces
`x⁴−6x³−18x²−12x+8 → x²−6x−2 → 0`. Rational part `g = 1/x + 6x/(x²+2)² + (3−x)/(x²+2)`. Derivative values
`V'=1, 2x; B'=0,6,−1` inlined; step 2's `C = −x²/2+3x−2` as `Ĉ = 2C = −x²+6x−4`. -/
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

/-- **Example 2.2.2** (§2.2, the quadratic Hermite reduction trace) for
`∫(x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)` (denominator `x²·(x²+2)³`). The three reduction steps
`(i,j) = (2,1),(3,2),(3,1)` of `HermiteReduce` (quadratic version), with `V₂ = x`, `U₂ = (x²+2)³`,
`V₃ = x²+2`, `U₃ = x`: each verifies the extended-Euclidean relation `U·V'·B + V·C = −A/j` and the update
`A ← −jC − U·B'`, reducing the numerator `A₀ → A₁ → A₂ → A₃ = x²+2` (so the remainder is `1/x`). The
derivative values `V₂'=1, V₃'=2x, B'=0,6,−1` are inlined, and step 2's `C₂ = −x⁴/2−x³/2+x²−2x−2` appears
as `Ĉ₂ = 2·C₂ = −x⁴−x³+2x²−4x−4` (the Bézout relation and update both scaled by `j = 2`). -/
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

/-- **Example 2.2.3** (§2.2, Mack's linear Hermite reduction trace) for
`∫(x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)`, with `D⁻ = gcd(D, D') = x⁵+4x³+4x` and `D* = D/D⁻ = x³+2x`.
Two reduction steps (one per while-iteration), each verifying the extended-Euclidean relation
`(−D*·D⁻'/D⁻)·B + D⁻*·C = A` and update `A ← C − B'·D*/D⁻*`: step 1 with first argument `−5x²−2`
(`= −D*·D⁻'/D⁻`) gives `(B,C) = (8x²+4, x⁴−2x²+16x+4)`, reducing `A₀ → A₁ = x⁴−2x²+4`; step 2 with
first argument `−2x²` gives `(B,C) = (3, x²+2)`, reducing `A₁ → A₂ = x²+2`, and `A₂/D* = 1/x`. -/
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

/-- **Lazard–Rioboo–Trager subresultant for `(x⁴−3x²+6)/(x⁶−5x⁴+5x²+4)`**: the degree-3 subresultant
value at a root `a` of `4a²+1` is `S₃(a,x) = −214ax³+107x²+642ax−214 = −214a·(x³+2ax²−3x−4a)`, i.e.
`−214a` times the Rothstein–Trager gcd `Gₐ`. -/
theorem lazardRiobooTrager_example {F : Type*} [Field F] (a : F) (ha : 4 * a ^ 2 + 1 = 0) :
    (-214 * C a * (X : F[X]) ^ 3 + 107 * X ^ 2 + 642 * C a * X - 214
      = -214 * C a * (X ^ 3 + 2 * C a * X ^ 2 - 3 * X - 4 * C a)) := by
  have hb : 4 * (C a) ^ 2 + 1 = (0 : F[X]) := by
    have h := congrArg (C : F →+* F[X]) ha
    simpa [map_ofNat] using h
  linear_combination (107 * ((X : F[X]) ^ 2 - 2)) * hb

/-- **Hermite reduction of `36/(x⁵−2x⁴−2x³+4x²+x−2)`** (denominator `(x²−1)²(x−2)`): rational part
`(12x+6)/(x²−1)`, remaining integrand `12/(x²−x−2)`, i.e.
`((12x+6)/(x²−1))′ + 12/(x²−x−2) = 36/(x⁵−2x⁴−2x³+4x²+x−2)` (numerator collapses to `36(x+1)`). -/
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

/-- **Full partial fraction of `36/(x⁵−2x⁴−2x³+4x²+x−2)`** (denominator `(x−1)²(x+1)²(x−2)`):
`36/D = −9/(x−1)² − 3/(x+1)² − 4/(x+1) + 4/(x−2)`. -/
theorem fullPartialFraction_example {F : Type*} [Field F] (t : F) (h1 : t - 1 ≠ 0) (h2 : t + 1 ≠ 0)
    (h3 : t - 2 ≠ 0) :
    36 / (t ^ 5 - 2 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 + t - 2)
      = -9 / (t - 1) ^ 2 - 3 / (t + 1) ^ 2 - 4 / (t + 1) + 4 / (t - 2) := by
  have hD : t ^ 5 - 2 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 + t - 2 = (t - 1) ^ 2 * (t + 1) ^ 2 * (t - 2) := by
    ring
  rw [hD]; field_simp; ring

/-- **Integral of `36/(x⁵−2x⁴−2x³+4x²+x−2)` from its full partial fraction**:
`∫ f = 4·log(x−2) − 4·log(x+1) + 9/(x−1) + 3/(x+1)`, i.e.
`(9/(x−1) + 3/(x+1))′ + (4/(x−2) − 4/(x+1)) = f` (the bracket is the log part's integrand). -/
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
