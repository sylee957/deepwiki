import DeepWiki.SymbolicIntegration.DifferentialAlgebra
import DeepWiki.SymbolicIntegration.DifferentialAlgebraFacts.Rao

/-! # Worked differential-algebra facts

Aggregator for coefficient-lifting derivations, logarithm/arctangent cancellation,
and Rao normal/special polynomials, with verification examples for adjacent differential-field facts.
-/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section LogArctan
variable {E : Type*} [Field E] [Differential E] [CharZero E]

/-- An element `i` with `i² = −1` is a constant: `Di = 0`. (Differentiate `i² = −1`: `2i·Di = 0`,
and `i ≠ 0` with `2 ≠ 0` in characteristic `0`.) -/
theorem deriv_eq_zero_of_sq_eq_neg_one {i : E} (hi : i ^ 2 = -1) : i′ = 0 := by
  have hine : i ≠ 0 := by rintro rfl; simp at hi
  have hd : (i ^ 2)′ = 0 := by rw [hi]; simp
  rw [deriv_pow] at hd
  -- `hd : (2 : E) * i ^ (2 - 1) * i′ = 0`, with `2 ≠ 0`, `i ≠ 0`.
  have h2 : (2 : E) ≠ 0 := by norm_num
  have : i ^ (2 - 1) = i := by norm_num
  rw [this] at hd
  exact (mul_eq_zero.mp hd).resolve_left (mul_ne_zero h2 hine)

/-- The combination of a logarithm of `v = (u + i)/(u − i)` and an
arc-tangent of `u` is a constant. With `i² = −1`, `u² + 1 ≠ 0`, `Δt₁ = Δv/v` (logarithm of `v`),
and `Δt₂ = Δu/(1 + u²)` (arc-tangent of `u`), the combination `t₁·i − 2·t₂` has zero derivative:
`i·Δv/v = 2·Δu/(1+u²)` (since `Δv/v = −2i·Δu/(u²+1)` and `i² = −1`), cancelling `2·Δt₂`. -/
theorem deriv_log_arctan_combination_eq_zero {i u v t₁ t₂ : E} (hi : i ^ 2 = -1)
    (hu : u ^ 2 + 1 ≠ 0) (hv : v = (u + i) / (u - i))
    (ht₁ : t₁′ = v′ / v) (ht₂ : t₂′ = u′ / (1 + u ^ 2)) :
    (t₁ * i - 2 * t₂)′ = 0 := by
  have hi0 : i′ = 0 := deriv_eq_zero_of_sq_eq_neg_one hi
  -- `u ± i ≠ 0`: else `u² = i² = −1`, i.e. `u² + 1 = 0`.
  have hupi : u + i ≠ 0 := by
    intro h; apply hu; have huv : u = -i := by linear_combination h
    rw [huv]; linear_combination hi
  have humi : u - i ≠ 0 := by
    intro h; apply hu; have huv : u = i := by linear_combination h
    rw [huv]; linear_combination hi
  have hvne : v ≠ 0 := by rw [hv]; exact div_ne_zero hupi humi
  -- `Δv/v = −2i·Δu/(u² + 1)`.
  -- `i`-power reduction from `i² = −1`.
  have hi3 : i ^ 3 = -i := by linear_combination i * hi
  have hdv : v′ / v = (-2 * i) * u′ / (u ^ 2 + 1) := by
    have hv2 : v′ = ((u - i) * u′ - (u + i) * u′) / (u - i) ^ 2 := by
      rw [hv, deriv_div, map_sub, map_add, hi0, add_zero, sub_zero]
    rw [hv2, hv]
    field_simp
    ring_nf
    simp only [hi3]
    ring
  -- assemble: `(t₁·i − 2·t₂)′ = i·Δt₁ − 2·Δt₂ = i·(Δv/v) − 2·Δu/(1+u²) = 0`.
  have h20 : (2 : E)′ = 0 := by
    have h2eq : (2 : E) = 1 + 1 := by norm_num
    rw [h2eq, map_add]; simp
  have hprod : (t₁ * i)′ = i * t₁′ := by rw [deriv_mul_eq, hi0, mul_zero, zero_add]
  have htwo : (2 * t₂ : E)′ = 2 * t₂′ := by rw [deriv_mul_eq, h20, mul_zero, add_zero]
  rw [map_sub, hprod, htwo, ht₁, ht₂, hdv]
  rw [show (1 : E) + u ^ 2 = u ^ 2 + 1 from by ring]
  field_simp
  linear_combination (-2 * u′) * hi

end LogArctan

/-! ## Verification examples -/

section Verification

-- The logarithmic derivative of a product of integer powers is the weighted sum of logarithmic derivatives.
example {F : Type*} [Field F] [Differential F] {ι : Type*} (s : Finset ι) (u : ι → F) (e : ι → ℤ)
    (h : ∀ i ∈ s, u i ≠ 0) :
    (∏ i ∈ s, u i ^ e i)′ / (∏ i ∈ s, u i ^ e i) = ∑ i ∈ s, (e i : F) * ((u i)′ / u i) :=
  logDeriv_prod_zpow_div s u e h

-- The logarithm-arctangent combination `t₁·√−1 − 2·t₂` is a `D`-constant.
example {E : Type*} [Field E] [Differential E] [CharZero E] {i u v t₁ t₂ : E} (hi : i ^ 2 = -1)
    (hu : u ^ 2 + 1 ≠ 0) (hv : v = (u + i) / (u - i)) (ht₁ : t₁′ = v′ / v)
    (ht₂ : t₂′ = u′ / (1 + u ^ 2)) : (t₁ * i - 2 * t₂)′ = 0 :=
  deriv_log_arctan_combination_eq_zero hi hu hv ht₁ ht₂

-- The Rao derivation satisfies the Leibniz rule.
example {k : Type*} [Field k] [Differential k] (a b p q : k[X]) :
    bDeriv a b (p * q) = p * bDeriv a b q + q * bDeriv a b p :=
  bDeriv_mul a b p q

-- A product of linear factors is Rao-normal iff every root avoids the special-value equation.
example {k : Type*} [Field k] [Differential k] (a b : k[X]) (s : Finset k) :
    IsNormalRao a b (∏ α ∈ s, (X - C α)) ↔ ∀ α ∈ s, a.eval α ≠ b.eval α * α′ :=
  isNormalRao_prod_X_sub_C_iff a b s

-- A product of linear factors is Rao-special iff every root satisfies the special-value equation.
example {k : Type*} [Field k] [Differential k] (a b : k[X]) (s : Finset k) :
    IsSpecialRao a b (∏ α ∈ s, (X - C α)) ↔ ∀ α ∈ s, a.eval α = b.eval α * α′ :=
  isSpecialRao_prod_X_sub_C_iff a b s

-- A Rao-special prime is coprime to the denominator under a coprime numerator-denominator pair.
example {k : Type*} [Field k] [Differential k] [CharZero k] {a b π : k[X]} (hab : IsCoprime a b)
    (hπ : Prime π) (hsp : IsSpecialRao a b π) : IsCoprime π b :=
  isCoprime_of_isSpecialRao_prime hab hπ hsp

end Verification

end DeepWiki.SymbolicIntegration
