import DeepWiki.SymbolicIntegration.DifferentialAlgebra.Basic

/-! # Logarithm-arctangent differential identities

Differential identities underlying conversion between complex logarithms and arc-tangents.
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

example {E : Type*} [Field E] [Differential E] [CharZero E] {i u v t₁ t₂ : E} (hi : i ^ 2 = -1)
    (hu : u ^ 2 + 1 ≠ 0) (hv : v = (u + i) / (u - i)) (ht₁ : t₁′ = v′ / v)
    (ht₂ : t₂′ = u′ / (1 + u ^ 2)) : (t₁ * i - 2 * t₂)′ = 0 :=
  deriv_log_arctan_combination_eq_zero hi hu hv ht₁ ht₂

end DeepWiki.SymbolicIntegration
