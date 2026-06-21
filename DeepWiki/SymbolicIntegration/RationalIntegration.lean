import DeepWiki.SymbolicIntegration.DifferentialFields

/-! # Integration of rational functions — the Hermite reduction (Bronstein §2.2)
Hermite's algorithm computes the *rational part* of `∫ A/D` (with `D` squarefree-factored)
without factoring `D` into irreducibles, by repeatedly lowering the power of a squarefree factor
in the denominator. Each step rests on one differential identity: if the numerator over `Vᵏ`
factors as `Q = (1-k)(B·V' + C·V)`, then `Q/Vᵏ` is the derivative of `B/Vᵏ⁻¹` plus a fraction
with denominator `Vᵏ⁻¹`. We prove that identity in any differential field; the algorithm itself
finds `B, C` (with `deg B < deg V`) by the extended Euclidean algorithm, using `gcd(V, V') = 1`
for squarefree `V`. -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {F : Type*} [Field F] [Differential F]

/-- **Hermite reduction step** (§2.2): the differential identity underlying Hermite's reduction.
Writing `k = m + 2 ≥ 2`, so `1 - k = -(m+1)`, if the numerator is `Q = (1-k)(B·V' + C·V)` then
`Q / Vᵏ = (B / Vᵏ⁻¹)′ + ((1-k)·C - B') / Vᵏ⁻¹`, lowering the power of `V` in the integrand by one
(the new fraction has denominator `Vᵏ⁻¹ = Vᵐ⁺¹`). Holds in any differential field; the
squarefreeness of `V` and degree bounds are what the *algorithm* uses to find `B` and `C`. -/
theorem hermite_reduction_step (B C V : F) (hV : V ≠ 0) (m : ℕ) :
    (-((m : F) + 1) * (B * V′ + C * V)) / V ^ (m + 2)
      = (B / V ^ (m + 1))′ + (-((m : F) + 1) * C - B′) / V ^ (m + 1) := by
  rw [deriv_div, deriv_pow]
  simp only [Nat.add_sub_cancel]
  field_simp
  push_cast
  ring

/-- **Bernoulli, rational part** (§2.1): the antiderivative of `tⁿ⁻¹` is `tⁿ/n`, i.e.
`D(tⁿ/n) = tⁿ⁻¹`, whenever `Dt = 1` (e.g. `t = x − a`) and `n ≠ 0`. This is the closed form
`∫ (x−a)⁻ᵏ dx = (x−a)¹⁻ᵏ/(1−k)` (the rational part of Bernoulli's algorithm) for `k ≠ 1`. -/
theorem deriv_zpow_div_self {t : F} (ht : t′ = 1) {n : ℤ} (hn : (n : F) ≠ 0) :
    (t ^ n / (n : F))′ = t ^ (n - 1) := by
  have hn0 : ((n : F))′ = 0 := by simp
  rw [Differential.deriv.leibniz_div_const (t ^ n) (n : F) hn0,
    smul_eq_mul, deriv_zpow, ht, mul_one, inv_mul_cancel_left₀ hn]

/-- **Bernoulli, logarithmic part** (§2.1): `∫ dx/(x−a) = log(x−a)` — the integrand `1/t` is the
*logarithmic derivative* of `t` (`logDeriv t = t⁻¹`) when `Dt = 1`, so its antiderivative is a
logarithm. -/
theorem logDeriv_eq_inv {t : F} (ht : t′ = 1) : Differential.logDeriv t = t⁻¹ := by
  rw [Differential.logDeriv, ht, one_div]

end DeepWiki.SymbolicIntegration
