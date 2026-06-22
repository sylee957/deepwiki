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

/-- **Horowitz–Ostrogradsky reduction identity** (§2.3): the differential identity underlying the
Horowitz method. For a denominator split `D = D⁻·D*` (`D⁻` the "powered" part `gcd(D, D')`, `D*` the
squarefree part), writing `E := D⁻′·D*/D⁻` (a *polynomial* — `D⁻ ∣ D⁻′·D*`), the rational function with
numerator `A = B′·D* − B·E + C·D⁻` satisfies `A/(D⁻·D*) = (B/D⁻)′ + C/D*`. So `∫ A/D = B/D⁻ + ∫ C/D*`,
the rational part `B/D⁻` split off in one shot. Holds in any differential field given `E·D⁻ = D⁻′·D*`;
the *algorithm* finds `B, C` (with `deg B < deg D⁻`, `deg C < deg D*`) by a linear system. -/
theorem horowitz_reduction_step (B C Dminus Dstar E : F) (hDm : Dminus ≠ 0) (hDs : Dstar ≠ 0)
    (hE : E * Dminus = Dminus′ * Dstar) :
    (B′ * Dstar - B * E + C * Dminus) / (Dminus * Dstar)
      = (B / Dminus)′ + C / Dstar := by
  rw [deriv_div]
  field_simp
  linear_combination -B * hE

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

/-- **Integral of a linear form over an irreducible quadratic** (§2.1): with `s = √(4c−b²)`, modeling
`log(t²+bt+c)` by `L` (`L′ = (2t+b)/(t²+bt+c)`) and `arctan((2t+b)/s)` by `Θ` (the arctan law
`Θ′ = (2/s)/(1+((2t+b)/s)²)`), the derivative of `(B/2)·L + ((2C−bB)/s)·Θ` is `(Bt+C)/(t²+bt+c)`. -/
theorem deriv_logArctan_eq_quadratic [CharZero F] {t : F} (_ht : t′ = 1)
    {B C b c s L Θ : F} (hB : B′ = 0) (hC : C′ = 0) (hb : b′ = 0) (_hc : c′ = 0) (hs : s′ = 0)
    (hs2 : s ^ 2 = 4 * c - b ^ 2) (hsne : s ≠ 0) (_hq : t ^ 2 + b * t + c ≠ 0)
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

/-- **Quadratic-power reduction, core identity** (§2.1): the polynomial numerator balance behind the
`k>1` reduction of `∫ (Bx+C)/(x²+bx+c)ᵏ` —
`2(2C−bB)·q − (2x+b)·((2C−bB)x + bC−2cB) = (Bx+C)·(4c−b²)` with `q = x²+bx+c`. -/
theorem quadraticPow_reduce_core {R : Type*} [CommRing R] (t B C b c : R) :
    2 * (2 * C - b * B) * (t ^ 2 + b * t + c)
        - (2 * t + b) * ((2 * C - b * B) * t + (b * C - 2 * c * B))
      = (B * t + C) * (4 * c - b ^ 2) := by ring

/-- **Quadratic-power reduction** (§2.1): the recursive reduction lowering the power of an irreducible
quadratic `q = x²+bx+c` (`4c−b² ≠ 0`), `k = m+2`:
`∫ (Bx+C)/qᵏ = ((2C−bB)x+bC−2cB)/((k−1)(4c−b²)q^(k−1)) + ∫ (2k−3)(2C−bB)/((k−1)(4c−b²)q^(k−1))`,
verified as a differential-field identity (collapsing via `quadraticPow_reduce_core`). -/
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

/-- **Complex logarithm as real arctangent** (§2.8, Rioboo, eq 2.17): with `i = √−1` (`i² = −1`,
constant) and `arctan'(u) = u'/(1+u²)`, `i · logDeriv((u+i)/(u−i)) = 2·u'/(1+u²)` — the logarithmic
derivative `−2i·u'/(u²+1)` times `i` gives `2·u'/(1+u²)`. -/
theorem logDeriv_imagQuot_eq_arctanDeriv {i u : F} (hi : i ^ 2 = -1)
    (hi' : i′ = 0) (h1 : u + i ≠ 0) (h2 : u - i ≠ 0) :
    i * Differential.logDeriv ((u + i) / (u - i)) = 2 * (u′ / (1 + u ^ 2)) := by
  have hq : (1 + u ^ 2 : F) = (u + i) * (u - i) := by linear_combination hi
  rw [Differential.logDeriv, deriv_div, map_add, map_sub, hi', hq]
  field_simp
  linear_combination (-2 * u′) * hi

end DeepWiki.SymbolicIntegration
