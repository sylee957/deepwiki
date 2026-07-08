import DeepWiki.SymbolicIntegration.Computable.RatFuncValuation.Basic
import DeepWiki.SymbolicIntegration.Computable.RischDE.NormalPoleOrderDrop

/-! # Normal-pole derivative valuation calculus

Normal-pole consequences for the `K(t)` valuation under `extendDeriv`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

section Lift

variable [CharZero K] (d : Derivation ℤ K[X] K[X])

/-- The `K(t)`-valuation lift of the normal-pole order drop: for `D = extendDeriv d` extending a
base derivation `d` on `K[X]`, a prime `p` normal for `d` (`¬ p ∣ d p`) over a characteristic-zero
field, `νₚ(D y) = νₚ(y) − 1` at a normal pole `νₚ(y) < 0`. Lifts the polynomial Wronskian-numerator
kernel to the fraction field via `D y = (d a·b − a·d b)/b²`. -/
theorem ratFuncOrd_extendDeriv_eq_sub_one_of_normal {p : K[X]} (hp : Prime p) (hnormal : ¬ p ∣ d p)
    {y : RatFunc K} (hpole : ratFuncOrd p y < 0) :
    ratFuncOrd p (extendDeriv d y) = ratFuncOrd p y - 1 := by
  -- `y ≠ 0` (a pole forces `y ≠ 0`): `ratFuncOrd p 0 = multiplicity p 0 − multiplicity p 1 ≥ 0`.
  have hyne : y ≠ 0 := by
    rintro rfl
    rw [ratFuncOrd, RatFunc.num_zero, RatFunc.denom_zero, multiplicity_one_of_prime hp] at hpole
    simp at hpole
  set a := y.num with ha
  set b := y.denom with hb
  have ha0 : a ≠ 0 := RatFunc.num_ne_zero hyne
  have hb0 : b ≠ 0 := RatFunc.denom_ne_zero y
  -- the pole means `multiplicity p a < multiplicity p b`.
  have hlt : multiplicity p a < multiplicity p b := by
    rw [ratFuncOrd, ← ha, ← hb] at hpole; omega
  -- extract the `p`-free cofactors `a = p^m·a'`, `b = p^k·b'`.
  obtain ⟨a', ha'eq, ha'⟩ :=
    (FiniteMultiplicity.of_prime_left hp ha0).exists_eq_pow_mul_and_not_dvd
  obtain ⟨b', hb'eq, hb'⟩ :=
    (FiniteMultiplicity.of_prime_left hp hb0).exists_eq_pow_mul_and_not_dvd
  set m := multiplicity p a with hm
  set k := multiplicity p b with hk
  -- `D y = (d a·b − a·d b)/b²` via `extendDeriv_mk` and `y = num/denom`.
  have hyrep : y = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b := by
    rw [ha, hb, RatFunc.num_div_denom]
  have hDy : extendDeriv d y
      = algebraMap K[X] (RatFunc K) (d a * b - a * d b) / algebraMap K[X] (RatFunc K) (b ^ 2) := by
    conv_lhs => rw [hyrep, ← RatFunc.mk_eq_div, extendDeriv_mk, RatFunc.mk_eq_div]
  -- the numerator's `p`-multiplicity is `m + k − 1` (the proven `K[X]` Wronskian kernel): fold the
  -- cofactor form `d(p^m·a')·(p^k·b') − … ` back into `d a·b − a·d b` via `a = p^m·a'`, `b = p^k·b'`.
  have hem : emultiplicity p (d a * b - a * d b) = ((m + k - 1 : ℕ) : ℕ∞) := by
    have h := emultiplicity_wronskian_numerator_eq_of_normal d hp hnormal hlt ha' hb'
    rw [← ha'eq, ← hb'eq] at h
    exact h
  have hnum_ne : d a * b - a * d b ≠ 0 := by
    intro hzero
    rw [hzero, emultiplicity_zero] at hem
    exact (ENat.coe_ne_top (m + k - 1)) hem.symm
  have hb2_ne : (b ^ 2 : K[X]) ≠ 0 := pow_ne_zero 2 hb0
  have hnum_mult : multiplicity p (d a * b - a * d b) = m + k - 1 :=
    multiplicity_eq_of_emultiplicity_eq_some hem
  -- assemble: `νₚ(D y) = νₚ(num) − νₚ(b²) = (m+k−1) − 2k = m − k − 1 = νₚ(y) − 1`.
  rw [hDy, ratFuncOrd_mk p hp hnum_ne hb2_ne, hnum_mult]
  have hk2 : multiplicity p (b ^ 2) = 2 * k := by
    rw [hk, show (b : K[X]) ^ 2 = b * b by ring,
      multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hb0 hb0))]; ring
  rw [hk2, ratFuncOrd, ← ha, ← hb, ← hm, ← hk]
  -- `k ≥ 1` since `m < k`, so the ℕ subtraction `m + k − 1` is honest.
  have hk1 : 1 ≤ k := Nat.one_le_of_lt hlt
  omega

/-- Derivative of a regular function is regular (`Res_p(D y) = 0` in valuation form). If `y` is regular at
`p` (`νₚ y ≥ 0`), then `D y = extendDeriv d y` is regular (`νₚ(D y) ≥ 0`) — so `D y` has no simple pole at `p`,
i.e. no residue. No normality needed: `y = a/b` reduced with `νₚ y ≥ 0` forces `b` a `p`-unit
(coprimality), and `D y = (d a·b − a·d b)/b²` then has a `p`-unit denominator over a polynomial numerator. The
`g`-regular ⟹ `Res(D g) = 0` step of the residue criterion (`descendGenuine`). -/
theorem ratFuncOrd_extendDeriv_nonneg_of_nonneg {p : K[X]} (hp : Prime p) {y : RatFunc K}
    (hy : 0 ≤ ratFuncOrd p y) : 0 ≤ ratFuncOrd p (extendDeriv d y) := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [map_zero, ratFuncOrd, RatFunc.num_zero, RatFunc.denom_zero, multiplicity_zero,
      multiplicity_one_of_prime hp]; norm_num
  have ha0 : y.num ≠ 0 := RatFunc.num_ne_zero hy0
  have hb0 : y.denom ≠ 0 := RatFunc.denom_ne_zero y
  have hbunit : multiplicity p y.denom = 0 := by
    by_contra hbne
    have hpb : p ∣ y.denom := by
      by_contra hnd; exact hbne (multiplicity_eq_zero.mpr hnd)
    have hpna : ¬ p ∣ y.num := fun h =>
      hp.not_unit ((RatFunc.isCoprime_num_denom y).isUnit_of_dvd' h hpb)
    rw [ratFuncOrd, multiplicity_eq_zero.mpr hpna] at hy
    omega
  have hyrep : y = algebraMap K[X] (RatFunc K) y.num / algebraMap K[X] (RatFunc K) y.denom :=
    (RatFunc.num_div_denom y).symm
  have hDy : extendDeriv d y = algebraMap K[X] (RatFunc K) (d y.num * y.denom - y.num * d y.denom)
      / algebraMap K[X] (RatFunc K) (y.denom ^ 2) := by
    conv_lhs => rw [hyrep, ← RatFunc.mk_eq_div, extendDeriv_mk, RatFunc.mk_eq_div]
  rcases eq_or_ne (d y.num * y.denom - y.num * d y.denom) 0 with hnum0 | hnum0
  · rw [hDy, hnum0, map_zero, zero_div, ratFuncOrd, RatFunc.num_zero, RatFunc.denom_zero,
      multiplicity_zero, multiplicity_one_of_prime hp]; norm_num
  rw [hDy, ratFuncOrd_mk p hp hnum0 (pow_ne_zero 2 hb0)]
  have hb2 : multiplicity p (y.denom ^ 2) = 0 := by
    rw [show y.denom ^ 2 = y.denom * y.denom by ring,
      multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hb0 hb0)), hbunit]
  rw [hb2]; simp

/-- The per-prime RDE no-pole bound: for a solution `y` of `D y + f·y = g` (`D = extendDeriv d`), a
prime `p` normal for `d`, if `p` is not a pole of `f` (`νₚ(f) ≥ 0`) nor of `g` (`νₚ(g) ≥ 0`), then
`y` has no pole at `p` (`νₚ(y) ≥ 0`). By contradiction through the order-drop lift and the strict-min
law. -/
theorem ratFuncOrd_nonneg_of_rde_at_normal {p : K[X]} (hp : Prime p) (hnormal : ¬ p ∣ d p)
    {f g y : RatFunc K} (hrde : extendDeriv d y + f * y = g)
    (hf : 0 ≤ ratFuncOrd p f) (hg : 0 ≤ ratFuncOrd p g) :
    0 ≤ ratFuncOrd p y := by
  by_contra hlt
  rw [not_le] at hlt
  -- a pole forces `y ≠ 0`.
  have hyne : y ≠ 0 := by rintro rfl; simp [ratFuncOrd, multiplicity_one_of_prime hp] at hlt
  have hDy_ord : ratFuncOrd p (extendDeriv d y) = ratFuncOrd p y - 1 :=
    ratFuncOrd_extendDeriv_eq_sub_one_of_normal d hp hnormal hlt
  -- `D y ≠ 0` (it has a pole, `νₚ(D y) = νₚ(y) − 1 < 0`).
  have hDyne : extendDeriv d y ≠ 0 := by
    rintro h; rw [h, ratFuncOrd, RatFunc.num_zero, RatFunc.denom_zero,
      multiplicity_one_of_prime hp] at hDy_ord; simp at hDy_ord; omega
  rcases eq_or_ne f 0 with hf0 | hf0
  · -- `f = 0`: then `D y = g`, so `νₚ(g) = νₚ(y) − 1 < 0`, contradicting `νₚ(g) ≥ 0`.
    rw [hf0, zero_mul, add_zero] at hrde
    rw [← hrde, hDy_ord] at hg; omega
  · -- `f ≠ 0`: `νₚ(f·y) = νₚ(f) + νₚ(y) > νₚ(y) − 1 = νₚ(D y)`, so the sum's order is the strict min.
    have hfy_ord : ratFuncOrd p (f * y) = ratFuncOrd p f + ratFuncOrd p y :=
      ratFuncOrd_mul p hp hf0 hyne
    have hlt_sum : ratFuncOrd p (extendDeriv d y) < ratFuncOrd p (f * y) := by
      rw [hDy_ord, hfy_ord]; omega
    have hsum_ord : ratFuncOrd p (extendDeriv d y + f * y) = ratFuncOrd p (extendDeriv d y) :=
      ratFuncOrd_add_of_lt p hp hDyne (mul_ne_zero hf0 hyne) hlt_sum
    rw [hrde, hDy_ord] at hsum_ord; omega

/-- An at-most-simple-pole derivative comes from a regular function. At a prime `p` normal for `d`,
if `D y = extendDeriv d y` has at most a simple pole (`νₚ(D y) ≥ −1`), then `y` is regular (`νₚ(y) ≥ 0`): a
pole `νₚ(y) < 0` would drop to `νₚ(D y) = νₚ(y) − 1 ≤ −2`. This is the pole-order heart of the residue
criterion (`descendGenuine`): in a Liouville form `a/d = D g + Σ cᵢ·logDeriv vᵢ` with `a/d` reduced
(simple poles) and the log part simple-poled, the rational part `g` carries no simple pole at those primes,
so `D g` contributes no residue there — every residue is a constant log coefficient. -/
theorem ratFuncOrd_nonneg_of_extendDeriv_ge_neg_one {p : K[X]} (hp : Prime p) (hnormal : ¬ p ∣ d p)
    {y : RatFunc K} (h : -1 ≤ ratFuncOrd p (extendDeriv d y)) : 0 ≤ ratFuncOrd p y := by
  by_contra hlt
  rw [not_le] at hlt
  rw [ratFuncOrd_extendDeriv_eq_sub_one_of_normal d hp hnormal hlt] at h
  omega

/-- The residue criterion's rational-part regularity (`descendGenuine` core). In a Liouville form
`f = D g + h` (`D = extendDeriv d`) with `f` reduced at `p` (`νₚ f ≥ −1`, a simple pole) and the log part
`h` simple-poled (`νₚ h ≥ −1`), the rational part `g` is regular at every prime `p` normal for `d`
(`νₚ g ≥ 0`): `D g = f − h` has at most a simple pole (ultrametric), and an at-most-simple-pole derivative
comes from a regular function. Hence `D g` carries no residue at `p`, so every residue of `f` is a
constant log coefficient — the pole-order half of the transcendental residue criterion. -/
theorem ratFuncOrd_nonneg_of_liouville_reduced {p : K[X]} (hp : Prime p) (hnormal : ¬ p ∣ d p)
    {f g h : RatFunc K} (hLiou : f = extendDeriv d g + h)
    (hf : -1 ≤ ratFuncOrd p f) (hh : -1 ≤ ratFuncOrd p h) : 0 ≤ ratFuncOrd p g := by
  refine ratFuncOrd_nonneg_of_extendDeriv_ge_neg_one d hp hnormal ?_
  have hDg : extendDeriv d g = f + -h := by rw [hLiou]; ring
  rw [hDg]
  exact le_ratFuncOrd_add p hp (by norm_num) hf (by rw [ratFuncOrd_neg p hp]; exact hh)

/-- The residue criterion's rational-part has no residue (`descendGenuine` valuation heart, combined). In
a Liouville form `f = D g + h` with `f` reduced (`νₚ f ≥ −1`) and `h` simple-poled (`νₚ h ≥ −1`), the
rational-part derivative `D g` is regular at every prime `p` normal for `d` (`νₚ(D g) ≥ 0`) — so it has no
simple pole and contributes no residue. Hence every residue of `f` at `p` is the residue of the log part
`h`, a constant log coefficient. Composes `ratFuncOrd_nonneg_of_liouville_reduced` (`g` regular) with
`ratFuncOrd_extendDeriv_nonneg_of_nonneg` (`D` of regular is regular). -/
theorem ratFuncOrd_extendDeriv_nonneg_of_liouville_reduced {p : K[X]} (hp : Prime p) (hnormal : ¬ p ∣ d p)
    {f g h : RatFunc K} (hLiou : f = extendDeriv d g + h)
    (hf : -1 ≤ ratFuncOrd p f) (hh : -1 ≤ ratFuncOrd p h) : 0 ≤ ratFuncOrd p (extendDeriv d g) :=
  ratFuncOrd_extendDeriv_nonneg_of_nonneg d hp
    (ratFuncOrd_nonneg_of_liouville_reduced d hp hnormal hLiou hf hh)

end Lift

end DeepWiki.SymbolicIntegration
