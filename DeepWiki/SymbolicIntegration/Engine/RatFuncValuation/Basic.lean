import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionExtension

/-! # Basic `K(t)` valuation calculus

A `p`-adic integer valuation `ratFuncOrd p x = νₚ(x)` on `RatFunc K`, with its representation,
multiplicative, and ultrametric laws. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- The `p`-adic integer valuation on `K(t)` `ratFuncOrd p x = νₚ(x)`: the `multiplicity` of the
prime `p` in the numerator minus its multiplicity in the denominator of `x ∈ RatFunc K`. A pole at `p`
is `νₚ(x) < 0`; `νₚ(0) = 0`. -/
noncomputable def ratFuncOrd (p : K[X]) (x : RatFunc K) : ℤ :=
  (multiplicity p x.num : ℤ) - (multiplicity p x.denom : ℤ)

/-- `multiplicity p 1 = 0` for a prime `p` (a prime never divides a unit). -/
theorem multiplicity_one_of_prime {p : K[X]} (hp : Prime p) : multiplicity p (1 : K[X]) = 0 :=
  multiplicity_eq_zero.mpr (fun h => hp.not_unit (isUnit_of_dvd_one h))

/-- `νₚ` of a polynomial image `algebraMap _ _ g` is `multiplicity p g` (the denominator is `1`,
contributing `multiplicity p 1 = 0`). -/
theorem ratFuncOrd_algebraMap (p g : K[X]) (hp : Prime p) :
    ratFuncOrd p (algebraMap K[X] (RatFunc K) g) = (multiplicity p g : ℤ) := by
  rw [ratFuncOrd, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, multiplicity_one_of_prime hp]
  simp

/-- `νₚ` reads through any representation: for `x = a/b` with `a, b ≠ 0`,
`νₚ(x) = multiplicity p a − multiplicity p b`, even when `(a, b)` is not the canonical `num`/`denom`. -/
theorem ratFuncOrd_mk (p : K[X]) (hp : Prime p) {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ratFuncOrd p (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b)
      = (multiplicity p a : ℤ) - (multiplicity p b : ℤ) := by
  set x : RatFunc K := algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b with hx
  have hxne : x ≠ 0 := by
    rw [hx, div_ne_zero_iff]
    exact ⟨(map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr ha,
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hb⟩
  have hnum0 : x.num ≠ 0 := RatFunc.num_ne_zero hxne
  -- cross-multiplication `num·b = a·denom`
  have hcross : x.num * b = a * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hb).mpr hx
  -- `multiplicity` is additive over products of `p`-finite-multiplicity factors
  have hmul : multiplicity p (x.num * b) = multiplicity p (a * x.denom) := by rw [hcross]
  have hfin_numb : FiniteMultiplicity p (x.num * b) :=
    FiniteMultiplicity.of_prime_left hp (mul_ne_zero hnum0 hb)
  have hfin_aden : FiniteMultiplicity p (a * x.denom) :=
    FiniteMultiplicity.of_prime_left hp (mul_ne_zero ha (RatFunc.denom_ne_zero x))
  rw [multiplicity_mul hp hfin_numb, multiplicity_mul hp hfin_aden] at hmul
  -- so `νₚ(num) + νₚ(b) = νₚ(a) + νₚ(denom)`, rearrange for `νₚ(x) = νₚ(a) − νₚ(b)`.
  rw [ratFuncOrd]
  omega

/-- `νₚ` is multiplicative: `νₚ(x·y) = νₚ(x) + νₚ(y)` for a prime `p` and nonzero `x, y ∈ K(t)`. -/
theorem ratFuncOrd_mul (p : K[X]) (hp : Prime p) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ratFuncOrd p (x * y) = ratFuncOrd p x + ratFuncOrd p y := by
  have hxrep : x = algebraMap K[X] (RatFunc K) x.num / algebraMap K[X] (RatFunc K) x.denom :=
    (RatFunc.num_div_denom x).symm
  have hyrep : y = algebraMap K[X] (RatFunc K) y.num / algebraMap K[X] (RatFunc K) y.denom :=
    (RatFunc.num_div_denom y).symm
  have hnx := RatFunc.num_ne_zero hx
  have hny := RatFunc.num_ne_zero hy
  have hdx := RatFunc.denom_ne_zero x
  have hdy := RatFunc.denom_ne_zero y
  -- `x·y` has representation `(num x·num y)/(denom x·denom y)`.
  have hxy : x * y = algebraMap K[X] (RatFunc K) (x.num * y.num)
      / algebraMap K[X] (RatFunc K) (x.denom * y.denom) := by
    rw [map_mul, map_mul]; conv_lhs => rw [hxrep, hyrep]
    rw [div_mul_div_comm]
  rw [hxy, ratFuncOrd_mk p hp (mul_ne_zero hnx hny) (mul_ne_zero hdx hdy),
    multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hnx hny)),
    multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hdx hdy)), ratFuncOrd,
    ratFuncOrd]
  push_cast; ring

/-- `νₚ` is ultrametric with the strict-min law: if `νₚ(x) < νₚ(y)` for a prime `p` and nonzero
`x, y`, then `νₚ(x + y) = νₚ(x)`; the dominant pole is not cancelled. -/
theorem ratFuncOrd_add_of_lt (p : K[X]) (hp : Prime p) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hlt : ratFuncOrd p x < ratFuncOrd p y) :
    ratFuncOrd p (x + y) = ratFuncOrd p x := by
  have hnx := RatFunc.num_ne_zero hx
  have hny := RatFunc.num_ne_zero hy
  have hdx := RatFunc.denom_ne_zero x
  have hdy := RatFunc.denom_ne_zero y
  have hxrep : x = algebraMap K[X] (RatFunc K) x.num / algebraMap K[X] (RatFunc K) x.denom :=
    (RatFunc.num_div_denom x).symm
  have hyrep : y = algebraMap K[X] (RatFunc K) y.num / algebraMap K[X] (RatFunc K) y.denom :=
    (RatFunc.num_div_denom y).symm
  -- common-denominator numerator `N = num x·denom y + denom x·num y`.
  set N : K[X] := x.num * y.denom + x.denom * y.num with hN
  have hsum : x + y = algebraMap K[X] (RatFunc K) N
      / algebraMap K[X] (RatFunc K) (x.denom * y.denom) := by
    rw [hN, map_add, map_mul, map_mul, map_mul]; conv_lhs => rw [hxrep, hyrep]
    rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero hdx) (RatFunc.algebraMap_ne_zero hdy)]
  -- `νₚ(num x·denom y) < νₚ(denom x·num y)` from `νₚ(x) < νₚ(y)`.
  have hfin := fun {z : K[X]} (hz : z ≠ 0) => FiniteMultiplicity.of_prime_left hp hz
  have hlt_terms : multiplicity p (x.num * y.denom) < multiplicity p (x.denom * y.num) := by
    rw [multiplicity_mul hp (hfin (mul_ne_zero hnx hdy)),
      multiplicity_mul hp (hfin (mul_ne_zero hdx hny))]
    rw [ratFuncOrd, ratFuncOrd] at hlt
    omega
  have hNne : N ≠ 0 := by
    rw [hN]; intro h
    have : x.num * y.denom = -(x.denom * y.num) := by linear_combination h
    rw [this, multiplicity_neg] at hlt_terms; exact lt_irrefl _ hlt_terms
  -- `νₚ(N) = νₚ(num x·denom y)` (strict-min), so `νₚ(x+y) = νₚ(N) − νₚ(denom x·denom y) = νₚ(x)`.
  have hNmult : multiplicity p N = multiplicity p (x.num * y.denom) := by
    rw [hN, add_comm]
    exact (hfin (mul_ne_zero hnx hdy)).multiplicity_add_of_gt hlt_terms
  rw [hsum, ratFuncOrd_mk p hp hNne (mul_ne_zero hdx hdy), hNmult,
    multiplicity_mul hp (hfin (mul_ne_zero hnx hdy)),
    multiplicity_mul hp (hfin (mul_ne_zero hdx hdy)), ratFuncOrd]
  push_cast; ring

/-- The ultrametric lower bound (common lower bound preserved): if `n ≤ 0` and `n ≤ νₚ x`, `n ≤ νₚ y`,
then `n ≤ νₚ(x + y)`. The `n ≤ 0` guard covers the `x + y = 0` case (`νₚ 0 = 0`). Via
`min_le_emultiplicity_add` on the common-denominator numerator. -/
theorem le_ratFuncOrd_add (p : K[X]) (hp : Prime p) {x y : RatFunc K} {n : ℤ} (hn : n ≤ 0)
    (hx : n ≤ ratFuncOrd p x) (hy : n ≤ ratFuncOrd p y) : n ≤ ratFuncOrd p (x + y) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using hy
  rcases eq_or_ne y 0 with rfl | hy0
  · simpa using hx
  rcases eq_or_ne (x + y) 0 with hxy0 | hxy0
  · rw [hxy0, ratFuncOrd, RatFunc.num_zero, RatFunc.denom_zero, multiplicity_zero,
      multiplicity_one_of_prime hp]
    omega
  have hnx := RatFunc.num_ne_zero hx0
  have hny := RatFunc.num_ne_zero hy0
  have hdx := RatFunc.denom_ne_zero x
  have hdy := RatFunc.denom_ne_zero y
  have hxrep : x = algebraMap K[X] (RatFunc K) x.num / algebraMap K[X] (RatFunc K) x.denom :=
    (RatFunc.num_div_denom x).symm
  have hyrep : y = algebraMap K[X] (RatFunc K) y.num / algebraMap K[X] (RatFunc K) y.denom :=
    (RatFunc.num_div_denom y).symm
  set N : K[X] := x.num * y.denom + x.denom * y.num with hN
  have hsum : x + y = algebraMap K[X] (RatFunc K) N
      / algebraMap K[X] (RatFunc K) (x.denom * y.denom) := by
    rw [hN, map_add, map_mul, map_mul, map_mul]; conv_lhs => rw [hxrep, hyrep]
    rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero hdx) (RatFunc.algebraMap_ne_zero hdy)]
  have hNne : N ≠ 0 := by
    intro h; rw [hsum, h, map_zero, zero_div] at hxy0; exact hxy0 rfl
  have hfin := fun {z : K[X]} (hz : z ≠ 0) => FiniteMultiplicity.of_prime_left hp hz
  have hAne : x.num * y.denom ≠ 0 := mul_ne_zero hnx hdy
  have hBne : x.denom * y.num ≠ 0 := mul_ne_zero hdx hny
  have hh := @min_le_emultiplicity_add K[X] _ p (x.num * y.denom) (x.denom * y.num)
  rw [← hN, (hfin hAne).emultiplicity_eq_multiplicity, (hfin hBne).emultiplicity_eq_multiplicity,
    (hfin hNne).emultiplicity_eq_multiplicity, multiplicity_mul hp (hfin hAne),
    multiplicity_mul hp (hfin hBne)] at hh
  rw [hsum, ratFuncOrd_mk p hp hNne (mul_ne_zero hdx hdy),
    multiplicity_mul hp (hfin (mul_ne_zero hdx hdy))]
  rw [ratFuncOrd] at hx hy
  rcases le_total (multiplicity p x.num + multiplicity p y.denom)
    (multiplicity p x.denom + multiplicity p y.num) with h | h
  · rw [min_eq_left (by exact_mod_cast h)] at hh
    have hle : multiplicity p x.num + multiplicity p y.denom ≤ multiplicity p N := by exact_mod_cast hh
    omega
  · rw [min_eq_right (by exact_mod_cast h)] at hh
    have hle : multiplicity p x.denom + multiplicity p y.num ≤ multiplicity p N := by exact_mod_cast hh
    omega

/-- `νₚ(−x) = νₚ(x)` (negation is a unit multiple). -/
theorem ratFuncOrd_neg (p : K[X]) (hp : Prime p) (x : RatFunc K) :
    ratFuncOrd p (-x) = ratFuncOrd p x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [neg_zero]
  · have hneg1 : ratFuncOrd p (-1 : RatFunc K) = 0 := by
      rw [show (-1 : RatFunc K) = algebraMap K[X] (RatFunc K) (-1) by rw [map_neg, map_one],
        ratFuncOrd_algebraMap p (-1) hp,
        multiplicity_eq_zero.mpr (fun hd => hp.not_unit (isUnit_of_dvd_unit hd isUnit_one.neg))]
      rfl
    rw [show -x = (-1 : RatFunc K) * x by ring,
      ratFuncOrd_mul p hp (neg_ne_zero.mpr one_ne_zero) hx0, hneg1, zero_add]

end DeepWiki.SymbolicIntegration
