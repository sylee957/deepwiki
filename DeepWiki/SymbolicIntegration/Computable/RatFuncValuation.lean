import DeepWiki.SymbolicIntegration.Computable.FractionFieldDeriv
import DeepWiki.SymbolicIntegration.Computable.RischDE.TowerCorrectG

/-! # The `K(t)`-valuation calculus for normal poles

A `p`-adic integer valuation `ratFuncOrd p x = νₚ(x)` on `RatFunc K`, with its representation,
multiplicative, and ultrametric laws, and the key lift: for the fraction-field derivation
`D = extendDeriv d`, a prime `p` normal for `d`, over a characteristic-zero field,
`νₚ(D y) = νₚ(y) − 1` at a normal pole `νₚ(y) < 0`. Used for the RDE normal-denominator bounds. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- **The `p`-adic integer valuation on `K(t)`** `ratFuncOrd p x = νₚ(x)`: the `multiplicity` of the
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

/-- **`νₚ` reads through any representation**: for `x = a/b` with `a, b ≠ 0`,
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

/-- **`νₚ` is multiplicative**: `νₚ(x·y) = νₚ(x) + νₚ(y)` for a prime `p` and nonzero `x, y ∈ K(t)`. -/
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

/-- **`νₚ` is ultrametric with the strict-min law**: if `νₚ(x) < νₚ(y)` for a prime `p` and nonzero
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

section Lift

variable [CharZero K] (d : Derivation ℤ K[X] K[X])

/-- **The `K(t)`-valuation lift of the normal-pole order drop**: for `D = extendDeriv d` extending a
base derivation `d` on `K[X]`, a prime `p` **normal** for `d` (`¬ p ∣ d p`) over a characteristic-zero
field, `νₚ(D y) = νₚ(y) − 1` at a **normal pole** `νₚ(y) < 0`. Lifts the polynomial Wronskian-numerator
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

/-- **The per-prime RDE no-pole bound**: for a solution `y` of `D y + f·y = g` (`D = extendDeriv d`), a
prime `p` **normal** for `d`, if `p` is not a pole of `f` (`νₚ(f) ≥ 0`) nor of `g` (`νₚ(g) ≥ 0`), then
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

/-- **An at-most-simple-pole derivative comes from a regular function.** At a prime `p` **normal** for `d`,
if `D y = extendDeriv d y` has at most a simple pole (`νₚ(D y) ≥ −1`), then `y` is regular (`νₚ(y) ≥ 0`): a
pole `νₚ(y) < 0` would drop to `νₚ(D y) = νₚ(y) − 1 ≤ −2`. This is the pole-order heart of the residue
criterion (`descendGenuine`): in a Liouville form `a/d = D g + Σ cᵢ·logDeriv vᵢ` with `a/d` **reduced**
(simple poles) and the log part simple-poled, the rational part `g` carries no simple pole at those primes,
so `D g` contributes **no** residue there — every residue is a constant log coefficient. -/
theorem ratFuncOrd_nonneg_of_extendDeriv_ge_neg_one {p : K[X]} (hp : Prime p) (hnormal : ¬ p ∣ d p)
    {y : RatFunc K} (h : -1 ≤ ratFuncOrd p (extendDeriv d y)) : 0 ≤ ratFuncOrd p y := by
  by_contra hlt
  rw [not_le] at hlt
  rw [ratFuncOrd_extendDeriv_eq_sub_one_of_normal d hp hnormal hlt] at h
  omega

end Lift

/-! ### The UFM recombination: per-prime no-pole bounds ⟹ `denom(x) ∣ q`

Per-prime valuation bounds `νₚ(y) ≥ −νₚ(q)` combine into the divisibility `denom(y) ∣ q` via
`UniqueFactorizationMonoid.dvd_iff_emultiplicity_le`. -/

/-- **`denom(x) ∣ q` from per-prime multiplicity bounds**: for `x ∈ K(t)`, `q ∈ K[X]` nonzero, if
`multiplicity p x.denom ≤ multiplicity p q` for every prime `p`, then `x.denom ∣ q`. -/
theorem ratFunc_denom_dvd_of_multiplicity_le {x : RatFunc K} {q : K[X]} (hq : q ≠ 0)
    (h : ∀ p : K[X], Prime p → multiplicity p x.denom ≤ multiplicity p q) :
    x.denom ∣ q := by
  rw [UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (RatFunc.denom_ne_zero x)]
  intro p hp
  rw [(FiniteMultiplicity.of_prime_left hp (RatFunc.denom_ne_zero x)).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left hp hq).emultiplicity_eq_multiplicity]
  exact_mod_cast h p hp

/-- **The valuation bound `−νₚ(x) ≤ νₚ(q)` reads as `multiplicity p x.denom ≤ multiplicity p q`**: at a
prime `p`, `−ratFuncOrd p x ≤ multiplicity p q` forces `multiplicity p x.denom ≤ multiplicity p q`, using
coprimality of `num`/`denom`. -/
theorem multiplicity_denom_le_of_ratFuncOrd {x : RatFunc K} {q : K[X]} (p : K[X]) (hp : Prime p)
    (h : -ratFuncOrd p x ≤ (multiplicity p q : ℤ)) :
    multiplicity p x.denom ≤ multiplicity p q := by
  by_cases hpd : p ∣ x.denom
  · -- `p ∣ denom` ⟹ `p ∤ num` (coprime), so `multiplicity p num = 0` and `−νₚ(x) = multiplicity p denom`.
    have hpn : ¬ p ∣ x.num := fun hpnum =>
      hp.not_unit ((RatFunc.isCoprime_num_denom x).isUnit_of_dvd' hpnum hpd)
    have hnum0 : multiplicity p x.num = 0 := multiplicity_eq_zero.mpr hpn
    rw [ratFuncOrd, hnum0] at h
    push_cast at h ⊢
    omega
  · -- `p ∤ denom` ⟹ `multiplicity p denom = 0 ≤ multiplicity p q`.
    rw [multiplicity_eq_zero.mpr hpd]; exact Nat.zero_le _

/-- **The global no-pole-bound ⟹ denominator divisibility**: for `x ∈ K(t)`, `q ∈ K[X]` nonzero, if
every prime `p` satisfies `νₚ(x) ≥ −νₚ(q)`, then `x.denom ∣ q`. Combines
`multiplicity_denom_le_of_ratFuncOrd` with `ratFunc_denom_dvd_of_multiplicity_le`. -/
theorem ratFunc_denom_dvd_of_ratFuncOrd_bound {x : RatFunc K} {q : K[X]} (hq : q ≠ 0)
    (h : ∀ p : K[X], Prime p → -(multiplicity p q : ℤ) ≤ ratFuncOrd p x) :
    x.denom ∣ q :=
  ratFunc_denom_dvd_of_multiplicity_le hq fun p hp =>
    multiplicity_denom_le_of_ratFuncOrd p hp (by have := h p hp; omega)

/-! ### Restatements -/

/-- Restatement: `νₚ` reads through any nonzero representation. -/
example (p : K[X]) (hp : Prime p) {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ratFuncOrd p (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b)
      = (multiplicity p a : ℤ) - (multiplicity p b : ℤ) :=
  ratFuncOrd_mk p hp ha hb

/-- Restatement of the lift: `νₚ(D y) = νₚ(y) − 1` at a normal pole, `D = extendDeriv d`. -/
example [CharZero K] (d : Derivation ℤ K[X] K[X]) {p : K[X]} (hp : Prime p) (hnormal : ¬ p ∣ d p)
    {y : RatFunc K} (hpole : ratFuncOrd p y < 0) :
    ratFuncOrd p (extendDeriv d y) = ratFuncOrd p y - 1 :=
  ratFuncOrd_extendDeriv_eq_sub_one_of_normal d hp hnormal hpole

#print axioms ratFuncOrd_mk
#print axioms ratFuncOrd_extendDeriv_eq_sub_one_of_normal

end DeepWiki.SymbolicIntegration
