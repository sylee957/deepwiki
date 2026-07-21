import DeepWiki.Algebra.RatFuncDerivation
import DeepWiki.Algebra.SquarefreeGcd

/-! # Proper rational functions and the derivative-denominator obstruction

`RatFunc.IsProper` (numerator degree below denominator degree) with its closure laws, the
canonical-representation transfer lemmas, and the **keystone obstruction**: over a field of
characteristic zero, a nonzero proper rational function with squarefree denominator is not
the derivative of any rational function — every prime in a candidate antiderivative's
denominator appears in the derivative's denominator with multiplicity at least two. This is
the completeness half of Hermite reduction. Mathlib lacks these; upstream candidates. -/

universe u

open Polynomial

namespace RatFunc

variable {K : Type u} [Field K]

/-- A rational function is **proper** when its (canonical) numerator degree is below its
denominator degree. -/
def IsProper (x : RatFunc K) : Prop := x.num.degree < x.denom.degree

/-- `0` is proper. -/
theorem isProper_zero : IsProper (0 : RatFunc K) := by
  rw [IsProper, num_zero, denom_zero]
  simp

/-- Properness from any fraction representation with a degree drop. -/
theorem isProper_of_eq_div {p q : K[X]} (hq : q ≠ 0) (hdeg : p.degree < q.degree)
    {x : RatFunc K} (hx : x = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) :
    IsProper x := by
  by_cases hx0 : x = 0
  · rw [hx0]; exact isProper_zero
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hx
    exact hx0 hx
  have hnum0 : x.num ≠ 0 := num_ne_zero hx0
  have hcross : x.num * q = p * x.denom := by
    have h2 : algebraMap K[X] (RatFunc K) x.num / algebraMap K[X] (RatFunc K) x.denom
        = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q :=
      (num_div_denom x).trans hx
    rw [div_eq_div_iff (algebraMap_ne_zero (denom_ne_zero x)) (algebraMap_ne_zero hq),
      ← map_mul, ← map_mul] at h2
    exact algebraMap_injective K h2
  have hdeg2 : x.num.natDegree + q.natDegree = p.natDegree + x.denom.natDegree := by
    have h3 := congrArg Polynomial.natDegree hcross
    rwa [Polynomial.natDegree_mul hnum0 hq, Polynomial.natDegree_mul hp0 (denom_ne_zero x)]
      at h3
  have hlt : p.natDegree < q.natDegree := by
    rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq] at hdeg
    exact_mod_cast hdeg
  rw [IsProper, Polynomial.degree_eq_natDegree hnum0,
    Polynomial.degree_eq_natDegree (denom_ne_zero x)]
  exact_mod_cast (by omega : x.num.natDegree < x.denom.natDegree)

/-- Conversely, a proper value forces the degree drop on every representation. -/
theorem degree_lt_of_isProper_of_eq_div {p q : K[X]} (hq : q ≠ 0)
    {x : RatFunc K} (hx : x = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q)
    (hprop : IsProper x) : p.degree < q.degree := by
  by_cases hp0 : p = 0
  · rw [hp0, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (fun hb => hq (Polynomial.degree_eq_bot.mp hb))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [eq_comm, div_eq_zero_iff] at hx
    rcases hx with h | h
    · exact hp0 (algebraMap_injective K (by rw [h, map_zero]))
    · exact algebraMap_ne_zero hq h
  have hnum0 : x.num ≠ 0 := num_ne_zero hx0
  have hcross : x.num * q = p * x.denom := by
    have h2 : algebraMap K[X] (RatFunc K) x.num / algebraMap K[X] (RatFunc K) x.denom
        = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q :=
      (num_div_denom x).trans hx
    rw [div_eq_div_iff (algebraMap_ne_zero (denom_ne_zero x)) (algebraMap_ne_zero hq),
      ← map_mul, ← map_mul] at h2
    exact algebraMap_injective K h2
  have hdeg2 : x.num.natDegree + q.natDegree = p.natDegree + x.denom.natDegree := by
    have h3 := congrArg Polynomial.natDegree hcross
    rwa [Polynomial.natDegree_mul hnum0 hq, Polynomial.natDegree_mul hp0 (denom_ne_zero x)]
      at h3
  have hlt : x.num.natDegree < x.denom.natDegree := by
    rw [IsProper, Polynomial.degree_eq_natDegree hnum0,
      Polynomial.degree_eq_natDegree (denom_ne_zero x)] at hprop
    exact_mod_cast hprop
  rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq]
  exact_mod_cast (by omega : p.natDegree < q.natDegree)

/-- Propers are closed under addition. -/
theorem IsProper.add {x y : RatFunc K} (hx : IsProper x) (hy : IsProper y) :
    IsProper (x + y) := by
  have hxd := denom_ne_zero x
  have hyd := denom_ne_zero y
  refine isProper_of_eq_div (p := x.num * y.denom + x.denom * y.num)
    (mul_ne_zero hxd hyd) ?_ ?_
  · calc (x.num * y.denom + x.denom * y.num).degree
        ≤ max (x.num * y.denom).degree (x.denom * y.num).degree := Polynomial.degree_add_le _ _
      _ < (x.denom * y.denom).degree := by
        rw [Polynomial.degree_mul, Polynomial.degree_mul, Polynomial.degree_mul]
        refine max_lt ?_ ?_
        · exact WithBot.add_lt_add_right (Polynomial.degree_eq_bot.not.mpr hyd) hx
        · rw [add_comm x.denom.degree y.num.degree,
            add_comm x.denom.degree y.denom.degree]
          exact WithBot.add_lt_add_right (Polynomial.degree_eq_bot.not.mpr hxd) hy
  · conv_lhs => rw [← num_div_denom x, ← num_div_denom y]
    rw [div_add_div _ _ (algebraMap_ne_zero hxd) (algebraMap_ne_zero hyd),
      ← map_mul, ← map_mul, ← map_mul, ← map_add]

/-- Propers are closed under negation. -/
theorem IsProper.neg {x : RatFunc K} (hx : IsProper x) : IsProper (-x) := by
  refine isProper_of_eq_div (denom_ne_zero x) (p := -x.num) ?_ ?_
  · rwa [Polynomial.degree_neg]
  · rw [map_neg, neg_div, num_div_denom]

/-- Propers are closed under subtraction. -/
theorem IsProper.sub {x y : RatFunc K} (hx : IsProper x) (hy : IsProper y) :
    IsProper (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

/-- Propers are closed under lists sums. -/
theorem isProper_list_sum {l : List (RatFunc K)} (h : ∀ x ∈ l, IsProper x) :
    IsProper l.sum := by
  induction l with
  | nil => exact isProper_zero
  | cons x t ih =>
      rw [List.sum_cons]
      exact (h x (by simp)).add (ih fun y hy => h y (by simp [hy]))

/-- Dividing a proper by a nonzero polynomial stays proper. -/
theorem IsProper.div_algebraMap {x : RatFunc K} {q : K[X]} (hq : q ≠ 0) (hx : IsProper x) :
    IsProper (x / algebraMap K[X] (RatFunc K) q) := by
  refine isProper_of_eq_div (q := x.denom * q) (mul_ne_zero (denom_ne_zero x) hq)
    (p := x.num) ?_ ?_
  · calc x.num.degree < x.denom.degree := hx
      _ ≤ (x.denom * q).degree :=
        Polynomial.degree_le_of_dvd (Dvd.intro q rfl) (mul_ne_zero (denom_ne_zero x) hq)
  · rw [map_mul, ← div_div, num_div_denom]

/-- The derivative of a proper rational function is proper (characteristic zero not
needed for this direction). -/
theorem IsProper.deriv {x : RatFunc K} (hx : IsProper x) : IsProper (RatFunc.deriv x) := by
  have hd0 : x.denom ≠ 0 := denom_ne_zero x
  refine isProper_of_eq_div (q := x.denom ^ 2) (pow_ne_zero 2 hd0)
    (p := Polynomial.derivative x.num * x.denom - x.num * Polynomial.derivative x.denom)
    ?_ ?_
  · have hbound : ∀ a b : K[X], a.degree < x.denom.degree → b.degree ≤ x.denom.degree →
        (a * b).degree < (x.denom ^ 2).degree := by
      intro a b ha hb
      rw [Polynomial.degree_mul, Polynomial.degree_pow, two_smul]
      calc a.degree + b.degree ≤ a.degree + x.denom.degree := add_le_add le_rfl hb
        _ < x.denom.degree + x.denom.degree :=
          WithBot.add_lt_add_right (Polynomial.degree_eq_bot.not.mpr hd0) ha
    calc (Polynomial.derivative x.num * x.denom - x.num * Polynomial.derivative x.denom).degree
        ≤ max (Polynomial.derivative x.num * x.denom).degree
            (x.num * Polynomial.derivative x.denom).degree := Polynomial.degree_sub_le _ _
      _ < (x.denom ^ 2).degree := by
        refine max_lt (hbound _ _ ?_ le_rfl) (hbound _ _ hx (Polynomial.degree_derivative_le))
        exact lt_of_le_of_lt Polynomial.degree_derivative_le hx
  · rw [RatFunc.deriv, map_sub, map_mul, map_mul, map_pow]

/-- Reduced (coprime) representations have associated denominators with the canonical one. -/
theorem denom_associated_of_eq_div {p q : K[X]} (hq : q ≠ 0) (hcp : IsCoprime p q)
    {x : RatFunc K} (hx : x = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) :
    Associated x.denom q := by
  have hcross : x.num * q = p * x.denom := by
    have h2 : algebraMap K[X] (RatFunc K) x.num / algebraMap K[X] (RatFunc K) x.denom
        = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q :=
      (num_div_denom x).trans hx
    rw [div_eq_div_iff (algebraMap_ne_zero (denom_ne_zero x)) (algebraMap_ne_zero hq),
      ← map_mul, ← map_mul] at h2
    exact algebraMap_injective K h2
  refine associated_of_dvd_dvd ?_ ?_
  · exact (isCoprime_num_denom x).symm.dvd_of_dvd_mul_left
      ⟨p, hcross.trans (mul_comm p x.denom)⟩
  · exact hcp.symm.dvd_of_dvd_mul_left ⟨x.num, hcross.symm.trans (mul_comm x.num q)⟩

variable [CharZero K]

/-- **The derivative-denominator obstruction**: a nonzero proper rational function with
squarefree denominator is not the derivative of any rational function — the candidate's
denominator primes appear squared in the derivative's denominator (characteristic zero). -/
theorem eq_zero_of_deriv_of_squarefree_denom {g h : RatFunc K}
    (hgh : RatFunc.deriv g = h) (hsf : Squarefree h.denom) (hprop : IsProper h) : h = 0 := by
  by_contra hne
  -- the target denominator is not a unit
  have hdunit : ¬ IsUnit h.denom := by
    intro hu
    have h1 : h.denom = 1 := (monic_denom h).eq_one_of_isUnit hu
    rw [IsProper, h1, Polynomial.degree_one] at hprop
    have h2 : h.num = 0 := by
      by_contra hnum
      exact absurd (lt_of_le_of_lt (Polynomial.zero_le_degree_iff.mpr hnum) hprop)
        (lt_irrefl _)
    exact hne (num_eq_zero_iff.mp h2)
  have hq0 : g.denom ≠ 0 := denom_ne_zero g
  by_cases hqu : IsUnit g.denom
  · -- the candidate is a polynomial, so its derivative has trivial denominator
    have hq1 : g.denom = 1 := (monic_denom g).eq_one_of_isUnit hqu
    have hg : g = algebraMap K[X] (RatFunc K) g.num := by
      conv_lhs => rw [← num_div_denom g]
      rw [hq1, map_one, div_one]
    rw [hg, deriv_algebraMap] at hgh
    exact hdunit (hgh ▸ denom_algebraMap (Polynomial.derivative g.num) ▸ isUnit_one)
  · -- a prime of the candidate's denominator squares into the target denominator
    obtain ⟨π, hπirr, hπq⟩ := WfDvdMonoid.exists_irreducible_factor hqu hq0
    have hπ : Prime π := (UniqueFactorizationMonoid.irreducible_iff_prime).mp hπirr
    obtain ⟨m, hm1, hmd, hmax⟩ := Polynomial.exists_max_pow_dvd hq0 hπirr hπq
    set N := Polynomial.derivative g.num * g.denom - g.num * Polynomial.derivative g.denom
      with hNdef
    have hrep : h = algebraMap K[X] (RatFunc K) N
        / algebraMap K[X] (RatFunc K) (g.denom ^ 2) := by
      rw [← hgh]
      conv_lhs => rw [show g = algebraMap K[X] (RatFunc K) g.num
        / algebraMap K[X] (RatFunc K) g.denom from (num_div_denom g).symm]
      rw [RatFunc.deriv_div hq0, ← map_mul, ← map_mul, ← map_sub, ← map_pow]
    by_cases hN0 : N = 0
    · rw [hN0, map_zero, zero_div] at hrep
      exact hne hrep
    have hcross : h.num * g.denom ^ 2 = N * h.denom := by
      have h2 : algebraMap K[X] (RatFunc K) h.num / algebraMap K[X] (RatFunc K) h.denom
          = algebraMap K[X] (RatFunc K) N
            / algebraMap K[X] (RatFunc K) (g.denom ^ 2) :=
        (num_div_denom h).trans hrep
      rw [div_eq_div_iff (algebraMap_ne_zero (denom_ne_zero h))
        (algebraMap_ne_zero (pow_ne_zero 2 hq0)), ← map_mul, ← map_mul] at h2
      exact algebraMap_injective K h2
    have hπp : ¬ π ∣ g.num := fun hd =>
      hπ.not_unit ((isCoprime_num_denom g).isUnit_of_dvd' hd hπq)
    -- the numerator's exact π-power is m − 1
    have hq'2 : ¬ π ^ m ∣ Polynomial.derivative g.denom :=
      Polynomial.pow_not_dvd_derivative hπirr hm1 hmd hmax
    have hN1 : π ^ (m - 1) ∣ N := by
      apply dvd_sub
      · exact Dvd.dvd.mul_left ((pow_dvd_pow π (by omega)).trans hmd) _
      · exact Dvd.dvd.mul_left (Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hmd) _
    have hN2 : ¬ π ^ m ∣ N := by
      intro hd
      have h2 : π ^ m ∣ Polynomial.derivative g.num * g.denom := Dvd.dvd.mul_left hmd _
      have h3 : π ^ m ∣ g.num * Polynomial.derivative g.denom := by
        have h4 := dvd_sub h2 hd
        rw [hNdef, sub_sub_cancel] at h4
        exact h4
      exact hq'2 (hπ.pow_dvd_of_dvd_mul_left m hπp h3)
    obtain ⟨N₀, hN₀⟩ := hN1
    have hπN₀ : ¬ π ∣ N₀ := by
      intro hd
      apply hN2
      rw [hN₀, show π ^ m = π ^ (m - 1) * π from by
        rw [← pow_succ, Nat.sub_add_cancel hm1]]
      exact mul_dvd_mul_left _ hd
    -- π^{m+1} divides the left side; cancel π^{m−1}
    have hlhs : π ^ (m + 1) ∣ N * h.denom := by
      rw [← hcross]
      refine Dvd.dvd.mul_left ?_ _
      calc π ^ (m + 1) ∣ π ^ (m * 2) := pow_dvd_pow π (by omega)
        _ ∣ g.denom ^ 2 := by
          rw [pow_mul]
          exact pow_dvd_pow_of_dvd hmd 2
    have hcancel : π ^ 2 ∣ N₀ * h.denom := by
      have h1 : π ^ (m - 1) * π ^ 2 ∣ π ^ (m - 1) * (N₀ * h.denom) := by
        rw [← pow_add, show m - 1 + 2 = m + 1 from by omega]
        rw [← mul_assoc, ← hN₀]
        exact hlhs
      exact (mul_dvd_mul_iff_left (pow_ne_zero (m - 1) hπ.ne_zero)).mp h1
    have hfinal : π ^ 2 ∣ h.denom := hπ.pow_dvd_of_dvd_mul_left 2 hπN₀ hcancel
    exact hπ.not_unit (hsf π (by rw [← sq]; exact hfinal))

end RatFunc
