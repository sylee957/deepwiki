import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncFractions

/-! # Rational-function regularity at a polynomial

A denominator-coprimality API for rational functions with no pole at a polynomial factor.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- A rational function is `Q`-regular if it has a representative with denominator coprime to `Q`. -/
def IsRatFuncRegular (Q : K[X]) (f : RatFunc K) : Prop :=
  ∃ p q : K[X], q ≠ 0 ∧ IsRelPrime Q q ∧
    f = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q

/-- `0` is `Q`-regular. -/
theorem isRatFuncRegular_zero (Q : K[X]) : IsRatFuncRegular Q 0 :=
  ⟨0, 1, one_ne_zero, isRelPrime_one_right, by simp⟩

/-- `Q`-regularity is closed under addition. -/
theorem IsRatFuncRegular.add {Q : K[X]} {f g : RatFunc K}
    (hf : IsRatFuncRegular Q f) (hg : IsRatFuncRegular Q g) : IsRatFuncRegular Q (f + g) := by
  obtain ⟨p1, q1, hq1, hQ1, hf⟩ := hf
  obtain ⟨p2, q2, hq2, hQ2, hg⟩ := hg
  refine ⟨p1 * q2 + q1 * p2, q1 * q2, mul_ne_zero hq1 hq2, hQ1.mul_right hQ2, ?_⟩
  have hinj := RatFunc.algebraMap_injective K
  set am := algebraMap K[X] (RatFunc K)
  have ha1 : am q1 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq1
  have ha2 : am q2 ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq2
  rw [hf, hg, map_add, map_mul, map_mul, map_mul]
  rw [div_add_div _ _ ha1 ha2, mul_comm (am q1) (am p2)]

/-- If `am r / am D` is `Q`-regular and `Q^e ∣ D`, then `Q^e ∣ r`. -/
theorem dvd_num_of_isRatFuncRegular {Q r D : K[X]} {e : ℕ} (hD : D ≠ 0) (hQe : Q ^ e ∣ D)
    (hf : IsRatFuncRegular Q (algebraMap K[X] (RatFunc K) r / algebraMap K[X] (RatFunc K) D)) :
    Q ^ e ∣ r := by
  obtain ⟨p, q, hq, hQ, heq⟩ := hf
  have hinj := RatFunc.algebraMap_injective K
  set am := algebraMap K[X] (RatFunc K)
  have had : am D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have haq : am q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq
  have hcross : am (r * q) = am (p * D) := by
    rw [div_eq_div_iff had haq] at heq
    rw [map_mul, map_mul]
    linear_combination heq
  have hpoly : r * q = p * D := hinj hcross
  exact (hQ.pow_left).dvd_of_dvd_mul_right (by rw [hpoly]; exact hQe.mul_left p)

/-- `Q`-regularity is closed under negation. -/
theorem IsRatFuncRegular.neg {Q : K[X]} {f : RatFunc K} (hf : IsRatFuncRegular Q f) :
    IsRatFuncRegular Q (-f) := by
  obtain ⟨p, q, hq, hQ, hfeq⟩ := hf
  exact ⟨-p, q, hq, hQ, by rw [hfeq, map_neg, neg_div]⟩

/-- A list sum of `Q`-regular rational functions is `Q`-regular. -/
theorem isRatFuncRegular_list_sum {α : Type*} {Q : K[X]} (L : List α)
    (f : α → RatFunc K) (hreg : ∀ a ∈ L, IsRatFuncRegular Q (f a)) :
    IsRatFuncRegular Q (L.map f).sum := by
  induction L with
  | nil => simpa using isRatFuncRegular_zero Q
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons]
    exact (hreg hd (List.mem_cons_self)).add (ih (fun a ha => hreg a (List.mem_cons_of_mem _ ha)))

/-- A list sum of `Q`-regular rational functions is `Q`-regular. -/
theorem isRatFuncRegular_list_sum_self {Q : K[X]} (L : List (RatFunc K))
    (h : ∀ f ∈ L, IsRatFuncRegular Q f) : IsRatFuncRegular Q L.sum := by
  induction L with
  | nil => simpa using isRatFuncRegular_zero Q
  | cons hd tl ih =>
    rw [List.sum_cons]
    exact (h hd (List.mem_cons_self ..)).add (ih fun f hf => h f (List.mem_cons_of_mem _ hf))

end DeepWiki.SymbolicIntegration
