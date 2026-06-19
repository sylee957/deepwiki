import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! # Linear filters and polynomial trends (§1.4, Problem 1.2)
A finite linear filter `{aⱼ}` passes a polynomial trend of degree `k` without
distortion (`∑ⱼ aⱼ m(t−j) = m(t)`) when its weights satisfy the moment conditions
`∑ⱼ aⱼ = 1` and `∑ⱼ jʳ aⱼ = 0` for `r = 1, …, k`. -/

namespace DeepWiki.TimeSeries

open Finset

variable {a : ℤ → ℝ} {s : Finset ℤ} {k : ℕ}

/-- Per-monomial: under the moment conditions, the filter reproduces each monomial
`t ↦ tⁱ` of degree `i ≤ k`: `∑ⱼ aⱼ (t − j)ⁱ = tⁱ`. -/
theorem filter_monomial (h0 : ∑ j ∈ s, a j = 1)
    (hm : ∀ r, 1 ≤ r → r ≤ k → ∑ j ∈ s, (j : ℝ) ^ r * a j = 0)
    {i : ℕ} (hi : i ≤ k) (t : ℝ) :
    ∑ j ∈ s, a j * (t - (j : ℝ)) ^ i = t ^ i := by
  have expand : ∀ j : ℤ, a j * (t - (j : ℝ)) ^ i
      = ∑ m ∈ range (i + 1), (i.choose m : ℝ) * (-(j : ℝ)) ^ (i - m) * a j * t ^ m := by
    intro j
    rw [sub_eq_add_neg, add_pow, mul_comm, sum_mul]
    refine sum_congr rfl fun m _ => ?_
    ring
  have hvanish : ∀ m ∈ range (i + 1), m ≠ i →
      (∑ j ∈ s, (i.choose m : ℝ) * (-(j : ℝ)) ^ (i - m) * a j * t ^ m) = 0 := by
    intro m hmem hne
    have hlt : m < i := lt_of_le_of_ne (Nat.lt_succ_iff.1 (mem_range.1 hmem)) hne
    have h1 : 1 ≤ i - m := by omega
    have h2 : i - m ≤ k := le_trans (Nat.sub_le i m) hi
    have factor : ∀ j : ℤ, (i.choose m : ℝ) * (-(j : ℝ)) ^ (i - m) * a j * t ^ m
        = ((i.choose m : ℝ) * (-1) ^ (i - m) * t ^ m) * ((j : ℝ) ^ (i - m) * a j) := by
      intro j; rw [neg_pow]; ring
    rw [sum_congr rfl fun j _ => factor j, ← mul_sum, hm _ h1 h2, mul_zero]
  have hmain : (∑ j ∈ s, (i.choose i : ℝ) * (-(j : ℝ)) ^ (i - i) * a j * t ^ i) = t ^ i := by
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul, mul_one]
    rw [← sum_mul, h0, one_mul]
  rw [sum_congr rfl fun j _ => expand j, sum_comm,
      Finset.sum_eq_single i hvanish fun h => absurd (mem_range.2 (Nat.lt_succ_of_le le_rfl)) h]
  exact hmain

/-- **Problem 1.2** (sufficiency): if the filter weights satisfy `∑ⱼ aⱼ = 1` and
`∑ⱼ jʳ aⱼ = 0` for `r = 1, …, k`, then the filter passes every polynomial trend of
degree `≤ k` without distortion: `∑ⱼ aⱼ m(t − j) = m(t)` for `m(t) = ∑_{r≤k} cᵣ tʳ`. -/
theorem filter_passes_poly (h0 : ∑ j ∈ s, a j = 1)
    (hm : ∀ r, 1 ≤ r → r ≤ k → ∑ j ∈ s, (j : ℝ) ^ r * a j = 0) (c : ℕ → ℝ) (t : ℝ) :
    ∑ j ∈ s, a j * (∑ r ∈ range (k + 1), c r * (t - (j : ℝ)) ^ r)
      = ∑ r ∈ range (k + 1), c r * t ^ r := by
  calc ∑ j ∈ s, a j * (∑ r ∈ range (k + 1), c r * (t - (j : ℝ)) ^ r)
      = ∑ j ∈ s, ∑ r ∈ range (k + 1), a j * (c r * (t - (j : ℝ)) ^ r) := by
        refine sum_congr rfl fun j _ => ?_; rw [mul_sum]
    _ = ∑ r ∈ range (k + 1), ∑ j ∈ s, a j * (c r * (t - (j : ℝ)) ^ r) := sum_comm
    _ = ∑ r ∈ range (k + 1), c r * ∑ j ∈ s, a j * (t - (j : ℝ)) ^ r := by
        refine sum_congr rfl fun r _ => ?_
        rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
    _ = ∑ r ∈ range (k + 1), c r * t ^ r := by
        refine sum_congr rfl fun r hr => ?_
        rw [filter_monomial h0 hm (Nat.lt_succ_iff.1 (mem_range.1 hr)) t]

end DeepWiki.TimeSeries
