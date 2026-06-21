import Mathlib.Tactic

/-! # The sample autocovariance and autocorrelation functions (§1.5)
For an observed series `x₀, …, x_{n−1}` (Definition 1.5.2): the sample mean `x̄`, the
sample autocovariance function `γ̂(h) = n⁻¹ ∑_{t<n−h} (x_{t+h} − x̄)(xₜ − x̄)`, and the
sample autocorrelation function `ρ̂(h) = γ̂(h) / γ̂(0)`. -/

namespace DeepWiki.TimeSeries

/-- The sample mean `x̄ = n⁻¹ ∑_{t<n} xₜ` of an observed series of length `n`. -/
noncomputable def sampleMean (n : ℕ) (x : ℕ → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, x t

/-- **Definition 1.5.2**: the sample autocovariance function
`γ̂(h) = n⁻¹ ∑_{t<n−h} (x_{t+h} − x̄)(xₜ − x̄)` of an observed series `x₀, …, x_{n−1}`. -/
noncomputable def sampleACVF (n : ℕ) (x : ℕ → ℝ) (h : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ t ∈ Finset.range (n - h), (x (t + h) - sampleMean n x) * (x t - sampleMean n x)

/-- **Definition 1.5.2** (companion): the sample autocorrelation function
`ρ̂(h) = γ̂(h) / γ̂(0)`. -/
noncomputable def sampleACF (n : ℕ) (x : ℕ → ℝ) (h : ℕ) : ℝ := sampleACVF n x h / sampleACVF n x 0

/-- `γ̂(0) = n⁻¹ ∑_{t<n} (xₜ − x̄)²` is the sample variance. -/
theorem sampleACVF_zero_eq (n : ℕ) (x : ℕ → ℝ) :
    sampleACVF n x 0 = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, (x t - sampleMean n x) ^ 2 := by
  simp only [sampleACVF, Nat.sub_zero, add_zero, sq]

/-- `γ̂(0) ≥ 0`: the sample variance is non-negative. -/
theorem sampleACVF_zero_nonneg (n : ℕ) (x : ℕ → ℝ) : 0 ≤ sampleACVF n x 0 := by
  rw [sampleACVF_zero_eq]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ => sq_nonneg _)

/-- `ρ̂(0) = 1` whenever the sample variance `γ̂(0)` is nonzero. -/
theorem sampleACF_zero {n : ℕ} {x : ℕ → ℝ} (h : sampleACVF n x 0 ≠ 0) : sampleACF n x 0 = 1 :=
  div_self h

/-- The centered, zero-padded data `ỹ(m) = xₘ − x̄` for `0 ≤ m < n`, else `0` — extended to `ℤ`. -/
noncomputable def centeredPad (n : ℕ) (x : ℕ → ℝ) (m : ℤ) : ℝ :=
  if 0 ≤ m ∧ m < n then x m.toNat - sampleMean n x else 0

/-- **Convolution form of the sample autocovariance** (the key to non-negative definiteness): for
`j ≤ i < n`, `γ̂(i−j) = n⁻¹ ∑_{k<2n} ỹ(k−i) ỹ(k−j)` with `ỹ` the centered zero-padded data. -/
theorem sampleACVF_eq_conv (n : ℕ) (x : ℕ → ℝ) {i j : ℕ} (hi : i < n) (hji : j ≤ i) :
    sampleACVF n x (i - j)
      = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (2 * n),
          centeredPad n x ((k : ℤ) - i) * centeredPad n x ((k : ℤ) - j) := by
  rw [sampleACVF]
  congr 1
  have hsub : Finset.Ico i (j + n) ⊆ Finset.range (2 * n) := by
    intro k hk; simp only [Finset.mem_Ico] at hk; simp only [Finset.mem_range]; omega
  have hzero : ∀ k ∈ Finset.range (2 * n), k ∉ Finset.Ico i (j + n) →
      centeredPad n x ((k : ℤ) - i) * centeredPad n x ((k : ℤ) - j) = 0 := by
    intro k _ hk
    simp only [Finset.mem_Ico, not_and, not_lt] at hk
    simp only [centeredPad]
    rcases lt_or_ge k i with h | h
    · rw [if_neg (show ¬((0 : ℤ) ≤ (k : ℤ) - i ∧ (k : ℤ) - i < n) from by omega), zero_mul]
    · rw [if_neg (show ¬((0 : ℤ) ≤ (k : ℤ) - j ∧ (k : ℤ) - j < n) from by
        have := hk h; omega), mul_zero]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by congr 1; omega) fun t ht => ?_
  simp only [Finset.mem_range] at ht
  have h1 : centeredPad n x ((↑(i + t) : ℤ) - i) = x t - sampleMean n x := by
    simp only [centeredPad]; rw [if_pos (by omega)]; congr 2; omega
  have h2 : centeredPad n x ((↑(i + t) : ℤ) - j) = x (t + (i - j)) - sampleMean n x := by
    simp only [centeredPad]; rw [if_pos (by omega)]; congr 2; omega
  rw [h1, h2]; ring

/-- **§7.2 (eq 7.2.3): the sample covariance matrix `Γ̂ₙ = [γ̂(i−j)]` is non-negative definite.**
The quadratic form `∑ᵢⱼ aᵢ aⱼ γ̂(|i−j|) = n⁻¹ ∑ₖ (∑ᵢ aᵢ ỹ(k−i))² ≥ 0` (with `ỹ` the centered
zero-padded data) — a sum of squares. -/
theorem sampleACVF_quadratic_nonneg (n : ℕ) (x : ℕ → ℝ) (a : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        a i * a j * (if j ≤ i then sampleACVF n x (i - j) else sampleACVF n x (j - i)) := by
  have hentry : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      a i * a j * (if j ≤ i then sampleACVF n x (i - j) else sampleACVF n x (j - i))
        = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (2 * n),
            (a i * centeredPad n x ((k : ℤ) - i)) * (a j * centeredPad n x ((k : ℤ) - j)) := by
    intro i hi j hj
    simp only [Finset.mem_range] at hi hj
    have he : (if j ≤ i then sampleACVF n x (i - j) else sampleACVF n x (j - i))
        = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (2 * n),
            centeredPad n x ((k : ℤ) - i) * centeredPad n x ((k : ℤ) - j) := by
      split_ifs with h
      · exact sampleACVF_eq_conv n x hi h
      · rw [sampleACVF_eq_conv n x hj (by omega : i ≤ j)]
        exact congr_arg _ (Finset.sum_congr rfl fun k _ => mul_comm _ _)
    rw [he, mul_left_comm, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (hentry i hi)]
  have reorder : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (n : ℝ)⁻¹ *
        ∑ k ∈ Finset.range (2 * n),
          (a i * centeredPad n x ((k : ℤ) - i)) * (a j * centeredPad n x ((k : ℤ) - j)))
      = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (2 * n),
          (∑ i ∈ Finset.range n, a i * centeredPad n x ((k : ℤ) - i)) ^ 2 := by
    simp_rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [← Finset.sum_mul_sum]; ring
  rw [reorder]
  positivity

end DeepWiki.TimeSeries
