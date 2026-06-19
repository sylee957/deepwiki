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

end DeepWiki.TimeSeries
