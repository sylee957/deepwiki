import DeepWiki.TimeSeries.MDependence
import DeepWiki.TimeSeries.SampleMeanVariance

/-! # Central limit theorem for m-dependent sequences (§6.4, Theorem 6.4.2) — foundations
A bottom-up construction of the `m`-dependent central limit theorem via Bernstein's
big-block/small-block method. This file begins with the foundational bricks: the autocovariance of an
`m`-dependent process vanishes beyond lag `m`, hence is summable, and the long-run variance is the
finite sum `∑_{|h| ≤ m} γ(h)` — the variance the standardized sample mean converges to. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **m-dependent ⟹ the autocovariance vanishes beyond lag `m`**: for `|k| > m`, `Xₖ` and `X₀` are
independent, so `acvfStat X μ k = cov[Xₖ, X₀] = 0`. -/
theorem acvfStat_eq_zero_of_mDependent {m : ℕ} {X : ℤ → Ω → ℝ} (h : IsMDependent m X μ)
    (hmem : ∀ t, MemLp (X t) 2 μ) {k : ℤ} (hk : (m : ℤ) < |k|) : acvfStat X μ k = 0 := by
  rw [acvfStat_apply]
  rcases lt_or_gt_of_ne (show k ≠ 0 by rintro rfl; rw [abs_zero] at hk; omega) with hneg | hpos
  · rw [abs_of_neg hneg] at hk
    exact (h.indepFun (by omega : k + (m : ℤ) < 0)).covariance_eq_zero (hmem k) (hmem 0)
  · rw [abs_of_pos hpos] at hk
    exact ((h.indepFun (by omega : (0 : ℤ) + (m : ℤ) < k)).symm).covariance_eq_zero
      (hmem k) (hmem 0)

/-- **m-dependent ⟹ summable autocovariance**: the autocovariance is supported on `|h| ≤ m`
(`acvfStat_eq_zero_of_mDependent`), hence summable — so the long-run variance `∑' h, γ(h)` is the
finite sum `∑_{|h| ≤ m} γ(h)`. -/
theorem summable_acvfStat_of_mDependent {m : ℕ} {X : ℤ → Ω → ℝ} (h : IsMDependent m X μ)
    (hmem : ∀ t, MemLp (X t) 2 μ) : Summable (acvfStat X μ) :=
  summable_of_ne_finset_zero (s := Finset.Icc (-(m : ℤ)) m) fun k hk =>
    acvfStat_eq_zero_of_mDependent h hmem (by
      rw [Finset.mem_Icc, not_and_or] at hk
      rcases hk with hk | hk
      · exact lt_abs.mpr (Or.inr (by omega))
      · exact lt_abs.mpr (Or.inl (by omega)))

/-- **The long-run variance of an m-dependent process is the finite sum `∑_{|h| ≤ m} γ(h)`**: the
autocovariance series collapses to lags within the dependence range. -/
theorem tsum_acvfStat_eq_sum_of_mDependent {m : ℕ} {X : ℤ → Ω → ℝ} (h : IsMDependent m X μ)
    (hmem : ∀ t, MemLp (X t) 2 μ) :
    ∑' k : ℤ, acvfStat X μ k = ∑ k ∈ Finset.Icc (-(m : ℤ)) m, acvfStat X μ k :=
  tsum_eq_sum fun k hk =>
    acvfStat_eq_zero_of_mDependent h hmem (by
      rw [Finset.mem_Icc, not_and_or] at hk
      rcases hk with hk | hk
      · exact lt_abs.mpr (Or.inr (by omega))
      · exact lt_abs.mpr (Or.inl (by omega)))

/-- **Variance of the sample mean of an m-dependent process** (the limit the CLT identifies):
`n · Var(X̄ₙ) → ∑_h γ(h) = ∑_{|h| ≤ m} γ(h)`. The summability hypothesis is discharged automatically
by `summable_acvfStat_of_mDependent`; this is the variance `v` of the limiting Gaussian. -/
theorem tendsto_nsmul_variance_sampleMean_of_mDependent {m : ℕ} {X : ℤ → Ω → ℝ}
    [IsProbabilityMeasure μ] (hX : IsWeaklyStationary X μ) (h : IsMDependent m X μ) :
    Tendsto (fun n : ℕ => (n : ℝ) * variance (fun ω => sampleMean n (fun t => X t ω)) μ) atTop
      (𝓝 (∑' k : ℤ, acvfStat X μ k)) :=
  tendsto_nsmul_variance_sampleMean hX (summable_acvfStat_of_mDependent h hX.memLp)

end DeepWiki.TimeSeries
