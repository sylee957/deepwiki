import DeepWiki.TimeSeries.StationaryProcesses
import DeepWiki.TimeSeries.SampleAutocovariance
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Asymptotic variance of the sample mean (Theorem 7.1.1)
For a stationary process with summable autocovariance `γ`, the variance of the sample mean satisfies
`n · Var(X̄ₙ) → ∑ⱼ γ(j)`. The proof factors into an analytic core — the triangular-weight Cesàro
limit `∑_{|h|<n} (1 − |h|/n) γ(h) → ∑ₕ γ(h)` (dominated convergence, Tannery's theorem) — and the
algebraic variance identity `n · Var(X̄ₙ) = ∑_{|h|<n} (1 − |h|/n) γ(h)`. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Analytic core of Theorem 7.1.1 (triangular-weight Cesàro limit):** for a summable
`γ : ℤ → ℝ`, the Cesàro-weighted partial sums `∑_{|h|<n} (1 − |h|/n) γ(h)` converge to `∑ₕ γ(h)`.
Each weight `(1 − |h|/n) → 1` pointwise and is dominated by `|γ(h)|`, so Tannery's theorem
(dominated convergence for sums) applies. -/
theorem tendsto_tsum_triangular {γ : ℤ → ℝ} (hγ : Summable γ) :
    Tendsto (fun n : ℕ => ∑' h : ℤ, if |(h : ℝ)| < n then (1 - |(h : ℝ)| / n) * γ h else 0)
      atTop (𝓝 (∑' h : ℤ, γ h)) := by
  refine tendsto_tsum_of_dominated_convergence (bound := fun h => |γ h|) hγ.abs (fun h => ?_) ?_
  · -- pointwise: eventually the indicator is on, and `(1 - |h|/n) γ h → γ h`
    refine Tendsto.congr' (f₁ := fun n : ℕ => (1 - |(h : ℝ)| / n) * γ h) ?_ ?_
    · filter_upwards [eventually_gt_atTop h.natAbs] with n hn
      have h2 : |h| < (n : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hn
      have hlt : |(h : ℝ)| < (n : ℝ) :=
        calc |(h : ℝ)| = ((|h| : ℤ) : ℝ) := (Int.cast_abs (R := ℝ)).symm
          _ < (n : ℝ) := by exact_mod_cast h2
      rw [if_pos hlt]
    · have h0 : Tendsto (fun n : ℕ => |(h : ℝ)| / n) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      have h1 : Tendsto (fun n : ℕ => 1 - |(h : ℝ)| / n) atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
        rwa [sub_zero] at this
      have h2 := h1.mul_const (γ h)
      rwa [one_mul] at h2
  · -- domination: `‖(1 - |h|/n) γ h‖ ≤ |γ h|` since `0 ≤ 1 - |h|/n ≤ 1` when `|h| < n`
    filter_upwards with n h
    split_ifs with hcond
    · have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (abs_nonneg _) hcond
      have hdiv0 : (0 : ℝ) ≤ |(h : ℝ)| / n := div_nonneg (abs_nonneg _) hn0.le
      have hdiv1 : |(h : ℝ)| / n < 1 := (div_lt_one hn0).mpr hcond
      have hle1 : ‖1 - |(h : ℝ)| / n‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
      rw [norm_mul, Real.norm_eq_abs (γ h)]
      exact mul_le_of_le_one_left (abs_nonneg _) hle1
    · rw [norm_zero]; exact abs_nonneg (γ h)

end DeepWiki.TimeSeries
