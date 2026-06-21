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

/-- The two boundary sums of the induction step reindex onto the integer intervals `[1, n]` and
`[-n, -1]`: `∑_{t<n} f(n − t) = ∑_{k∈[1,n]} f k` and `∑_{s<n} f(s − n) = ∑_{k∈[-n,-1]} f k`. -/
private theorem sum_range_sub_aux (f : ℤ → ℝ) (n : ℕ) :
    ∑ t ∈ Finset.range n, f ((n : ℤ) - t) = ∑ k ∈ Finset.Icc (1 : ℤ) n, f k := by
  refine Finset.sum_nbij' (fun t => (n : ℤ) - t) (fun k => ((n : ℤ) - k).toNat) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_range] at ht
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro t ht
    simp only [Finset.mem_range] at ht
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    omega
  · intro t ht
    rfl

/-- Companion of `sum_range_sub_aux`: `∑_{s<n} f(s − n) = ∑_{k∈[-n,-1]} f k`. -/
private theorem sum_range_sub_aux2 (f : ℤ → ℝ) (n : ℕ) :
    ∑ s ∈ Finset.range n, f ((s : ℤ) - n) = ∑ k ∈ Finset.Icc (-(n : ℤ)) (-1), f k := by
  refine Finset.sum_nbij' (fun s => (s : ℤ) - n) (fun k => (k + n).toNat) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_range] at hs; simp only [Finset.mem_Icc]; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
  · intro s hs; simp only [Finset.mem_range] at hs; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro s hs; rfl

/-- **Counting identity (Theorem 7.1.1 kernel):** the square double sum of `f(s − t)` collapses to a
triangular-weighted single sum, `∑_{s,t<n} f(s − t) = ∑_{|h|≤n} (n − |h|) f(h)`, because the lag
`h = s − t` is hit by exactly `n − |h|` index pairs. Proved by induction: passing from `n` to `n+1`
adds the boundary row and column `∑_{−n ≤ h ≤ n} f(h)`. -/
theorem sum_range_sum_range_sub (f : ℤ → ℝ) (n : ℕ) :
    ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, f ((s : ℤ) - t)
      = ∑ h ∈ Finset.Icc (-(n : ℤ)) n, ((n : ℝ) - |h|) * f h := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- expand the `(n+1)×(n+1)` square into the `n×n` square plus its boundary row/column/corner
    have hS : ∑ s ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1), f ((s : ℤ) - t)
        = (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, f ((s : ℤ) - t))
          + (∑ s ∈ Finset.range n, f ((s : ℤ) - n)) + (∑ t ∈ Finset.range n, f ((n : ℤ) - t))
          + f 0 := by
      simp_rw [Finset.sum_range_succ, Finset.sum_add_distrib, sub_self]
      ring
    -- the boundary equals `∑_{−n ≤ h ≤ n} f h`
    have hbdry : (∑ s ∈ Finset.range n, f ((s : ℤ) - n)) + (∑ t ∈ Finset.range n, f ((n : ℤ) - t))
        + f 0 = ∑ h ∈ Finset.Icc (-(n : ℤ)) n, f h := by
      rw [sum_range_sub_aux2, sum_range_sub_aux]
      have hunion : Finset.Icc (-(n : ℤ)) n
          = Finset.Icc (-(n : ℤ)) (-1) ∪ insert 0 (Finset.Icc (1 : ℤ) n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert]; omega
      have hdisj : Disjoint (Finset.Icc (-(n : ℤ)) (-1)) (insert 0 (Finset.Icc (1 : ℤ) n)) := by
        simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_insert]; intro a ha; omega
      have h0 : (0 : ℤ) ∉ Finset.Icc (1 : ℤ) n := by simp only [Finset.mem_Icc]; omega
      rw [hunion, Finset.sum_union hdisj, Finset.sum_insert h0]; ring
    -- drop the zero-weighted far endpoints `±(n+1)`, then split the coefficient `(n+1−|h|) = (n−|h|)+1`
    have hdrop : ∑ h ∈ Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1), (((n : ℝ) + 1) - |h|) * f h
        = ∑ h ∈ Finset.Icc (-(n : ℤ)) n, (((n : ℝ) + 1) - |h|) * f h := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
      · intro x hx hx'
        simp only [Finset.mem_Icc] at hx hx'
        have hx2 : |x| = (n : ℤ) + 1 := by rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
        rw [hx2]; push_cast; ring
    -- split the coefficient `(n+1−|h|) = (n−|h|) + 1`
    have hsplit : ∑ h ∈ Finset.Icc (-(n : ℤ)) n, (((n : ℝ) + 1) - |h|) * f h
        = (∑ h ∈ Finset.Icc (-(n : ℤ)) n, ((n : ℝ) - |h|) * f h)
          + ∑ h ∈ Finset.Icc (-(n : ℤ)) n, f h := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun h _ => by ring
    rw [hS, ih]
    simp only [Nat.cast_succ]
    rw [hdrop]
    linarith [hbdry, hsplit]

end DeepWiki.TimeSeries
