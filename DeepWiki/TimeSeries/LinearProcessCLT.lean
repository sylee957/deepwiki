import DeepWiki.TimeSeries.SampleMeanCLT

/-! # Boundary `L²` estimates for the moving-average central limit theorem
The technical core of the `MA(q)` sample-mean central limit theorem (Theorem 7.1.2 for a finite
moving average): the windowed shift-difference `∑_{t<n} (Z_{t−1} − Z_t)` telescopes to its two
boundary terms `Z_{−1} − Z_{n−1}`, so its `L²` norm is bounded by `2M` *independently of `n`*. This
`n`-independence is what makes the rescaled difference `√n X̄ₙ − (∑θ) √n Z̄ₙ` vanish in `L²`. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
/-- The windowed shift-difference telescopes to its two boundary terms:
`∑_{t<n} (Z_{t−1} − Z_t) = Z_{−1} − Z_{n−1}`. -/
theorem sum_range_shift_sub (Z : ℤ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∑ t ∈ Finset.range n, (Z ((t : ℤ) - 1) ω - Z (t : ℤ) ω) = Z (-1) ω - Z ((n : ℤ) - 1) ω := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hc : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
    rw [hc]; ring

/-- **Boundary `L²` estimate (single shift):** the windowed shift-difference has `L²` norm at most
`2M`, uniformly in `n`, when each `Z_s` has `L²` norm at most `M` — because it telescopes to the two
boundary terms `Z_{−1} − Z_{n−1}` (Minkowski). -/
theorem eLpNorm_sum_range_shift_sub_le {Z : ℤ → Ω → ℝ} {M : ℝ≥0∞}
    (hmeas : ∀ s, AEStronglyMeasurable (Z s) P) (hZ : ∀ s, eLpNorm (Z s) 2 P ≤ M) (n : ℕ) :
    eLpNorm (fun ω => ∑ t ∈ Finset.range n, (Z ((t : ℤ) - 1) ω - Z (t : ℤ) ω)) 2 P ≤ 2 * M := by
  rw [show (fun ω => ∑ t ∈ Finset.range n, (Z ((t : ℤ) - 1) ω - Z (t : ℤ) ω))
        = fun ω => Z (-1) ω - Z ((n : ℤ) - 1) ω from funext (sum_range_shift_sub Z n)]
  calc eLpNorm (fun ω => Z (-1) ω - Z ((n : ℤ) - 1) ω) 2 P
      ≤ eLpNorm (Z (-1)) 2 P + eLpNorm (Z ((n : ℤ) - 1)) 2 P :=
        eLpNorm_sub_le (hmeas _) (hmeas _) (by norm_num)
    _ ≤ M + M := add_le_add (hZ _) (hZ _)
    _ = 2 * M := (two_mul M).symm

/-- **Boundary `L²` estimate (lag `j`):** the windowed lag-difference `∑_{t<n} (Z_{t−j} − Z_t)` has
`L²` norm at most `2jM`, uniformly in `n`. By induction on `j`, splitting the `(j+1)`-lag difference
into a single shift of the `j`-shifted sequence (the kernel bound `2M`) plus the `j`-lag difference
(the inductive `2jM`). -/
theorem eLpNorm_sum_range_lag_sub_le {Z : ℤ → Ω → ℝ} {M : ℝ≥0∞}
    (hmeas : ∀ s, AEStronglyMeasurable (Z s) P) (hZ : ∀ s, eLpNorm (Z s) 2 P ≤ M) (n j : ℕ) :
    eLpNorm (fun ω => ∑ t ∈ Finset.range n, (Z ((t : ℤ) - j) ω - Z (t : ℤ) ω)) 2 P ≤ 2 * j * M := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hsplit : (fun ω => ∑ t ∈ Finset.range n, (Z ((t : ℤ) - (j + 1 : ℕ)) ω - Z (t : ℤ) ω))
        = (fun ω => ∑ t ∈ Finset.range n, (Z ((t : ℤ) - 1 - j) ω - Z ((t : ℤ) - j) ω))
          + fun ω => ∑ t ∈ Finset.range n, (Z ((t : ℤ) - j) ω - Z (t : ℤ) ω) := by
      ext ω
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hc : (t : ℤ) - ((j + 1 : ℕ) : ℤ) = (t : ℤ) - 1 - (j : ℤ) := by push_cast; ring
      rw [hc]; ring
    rw [hsplit]
    refine le_trans (eLpNorm_add_le
      (Finset.aestronglyMeasurable_fun_sum _ fun t _ => (hmeas _).sub (hmeas _))
      (Finset.aestronglyMeasurable_fun_sum _ fun t _ => (hmeas _).sub (hmeas _)) (by norm_num)) ?_
    have hF : eLpNorm (fun ω => ∑ t ∈ Finset.range n, (Z ((t : ℤ) - 1 - j) ω - Z ((t : ℤ) - j) ω))
        2 P ≤ 2 * M :=
      eLpNorm_sum_range_shift_sub_le (Z := fun s => Z (s - j)) (fun s => hmeas _) (fun s => hZ _) n
    calc _ ≤ 2 * M + 2 * (j : ℝ≥0∞) * M := add_le_add hF ih
      _ = 2 * ((j : ℕ) + 1 : ℕ) * M := by push_cast; ring

end DeepWiki.TimeSeries
