import DeepWiki.TimeSeries.LinearProcessCLT
import DeepWiki.TimeSeries.LinearProcess
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Toward the general linear-process central limit theorem (Theorem 7.1.2)
Bridges the raw-function boundary `L²` estimates of `LinearProcessCLT` to the Hilbert space
`Lp ℝ 2 μ`, so the moving-average central limit theorem can be lifted from finite `MA(q)` to the
general (`MA(∞)` / ARMA) linear process driven by iid noise. The window lag-sum is finite (raw),
embedded by `MemLp.toLp`; the *filter* `∑ⱼ ψⱼ • (lag j)` is the convergent `L²` series. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The windowed lag-`j` difference is square-integrable (a finite sum of `L²` differences). -/
theorem memLp_lag {Z : ℤ → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ) (n j : ℕ) :
    MemLp (fun ω => ∑ t ∈ Finset.range n, (Z ((t : ℤ) - j) ω - Z (t : ℤ) ω)) 2 μ :=
  memLp_finsetSum _ (fun _ _ => (hZ _).sub (hZ _))

/-- The `L²` norm of the embedded windowed lag-`j` difference is bounded by `2jM` (`M = ‖Z₀‖₂`),
uniformly in `n` — the `Lp`-norm form of the raw boundary estimate `eLpNorm_sum_range_lag_sub_le`,
transported through `MemLp.toLp`. -/
theorem norm_toLp_lag_le {Z : ℤ → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ)
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ) (n j : ℕ) :
    ‖(memLp_lag hZ n j).toLp _‖ ≤ 2 * j * (eLpNorm (Z 0) 2 μ).toReal := by
  rw [Lp.norm_toLp]
  have hbound := eLpNorm_sum_range_lag_sub_le (P := μ) (fun s => (hZ s).aestronglyMeasurable)
    (fun s => le_of_eq ((hident s).eLpNorm_eq 2)) n j
  have htop : (2 : ℝ≥0∞) * j * eLpNorm (Z 0) 2 μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (hZ 0).eLpNorm_lt_top.ne
  calc (eLpNorm (fun ω => ∑ t ∈ Finset.range n, (Z ((t : ℤ) - j) ω - Z (t : ℤ) ω)) 2 μ).toReal
      ≤ (2 * (j : ℝ≥0∞) * eLpNorm (Z 0) 2 μ).toReal := ENNReal.toReal_mono htop hbound
    _ = 2 * j * (eLpNorm (Z 0) 2 μ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; norm_num

/-- **Infinite-filter boundary `L²` bound:** for a causal filter `ψ : ℕ → ℝ` with `∑ⱼ |ψⱼ|·j < ∞`,
the `L²` norm of the boundary term `∑ⱼ ψⱼ • (lag j)` of the linear process is bounded by
`∑ⱼ |ψⱼ|·2jM`, uniformly in `n` — Banach absolute convergence (`norm_tsum_le_tsum_norm`) plus the
per-lag bound. This is the `‖D_n‖₂ ≤ C` of the general (`MA(∞)` / ARMA) sample-mean CLT. -/
theorem norm_tsum_filter_lag_le {Z : ℤ → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ)
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ) {ψ : ℕ → ℝ}
    (hψ : Summable fun j : ℕ => |ψ j| * (2 * j * (eLpNorm (Z 0) 2 μ).toReal)) (n : ℕ) :
    ‖∑' j : ℕ, ψ j • (memLp_lag hZ n j).toLp _‖
      ≤ ∑' j : ℕ, |ψ j| * (2 * j * (eLpNorm (Z 0) 2 μ).toReal) := by
  have hb : ∀ j : ℕ, ‖ψ j • (memLp_lag hZ n j).toLp _‖
      ≤ |ψ j| * (2 * j * (eLpNorm (Z 0) 2 μ).toReal) := by
    intro j
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_toLp_lag_le hZ hident n j) (abs_nonneg _)
  have hsummn : Summable fun j : ℕ => ‖ψ j • (memLp_lag hZ n j).toLp _‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hψ
  calc ‖∑' j : ℕ, ψ j • (memLp_lag hZ n j).toLp _‖
      ≤ ∑' j : ℕ, ‖ψ j • (memLp_lag hZ n j).toLp _‖ := norm_tsum_le_tsum_norm hsummn
    _ ≤ ∑' j : ℕ, |ψ j| * (2 * j * (eLpNorm (Z 0) 2 μ).toReal) := hsummn.tsum_le_tsum hb hψ

end DeepWiki.TimeSeries
