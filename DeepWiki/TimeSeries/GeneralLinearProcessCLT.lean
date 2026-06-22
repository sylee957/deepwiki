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

/-- `MemLp.toLp` commutes with finite sums: `∑ᵢ (fᵢ).toLp = (∑ᵢ fᵢ).toLp`. -/
theorem toLp_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ) :
    ∑ i ∈ s, (hf i).toLp (f i)
      = (memLp_finsetSum s (fun i _ => hf i)).toLp (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact (MemLp.toLp_zero _).symm
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (by filter_upwards with ω; simp [Finset.sum_insert ha])

/-- The `Lp` windowed lag-`j` sum over the embedding equals the embedding of the raw lag-`j` sum:
`∑_{t<n} (Z_{t−j} − Z_t)` as a single `Lp` element, identifying the two ways of forming it. -/
theorem lag_toLpSeq_eq {Z : ℤ → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ) (n j : ℕ) :
    ∑ t ∈ Finset.range n, (toLpSeq Z hZ ((t : ℤ) - j) - toLpSeq Z hZ (t : ℤ))
      = (memLp_lag hZ n j).toLp _ := by
  have hterm : ∀ t : ℕ, toLpSeq Z hZ ((t : ℤ) - j) - toLpSeq Z hZ (t : ℤ)
      = ((hZ ((t : ℤ) - j)).sub (hZ (t : ℤ))).toLp (Z ((t : ℤ) - j) - Z (t : ℤ)) := by
    intro t; simp only [toLpSeq]; rw [← MemLp.toLp_sub]
  simp_rw [hterm]
  exact toLp_finsetSum (Finset.range n) (fun t => (hZ ((t : ℤ) - j)).sub (hZ (t : ℤ)))

/-- A finite sum commutes with an infinite sum (`tsum`) in a complete topological additive group:
`∑ᵢ∈s ∑'ₖ fᵢ k = ∑'ₖ ∑ᵢ∈s fᵢ k`, when each `fᵢ` is summable. -/
theorem finsetSum_tsum {ι κ M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [T2Space M] (s : Finset ι) {f : ι → κ → M}
    (hf : ∀ i, Summable (f i)) :
    ∑ i ∈ s, ∑' k, f i k = ∑' k, ∑ i ∈ s, f i k := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, ← Summable.tsum_add (hf a) (summable_sum fun i _ => hf i)]
    exact tsum_congr fun k => by rw [Finset.sum_insert ha]

/-- **Structural identity `D_n = ∑ⱼ ψⱼ•(lag j)`:** the windowed sample sum of the causal linear
process `Xₜ = ∑ⱼ ψⱼ Z_{t−j}` minus `(∑ψ)` times the windowed noise sum equals the filter-weighted
lag-difference. The bridge from the actual linear process to the boundary-bounded element. -/
theorem linearProcess_sampleSum_sub {Z : ℤ → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ) {ψ : ℕ → ℝ}
    (hψ : Summable ψ) (hsum : ∀ t : ℤ, Summable fun j : ℕ => ψ j • toLpSeq Z hZ (t - (j : ℤ)))
    (n : ℕ) :
    (∑ t ∈ Finset.range n, ∑' j : ℕ, ψ j • toLpSeq Z hZ ((t : ℤ) - (j : ℤ)))
        - (∑' j : ℕ, ψ j) • ∑ t ∈ Finset.range n, toLpSeq Z hZ (t : ℤ)
      = ∑' j : ℕ, ψ j • (memLp_lag hZ n j).toLp _ := by
  rw [finsetSum_tsum (Finset.range n) (fun t => hsum (t : ℤ)), ← hψ.tsum_smul_const,
    ← Summable.tsum_sub (summable_sum (s := Finset.range n) fun t _ => hsum (t : ℤ))
      (hψ.smul_const _)]
  refine tsum_congr fun j => ?_
  rw [← Finset.smul_sum, ← smul_sub, ← Finset.sum_sub_distrib, lag_toLpSeq_eq]

end DeepWiki.TimeSeries
