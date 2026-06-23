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

/-- **The causal linear process `Xₜ = ∑_{j≥0} ψⱼ Z_{t−j}`** as an `L²(μ)` element — the `MA(∞)`
representation driven by a causal filter `ψ : ℕ → ℝ` over the `L²`-embedded noise `toLpSeq Z`. -/
noncomputable def causalLinearProcessLp (ψ : ℕ → ℝ) (Z : ℤ → Ω → ℝ) (hZ : ∀ t, MemLp (Z t) 2 μ)
    (t : ℤ) : Lp ℝ 2 μ :=
  ∑' j : ℕ, ψ j • toLpSeq Z hZ (t - (j : ℤ))

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

/-- **`‖D_n‖ ≤ C` for the causal linear process:** the `L²` norm of the windowed sample-sum minus
its `(∑ψ)`-scaled noise part is bounded by `∑ⱼ |ψⱼ|·2jM`, uniformly in `n` — combining the
structural identity `linearProcess_sampleSum_sub` with the boundary bound `norm_tsum_filter_lag_le`. -/
theorem norm_sampleSum_sub_le {Z : ℤ → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ) {ψ : ℕ → ℝ}
    (hψ : Summable ψ) (hsum : ∀ t : ℤ, Summable fun j : ℕ => ψ j • toLpSeq Z hZ (t - (j : ℤ)))
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ)
    (hψj : Summable fun j : ℕ => |ψ j| * (2 * j * (eLpNorm (Z 0) 2 μ).toReal)) (n : ℕ) :
    ‖(∑ t ∈ Finset.range n, ∑' j : ℕ, ψ j • toLpSeq Z hZ ((t : ℤ) - (j : ℤ)))
          - (∑' j : ℕ, ψ j) • ∑ t ∈ Finset.range n, toLpSeq Z hZ (t : ℤ)‖
      ≤ ∑' j : ℕ, |ψ j| * (2 * j * (eLpNorm (Z 0) 2 μ).toReal) := by
  rw [linearProcess_sampleSum_sub hZ hψ hsum n]
  exact norm_tsum_filter_lag_le hZ hident hψj n

/-- The `eLpNorm` of an `Lp` element's coercion is its (extended) norm: `eLpNorm ⇑W = ‖W‖ₑ`. -/
theorem eLpNorm_coeFn {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} (W : Lp E p μ) :
    eLpNorm (⇑W) p μ = ‖W‖ₑ := by
  rw [← Lp.enorm_toLp (Lp.memLp W), Lp.toLp_coeFn]

/-- Finite sums respect almost-everywhere equality: if `fᵢ =ᵐ gᵢ` for each `i ∈ s`, then the
pointwise finite sums are a.e. equal. -/
theorem sum_eventuallyEq {ι : Type*} (s : Finset ι) {f g : ι → Ω → ℝ}
    (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (fun ω => ∑ i ∈ s, f i ω) =ᵐ[μ] fun ω => ∑ i ∈ s, g i ω := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **`L²`-negligibility for the general linear process:** the difference between the rescaled
sample mean of the causal linear process and the `(∑ψ)`-scaled rescaled noise sum tends to `0` in
`L²`, when `∑ⱼ |ψⱼ|·j < ∞`. From the structural identity (`‖D_n‖ ≤ C` uniformly) and `√n·n⁻¹ → 0`. -/
theorem tendsto_eLpNorm_linearProcess_sub {Z : ℤ → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ) {ψ : ℕ → ℝ}
    (hψ : Summable ψ) (hsum : ∀ t : ℤ, Summable fun j : ℕ => ψ j • toLpSeq Z hZ (t - (j : ℤ)))
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ)
    (hψj : Summable fun j : ℕ => |ψ j| * (2 * j * (eLpNorm (Z 0) 2 μ).toReal)) :
    Tendsto (fun n : ℕ => eLpNorm
      ((fun ω => Real.sqrt n * sampleMean n fun t => (causalLinearProcessLp ψ Z hZ (t : ℤ) : Ω → ℝ) ω)
        - fun ω => (∑' j : ℕ, ψ j)
            * (Real.sqrt n * sampleMean n fun t => (toLpSeq Z hZ (t : ℤ) : Ω → ℝ) ω)) 2 μ)
      atTop (𝓝 0) := by
  set C := ∑' j : ℕ, |ψ j| * (2 * j * (eLpNorm (Z 0) 2 μ).toReal) with hC
  have hbound : ∀ n : ℕ, eLpNorm
      ((fun ω => Real.sqrt n * sampleMean n fun t => (causalLinearProcessLp ψ Z hZ (t : ℤ) : Ω → ℝ) ω)
        - fun ω => (∑' j : ℕ, ψ j)
            * (Real.sqrt n * sampleMean n fun t => (toLpSeq Z hZ (t : ℤ) : Ω → ℝ) ω)) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt n * (n : ℝ)⁻¹) * ENNReal.ofReal C := by
    intro n
    have hae : ((fun ω => Real.sqrt n
            * sampleMean n fun t => (causalLinearProcessLp ψ Z hZ (t : ℤ) : Ω → ℝ) ω)
          - fun ω => (∑' j : ℕ, ψ j)
              * (Real.sqrt n * sampleMean n fun t => (toLpSeq Z hZ (t : ℤ) : Ω → ℝ) ω))
        =ᵐ[μ] (Real.sqrt n * (n : ℝ)⁻¹)
          • ((∑ t ∈ Finset.range n, causalLinearProcessLp ψ Z hZ (t : ℤ)
              - (∑' j : ℕ, ψ j) • ∑ t ∈ Finset.range n, toLpSeq Z hZ (t : ℤ) : Lp ℝ 2 μ) : Ω → ℝ) := by
      filter_upwards [Lp.coeFn_finsetSum (Finset.range n)
          (fun t => causalLinearProcessLp ψ Z hZ (t : ℤ)),
        Lp.coeFn_finsetSum (Finset.range n) (fun t => toLpSeq Z hZ (t : ℤ)),
        Lp.coeFn_sub (∑ t ∈ Finset.range n, causalLinearProcessLp ψ Z hZ (t : ℤ))
          ((∑' j : ℕ, ψ j) • ∑ t ∈ Finset.range n, toLpSeq Z hZ (t : ℤ)),
        Lp.coeFn_smul (∑' j : ℕ, ψ j) (∑ t ∈ Finset.range n, toLpSeq Z hZ (t : ℤ))]
        with ω e1 e2 e3 e4
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sampleMean, e3, e4, e1, e2,
        Finset.sum_apply]
      ring
    rw [eLpNorm_congr_ae hae, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity), eLpNorm_coeFn]
    gcongr
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [causalLinearProcessLp]
    exact norm_sampleSum_sub_le hZ hψ hsum hident hψj n
  have hroot : Tendsto (fun n : ℕ => Real.sqrt n * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    refine (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.sqrt n ≠ 0 := by positivity
    have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn'.le
    simp only [Function.comp_apply]
    rw [show (n : ℝ)⁻¹ = (Real.sqrt n * Real.sqrt n)⁻¹ from by rw [hsq], mul_inv, ← mul_assoc,
      mul_inv_cancel₀ hs, one_mul]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt n * (n : ℝ)⁻¹) * ENNReal.ofReal C)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt n * (n : ℝ)⁻¹)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]; exact (ENNReal.continuous_ofReal.tendsto 0).comp hroot
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hbound

end DeepWiki.TimeSeries
