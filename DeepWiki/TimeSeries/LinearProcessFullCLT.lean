import DeepWiki.TimeSeries.GeneralLinearProcessCLT
import DeepWiki.TimeSeries.LinearProcessCLT
import DeepWiki.TimeSeries.DoubleLimitDistribution

/-! # Sample-mean CLT for the causal linear process under `∑ⱼ |ψⱼ| < ∞`
Assembling the full Theorem 7.1.2 (Brockwell–Davis): for a causal linear process
`Xₜ = ∑_{j≥0} ψⱼ Z_{t−j}` over centered iid `L²` noise with only `∑ⱼ |ψⱼ| < ∞`, the sample mean is
asymptotically normal, `√n X̄ₙ ⇒ (∑ψ) Y₀`. The route: finite `MA(m)` truncations converge
(`causalLinearProcess_sampleMean_clt`), their limits converge (scalars `sₘ → ∑ψ`), and the
truncation error is uniformly small in `L²` — `‖√n(X̄ₙ − X̄ₙ^{(m)})‖₂ ≤ σ·∑_{j>m}|ψⱼ| → 0` by iid
orthogonality — so the **double-limit theorem** `tendstoInDistribution_of_eventually_approx` applies. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **iid centered `L²` noise satisfies the white-noise moment condition** `∫ Zₐ·Z_b = σ²·[a=b]`
with `σ² = ∫ Z₀²`: off-diagonal terms vanish by independence (`∫ Zₐ Z_b = μ[Zₐ]·μ[Z_b] = 0`,
centered), diagonal terms are the common second moment (`IdentDistrib`). The hypothesis
`inner_toLpSeq` consumes to make the lagged `L²` vectors orthogonal. -/
theorem integral_mul_eq_iid [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hmem : ∀ t, MemLp (Z t) 2 μ) (hindep : iIndepFun Z μ)
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ) (hcenter : μ[Z 0] = 0) (a b : ℤ) :
    ∫ ω, Z a ω * Z b ω ∂μ = if a = b then (∫ ω, Z 0 ω * Z 0 ω ∂μ) else 0 := by
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl]
    exact ((hident a).comp (show Measurable (fun x : ℝ => x * x) by fun_prop)).integral_eq
  · rw [if_neg hab]
    rw [(hindep.indepFun hab).integral_fun_mul_eq_mul_integral (hmem a).1 (hmem b).1]
    have haz : ∫ ω, Z a ω ∂μ = 0 := (hident a).integral_eq.trans hcenter
    rw [haz, zero_mul]

/-- **Orthogonal-sum norm of `n` lagged noise vectors:** `‖∑_{t<n} Z_{t−j}‖² = n · σ²` in `L²`
(`σ² = ∫ Z₀²`), uniformly in the lag `j` — the `n` distinct lags are pairwise orthogonal
(`inner_toLpSeq` + `integral_mul_eq_iid`), so the Pythagorean identity gives `n` copies of the common
second moment. The `√n·σ` growth that makes the truncation tail negligible. -/
theorem norm_sum_toLpSeq_lag_sq [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hmem : ∀ t, MemLp (Z t) 2 μ) (hindep : iIndepFun Z μ)
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ) (hcenter : μ[Z 0] = 0) (n : ℕ) (j : ℤ) :
    ‖∑ t ∈ Finset.range n, toLpSeq Z hmem ((t : ℤ) - j)‖ ^ 2
      = n * (∫ ω, Z 0 ω * Z 0 ω ∂μ) := by
  have hmom := integral_mul_eq_iid hmem hindep hident hcenter
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  have key : ∀ s ∈ Finset.range n,
      (inner ℝ (toLpSeq Z hmem ((s : ℤ) - j))
          (∑ t ∈ Finset.range n, toLpSeq Z hmem ((t : ℤ) - j)) : ℝ)
        = ∫ ω, Z 0 ω * Z 0 ω ∂μ := by
    intro s hs
    rw [inner_sum, Finset.sum_eq_single s
      (fun t _ hts => by rw [inner_toLpSeq hmem hmom, if_neg (fun h => hts (by omega))])
      (fun hs' => absurd hs hs'), inner_toLpSeq hmem hmom, if_pos rfl]
  rw [Finset.sum_congr rfl key, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **`L²` bound on a windowed causal-linear-process sum:** for absolutely summable filter `φ`,
`‖∑_{t<n} Xₜ‖ ≤ √n · ‖toLpSeq 0‖ · ∑ⱼ |φⱼ|` where `Xₜ = ∑ⱼ φⱼ Z_{t−j}` — interchange the windowed
sum with the filter tsum (`finsetSum_tsum`), Minkowski over the filter (`norm_tsum_le_tsum_norm`), and
the orthogonal `√n·σ` bound on each lagged window (`norm_sum_toLpSeq_lag_sq`). With `φ` the tail
`ψⱼ·1_{j>m}`, the `1/√n`-scaled version is `‖√n(X̄ₙ − X̄ₙ^{(m)})‖₂ ≤ σ·∑_{j>m}|ψⱼ|`. -/
theorem norm_sum_causalLinearProcessLp_le [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hmem : ∀ t, MemLp (Z t) 2 μ) (hindep : iIndepFun Z μ)
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ) (hcenter : μ[Z 0] = 0)
    {φ : ℕ → ℝ} (hφ : Summable fun j => |φ j|)
    (hsum : ∀ t : ℤ, Summable fun j : ℕ => φ j • toLpSeq Z hmem (t - (j : ℤ))) (n : ℕ) :
    ‖∑ t ∈ Finset.range n, causalLinearProcessLp φ Z hmem t‖
      ≤ Real.sqrt n * ‖toLpSeq Z hmem 0‖ * ∑' j : ℕ, |φ j| := by
  have hAnorm : ∀ j : ℤ,
      ‖∑ t ∈ Finset.range n, toLpSeq Z hmem ((t : ℤ) - j)‖
        = Real.sqrt n * ‖toLpSeq Z hmem 0‖ := by
    intro j
    have hsq := norm_sum_toLpSeq_lag_sq hmem hindep hident hcenter n j
    have h0 : ‖toLpSeq Z hmem (0 : ℤ)‖ ^ 2 = ∫ ω, Z 0 ω * Z 0 ω ∂μ := by
      rw [← real_inner_self_eq_norm_sq,
        inner_toLpSeq hmem (integral_mul_eq_iid hmem hindep hident hcenter), if_pos rfl]
    have hnn1 : (0 : ℝ) ≤ ‖∑ t ∈ Finset.range n, toLpSeq Z hmem ((t : ℤ) - j)‖ := norm_nonneg _
    have hnn2 : (0 : ℝ) ≤ Real.sqrt n * ‖toLpSeq Z hmem 0‖ := by positivity
    have hsq2 : ‖∑ t ∈ Finset.range n, toLpSeq Z hmem ((t : ℤ) - j)‖ ^ 2
        = (Real.sqrt n * ‖toLpSeq Z hmem 0‖) ^ 2 := by
      rw [hsq, ← h0, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [← Real.sqrt_sq hnn1, hsq2, Real.sqrt_sq hnn2]
  simp only [causalLinearProcessLp]
  rw [finsetSum_tsum (Finset.range n) (fun t => hsum (t : ℤ))]
  rw [show (fun j : ℕ => ∑ t ∈ Finset.range n, φ j • toLpSeq Z hmem ((t : ℤ) - (j : ℤ)))
        = fun j : ℕ => φ j • ∑ t ∈ Finset.range n, toLpSeq Z hmem ((t : ℤ) - (j : ℤ))
      from funext fun j => (Finset.smul_sum).symm]
  have hsummorm : Summable fun j : ℕ =>
      ‖φ j • ∑ t ∈ Finset.range n, toLpSeq Z hmem ((t : ℤ) - (j : ℤ))‖ := by
    simp only [norm_smul, Real.norm_eq_abs, hAnorm]
    exact hφ.mul_right _
  calc ‖∑' j : ℕ, φ j • ∑ t ∈ Finset.range n, toLpSeq Z hmem ((t : ℤ) - (j : ℤ))‖
      ≤ ∑' j : ℕ, ‖φ j • ∑ t ∈ Finset.range n, toLpSeq Z hmem ((t : ℤ) - (j : ℤ))‖ :=
        norm_tsum_le_tsum_norm hsummorm
    _ = ∑' j : ℕ, |φ j| * (Real.sqrt n * ‖toLpSeq Z hmem 0‖) := by
        refine tsum_congr fun j => ?_; rw [norm_smul, Real.norm_eq_abs, hAnorm]
    _ = Real.sqrt n * ‖toLpSeq Z hmem 0‖ * ∑' j : ℕ, |φ j| := by rw [tsum_mul_right, mul_comm]

/-- **Uniform `L²` bound on the standardized sample mean of a causal linear process:** for `n ≥ 1`
and absolutely summable filter `φ`, `‖√n X̄ₙ‖₂ ≤ ‖toLpSeq 0‖ · ∑ⱼ |φⱼ|`, *independently of `n`* —
the `(√n · n⁻¹)` rescaling exactly cancels the `√n` orthogonal growth of the windowed sum
(`norm_sum_causalLinearProcessLp_le`). Applied to the truncation tail `φ = ψ·1_{j>m}`, this is the
double-limit approximation `h3`. -/
theorem eLpNorm_sqrt_sampleMean_causalLinearProcessLp_le [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hmem : ∀ t, MemLp (Z t) 2 μ) (hindep : iIndepFun Z μ)
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ) (hcenter : μ[Z 0] = 0)
    {φ : ℕ → ℝ} (hφ : Summable fun j => |φ j|)
    (hsum : ∀ t : ℤ, Summable fun j : ℕ => φ j • toLpSeq Z hmem (t - (j : ℤ))) {n : ℕ} (hn : 1 ≤ n) :
    eLpNorm (fun ω => Real.sqrt n * sampleMean n
        fun t => (causalLinearProcessLp φ Z hmem (t : ℤ) : Ω → ℝ) ω) 2 μ
      ≤ ENNReal.ofReal (‖toLpSeq Z hmem 0‖ * ∑' j : ℕ, |φ j|) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hae : (fun ω => Real.sqrt n * sampleMean n
        fun t => (causalLinearProcessLp φ Z hmem (t : ℤ) : Ω → ℝ) ω)
      =ᵐ[μ] (Real.sqrt n * (n : ℝ)⁻¹)
        • ((∑ t ∈ Finset.range n, causalLinearProcessLp φ Z hmem (t : ℤ) : Lp ℝ 2 μ) : Ω → ℝ) := by
    filter_upwards [Lp.coeFn_finsetSum (Finset.range n)
      (fun t => causalLinearProcessLp φ Z hmem (t : ℤ))] with ω e1
    simp only [Pi.smul_apply, smul_eq_mul, sampleMean, e1, Finset.sum_apply]
    ring
  rw [eLpNorm_congr_ae hae, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity), eLpNorm_coeFn,
    ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (Real.sqrt n * (n : ℝ)⁻¹)
        * ‖∑ t ∈ Finset.range n, causalLinearProcessLp φ Z hmem (t : ℤ)‖
      ≤ (Real.sqrt n * (n : ℝ)⁻¹)
        * (Real.sqrt n * ‖toLpSeq Z hmem 0‖ * ∑' j : ℕ, |φ j|) := by
        gcongr
        exact norm_sum_causalLinearProcessLp_le hmem hindep hident hcenter hφ hsum n
    _ = ‖toLpSeq Z hmem 0‖ * ∑' j : ℕ, |φ j| := by
        rw [show (Real.sqrt n * (n : ℝ)⁻¹)
              * (Real.sqrt n * ‖toLpSeq Z hmem 0‖ * ∑' j : ℕ, |φ j|)
            = (Real.sqrt n * Real.sqrt n)
              * ((n : ℝ)⁻¹ * (‖toLpSeq Z hmem 0‖ * ∑' j : ℕ, |φ j|)) from by ring,
          Real.mul_self_sqrt hn'.le, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]

/-- **The causal linear process is `ℝ`-linear in its filter (difference form):** for summable
filters, `causalLinearProcessLp φ₁ − causalLinearProcessLp φ₂ = causalLinearProcessLp (φ₁ − φ₂)`.
With `φ₂ = ψ·1_{j≤m}` the difference of the full and truncated processes is the tail process. -/
theorem causalLinearProcessLp_sub {Z : ℤ → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ) {φ₁ φ₂ : ℕ → ℝ}
    (hsum₁ : ∀ t : ℤ, Summable fun j : ℕ => φ₁ j • toLpSeq Z hZ (t - (j : ℤ)))
    (hsum₂ : ∀ t : ℤ, Summable fun j : ℕ => φ₂ j • toLpSeq Z hZ (t - (j : ℤ))) (t : ℤ) :
    causalLinearProcessLp φ₁ Z hZ t - causalLinearProcessLp φ₂ Z hZ t
      = causalLinearProcessLp (fun j => φ₁ j - φ₂ j) Z hZ t := by
  simp only [causalLinearProcessLp]
  rw [← Summable.tsum_sub (hsum₁ t) (hsum₂ t)]
  exact tsum_congr fun j => (sub_smul _ _ _).symm

/-- **The summable tail vanishes:** for `∑ⱼ |ψⱼ| < ∞`, the tail mass `∑_{j>m} |ψⱼ| → 0` as
`m → ∞` (the total minus the partial sum). The eventually-in-`m` ingredient that makes the
double-limit approximation `h3` hold. -/
theorem tendsto_tsum_ite_lt_zero {ψ : ℕ → ℝ} (hψ : Summable fun j => |ψ j|) :
    Tendsto (fun m : ℕ => ∑' j : ℕ, if m < j then |ψ j| else 0) atTop (𝓝 0) := by
  have hsumA : ∀ m : ℕ, Summable fun j : ℕ => if m < j then |ψ j| else 0 := fun m =>
    Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity)
      (fun j => by split_ifs with h; exacts [le_refl _, abs_nonneg _]) hψ
  have hsumB : ∀ m : ℕ, Summable fun j : ℕ => if j ≤ m then |ψ j| else 0 := fun m =>
    summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun j hj => by
      simp only [Finset.mem_range, not_lt] at hj; rw [if_neg (by omega)]
  have hadd : ∀ m : ℕ, (∑' j : ℕ, if m < j then |ψ j| else 0)
      = (∑' j : ℕ, |ψ j|) - ∑ j ∈ Finset.range (m + 1), |ψ j| := by
    intro m
    have h2 : (∑' j : ℕ, if j ≤ m then |ψ j| else 0) = ∑ j ∈ Finset.range (m + 1), |ψ j| := by
      rw [tsum_eq_sum (s := Finset.range (m + 1)) fun j hj => by
        simp only [Finset.mem_range, not_lt] at hj; rw [if_neg (by omega)]]
      exact Finset.sum_congr rfl fun j hj => by
        simp only [Finset.mem_range] at hj; rw [if_pos (by omega)]
    have h1 : (∑' j : ℕ, if m < j then |ψ j| else 0)
        + (∑' j : ℕ, if j ≤ m then |ψ j| else 0) = ∑' j : ℕ, |ψ j| := by
      rw [← Summable.tsum_add (hsumA m) (hsumB m)]
      exact tsum_congr fun j => by
        rcases lt_or_ge m j with h | h
        · rw [if_pos h, if_neg (by omega : ¬ j ≤ m)]; ring
        · rw [if_neg (by omega : ¬ m < j), if_pos (by omega : j ≤ m)]; ring
    rw [eq_sub_iff_add_eq, ← h2]; exact h1
  rw [show (fun m : ℕ => ∑' j : ℕ, if m < j then |ψ j| else 0)
        = fun m : ℕ => (∑' j : ℕ, |ψ j|) - ∑ j ∈ Finset.range (m + 1), |ψ j| from funext hadd]
  have hps : Tendsto (fun m : ℕ => ∑ j ∈ Finset.range (m + 1), |ψ j|) atTop
      (𝓝 (∑' j : ℕ, |ψ j|)) := hψ.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  rw [show (0 : ℝ) = (∑' j : ℕ, |ψ j|) - ∑' j : ℕ, |ψ j| from (sub_self _).symm]
  exact tendsto_const_nhds.sub hps

/-- **`L²` bound on the truncation error of the standardized sample mean:** the difference between
the full standardized sample mean `√n X̄ₙ` and its finite-`MA(m)` truncation `√n X̄ₙ^{(m)}` has
`L²` norm `≤ ‖toLpSeq 0‖ · ∑_{j>m} |ψⱼ|`, *uniformly in `n ≥ 1`* — the difference is the tail
process `Xₜ − Xₜ^{(m)} = ∑_{j>m} ψⱼ Z_{t−j}` (`causalLinearProcessLp_sub`), bounded by
`eLpNorm_sqrt_sampleMean_causalLinearProcessLp_le`. The eventually-vanishing approximation `h3`. -/
theorem eLpNorm_sqrt_sampleMean_truncation_sub_le [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hZ : ∀ t, MemLp (Z t) 2 μ) (hindep : iIndepFun Z μ)
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ) (hcenter : μ[Z 0] = 0) {ψ : ℕ → ℝ}
    (hψ : Summable fun j => |ψ j|)
    (hsum : ∀ t : ℤ, Summable fun j : ℕ => ψ j • toLpSeq Z hZ (t - (j : ℤ))) (m : ℕ) {n : ℕ}
    (hn : 1 ≤ n) :
    eLpNorm ((fun ω => Real.sqrt n * sampleMean n fun t =>
          (causalLinearProcessLp ψ Z hZ (t : ℤ) : Ω → ℝ) ω)
        - fun ω => Real.sqrt n * sampleMean n fun t =>
          (causalLinearProcessLp (fun j => if j ≤ m then ψ j else 0) Z hZ (t : ℤ) : Ω → ℝ) ω) 2 μ
      ≤ ENNReal.ofReal (‖toLpSeq Z hZ 0‖ * ∑' j : ℕ, if m < j then |ψ j| else 0) := by
  set ψm : ℕ → ℝ := fun j => if j ≤ m then ψ j else 0 with hψm
  set ψt : ℕ → ℝ := fun j => if m < j then ψ j else 0 with hψt
  have hsumm : ∀ t : ℤ, Summable fun j : ℕ => ψm j • toLpSeq Z hZ (t - (j : ℤ)) := fun t =>
    summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun j hj => by
      simp only [Finset.mem_range, not_lt] at hj
      simp only [hψm, if_neg (by omega : ¬ j ≤ m), zero_smul]
  have hsumt : ∀ t : ℤ, Summable fun j : ℕ => ψt j • toLpSeq Z hZ (t - (j : ℤ)) := fun t =>
    ((hsum t).sub (hsumm t)).congr fun j => by
      rw [← sub_smul]; congr 1; simp only [hψt, hψm]
      rcases le_or_gt j m with h | h
      · rw [if_pos h, if_neg (by omega : ¬ m < j), sub_self]
      · rw [if_neg (by omega : ¬ j ≤ m), if_pos h, sub_zero]
  have hψt_abs : Summable fun j => |ψt j| := Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun j => by simp only [hψt]; split_ifs with h <;> simp [abs_nonneg]) hψ
  have hsub_eq : ∀ t : ℤ, causalLinearProcessLp ψ Z hZ t - causalLinearProcessLp ψm Z hZ t
      = causalLinearProcessLp ψt Z hZ t := fun t => by
    rw [causalLinearProcessLp_sub hZ hsum hsumm t]
    congr 1; funext j; simp only [hψt, hψm]
    rcases le_or_gt j m with h | h
    · rw [if_pos h, if_neg (by omega : ¬ m < j), sub_self]
    · rw [if_neg (by omega : ¬ j ≤ m), if_pos h, sub_zero]
  have hpt : ∀ t : ℤ, (fun ω => (causalLinearProcessLp ψ Z hZ t : Ω → ℝ) ω
        - (causalLinearProcessLp ψm Z hZ t : Ω → ℝ) ω)
      =ᵐ[μ] fun ω => (causalLinearProcessLp ψt Z hZ t : Ω → ℝ) ω := fun t => by
    rw [← hsub_eq t]; exact (Lp.coeFn_sub _ _).symm
  have key : ((fun ω => Real.sqrt n * sampleMean n fun t =>
          (causalLinearProcessLp ψ Z hZ (t : ℤ) : Ω → ℝ) ω)
        - fun ω => Real.sqrt n * sampleMean n fun t =>
          (causalLinearProcessLp ψm Z hZ (t : ℤ) : Ω → ℝ) ω)
      =ᵐ[μ] fun ω => Real.sqrt n * sampleMean n fun t =>
          (causalLinearProcessLp ψt Z hZ (t : ℤ) : Ω → ℝ) ω := by
    have hae := sum_eventuallyEq (Finset.range n) (fun t (_ : t ∈ Finset.range n) => hpt (t : ℤ))
    filter_upwards [hae] with ω hω
    simp only [Pi.sub_apply, sampleMean]
    rw [Finset.sum_sub_distrib] at hω
    rw [← hω]; ring
  rw [eLpNorm_congr_ae key]
  refine le_trans (eLpNorm_sqrt_sampleMean_causalLinearProcessLp_le hZ hindep hident hcenter
    hψt_abs hsumt hn) (le_of_eq ?_)
  congr 2
  exact tsum_congr fun j => by simp only [hψt]; split_ifs <;> simp [abs_zero]

end DeepWiki.TimeSeries
