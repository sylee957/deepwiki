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

/-- **Lévy–Prokhorov bound on the truncation error of the standardized sample mean:** for `n ≥ 1`,
if the tail mass is small enough (`‖toLpSeq 0‖ · ∑_{j>m} |ψⱼ| ≤ δ^{3/2}`), the laws of `√n X̄ₙ` and
its `MA(m)` truncation are within `δ` in Lévy–Prokhorov distance. Chebyshev
(`meas_ge_le_mul_pow_eLpNorm_enorm`) on the `L²` truncation bound, fed into the in-measure ⟹
Lévy–Prokhorov estimate `levyProkhorovEDist_map_le`. The per-`(m,n)` ingredient of the double-limit
approximation `h3`. -/
theorem levyProkhorovDist_truncation_le [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hZ : ∀ t, MemLp (Z t) 2 μ) (hindep : iIndepFun Z μ)
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ) (hcenter : μ[Z 0] = 0) {ψ : ℕ → ℝ}
    (hψ : Summable fun j => |ψ j|)
    (hsum : ∀ t : ℤ, Summable fun j : ℕ => ψ j • toLpSeq Z hZ (t - (j : ℤ))) (m : ℕ) {n : ℕ}
    (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    (hm : ‖toLpSeq Z hZ 0‖ * ∑' j : ℕ, (if m < j then |ψ j| else 0) ≤ δ * Real.sqrt δ) :
    levyProkhorovDist
        (μ.map fun ω => Real.sqrt n * sampleMean n fun t =>
          (causalLinearProcessLp ψ Z hZ (t : ℤ) : Ω → ℝ) ω)
        (μ.map fun ω => Real.sqrt n * sampleMean n fun t =>
          (causalLinearProcessLp (fun j => if j ≤ m then ψ j else 0) Z hZ (t : ℤ) : Ω → ℝ) ω)
      ≤ δ := by
  set B : ℝ := ‖toLpSeq Z hZ 0‖ * ∑' j : ℕ, (if m < j then |ψ j| else 0) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set Xf : Ω → ℝ := fun ω => Real.sqrt n * sampleMean n fun t =>
    (causalLinearProcessLp ψ Z hZ (t : ℤ) : Ω → ℝ) ω with hXf
  set Xf' : Ω → ℝ := fun ω => Real.sqrt n * sampleMean n fun t =>
    (causalLinearProcessLp (fun j => if j ≤ m then ψ j else 0) Z hZ (t : ℤ) : Ω → ℝ) ω with hXf'
  have hmeas : ∀ φ : ℕ → ℝ, AEStronglyMeasurable (fun ω => Real.sqrt n * sampleMean n fun t =>
      (causalLinearProcessLp φ Z hZ (t : ℤ) : Ω → ℝ) ω) μ := fun φ => by
    simp only [sampleMean]
    exact ((Finset.aestronglyMeasurable_fun_sum _ fun t _ =>
      Lp.aestronglyMeasurable _).const_mul _).const_mul _
  have heLp : eLpNorm (Xf - Xf') 2 μ ≤ ENNReal.ofReal B :=
    eLpNorm_sqrt_sampleMean_truncation_sub_le hZ hindep hident hcenter hψ hsum m hn
  have hcheb : μ {ω | δ ≤ dist (Xf ω) (Xf' ω)} ≤ ENNReal.ofReal δ := by
    have hset : {ω | δ ≤ dist (Xf ω) (Xf' ω)} = {ω | ENNReal.ofReal δ ≤ ‖(Xf - Xf') ω‖ₑ} := by
      ext ω
      simp only [Set.mem_setOf_eq, Pi.sub_apply, Real.dist_eq, ← Real.norm_eq_abs, ← ofReal_norm]
      exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).symm
    rw [hset]
    refine le_trans (meas_ge_le_mul_pow_eLpNorm_enorm μ two_ne_zero ENNReal.ofNat_ne_top
      ((hmeas _).sub (hmeas _)) (ENNReal.ofReal_pos.mpr hδ).ne'
      (fun h => absurd h ENNReal.ofReal_ne_top)) ?_
    rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.rpow_natCast]
    calc (ENNReal.ofReal δ)⁻¹ ^ 2 * eLpNorm (Xf - Xf') 2 μ ^ 2
        ≤ (ENNReal.ofReal δ)⁻¹ ^ 2 * ENNReal.ofReal B ^ 2 := by gcongr
      _ = ENNReal.ofReal (B ^ 2 / δ ^ 2) := by
          rw [← ENNReal.ofReal_inv_of_pos hδ, ← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_pow hB0, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
      _ ≤ ENNReal.ofReal δ := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_iff₀ (by positivity)]
          have h1 : B ^ 2 ≤ (δ * Real.sqrt δ) ^ 2 := pow_le_pow_left₀ hB0 hm 2
          have h2 : (δ * Real.sqrt δ) ^ 2 = δ * δ ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hδ.le]; ring
          linarith [h1, h2]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (le_trans (levyProkhorovEDist_map_le Xf Xf' (hmeas _).aemeasurable (hmeas _).aemeasurable hδ)
      (sup_le le_rfl hcheb))).trans_eq (ENNReal.toReal_ofReal hδ.le)

/-- **Central limit theorem for the sample mean of a causal linear process (full Theorem 7.1.2,
Brockwell–Davis), under the weak hypothesis `∑ⱼ |ψⱼ| < ∞`:** for `Xₜ = ∑_{j≥0} ψⱼ Z_{t−j}` over
centered iid `L²` noise, the standardized sample mean converges in distribution to
`(∑ψ) Y₀ = N(0, (∑ψ)² σ²)`. The finite-`MA(m)` truncations converge
(`causalLinearProcess_sampleMean_clt`), their Gaussian limits converge as the partial sums
`∑_{j≤m} ψⱼ → ∑ψ`, and the truncation error vanishes uniformly in `n`
(`levyProkhorovDist_truncation_le`); the **double-limit theorem**
`tendstoInDistribution_of_eventually_approx` ties them together. This removes the `∑ⱼ |ψⱼ|·j < ∞`
strengthening required by `causalLinearProcess_sampleMean_clt`. -/
theorem causalLinearProcess_sampleMean_clt_of_summable [IsProbabilityMeasure μ] {Ω' : Type*}
    [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : ℤ → Ω → ℝ} {Y₀ : Ω' → ℝ}
    (hZ : ∀ t, MemLp (Z t) 2 μ) {ψ : ℕ → ℝ} (hψ : Summable fun j => |ψ j|)
    (hsum : ∀ t : ℤ, Summable fun j : ℕ => ψ j • toLpSeq Z hZ (t - (j : ℤ)))
    (hindep : iIndepFun Z μ) (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ) (hcenter : μ[Z 0] = 0)
    (hY₀ : HasLaw Y₀ (gaussianReal 0 Var[Z 0; μ].toNNReal) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n * sampleMean n fun t =>
        (causalLinearProcessLp ψ Z hZ (t : ℤ) : Ω → ℝ) ω)
      atTop ((∑' j : ℕ, ψ j) • Y₀) (fun _ => μ) μ' := by
  have hψ' : Summable ψ := summable_abs_iff.mp hψ
  have hY₀meas : AEMeasurable Y₀ μ' := hY₀.aemeasurable
  refine tendstoInDistribution_of_eventually_approx
    (Y := fun (n : ℕ) ω => Real.sqrt n * sampleMean n fun t =>
      (causalLinearProcessLp ψ Z hZ (t : ℤ) : Ω → ℝ) ω)
    (Y' := fun (m n : ℕ) ω => Real.sqrt n * sampleMean n fun t =>
      (causalLinearProcessLp (fun j => if j ≤ m then ψ j else 0) Z hZ (t : ℤ) : Ω → ℝ) ω)
    (W := fun m => (∑' j : ℕ, if j ≤ m then ψ j else 0) • Y₀) (Z := (∑' j : ℕ, ψ j) • Y₀)
    (fun n => ((Finset.aestronglyMeasurable_fun_sum _ fun t _ =>
      Lp.aestronglyMeasurable _).const_mul _).const_mul _ |>.aemeasurable)
    (hY₀meas.const_smul _) (fun m => ?_) ?_ ?_
  · -- h1: each truncation's CLT
    have hsummψm : ∀ t : ℤ, Summable fun j : ℕ =>
        (if j ≤ m then ψ j else 0) • toLpSeq Z hZ (t - (j : ℤ)) := fun t =>
      summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun j hj => by
        simp only [Finset.mem_range, not_lt] at hj; rw [if_neg (by omega), zero_smul]
    exact causalLinearProcess_sampleMean_clt hZ
      (summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun j hj => by
        simp only [Finset.mem_range, not_lt] at hj; rw [if_neg (by omega)])
      hsummψm hindep hident hcenter hY₀
      (summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun j hj => by
        simp only [Finset.mem_range, not_lt] at hj; rw [if_neg (by omega)]; simp)
  · -- h2: Wₘ ⇒ Z as the partial sums converge
    refine tendstoInDistribution_of_ae_tendsto (fun m => hY₀meas.const_smul _) (hY₀meas.const_smul _)
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    refine Filter.Tendsto.mul_const _ ?_
    have hps : Tendsto (fun m : ℕ => ∑ j ∈ Finset.range (m + 1), ψ j) atTop (𝓝 (∑' j : ℕ, ψ j)) :=
      hψ'.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine hps.congr fun m => ?_
    rw [tsum_eq_sum (s := Finset.range (m + 1)) fun j hj => by
      simp only [Finset.mem_range, not_lt] at hj; rw [if_neg (by omega)]]
    exact Finset.sum_congr rfl fun j hj => by simp only [Finset.mem_range] at hj; rw [if_pos (by omega)]
  · -- h3: eventually-in-m, uniform-in-n Lévy–Prokhorov closeness
    intro δ hδ
    have hBtend : Tendsto (fun m : ℕ => ‖toLpSeq Z hZ 0‖ * ∑' j : ℕ, if m < j then |ψ j| else 0)
        atTop (𝓝 0) := by
      have h := (tendsto_tsum_ite_lt_zero hψ).const_mul (‖toLpSeq Z hZ 0‖)
      rwa [mul_zero] at h
    filter_upwards [hBtend.eventually_le_const (show (0 : ℝ) < δ * Real.sqrt δ by positivity)]
      with m hm n
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0; simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul]
      rw [levyProkhorovDist_self]; exact hδ.le
    · exact levyProkhorovDist_truncation_le hZ hindep hident hcenter hψ hsum m hn hδ hm

/-- **Central limit theorem for the sample mean of an AR(1) process**: the causal `AR(1)` process
`Xₜ = ∑_{j≥0} φʲ Z_{t−j}` (`|φ| < 1`) over centered iid `L²` noise has an asymptotically normal
sample mean, `√n X̄ₙ ⇒ (1 − φ)⁻¹ Y₀ = N(0, σ²/(1 − φ)²)`. A concrete instance of the full Theorem
7.1.2 (`causalLinearProcess_sampleMean_clt_of_summable`) with the geometric filter `ψⱼ = φʲ`, whose
absolute summability is the geometric series. -/
theorem ar1_sampleMean_clt [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : ℤ → Ω → ℝ} {Y₀ : Ω' → ℝ} {φ : ℝ} (hφ : |φ| < 1)
    (hZ : ∀ t, MemLp (Z t) 2 μ) (hindep : iIndepFun Z μ) (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ)
    (hcenter : μ[Z 0] = 0) (hY₀ : HasLaw Y₀ (gaussianReal 0 Var[Z 0; μ].toNNReal) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n * sampleMean n fun t =>
        (causalLinearProcessLp (fun j => φ ^ j) Z hZ (t : ℤ) : Ω → ℝ) ω)
      atTop ((1 - φ)⁻¹ • Y₀) (fun _ => μ) μ' := by
  have hgeom : Summable fun j : ℕ => |φ| ^ j := summable_geometric_of_lt_one (abs_nonneg φ) hφ
  have hψ : Summable fun j : ℕ => |φ ^ j| := by simpa only [abs_pow] using hgeom
  have hsum : ∀ t : ℤ, Summable fun j : ℕ => (φ ^ j) • toLpSeq Z hZ (t - (j : ℤ)) := fun t => by
    refine Summable.of_norm ?_
    have hb : ∀ j : ℕ, ‖(φ ^ j) • toLpSeq Z hZ (t - (j : ℤ))‖
        = |φ| ^ j * (eLpNorm (Z 0) 2 μ).toReal := fun j => by
      simp only [toLpSeq, norm_smul, Real.norm_eq_abs, abs_pow]
      rw [Lp.norm_toLp, (hident (t - (j : ℤ))).eLpNorm_eq 2]
    simp only [hb]
    exact hgeom.mul_right _
  rw [show ((1 - φ)⁻¹ : ℝ) = ∑' j : ℕ, φ ^ j from
    (tsum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])).symm]
  exact causalLinearProcess_sampleMean_clt_of_summable hZ hψ hsum hindep hident hcenter hY₀

/-- **Weak law of large numbers for the causal linear process** (Brockwell–Davis Proposition 6.3.2):
for `Xₜ = ∑_{j≥0} ψⱼ Z_{t−j}` over centered iid `L²` noise with `∑ⱼ |ψⱼ| < ∞`, the sample mean
converges to `0` in probability, `X̄ₙ →ᵖ 0`. From the `L²` bound `‖√n X̄ₙ‖₂ ≤ C`
(`eLpNorm_sqrt_sampleMean_causalLinearProcessLp_le`): `‖X̄ₙ‖₂ ≤ C/√n → 0`, and `L²` convergence
implies convergence in measure. -/
theorem causalLinearProcess_sampleMean_wlln [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hmem : ∀ t, MemLp (Z t) 2 μ) (hindep : iIndepFun Z μ)
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) μ μ) (hcenter : μ[Z 0] = 0)
    {φ : ℕ → ℝ} (hφ : Summable fun j => |φ j|)
    (hsum : ∀ t : ℤ, Summable fun j : ℕ => φ j • toLpSeq Z hmem (t - (j : ℤ))) :
    TendstoInMeasure μ (fun (n : ℕ) ω => sampleMean n
      fun t => (causalLinearProcessLp φ Z hmem (t : ℤ) : Ω → ℝ) ω) atTop (fun _ => (0 : ℝ)) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun ω => sampleMean n
      fun t => (causalLinearProcessLp φ Z hmem (t : ℤ) : Ω → ℝ) ω) μ := fun n => by
    simp only [sampleMean]
    exact (Finset.aestronglyMeasurable_fun_sum _ fun t _ => Lp.aestronglyMeasurable _).const_mul _
  refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hmeas
    aestronglyMeasurable_const ?_
  have hsqrt : Tendsto (fun n : ℕ => ENNReal.ofReal (√(n : ℝ))) atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun n : ℕ => ENNReal.ofReal (‖toLpSeq Z hmem 0‖ * ∑' j : ℕ, |φ j|)
      * (ENNReal.ofReal (√(n : ℝ)))⁻¹) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (ENNReal.ofReal (√(n : ℝ)))⁻¹) atTop (𝓝 0) :=
      ENNReal.inv_top ▸ tendsto_inv_iff.mpr hsqrt
    have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (‖toLpSeq Z hmem 0‖ * ∑' j : ℕ, |φ j|))
      hinv (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Filter.Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have key := eLpNorm_sqrt_sampleMean_causalLinearProcessLp_le hmem hindep hident hcenter hφ hsum hn
  rw [show (fun ω => Real.sqrt (n : ℝ) * sampleMean n
        fun t => (causalLinearProcessLp φ Z hmem (t : ℤ) : Ω → ℝ) ω)
      = (√(n : ℝ)) • (fun ω => sampleMean n
        fun t => (causalLinearProcessLp φ Z hmem (t : ℤ) : Ω → ℝ) ω) from by
        funext ω; simp [Pi.smul_apply, smul_eq_mul], eLpNorm_const_smul,
    Real.enorm_eq_ofReal hn'.le] at key
  rw [show ((fun (n : ℕ) ω => sampleMean n
        fun t => (causalLinearProcessLp φ Z hmem (t : ℤ) : Ω → ℝ) ω) n - fun _ => (0 : ℝ))
      = (fun ω => sampleMean n fun t => (causalLinearProcessLp φ Z hmem (t : ℤ) : Ω → ℝ) ω)
      from by funext ω; simp,
    show ENNReal.ofReal (‖toLpSeq Z hmem 0‖ * ∑' j : ℕ, |φ j|) * (ENNReal.ofReal (√(n : ℝ)))⁻¹
      = ENNReal.ofReal (‖toLpSeq Z hmem 0‖ * ∑' j : ℕ, |φ j|) / ENNReal.ofReal (√(n : ℝ))
      from (div_eq_mul_inv _ _).symm]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hn').ne')
    (Or.inl ENNReal.ofReal_ne_top)).mpr (by rw [mul_comm]; exact key)

end DeepWiki.TimeSeries
