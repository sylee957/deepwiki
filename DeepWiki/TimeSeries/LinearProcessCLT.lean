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

/-- **Full boundary `L²` bound for `MA(q)`:** the linear combination of lag-differences with the
moving-average coefficients has `L²` norm bounded by `∑ⱼ ‖θⱼ‖ · 2jM`, a constant independent of `n`.
This is `‖D_n‖₂ ≤ C` for `D_n = Sₙ − (∑θ) Tₙ`; Minkowski over the lags `j` plus the lag-`j` estimate. -/
theorem eLpNorm_maq_boundary_le (θ : Polynomial ℝ) {Z : ℤ → Ω → ℝ} {M : ℝ≥0∞}
    (hmeas : ∀ s, AEStronglyMeasurable (Z s) P) (hZ : ∀ s, eLpNorm (Z s) 2 P ≤ M) (n : ℕ) :
    eLpNorm (∑ j ∈ Finset.range (θ.natDegree + 1),
        θ.coeff j • fun ω => ∑ t ∈ Finset.range n, (Z ((t : ℤ) - j) ω - Z (t : ℤ) ω)) 2 P
      ≤ ∑ j ∈ Finset.range (θ.natDegree + 1), ‖θ.coeff j‖ₑ * (2 * j * M) := by
  refine le_trans (eLpNorm_sum_le (fun j _ => ?_) (by norm_num)) (Finset.sum_le_sum fun j _ => ?_)
  · exact (Finset.aestronglyMeasurable_fun_sum _ fun t _ => (hmeas _).sub (hmeas _)).const_smul _
  · exact le_trans (eLpNorm_const_smul_le)
      (mul_le_mul' le_rfl (eLpNorm_sum_range_lag_sub_le hmeas hZ n j))

omit [MeasurableSpace Ω] in
/-- **Algebraic identity for the `MA(q)` central limit theorem:** the difference between the rescaled
`MA(q)` sample mean and the `∑θ`-scaled rescaled noise mean equals `(√n · n⁻¹)` times the
coefficient-weighted lag-difference `D_n = ∑ⱼ θⱼ (∑_{t<n}(Z_{t−j} − Z_t))`. Exposing this `D_n`
structure lets the boundary `L²` bound control the difference. -/
theorem maq_sub_smul_eq (θ : Polynomial ℝ) (Z : ℤ → Ω → ℝ) (n : ℕ) :
    ((fun ω => Real.sqrt n * sampleMean n
          (fun t => ∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j * Z ((t : ℤ) - j) ω))
        - fun ω => (∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j)
            * (Real.sqrt n * sampleMean n (fun k => Z (k : ℤ) ω)))
      = (Real.sqrt n * (n : ℝ)⁻¹) • ∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j •
          fun ω => ∑ t ∈ Finset.range n, (Z ((t : ℤ) - j) ω - Z (t : ℤ) ω) := by
  ext ω
  have key : (∑ t ∈ Finset.range n,
        ∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j * Z ((t : ℤ) - j) ω)
      - (∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j) * ∑ k ∈ Finset.range n, Z (k : ℤ) ω
      = ∑ j ∈ Finset.range (θ.natDegree + 1),
          θ.coeff j * ∑ t ∈ Finset.range n, (Z ((t : ℤ) - j) ω - Z (t : ℤ) ω) := by
    rw [Finset.sum_comm, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by rw [mul_sub]
  simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, sampleMean]
  rw [← key]; ring

/-- **`L²`-negligibility of the `MA(q)` perturbation:** the difference between the rescaled `MA(q)`
sample mean and the `∑θ`-scaled rescaled noise mean tends to `0` in `L²`. From the algebraic identity
`maq_sub_smul_eq` (difference `= (√n·n⁻¹)·D_n`), the boundary bound `‖D_n‖₂ ≤ C`, and `√n·n⁻¹ → 0`. -/
theorem tendsto_eLpNorm_maq_sub (θ : Polynomial ℝ) {Z : ℤ → Ω → ℝ}
    (hmeas : ∀ s, AEStronglyMeasurable (Z s) P) (hmem : ∀ s, MemLp (Z s) 2 P)
    (hident : ∀ s, IdentDistrib (Z s) (Z 0) P P) :
    Tendsto (fun n : ℕ => eLpNorm
      ((fun ω => Real.sqrt n * sampleMean n
            (fun t => ∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j * Z ((t : ℤ) - j) ω))
        - fun ω => (∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j)
            * (Real.sqrt n * sampleMean n (fun k => Z (k : ℤ) ω))) 2 P) atTop (𝓝 0) := by
  have hZ : ∀ s, eLpNorm (Z s) 2 P ≤ eLpNorm (Z 0) 2 P := fun s => le_of_eq ((hident s).eLpNorm_eq 2)
  set C := ∑ j ∈ Finset.range (θ.natDegree + 1), ‖θ.coeff j‖ₑ * (2 * (j : ℝ≥0∞) * eLpNorm (Z 0) 2 P)
    with hC
  have hCtop : C ≠ ⊤ := by
    refine ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top (by simp [enorm_ne_top]) ?_
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (hmem 0).eLpNorm_lt_top.ne
  have hbound : ∀ n : ℕ, eLpNorm
      ((fun ω => Real.sqrt n * sampleMean n
            (fun t => ∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j * Z ((t : ℤ) - j) ω))
        - fun ω => (∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j)
            * (Real.sqrt n * sampleMean n (fun k => Z (k : ℤ) ω))) 2 P
        ≤ ENNReal.ofReal (Real.sqrt n * (n : ℝ)⁻¹) * C := by
    intro n
    rw [maq_sub_smul_eq, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    exact mul_le_mul' le_rfl (eLpNorm_maq_boundary_le θ hmeas hZ n)
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
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt n * (n : ℝ)⁻¹) * C) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt n * (n : ℝ)⁻¹)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp hroot
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hCtop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) hbound

end DeepWiki.TimeSeries
