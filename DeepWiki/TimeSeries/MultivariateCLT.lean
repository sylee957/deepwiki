import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Multivariate central limit theorem (foundation)
Building the multivariate CLT for iid random vectors via the Cramér–Wold device: the characteristic
function of a measure on a finite-dimensional inner product space, evaluated at `t`, equals the
characteristic function of the *one-dimensional projection* `⟪·, t⟫` at `1` (`charFun_proj`). This
reduces multivariate charFun convergence to Mathlib's univariate CLT, and Lévy's continuity theorem
(`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) then gives convergence in distribution. The
foundational enabler for Bartlett's formula (Thm 7.2.1/7.2.2) and the Ch10–13 multivariate theory. -/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology RealInnerProductSpace ENNReal

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Characteristic function via one-dimensional projection:** for `X : Ω → E` into a real inner
product space, the characteristic function of the law of `X` at `t` equals that of the law of the
scalar projection `⟪X ·, t⟫` at `1` — both are `∫ exp(I⟪X ω, t⟫) dμ`. The bridge that reduces
multivariate characteristic functions to univariate ones (the Cramér–Wold device). -/
theorem charFun_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] {X : Ω → E} (hX : AEMeasurable X μ) (t : E) :
    charFun (μ.map X) t = charFun (μ.map fun ω => (⟪X ω, t⟫ : ℝ)) 1 := by
  rw [charFun_apply, charFun_apply, integral_map hX (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp [RCLike.inner_apply]

/-- **Univariate characteristic-function limit (general variance):** for centered iid `L²`
real random variables `W`, the characteristic function of `(√n)⁻¹ ∑ Wₖ` at `1` converges to
`exp(−v/2)`, where `v = E[W₀²]` is the (centered) variance. Mathlib's normalized limit
`tendsto_charFun_inv_sqrt_mul_pow` rescaled by `√v` (with the degenerate `v = 0` case handled
separately). The per-direction ingredient of the multivariate CLT. -/
theorem tendsto_charFun_inv_sqrt_mul_sum_one [IsProbabilityMeasure μ] {W : ℕ → Ω → ℝ}
    (hindep : iIndepFun W μ) (hident : ∀ i, IdentDistrib (W i) (W 0) μ μ) (h0 : μ[W 0] = 0)
    (hmem : Integrable (fun ω => W 0 ω ^ 2) μ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω => (√n)⁻¹ * ∑ k ∈ Finset.range n, W k ω) 1)
      atTop (𝓝 (Complex.exp (Complex.ofReal (-(∫ ω, W 0 ω ^ 2 ∂μ) / 2)))) := by
  have hWm : AEMeasurable (W 0) μ := (hident 0).aemeasurable_fst
  have hfun : (fun n : ℕ => charFun (μ.map fun ω => (√n)⁻¹ * ∑ k ∈ Finset.range n, W k ω) 1)
      = fun n : ℕ => (charFun (μ.map (W 0)) ((√n)⁻¹ * 1)) ^ n :=
    funext fun n => charFun_inv_sqrt_mul_sum hindep hident
  rw [hfun]
  set v : ℝ := ∫ ω, W 0 ω ^ 2 ∂μ with hv
  have hv0 : 0 ≤ v := by rw [hv]; exact integral_nonneg fun ω => by positivity
  rcases eq_or_lt_of_le hv0 with hveq | hvpos
  · -- degenerate: `W₀ = 0` a.e., so every `charFun (μ.map W₀) s = 1`
    have hW0 : W 0 =ᵐ[μ] 0 := by
      have h := (integral_eq_zero_iff_of_nonneg (fun ω => by positivity) hmem).1 (hv ▸ hveq.symm)
      filter_upwards [h] with ω hω
      simpa [pow_eq_zero_iff] using hω
    have hc : ∀ s : ℝ, charFun (μ.map (W 0)) s = 1 := fun s => by
      rw [charFun_apply, integral_map hWm (by fun_prop),
        integral_congr_ae (g := fun _ => (1 : ℂ)) (by filter_upwards [hW0] with ω hω; simp [hω])]
      simp
    simp only [hc, one_pow]
    rw [← hveq]
    simp
  · -- nondegenerate: normalise `W₀` by `√v`
    have hsqvpos : 0 < √v := Real.sqrt_pos.mpr hvpos
    set X : Ω → ℝ := fun ω => W 0 ω / √v with hX
    have hXmem : AEMeasurable X μ := hWm.div_const _
    have hX0 : μ[X] = 0 := by rw [hX, integral_div, h0, zero_div]
    have hX1 : μ[X ^ 2] = 1 := by
      have hxe : (X ^ 2) = fun ω => W 0 ω ^ 2 / v := by
        funext ω; simp only [hX, Pi.pow_apply, div_pow, Real.sq_sqrt hv0]
      rw [hxe, integral_div, ← hv, div_self hvpos.ne']
    have hmap : ∀ s : ℝ, charFun (μ.map (W 0)) s = charFun (μ.map X) (√v * s) := fun s => by
      have hWeq : (W 0) = fun ω => √v * X ω := by funext ω; simp only [hX]; field_simp
      rw [hWeq, charFun_map_mul_comp hXmem]
    have hlim : Complex.exp (-((√v : ℝ) : ℂ) ^ 2 / 2) = Complex.exp (Complex.ofReal (-v / 2)) := by
      congr 1; rw [← Complex.ofReal_pow, Real.sq_sqrt hv0]; push_cast; ring
    have key := tendsto_charFun_inv_sqrt_mul_pow hXmem hX0 hX1 (√v)
    rw [hlim] at key
    refine Tendsto.congr (fun n => ?_) key
    rw [hmap ((√n)⁻¹ * 1), mul_one, mul_comm]

end DeepWiki.TimeSeries
