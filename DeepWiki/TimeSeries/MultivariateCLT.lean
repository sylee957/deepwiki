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
open scoped Topology RealInnerProductSpace ENNReal Matrix

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

/-- **Multivariate central limit theorem for iid random vectors:** for centered iid `L²` random
vectors `Z : ℕ → Ω → EuclideanSpace ℝ (Fin k)` whose directional variances match the positive
semidefinite matrix `S` (`∫ ⟪Z₀, t⟫² = tᵀ S t`), the standardized partial sums
`(√n)⁻¹ ∑_{k<n} Zₖ` converge in distribution to the multivariate Gaussian `N(0, S)`. Via the
Cramér–Wold device (`charFun_proj`): the characteristic function at every `t` reduces to the
univariate CLT for the projections `⟪Zₖ, t⟫` (`tendsto_charFun_inv_sqrt_mul_sum_one`), matched to
`charFun_multivariateGaussian` through Lévy's continuity theorem. The foundation for Bartlett's
formula and the multivariate/spectral asymptotics of Ch10–13. -/
theorem multivariate_iid_clt {k : ℕ} [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    {V : Ω' → EuclideanSpace ℝ (Fin k)} {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef)
    (hZmem : ∀ i, MemLp (Z i) 2 μ) (hindep : iIndepFun Z μ)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ) (hcenter : ∫ ω, Z 0 ω ∂μ = 0)
    (hcov : ∀ t : EuclideanSpace ℝ (Fin k), ∫ ω, (⟪Z 0 ω, t⟫ : ℝ) ^ 2 ∂μ = t ⬝ᵥ S *ᵥ t)
    (hV : HasLaw V (multivariateGaussian 0 S) μ') :
    TendstoInDistribution (fun (n : ℕ) ω => (√n)⁻¹ • ∑ k ∈ Finset.range n, Z k ω) atTop V
      (fun _ => μ) μ' := by
  have hZae : ∀ i, AEMeasurable (Z i) μ := fun i => (hZmem i).aestronglyMeasurable.aemeasurable
  have hZint : Integrable (Z 0) μ := (hZmem 0).integrable (by norm_num)
  have haemeas : ∀ n : ℕ, AEMeasurable
      (fun ω => (√(n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, Z k ω) μ :=
    fun n => (Finset.aemeasurable_fun_sum (Finset.range n) fun k _ => hZae k).const_smul
      ((√(n : ℝ))⁻¹)
  refine ⟨haemeas, hV.aemeasurable, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
  rw! [hV.map_eq]
  simp only [ProbabilityMeasure.coe_mk]
  rw [charFun_multivariateGaussian hS]
  -- projections `W k = ⟪Z k ·, t⟫` are centered iid `L²`
  have hLm : Measurable fun x : EuclideanSpace ℝ (Fin k) => (⟪x, t⟫ : ℝ) :=
    ((innerSL ℝ).flip t).continuous.measurable
  set W : ℕ → Ω → ℝ := fun k ω => ⟪Z k ω, t⟫ with hW
  have hWiid : iIndepFun W μ := hindep.comp (fun _ x => ⟪x, t⟫) (fun _ => hLm)
  have hWident : ∀ i, IdentDistrib (W i) (W 0) μ μ := fun i =>
    (hident i).comp hLm
  have hW0 : μ[W 0] = 0 := by
    simp only [hW]
    rw [integral_congr_ae (ae_of_all _ fun ω => real_inner_comm t (Z 0 ω)),
      integral_inner hZint, hcenter, inner_zero_right]
  have hWmem : Integrable (fun ω => W 0 ω ^ 2) μ := by
    have hWLp : MemLp (W 0) 2 μ :=
      (((innerSL ℝ).flip t).lipschitz).comp_memLp (by simp) (hZmem 0)
    exact hWLp.integrable_sq
  have hlim := tendsto_charFun_inv_sqrt_mul_sum_one hWiid hWident hW0 hWmem
  have hfn : ∀ n : ℕ, charFun ((μ.map fun ω => (√n)⁻¹ • ∑ k ∈ Finset.range n, Z k ω)) t
      = charFun (μ.map fun ω => (√n)⁻¹ * ∑ k ∈ Finset.range n, W k ω) 1 := fun n => by
    rw [charFun_proj (haemeas n) t]
    congr 2; funext ω
    rw [real_inner_smul_left, sum_inner]
  have hlimeq : Complex.exp ((⟪t, (0 : EuclideanSpace ℝ (Fin k))⟫ : ℝ) * I - ↑(t ⬝ᵥ S *ᵥ t) / 2)
      = Complex.exp (Complex.ofReal (-(∫ ω, W 0 ω ^ 2 ∂μ) / 2)) := by
    rw [inner_zero_right, hW]
    simp only [hcov]
    congr 1
    push_cast; ring
  rw [hlimeq]
  exact (hlim.congr fun n => (hfn n).symm)

/-- **Cramér–Wold device for convergence to a multivariate Gaussian:** a sequence `Xₙ` of random vectors
into `EuclideanSpace ℝ (Fin k)` converges in distribution to `multivariateGaussian 0 S` (`S` positive
semidefinite) as soon as *every* one-dimensional projection converges — `charFun (law ⟪Xₙ, t⟫) 1 →
charFun (gaussianReal 0 (t ⬝ᵥ S t)) 1` for all `t`. This reduces a multivariate CLT to the univariate CLT
applied in each direction `t`: `charFun_proj` rewrites the joint characteristic function as a projected
one, `charFun_multivariateGaussian` identifies the limit, and Lévy's theorem closes it. The lifting engine
turning the 1-D `m`-dependent / linear-process CLTs into their vector forms (Bartlett's theorem). -/
theorem tendstoInDistribution_multivariateGaussian_of_tendsto_charFun_proj {k : ℕ}
    [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {X : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef) {V : Ω' → EuclideanSpace ℝ (Fin k)}
    (hV : HasLaw V (multivariateGaussian 0 S) μ') (hmeas : ∀ n, AEMeasurable (X n) μ)
    (hproj : ∀ t : EuclideanSpace ℝ (Fin k),
      Tendsto (fun n => charFun (μ.map fun ω => (⟪X n ω, t⟫ : ℝ)) 1) atTop
        (𝓝 (charFun (gaussianReal 0 (t ⬝ᵥ S *ᵥ t).toNNReal) 1))) :
    TendstoInDistribution X atTop V (fun _ => μ) μ' := by
  refine ⟨hmeas, hV.aemeasurable, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
  rw! [hV.map_eq]
  simp only [ProbabilityMeasure.coe_mk]
  rw [charFun_multivariateGaussian hS]
  have hchar : (fun n => charFun (μ.map (X n)) t)
      = fun n => charFun (μ.map fun ω => (⟪X n ω, t⟫ : ℝ)) 1 :=
    funext fun n => charFun_proj (hmeas n) t
  rw [hchar]
  have hnn : (0 : ℝ) ≤ t ⬝ᵥ S *ᵥ t := by simpa using hS.dotProduct_mulVec_nonneg t
  have hlim : charFun (gaussianReal 0 (t ⬝ᵥ S *ᵥ t).toNNReal) 1
      = exp ((⟪t, (0 : EuclideanSpace ℝ (Fin k))⟫ : ℝ) * I - ↑(t ⬝ᵥ S *ᵥ t) / 2) := by
    rw [charFun_gaussianReal, inner_zero_right]
    push_cast [Real.coe_toNNReal _ hnn]
    ring_nf
  rw [← hlim]
  exact hproj t

end DeepWiki.TimeSeries
