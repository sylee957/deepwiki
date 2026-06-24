import DeepWiki.TimeSeries.MDependentCLT
import DeepWiki.TimeSeries.MultivariateCLT
import DeepWiki.TimeSeries.MovingAverageMDependent

/-! # Toward the multivariate m-dependent CLT
The scalar projections `⟪Yₜ, λ⟫` of a vector `m`-dependent process inherit `m`-dependence
(`IsMDependent.comp`) and strict stationarity (`IsStrictlyStationary.comp`); their long-run variance is
the quadratic form `λ ⬝ᵥ S λ` of the long-run cross-covariance matrix (`covariance_inner_inner` summed
over lags). Here: the cross-covariance of coordinate blocks vanishes beyond the dependence range, the
finite-support fact giving summability of the cross-covariances. -/

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Cross-covariance of coordinates vanishes beyond the dependence range:** for a vector `m`-dependent
process `Y`, `cov[Yₜⁱ, Yₛʲ] = 0` whenever `s + m < t` — the blocks `Y s`, `Y t` are independent, hence so
are their coordinate projections. The finite-support fact giving summability of the cross-covariances feeding
the multivariate m-dependent CLT. -/
theorem covariance_component_eq_zero_of_mDependent {d m : ℕ} [IsFiniteMeasure μ]
    {Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)} (h : IsMDependent m Y μ)
    (hmem : ∀ t i, MemLp (fun ω => Y t ω i) 2 μ) {s t : ℤ} (hst : s + (m : ℤ) < t) (i j : Fin d) :
    cov[fun ω => Y t ω i, fun ω => Y s ω j; μ] = 0 := by
  have hindep : IndepFun (Y s) (Y t) μ := h.indepFun hst
  have hjmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v j) := by fun_prop
  have himeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v i) := by fun_prop
  rw [covariance_comm]
  exact (hindep.comp hjmeas himeas).covariance_eq_zero (hmem s j) (hmem t i)

/-- **The cross-covariances of a vector `m`-dependent process are summable over lags:** each
`k ↦ cov[Yₖⁱ, Y₀ʲ]` has finite support (it vanishes for `|k| > m` by
`covariance_component_eq_zero_of_mDependent`), hence is summable. The long-run cross-covariance
`Sᵢⱼ = ∑'ₖ cov[Yₖⁱ, Y₀ʲ]` is therefore well-defined — the entries of the limiting covariance matrix. -/
theorem summable_covariance_component_of_mDependent {d m : ℕ} [IsFiniteMeasure μ]
    {Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)} (h : IsMDependent m Y μ)
    (hmem : ∀ t i, MemLp (fun ω => Y t ω i) 2 μ) (i j : Fin d) :
    Summable fun k => cov[fun ω => Y k ω i, fun ω => Y 0 ω j; μ] := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(m : ℤ)) m) fun k hk => ?_
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  rcases hk with hlt | hgt
  · rw [covariance_comm]
    exact covariance_component_eq_zero_of_mDependent h hmem (by omega : k + (m : ℤ) < 0) j i
  · exact covariance_component_eq_zero_of_mDependent h hmem (by omega : (0 : ℤ) + m < k) i j

/-- **Variance identification:** the long-run variance of a projected vector `m`-dependent process is the
quadratic form of the long-run cross-covariance matrix —
`∑'ₖ acvf⟪Y,λ⟫(k) = ∑ᵢ ∑ⱼ λᵢ λⱼ (∑'ₖ cov[Yₖⁱ, Y₀ʲ])`. Each lag's autocovariance expands bilinearly
(`covariance_inner_inner`) and the lag-sum commutes with the finite coordinate sums (`tsum_sum`, justified
by `summable_covariance_component_of_mDependent`). This is the variance feeding the Cramér–Wold lift: it
equals `λ ⬝ᵥ S λ` with `Sᵢⱼ = ∑'ₖ cov[Yₖⁱ, Y₀ʲ]`. -/
theorem tsum_acvfStat_inner_eq {d m : ℕ} [IsFiniteMeasure μ]
    {Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)} (h : IsMDependent m Y μ)
    (hmem : ∀ t i, MemLp (fun ω => Y t ω i) 2 μ) (lam : EuclideanSpace ℝ (Fin d)) :
    ∑' k, acvfStat (fun t ω => (⟪Y t ω, lam⟫ : ℝ)) μ k
      = ∑ i, ∑ j, lam i * lam j * ∑' k, cov[fun ω => Y k ω i, fun ω => Y 0 ω j; μ] := by
  have hbil : ∀ k, acvfStat (fun t ω => (⟪Y t ω, lam⟫ : ℝ)) μ k
      = ∑ i, ∑ j, lam i * lam j * cov[fun ω => Y k ω i, fun ω => Y 0 ω j; μ] := fun k => by
    rw [acvfStat_apply]; exact covariance_inner_inner lam (fun i => hmem k i) fun j => hmem 0 j
  simp_rw [hbil]
  rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ =>
    (summable_covariance_component_of_mDependent h hmem i j).mul_left _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum fun j _ =>
    (summable_covariance_component_of_mDependent h hmem i j).mul_left _]
  exact Finset.sum_congr rfl fun j _ => tsum_mul_left

/-- **A matrix quadratic form as a double sum:** `v ⬝ᵥ S v = ∑ᵢ ∑ⱼ vᵢ vⱼ Sᵢⱼ`. -/
theorem dotProduct_mulVec_eq_quadratic {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ S *ᵥ v = ∑ i, ∑ j, v i * v j * S i j := by
  rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The long-run cross-covariance matrix** of a vector process: `Sᵢⱼ = ∑'ₖ cov[Yₖⁱ, Y₀ʲ]`. For a
vector `m`-dependent process its quadratic forms are the long-run variances of the projections
(`longRunCovMatrix_quadratic`); it is the covariance matrix of the limiting Gaussian. -/
noncomputable def longRunCovMatrix {d : ℕ} (Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑' k, cov[fun ω => Y k ω i, fun ω => Y 0 ω j; μ]

/-- **The quadratic form of the long-run covariance matrix is the long-run variance of the projection:**
`λ ⬝ᵥ S λ = ∑'ₖ acvf⟪Y,λ⟫(k)` where `S = longRunCovMatrix Y μ`. Combines the matrix quadratic-form
expansion with the variance identification `tsum_acvfStat_inner_eq`. -/
theorem longRunCovMatrix_quadratic {d m : ℕ} [IsFiniteMeasure μ]
    {Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)} (h : IsMDependent m Y μ)
    (hmem : ∀ t i, MemLp (fun ω => Y t ω i) 2 μ) (lam : EuclideanSpace ℝ (Fin d)) :
    lam ⬝ᵥ longRunCovMatrix Y μ *ᵥ lam = ∑' k, acvfStat (fun t ω => (⟪Y t ω, lam⟫ : ℝ)) μ k := by
  rw [dotProduct_mulVec_eq_quadratic, tsum_acvfStat_inner_eq h hmem]
  rfl

/-- **Scaling a standard normal:** if `G ~ N(0,1)` then `√v · G ~ N(0, v)` (as `gaussianReal 0 v.toNNReal`),
for **any** real `v` — since `(√v)² = max v 0 = (v.toNNReal : ℝ)` the identity needs no sign hypothesis.
The limit law of the 1-D `m`-dependent CLT's `√(∑'acvf) • G` is thus `N(0, ∑'acvf)`. -/
theorem hasLaw_sqrt_smul_gaussian {v : ℝ} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {G : Ω' → ℝ} (hG : HasLaw G (gaussianReal 0 1) P') :
    HasLaw (fun ω => Real.sqrt v • G ω) (gaussianReal 0 v.toNNReal) P' := by
  refine ⟨by fun_prop, ?_⟩
  have hcm : (gaussianReal (0 : ℝ) 1).map (Real.sqrt v * ·) = gaussianReal 0 v.toNNReal := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_mk, Real.coe_toNNReal']
    rcases le_or_gt 0 v with hv | hv
    · rw [Real.sq_sqrt hv, max_eq_left hv]
    · rw [Real.sqrt_eq_zero_of_nonpos hv.le]; simp [max_eq_right hv.le]
  rw [show (fun ω => Real.sqrt v • G ω) = (Real.sqrt v * ·) ∘ G from rfl,
    ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hG.aemeasurable, hG.map_eq, hcm]

omit [MeasurableSpace Ω] in
/-- **The projection of the normalized vector sum is the projected scalar normalized sum:**
`⟪√n • (n⁻¹ • ∑ₜ Yₜ), λ⟫ = √n · sampleMean n ⟪Y·, λ⟫`. Inner linearity (`real_inner_smul_left`, `sum_inner`)
turns the projection of the vector statistic into the scalar statistic the 1-D `m`-dependent CLT governs. -/
theorem inner_smul_sampleMean_eq {d : ℕ} {Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)}
    (lam : EuclideanSpace ℝ (Fin d)) (n : ℕ) (ω : Ω) :
    (⟪(Real.sqrt n : ℝ) • ((n : ℝ)⁻¹ • ∑ t ∈ Finset.range n, Y (t : ℤ) ω), lam⟫ : ℝ)
      = Real.sqrt n * sampleMean n (fun s => (⟪Y (s : ℤ) ω, lam⟫ : ℝ)) := by
  rw [real_inner_smul_left, real_inner_smul_left, sum_inner, sampleMean]

omit [MeasurableSpace Ω] in
/-- `⟪X·, λ⟫` as a coordinate sum: `⟪X ω, λ⟫ = ∑ᵢ λᵢ · Xᵢ`. -/
theorem inner_eq_sum_coord {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d)) (lam : EuclideanSpace ℝ (Fin d))
    (ω : Ω) : (⟪X ω, lam⟫ : ℝ) = ∑ i, lam i * X ω i := by
  rw [PiLp.inner_apply]; simp [RCLike.inner_apply]

/-- **A projection of an `L²` random vector is `L²`:** if every coordinate `Xᵢ ∈ L²` then `⟪X·, λ⟫ ∈ L²`
(a finite combination of `L²` coordinates). -/
theorem memLp_inner {d : ℕ} {X : Ω → EuclideanSpace ℝ (Fin d)} (lam : EuclideanSpace ℝ (Fin d))
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) : MemLp (fun ω => (⟪X ω, lam⟫ : ℝ)) 2 μ := by
  have he : (fun ω => (⟪X ω, lam⟫ : ℝ)) = ∑ i, fun ω => lam i * X ω i := by
    funext ω; rw [inner_eq_sum_coord, Finset.sum_apply]
  rw [he]; exact memLp_finsetSum' Finset.univ fun i _ => (hX i).const_mul (lam i)

/-- **A projection of a centered random vector is centered:** if every coordinate is integrable with mean
`0` then `μ[⟪X·, λ⟫] = 0`. -/
theorem integral_inner_eq_zero {d : ℕ} {X : Ω → EuclideanSpace ℝ (Fin d)}
    (lam : EuclideanSpace ℝ (Fin d)) (hint : ∀ i, Integrable (fun ω => X ω i) μ)
    (hc : ∀ i, ∫ ω, X ω i ∂μ = 0) : ∫ ω, (⟪X ω, lam⟫ : ℝ) ∂μ = 0 := by
  simp_rw [inner_eq_sum_coord]
  rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
  simp [integral_const_mul, hc]

/-- **Per-direction central limit theorem for a vector `m`-dependent process:** for each `λ`, the projected
sample mean `√n · sampleMean ⟪Y·, λ⟫` converges in distribution to `√(λ ⬝ᵥ S λ) · G` (`G ~ N(0,1)`,
`S = longRunCovMatrix Y μ`). The projection `⟪Y·, λ⟫` inherits `m`-dependence and strict stationarity
(`IsMDependent.comp`, `IsStrictlyStationary.comp`), is `L²`/centered (`memLp_inner`,
`integral_inner_eq_zero`), so the 1-D `m`-dependent CLT applies, and the limiting variance is identified by
`longRunCovMatrix_quadratic`. The per-direction input to the Cramér–Wold device. -/
theorem tendstoInDistribution_sampleMean_inner {d m : ℕ} [IsProbabilityMeasure μ]
    {Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {G : Ω' → ℝ} (hmdep : IsMDependent m Y μ)
    (hstat : IsStrictlyStationary Y μ) (hmeas : ∀ t, Measurable (Y t))
    (hmem : ∀ t i, MemLp (fun ω => Y t ω i) 2 μ) (hcenter : ∀ t i, ∫ ω, Y t ω i ∂μ = 0)
    (hG : HasLaw G (gaussianReal 0 1) P') (lam : EuclideanSpace ℝ (Fin d)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n * sampleMean n (fun s => (⟪Y (s : ℤ) ω, lam⟫ : ℝ)))
      atTop (fun ω' => Real.sqrt (lam ⬝ᵥ longRunCovMatrix Y μ *ᵥ lam) • G ω') (fun _ => μ) P' := by
  have hlammeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) => (⟪v, lam⟫ : ℝ)) := by fun_prop
  have hWmeas : ∀ t, Measurable (fun ω => (⟪Y t ω, lam⟫ : ℝ)) := fun t => hlammeas.comp (hmeas t)
  have hWmem : ∀ t, MemLp (fun ω => (⟪Y t ω, lam⟫ : ℝ)) 2 μ :=
    fun t => memLp_inner lam fun i => hmem t i
  rw [longRunCovMatrix_quadratic hmdep hmem lam]
  exact IsMDependent.tendstoInDistribution_sqrt_sampleMean (hmdep.comp hlammeas)
    (hstat.comp hmeas hlammeas)
    (IsStrictlyStationary.isWeaklyStationary hWmeas hWmem (hstat.comp hmeas hlammeas))
    hWmeas hWmem
    (fun t => integral_inner_eq_zero lam (fun i => (hmem t i).integrable (by norm_num))
      fun i => hcenter t i) hG

end DeepWiki.TimeSeries
