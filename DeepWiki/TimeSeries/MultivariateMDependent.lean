import DeepWiki.TimeSeries.MDependentCLT
import DeepWiki.TimeSeries.MultivariateCLT
import DeepWiki.TimeSeries.MovingAverageMDependent
import DeepWiki.TimeSeries.MultivariateDelta

/-! # Toward the multivariate m-dependent CLT
The scalar projections `⟪Yₜ, λ⟫` of a vector `m`-dependent process inherit `m`-dependence
(`IsMDependent.comp`) and strict stationarity (`IsStrictlyStationary.comp`); their long-run variance is
the quadratic form `λ ⬝ᵥ S λ` of the long-run cross-covariance matrix (`covariance_inner_inner` summed
over lags). Here: the cross-covariance of coordinate blocks vanishes beyond the dependence range, the
finite-support fact giving summability of the cross-covariances. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace Matrix ENNReal

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

/-- **The multivariate central limit theorem for `m`-dependent processes** (the vector form of
Brockwell–Davis Theorem 6.4.2, the Bartlett engine): a strictly-stationary, centered, `L²`, vector
`m`-dependent process `Y` has normalized partial sums `√n · (n⁻¹ ∑ₜ Yₜ)` converging in distribution to
`N(0, S)` where `S = longRunCovMatrix Y μ`. Proven by the Cramér–Wold device: each one-dimensional
projection is governed by the 1-D `m`-dependent CLT (`tendstoInDistribution_sampleMean_inner`), and Lévy's
theorem + the scaled-Gaussian law + the projection linearity match the per-direction characteristic
functions. (`PosSemidef` of `S` — the long-run covariance — is taken as a hypothesis.) -/
theorem IsMDependent.tendstoInDistribution_multivariate {d m : ℕ} [IsProbabilityMeasure μ]
    {Y : ℤ → Ω → EuclideanSpace ℝ (Fin d)} {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] (hmdep : IsMDependent m Y μ) (hstat : IsStrictlyStationary Y μ)
    (hmeas : ∀ t, Measurable (Y t)) (hmem : ∀ t i, MemLp (fun ω => Y t ω i) 2 μ)
    (hcenter : ∀ t i, ∫ ω, Y t ω i ∂μ = 0) (hpsd : (longRunCovMatrix Y μ).PosSemidef)
    {V : Ω' → EuclideanSpace ℝ (Fin d)}
    (hV : HasLaw V (multivariateGaussian 0 (longRunCovMatrix Y μ)) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n : ℝ) • ((n : ℝ)⁻¹ • ∑ t ∈ Finset.range n, Y (t : ℤ) ω))
      atTop V (fun _ => μ) μ' := by
  refine tendstoInDistribution_multivariateGaussian_of_tendsto_charFun_proj hpsd hV
    (fun n => by fun_prop) fun lam => ?_
  have hG : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  have hpp := tendstoInDistribution_sampleMean_inner hmdep hstat hmeas hmem hcenter hG lam
  have hlevy := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hpp.tendsto 1
  simp only [ProbabilityMeasure.coe_mk] at hlevy
  rw [(hasLaw_sqrt_smul_gaussian (v := lam ⬝ᵥ longRunCovMatrix Y μ *ᵥ lam) hG).map_eq] at hlevy
  simp_rw [inner_smul_sampleMean_eq]
  exact hlevy

/-- **The lagged product of an `m`-dependent process is `(m+k)`-dependent:** if `X` is `m`-dependent then
`t ↦ Xₜ · Xₜ₊ₖ` is `(m+k)`-dependent — each `Wₜ` is a measurable function of `X` on the 2-point window
`{t, t+k}`, and windows `{s, s+k}`, `{t, t+k}` more than `m+k` apart contain `X`-indices more than `m`
apart, hence independent. The sample-autocovariance lag process `XₜXₜ₊ₖ` whose CLT is Bartlett's theorem. -/
theorem IsMDependent.mul_shift {m : ℕ} {X : ℤ → Ω → ℝ} (h : IsMDependent m X μ) (k : ℕ) :
    IsMDependent (m + k) (fun t ω => X t ω * X (t + k) ω) μ := by
  intro S T hsep
  set S' : Finset ℤ := S ∪ S.image (· + (k : ℤ)) with hS'
  set T' : Finset ℤ := T ∪ T.image (· + (k : ℤ)) with hT'
  have hsep' : ∀ a ∈ S', ∀ b ∈ T', a + (m : ℤ) < b := by
    intro a ha b hb
    simp only [hS', hT', Finset.mem_union, Finset.mem_image] at ha hb
    rcases ha with has | ⟨s, hs, rfl⟩ <;> rcases hb with hbt | ⟨t, ht, rfl⟩ <;>
      · have := hsep _ ‹_› _ ‹_›; push_cast at this ⊢; omega
  have hmemS : ∀ i : S, (i : ℤ) ∈ S' ∧ (i : ℤ) + (k : ℤ) ∈ S' := fun i =>
    ⟨Finset.mem_union_left _ i.2, Finset.mem_union_right _ (Finset.mem_image_of_mem _ i.2)⟩
  have hmemT : ∀ i : T, (i : ℤ) ∈ T' ∧ (i : ℤ) + (k : ℤ) ∈ T' := fun i =>
    ⟨Finset.mem_union_left _ i.2, Finset.mem_union_right _ (Finset.mem_image_of_mem _ i.2)⟩
  exact (h S' T' hsep').comp
    (φ := fun g (i : S) => g ⟨(i : ℤ), (hmemS i).1⟩ * g ⟨(i : ℤ) + (k : ℤ), (hmemS i).2⟩)
    (ψ := fun g (i : T) => g ⟨(i : ℤ), (hmemT i).1⟩ * g ⟨(i : ℤ) + (k : ℤ), (hmemT i).2⟩)
    (by fun_prop) (by fun_prop)

/-- **The lagged product of a strictly-stationary process is strictly stationary:** if `X` is strictly
stationary (measurable coords) then `t ↦ Xₜ·Xₜ₊ₖ` is strictly stationary. Each finite joint law of the
products is a coordinatewise image of a finite joint law of `X` on the doubled index set `{tᵢ, tᵢ+k}`
(combined via `finSumFinEquiv`), which is shift-invariant. -/
theorem IsStrictlyStationary.mul_shift {X : ℤ → Ω → ℝ} (h : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) (k : ℕ) :
    IsStrictlyStationary (fun t ω => X t ω * X (t + k) ω) μ := by
  intro n t hsh
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv with he
  set s : ℤ → Fin (n + n) → ℤ :=
    fun c j => Sum.elim (fun i => t i + c) (fun i => t i + c + (k : ℤ)) (e.symm j) with hs
  set φ : (Fin (n + n) → ℝ) → (Fin n → ℝ) := fun g i => g (e (.inl i)) * g (e (.inr i)) with hφ
  have key : ∀ c : ℤ, (μ.map fun ω (i : Fin n) => X (t i + c) ω * X (t i + c + (k : ℤ)) ω)
      = (μ.map fun ω j => X (s c j) ω).map φ := fun c => by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext ω i
    simp only [hφ, Function.comp_apply, hs, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  have hshift : (μ.map fun ω j => X (s 0 j) ω) = μ.map fun ω j => X (s hsh j) ω := by
    rw [h (n + n) (s 0) hsh]
    congr 1
    funext ω j
    have : s 0 j + hsh = s hsh j := by
      simp only [hs]
      rcases e.symm j with i | i <;> (simp only [Sum.elim_inl, Sum.elim_inr]; ring)
    rw [this]
  have hL : (fun ω (i : Fin n) => X (t i) ω * X (t i + (k : ℤ)) ω)
      = fun ω (i : Fin n) => X (t i + 0) ω * X (t i + 0 + (k : ℤ)) ω := by simp
  have hR : (fun ω (i : Fin n) => X (t i + hsh) ω * X (t i + hsh + (k : ℤ)) ω)
      = fun ω (i : Fin n) => X (t i + hsh) ω * X (t i + hsh + (k : ℤ)) ω := rfl
  rw [hL, key 0, hshift, ← key hsh]

/-- **A windowed function of an `m`-dependent process is `(m+k)`-dependent:** if `X` is `m`-dependent and
`f` is measurable, then `t ↦ f(Xₜ, …, Xₜ₊ₖ)` is `(m+k)`-dependent — each value depends on `X` only on the
window `{t, …, t+k}`, and `Y`-blocks more than `m+k` apart have windows whose `X`-indices are more than `m`
apart (hence independent). Covers the vector autocovariance process `Yₜ = (XₜXₜ₊ₕ)ₕ` (`f w = (w 0 · w h)ₕ`),
the multivariate input to Bartlett's theorem. -/
theorem IsMDependent.window {V : Type*} [MeasurableSpace V] {m : ℕ} {X : ℤ → Ω → ℝ}
    (h : IsMDependent m X μ) (k : ℕ) {f : (Fin (k + 1) → ℝ) → V} (hf : Measurable f) :
    IsMDependent (m + k) (fun t ω => f fun i => X (t + (i : ℕ)) ω) μ := by
  intro S T hsep
  set W : Finset ℤ → Finset ℤ :=
    fun U => U.biUnion fun s => (Finset.range (k + 1)).image fun (i : ℕ) => s + (i : ℤ) with hW
  have hmemW : ∀ (U : Finset ℤ) (s : ℤ), s ∈ U → ∀ i : Fin (k + 1), s + (i : ℕ) ∈ W U :=
    fun U s hs i => by
      simp only [hW, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨s, hs, (i : ℕ), Finset.mem_range.mpr i.2, rfl⟩
  have hsep' : ∀ a ∈ W S, ∀ b ∈ W T, a + (m : ℤ) < b := by
    intro a ha b hb
    simp only [hW, Finset.mem_biUnion, Finset.mem_image] at ha hb
    obtain ⟨s, hs, i, hik, rfl⟩ := ha
    obtain ⟨t, ht, j, hjk, rfl⟩ := hb
    have := hsep s hs t ht
    have hik' := Finset.mem_range.mp hik
    have hjk' := Finset.mem_range.mp hjk
    push_cast at this ⊢; omega
  exact (h (W S) (W T) hsep').comp
    (φ := fun g (s : S) => f fun i => g ⟨(s : ℤ) + (i : ℕ), hmemW S (s : ℤ) s.2 i⟩)
    (ψ := fun g (s : T) => f fun i => g ⟨(s : ℤ) + (i : ℕ), hmemW T (s : ℤ) s.2 i⟩)
    (by fun_prop) (by fun_prop)

/-- **A windowed function of a strictly-stationary process is strictly stationary:** if `X` is strictly
stationary (measurable coords) then `t ↦ f(Xₜ, …, Xₜ₊ₖ)` is strictly stationary. Each finite joint law of
the windowed values is the coordinatewise image of a finite joint law of `X` on the combined window index
`Fin n × Fin (k+1)` (via `finProdFinEquiv`), which is shift-invariant. Covers `Yₜ = (XₜXₜ₊ₕ)ₕ`. -/
theorem IsStrictlyStationary.window {V : Type*} [MeasurableSpace V] {X : ℤ → Ω → ℝ}
    (h : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t)) (k : ℕ)
    {f : (Fin (k + 1) → ℝ) → V} (hf : Measurable f) :
    IsStrictlyStationary (fun t ω => f fun i => X (t + (i : ℕ)) ω) μ := by
  intro n t hsh
  set e : Fin n × Fin (k + 1) ≃ Fin (n * (k + 1)) := finProdFinEquiv with he
  set s : ℤ → Fin (n * (k + 1)) → ℤ :=
    fun c j => (fun p : Fin n × Fin (k + 1) => t p.1 + c + (p.2 : ℕ)) (e.symm j) with hs
  set φ : (Fin (n * (k + 1)) → ℝ) → (Fin n → V) := fun g a => f fun i => g (e (a, i)) with hφ
  have key : ∀ c : ℤ, (μ.map fun ω (a : Fin n) => f fun i => X (t a + c + (i : ℕ)) ω)
      = (μ.map fun ω j => X (s c j) ω).map φ := fun c => by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext ω a
    simp only [hφ, Function.comp_apply, hs, Equiv.symm_apply_apply]
  have hshift : (μ.map fun ω j => X (s 0 j) ω) = μ.map fun ω j => X (s hsh j) ω := by
    rw [h (n * (k + 1)) (s 0) hsh]
    congr 1
    funext ω j
    have : s 0 j + hsh = s hsh j := by simp only [hs]; obtain ⟨a, i⟩ := e.symm j; push_cast; ring
    rw [this]
  have hL : (fun ω (a : Fin n) => f fun i => X (t a + (i : ℕ)) ω)
      = fun ω (a : Fin n) => f fun i => X (t a + 0 + (i : ℕ)) ω := by simp
  rw [hL, key 0, hshift, ← key hsh]

/-- **A product of two `L⁴` random variables is `L²`** (Hölder, `1/2 = 1/4 + 1/4`): the lagged products
`XₛXₜ` of a process with finite fourth moments are square-integrable — the `L²` hypothesis the
`m`-dependent CLT needs for the sample-autocovariance lag process. -/
theorem memLp_mul_of_memLp_four {Y Z : Ω → ℝ} (hY : MemLp Y 4 μ) (hZ : MemLp Z 4 μ) :
    MemLp (fun ω => Y ω * Z ω) 2 μ := by
  haveI : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← two_mul, show (4 : ℝ≥0∞) = 2 * 2 from by norm_num,
      ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inr (by norm_num)), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]⟩
  exact hZ.mul hY

/-- **Single-lag central limit theorem for the sample autocovariance** (the scalar case of Bartlett's
theorem): for a strictly-stationary, `m`-dependent process `X` with finite fourth moments and constant
lag-`k` product mean `γ = E[XₜXₜ₊ₖ]`, the centered sample autocovariance `√n · n⁻¹ ∑ₜ (XₜXₜ₊ₖ − γ)`
converges in distribution to `√v · G` (`G ~ N(0,1)`, `v` the long-run variance of `XₜXₜ₊ₖ`). The product
process `XₜXₜ₊ₖ − γ` is `(m+k)`-dependent (`IsMDependent.mul_shift`), strictly stationary
(`IsStrictlyStationary.mul_shift`), `L²` (`memLp_mul_of_memLp_four`) and centered, so the 1-D `m`-dependent
CLT applies. (The explicit value of `v` is Bartlett's formula, not expanded here.) -/
theorem tendstoInDistribution_sampleMean_centered_mul_shift {m : ℕ} {X : ℤ → Ω → ℝ}
    [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {G : Ω' → ℝ} (hmdep : IsMDependent m X μ)
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    (hmem4 : ∀ t, MemLp (X t) 4 μ) (k : ℕ) (γ : ℝ)
    (hcenter : ∀ t, ∫ ω, X t ω * X (t + k) ω ∂μ = γ) (hG : HasLaw G (gaussianReal 0 1) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n * sampleMean n (fun t => X (t : ℤ) ω * X (t + k) ω - γ))
      atTop (fun ω' => Real.sqrt (∑' j, acvfStat (fun t ω => X t ω * X (t + k) ω - γ) μ j) • G ω')
      (fun _ => μ) P' :=
  IsMDependent.tendstoInDistribution_sqrt_sampleMean
    (IsMDependent.comp (IsMDependent.mul_shift hmdep k) (g := fun x => x - γ) (by fun_prop))
    (IsStrictlyStationary.comp (IsStrictlyStationary.mul_shift hstat hmeas k) (fun t => by fun_prop)
      (g := fun x => x - γ) (by fun_prop))
    (IsStrictlyStationary.isWeaklyStationary (fun t => by fun_prop)
      (fun t => (memLp_mul_of_memLp_four (hmem4 t) (hmem4 (t + k))).sub (memLp_const γ))
      (IsStrictlyStationary.comp (IsStrictlyStationary.mul_shift hstat hmeas k) (fun t => by fun_prop)
        (g := fun x => x - γ) (by fun_prop)))
    (fun t => by fun_prop)
    (fun t => (memLp_mul_of_memLp_four (hmem4 t) (hmem4 (t + k))).sub (memLp_const γ))
    (fun t => by
      rw [integral_sub ((memLp_mul_of_memLp_four (hmem4 t) (hmem4 (t + k))).integrable (by norm_num))
        (integrable_const γ), integral_const, hcenter t]
      simp)
    hG

/-- **The centered vector autocovariance process is `(m+k)`-dependent:** `Yₜ = (XₜXₜ₊ₕ − γₕ)ₕ` (as an
`EuclideanSpace ℝ (Fin (k+1))`) inherits `m`-dependence from `X` — it is the windowed function
`f w = (w 0 · w h − γₕ)ₕ` of `X` (`IsMDependent.window`). The `m`-dependent vector statistic whose CLT is
multivariate Bartlett. -/
theorem isMDependent_vecAutocov {m : ℕ} {X : ℤ → Ω → ℝ} (hmdep : IsMDependent m X μ) (k : ℕ)
    (γ : Fin (k + 1) → ℝ) :
    IsMDependent (m + k)
      (fun t ω => (WithLp.toLp 2 fun i => X t ω * X (t + (i : ℕ)) ω - γ i :
        EuclideanSpace ℝ (Fin (k + 1)))) μ := by
  have heq : (fun (t : ℤ) ω => (WithLp.toLp 2 fun i => X t ω * X (t + (i : ℕ)) ω - γ i :
        EuclideanSpace ℝ (Fin (k + 1))))
      = fun t ω => (WithLp.toLp 2 fun i =>
        (fun j : Fin (k + 1) => X (t + (j : ℕ)) ω) 0 * (fun j : Fin (k + 1) => X (t + (j : ℕ)) ω) i
          - γ i : EuclideanSpace ℝ (Fin (k + 1))) := by
    funext t ω; congr 1; funext i; simp
  rw [heq]
  exact IsMDependent.window hmdep k
    (f := fun w => (WithLp.toLp 2 fun i => w 0 * w i - γ i : EuclideanSpace ℝ (Fin (k + 1))))
    (by fun_prop)

/-- **The centered vector autocovariance process is strictly stationary:** `Yₜ = (XₜXₜ₊ₕ − γₕ)ₕ` inherits
strict stationarity from `X` (the windowed function `f w = (w 0 · w h − γₕ)ₕ`, `IsStrictlyStationary.window`). -/
theorem isStrictlyStationary_vecAutocov {X : ℤ → Ω → ℝ} (hstat : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) (k : ℕ) (γ : Fin (k + 1) → ℝ) :
    IsStrictlyStationary
      (fun t ω => (WithLp.toLp 2 fun i => X t ω * X (t + (i : ℕ)) ω - γ i :
        EuclideanSpace ℝ (Fin (k + 1)))) μ := by
  have heq : (fun (t : ℤ) ω => (WithLp.toLp 2 fun i => X t ω * X (t + (i : ℕ)) ω - γ i :
        EuclideanSpace ℝ (Fin (k + 1))))
      = fun t ω => (WithLp.toLp 2 fun i =>
        (fun j : Fin (k + 1) => X (t + (j : ℕ)) ω) 0 * (fun j : Fin (k + 1) => X (t + (j : ℕ)) ω) i
          - γ i : EuclideanSpace ℝ (Fin (k + 1))) := by
    funext t ω; congr 1; funext i; simp
  rw [heq]
  exact IsStrictlyStationary.window hstat hmeas k
    (f := fun w => (WithLp.toLp 2 fun i => w 0 * w i - γ i : EuclideanSpace ℝ (Fin (k + 1))))
    (by fun_prop)

/-- **The multivariate central limit theorem for the sample autocovariances** (the vector form of
Bartlett's theorem): for a strictly-stationary, `m`-dependent process `X` with finite fourth moments and
constant lag-`h` product means `γₕ = E[XₜXₜ₊ₕ]`, the centered sample autocovariance vector
`√n · n⁻¹ ∑ₜ (XₜXₜ₊ₕ − γₕ)_{h≤k}` converges in distribution to `N(0, S)` where `S` is the long-run
covariance matrix of the lag-product process. Applies the multivariate `m`-dependent CLT to the vector
autocovariance process (`isMDependent_vecAutocov`, `isStrictlyStationary_vecAutocov`, with `L²` coordinates
from `memLp_mul_of_memLp_four` and centering from `hcenter`). `PosSemidef` of `S` is a hypothesis; its
explicit value is Bartlett's formula. -/
theorem tendstoInDistribution_sampleAutocovVec {m : ℕ} {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (hmdep : IsMDependent m X μ) (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    (hmem4 : ∀ t, MemLp (X t) 4 μ) (k : ℕ) (γ : Fin (k + 1) → ℝ)
    (hcenter : ∀ (t : ℤ) (i : Fin (k + 1)), ∫ ω, X t ω * X (t + (i : ℕ)) ω ∂μ = γ i)
    (hpsd : (longRunCovMatrix (fun t ω => (WithLp.toLp 2 fun i => X t ω * X (t + (i : ℕ)) ω - γ i :
        EuclideanSpace ℝ (Fin (k + 1)))) μ).PosSemidef)
    {V : Ω' → EuclideanSpace ℝ (Fin (k + 1))}
    (hV : HasLaw V (multivariateGaussian 0 (longRunCovMatrix
        (fun t ω => (WithLp.toLp 2 fun i => X t ω * X (t + (i : ℕ)) ω - γ i :
          EuclideanSpace ℝ (Fin (k + 1)))) μ)) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n : ℝ) • ((n : ℝ)⁻¹ • ∑ t ∈ Finset.range n,
        (WithLp.toLp 2 fun i => X (t : ℤ) ω * X (t + (i : ℕ)) ω - γ i :
          EuclideanSpace ℝ (Fin (k + 1))))) atTop V (fun _ => μ) μ' :=
  IsMDependent.tendstoInDistribution_multivariate (isMDependent_vecAutocov hmdep k γ)
    (isStrictlyStationary_vecAutocov hstat hmeas k γ) (by fun_prop)
    (fun t i => (memLp_mul_of_memLp_four (hmem4 t) (hmem4 (t + (i : ℕ)))).sub (memLp_const (γ i)))
    (fun t i => by
      show ∫ ω, (X t ω * X (t + (i : ℕ)) ω - γ i) ∂μ = 0
      rw [integral_sub
          ((memLp_mul_of_memLp_four (hmem4 t) (hmem4 (t + (i : ℕ)))).integrable (by norm_num))
          (integrable_const (γ i)), integral_const, hcenter t i]
      simp)
    hpsd hV

/-- **Consistency of the (centered) sample autocovariance:** for a strictly-stationary, `m`-dependent `X`
with finite fourth moments and constant lag-`k` product mean `γ = E[XₜXₜ₊ₖ]`, the centered sample
autocovariance `n⁻¹ ∑ₜ (XₜXₜ₊ₖ − γ)` converges to `0` in probability. From the scalar Bartlett CLT
(`√n · sampleMean ⇒ √v·G`, so `√n · sampleMean` is tight, `tight_of_tendstoInDistribution`) and `o_p · O_p`
(`tendstoInMeasure_mul_zero_of_tight` with `(√n)⁻¹ →ᵖ 0`): `sampleMean = (√n)⁻¹ · (√n · sampleMean) →ᵖ 0`.
The `γ̂(k) →ᵖ γ(k)` prerequisite for the sample-autocorrelation CLT via the multivariate delta method. -/
theorem tendstoInMeasure_sampleMean_centered_mul_shift {m : ℕ} {X : ℤ → Ω → ℝ}
    [IsProbabilityMeasure μ] (hmdep : IsMDependent m X μ) (hstat : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) (hmem4 : ∀ t, MemLp (X t) 4 μ) (k : ℕ) (γ : ℝ)
    (hcenter : ∀ t, ∫ ω, X t ω * X (t + k) ω ∂μ = γ) :
    TendstoInMeasure μ (fun n ω => sampleMean n (fun t => X (t : ℤ) ω * X (t + k) ω - γ)) atTop
      (fun _ => 0) := by
  have hG : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  have htight := tight_of_tendstoInDistribution
    (tendstoInDistribution_sampleMean_centered_mul_shift hmdep hstat hmeas hmem4 k γ hcenter hG)
  simp only [Real.norm_eq_abs, abs_abs] at htight
  have hsqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have ha : TendstoInMeasure μ (fun (n : ℕ) (_ : Ω) => (Real.sqrt n)⁻¹) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ fun _ => hsqrt)
  have heq : (fun n ω => sampleMean n (fun t => X (t : ℤ) ω * X (t + k) ω - γ))
      = fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
        (Real.sqrt n * sampleMean n (fun t => X (t : ℤ) ω * X (t + k) ω - γ)) := by
    funext n ω
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn, sampleMean]
    · rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)), one_mul]
  rw [heq]
  exact tendstoInMeasure_mul_zero_of_tight ha htight

end DeepWiki.TimeSeries
