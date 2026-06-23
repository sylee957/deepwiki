import DeepWiki.TimeSeries.MDependentCLT
import DeepWiki.TimeSeries.IidStrictlyStationary

/-! # Moving-average processes are m-dependent (Brockwell–Davis §6.4, Examples 6.4.3–6.4.4)
An MA(q) process `Xₜ = ∑_{j=0}^q θⱼ Z_{t−j}` driven by i.i.d. noise is `q`-dependent: two blocks of the
series separated by more than `q` time steps depend on disjoint noise windows, hence are independent.
Combined with the m-dependent central limit theorem this yields the asymptotic normality of `X̄ₙ` for
finite moving averages. This file builds the process and its structural properties; the `q`-dependence
and the resulting CLT follow. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **MA(q) process** `Xₜ = ∑_{j=0}^q θⱼ Z_{t−j}` driven by the noise `Z`. -/
noncomputable def movingAverage (θ : ℕ → ℝ) (q : ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range (q + 1), θ j * Z (t - j) ω

omit [MeasurableSpace Ω] in
/-- Pointwise value of the MA(q) process. -/
@[simp] theorem movingAverage_apply (θ : ℕ → ℝ) (q : ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    movingAverage θ q Z t ω = ∑ j ∈ Finset.range (q + 1), θ j * Z (t - j) ω := rfl

/-- The MA(q) process is measurable when the noise is. -/
theorem measurable_movingAverage {θ : ℕ → ℝ} {q : ℕ} {Z : ℤ → Ω → ℝ} (hZ : ∀ t, Measurable (Z t))
    (t : ℤ) : Measurable (movingAverage θ q Z t) :=
  Finset.measurable_sum _ fun _ _ => (hZ _).const_mul _

/-- The MA(q) process is `L²` when the noise is. -/
theorem memLp_movingAverage {θ : ℕ → ℝ} {q : ℕ} {Z : ℤ → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ) (t : ℤ) :
    MemLp (movingAverage θ q Z t) 2 μ :=
  memLp_finsetSum _ fun _ _ => (hZ _).const_mul _

/-- The MA(q) process is centered when the noise is. -/
theorem integral_movingAverage [IsProbabilityMeasure μ] {θ : ℕ → ℝ} {q : ℕ} {Z : ℤ → Ω → ℝ}
    (hZmem : ∀ t, MemLp (Z t) 2 μ) (hZc : ∀ t, μ[Z t] = 0) (t : ℤ) :
    μ[movingAverage θ q Z t] = 0 := by
  simp only [movingAverage]
  rw [integral_finsetSum _ fun _ _ => ((hZmem _).const_mul _).integrable one_le_two]
  simp [integral_const_mul, hZc]

/-- **An MA(q) process over i.i.d. noise is `q`-dependent**: two blocks of `X` separated by more than
`q` time steps depend on disjoint windows `[s−q, s]` of the noise, hence are independent. The block
tuple over `S` factors as a measurable window-map `φ` of the noise tuple over `S' = ⋃_{s∈S} [s−q, s]`,
the noise tuples over the disjoint windows `S'`, `T'` are independent (`iIndepFun.indepFun_finset`), and
independence transfers through `φ`, `ψ` (`IndepFun.comp`). -/
theorem isMDependent_movingAverage {θ : ℕ → ℝ} {q : ℕ} {Z : ℤ → Ω → ℝ} (hindep : iIndepFun Z μ)
    (hmeas : ∀ i, Measurable (Z i)) : IsMDependent q (movingAverage θ q Z) μ := by
  intro S T hST
  classical
  set S' := S.biUnion (fun s => Finset.Icc (s - (q : ℤ)) s) with hS'
  set T' := T.biUnion (fun t => Finset.Icc (t - (q : ℤ)) t) with hT'
  have hdisj : Disjoint S' T' := by
    rw [Finset.disjoint_left]
    intro a haS haT
    simp only [hS', hT', Finset.mem_biUnion, Finset.mem_Icc] at haS haT
    obtain ⟨s, hs, hs1, hs2⟩ := haS
    obtain ⟨t, ht, ht1, ht2⟩ := haT
    have h := hST s hs t ht
    omega
  have hmemS : ∀ (i : ↥S) (j : ℕ), j < q + 1 → (↑i : ℤ) - j ∈ S' := by
    intro i j hj
    rw [hS', Finset.mem_biUnion]
    exact ⟨↑i, i.2, by rw [Finset.mem_Icc]; omega⟩
  have hmemT : ∀ (i : ↥T) (j : ℕ), j < q + 1 → (↑i : ℤ) - j ∈ T' := by
    intro i j hj
    rw [hT', Finset.mem_biUnion]
    exact ⟨↑i, i.2, by rw [Finset.mem_Icc]; omega⟩
  set φ : (↥S' → ℝ) → (↥S → ℝ) := fun w i => ∑ j ∈ Finset.range (q + 1), θ j *
    (if h : (↑i : ℤ) - j ∈ S' then w ⟨↑i - j, h⟩ else 0) with hφ
  set ψ : (↥T' → ℝ) → (↥T → ℝ) := fun w i => ∑ j ∈ Finset.range (q + 1), θ j *
    (if h : (↑i : ℤ) - j ∈ T' then w ⟨↑i - j, h⟩ else 0) with hψ
  have hφm : Measurable φ := by
    refine measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ =>
      Measurable.const_mul ?_ _
    by_cases h : (↑i : ℤ) - j ∈ S'
    · simp only [dif_pos h]; exact measurable_pi_apply _
    · simp only [dif_neg h]; exact measurable_const
  have hψm : Measurable ψ := by
    refine measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ =>
      Measurable.const_mul ?_ _
    by_cases h : (↑i : ℤ) - j ∈ T'
    · simp only [dif_pos h]; exact measurable_pi_apply _
    · simp only [dif_neg h]; exact measurable_const
  have hcompS : (fun ω (i : ↥S) => movingAverage θ q Z (↑i) ω)
      = fun ω => φ (fun a : ↥S' => Z (↑a) ω) := by
    funext ω i
    simp only [hφ, movingAverage]
    exact Finset.sum_congr rfl fun j hj => by rw [dif_pos (hmemS i j (Finset.mem_range.mp hj))]
  have hcompT : (fun ω (i : ↥T) => movingAverage θ q Z (↑i) ω)
      = fun ω => ψ (fun a : ↥T' => Z (↑a) ω) := by
    funext ω i
    simp only [hψ, movingAverage]
    exact Finset.sum_congr rfl fun j hj => by rw [dif_pos (hmemT i j (Finset.mem_range.mp hj))]
  rw [hcompS, hcompT]
  exact (iIndepFun.indepFun_finset S' T' hdisj hindep hmeas).comp hφm hψm

/-- **A moving average of a strictly stationary process is strictly stationary**: each `MA(q)` tuple
`(X_{t i})ᵢ` is a fixed measurable functional `F` of the noise window tuple `(Z_{s p})ₚ`
(`s p = t (p.1) − p.2` over the flattened index `Fin k × Fin (q+1)`), and the shift commutes with `F`,
so shift-invariance of the noise joint law transfers through `F` (`Measure.map_map`). With
`isMDependent_movingAverage` and the structural lemmas this supplies the hypotheses of the `m`-dependent
CLT for `MA(q)` over strictly-stationary (e.g. i.i.d.) noise. -/
theorem IsStrictlyStationary.movingAverage {θ : ℕ → ℝ} {q : ℕ} {Z : ℤ → Ω → ℝ}
    (hZmeas : ∀ t, Measurable (Z t)) (hZstat : IsStrictlyStationary Z μ) :
    IsStrictlyStationary (DeepWiki.TimeSeries.movingAverage θ q Z) μ := by
  intro k t h
  set e := finProdFinEquiv (m := k) (n := q + 1) with he
  set s : Fin (k * (q + 1)) → ℤ := fun p => t (e.symm p).1 - ((e.symm p).2 : ℤ) with hs
  set F : (Fin (k * (q + 1)) → ℝ) → (Fin k → ℝ) :=
    fun w i => ∑ j : Fin (q + 1), θ (j : ℕ) * w (e (i, j)) with hF
  have hFm : Measurable F :=
    measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply _).const_mul _
  have hcomp : ∀ c : ℤ, (fun ω (i : Fin k) => DeepWiki.TimeSeries.movingAverage θ q Z (t i + c) ω)
      = F ∘ fun ω p => Z (s p + c) ω := by
    intro c
    funext ω i
    simp only [hF, Function.comp_apply, movingAverage_apply]
    rw [← Fin.sum_univ_eq_sum_range (fun j => θ j * Z (t i + c - (j : ℤ)) ω) (q + 1)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hse : s (e (i, j)) = t i - (j : ℤ) := by simp only [hs, Equiv.symm_apply_apply]
    rw [hse]
    congr 2
    omega
  have eL : (fun ω (i : Fin k) => DeepWiki.TimeSeries.movingAverage θ q Z (t i) ω)
      = F ∘ fun ω p => Z (s p) ω := by simpa using hcomp 0
  rw [eL, hcomp h,
    ← Measure.map_map hFm (measurable_pi_lambda _ fun p => hZmeas (s p)),
    ← Measure.map_map hFm (measurable_pi_lambda _ fun p => hZmeas (s p + h)),
    hZstat (k * (q + 1)) s h]

/-- **A strictly stationary `L²` process is weakly stationary**: shift-invariance of the finite joint
laws gives a constant mean (the `k = 1` law equality, `IdentDistrib.integral_eq`) and a shift-invariant
autocovariance (the `k = 2` joint-law equality — covariance pushes through the pair-tuple map,
`covariance_map`). Bridges `IsStrictlyStationary` to the `IsWeaklyStationary` hypothesis of `thm_6_4_2`. -/
theorem IsStrictlyStationary.isWeaklyStationary {X : ℤ → Ω → ℝ} (hXmeas : ∀ t, Measurable (X t))
    (hXmem : ∀ t, MemLp (X t) 2 μ) (hstat : IsStrictlyStationary X μ) : IsWeaklyStationary X μ where
  memLp := hXmem
  mean_const := by
    intro s t
    have hlaw : μ.map (X s) = μ.map (X t) := by
      have h1 := hstat 1 (fun _ => s) (t - s)
      rw [show (X s) = (fun w : Fin 1 → ℝ => w 0) ∘ fun ω (_ : Fin 1) => X s ω from by funext ω; rfl,
        show (X t) = (fun w : Fin 1 → ℝ => w 0) ∘ fun ω (_ : Fin 1) => X (s + (t - s)) ω from by
          funext ω; simp,
        ← Measure.map_map (measurable_pi_apply 0) (measurable_pi_lambda _ fun _ => hXmeas _),
        ← Measure.map_map (measurable_pi_apply 0) (measurable_pi_lambda _ fun _ => hXmeas _), h1]
    exact (⟨(hXmeas s).aemeasurable, (hXmeas t).aemeasurable, hlaw⟩ :
      IdentDistrib (X s) (X t) μ μ).integral_eq
  acvf_shift := by
    intro r s h
    have hev : ∀ a b : ℤ, cov[(fun w : Fin 2 → ℝ => w 0), (fun w => w 1);
        μ.map fun ω i => X (![a, b] i) ω] = cov[X a, X b; μ] := by
      intro a b
      rw [covariance_map (measurable_pi_apply 0).aestronglyMeasurable
        (measurable_pi_apply 1).aestronglyMeasurable
        (measurable_pi_lambda _ fun _ => hXmeas _).aemeasurable]
      congr 1
    rw [← hev r s, ← hev (r + h) (s + h)]
    congr 1
    rw [hstat 2 ![r, s] h]
    congr 1
    funext ω i
    fin_cases i <;> simp

/-- **Central limit theorem for a moving average** (Brockwell–Davis Example 6.4.4): for an MA(q) process
`Xₜ = ∑_{j=0}^q θⱼ Z_{t−j}` over centered `L²` i.i.d. (indeed strictly-stationary independent) noise `Z`,
the standardized sample mean `√n X̄ₙ` converges in distribution to `N(0, vₘ)` with `vₘ = ∑_{|h|≤q} γ(h)` —
realized as `√vₘ · G` for a standard normal `G`. The process is `q`-dependent (`isMDependent_movingAverage`),
strictly and weakly stationary, centered and `L²`, so the `m`-dependent CLT `thm_6_4_2` applies. -/
theorem movingAverage_clt {θ : ℕ → ℝ} {q : ℕ} {Z : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {G : Ω' → ℝ}
    (hindep : iIndepFun Z μ) (hZstat : IsStrictlyStationary Z μ) (hmeas : ∀ t, Measurable (Z t))
    (hmem : ∀ t, MemLp (Z t) 2 μ) (hcenter : ∀ t, μ[Z t] = 0) (hG : HasLaw G (gaussianReal 0 1) P') :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n *
        sampleMean n (fun t => movingAverage θ q Z (t : ℤ) ω)) atTop
      (fun ω => Real.sqrt (∑' k : ℤ, acvfStat (movingAverage θ q Z) μ k) • G ω) (fun _ => μ) P' := by
  have hMAstat : IsStrictlyStationary (movingAverage θ q Z) μ :=
    IsStrictlyStationary.movingAverage hmeas hZstat
  exact (isMDependent_movingAverage hindep hmeas).tendstoInDistribution_sqrt_sampleMean hMAstat
    (hMAstat.isWeaklyStationary (measurable_movingAverage hmeas) (memLp_movingAverage hmem))
    (measurable_movingAverage hmeas) (memLp_movingAverage hmem)
    (integral_movingAverage hmem hcenter) hG

/-- **Central limit theorem for a moving average of i.i.d. noise** (Brockwell–Davis Example 6.4.4, as
stated): for an MA(q) process `Xₜ = ∑_{j=0}^q θⱼ Z_{t−j}` over centered `L²` i.i.d. noise `Z`,
`√n X̄ₙ ⇒ N(0, ∑_{|h|≤q} γ(h))`. Same as `movingAverage_clt`, with strict stationarity of the noise
supplied by `iIndepFun.isStrictlyStationary` (i.i.d. ⟹ strictly stationary). -/
theorem movingAverage_clt_iid {θ : ℕ → ℝ} {q : ℕ} {Z : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {G : Ω' → ℝ}
    (hindep : iIndepFun Z μ) (hmeas : ∀ t, Measurable (Z t))
    (hident : ∀ t, IdentDistrib (Z t) (Z 0) μ μ) (hmem : ∀ t, MemLp (Z t) 2 μ)
    (hcenter : ∀ t, μ[Z t] = 0) (hG : HasLaw G (gaussianReal 0 1) P') :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n *
        sampleMean n (fun t => movingAverage θ q Z (t : ℤ) ω)) atTop
      (fun ω => Real.sqrt (∑' k : ℤ, acvfStat (movingAverage θ q Z) μ k) • G ω) (fun _ => μ) P' :=
  movingAverage_clt hindep (iIndepFun.isStrictlyStationary hindep hmeas hident) hmeas hmem hcenter hG

end DeepWiki.TimeSeries
