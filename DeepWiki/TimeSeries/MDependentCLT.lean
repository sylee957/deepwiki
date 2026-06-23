import DeepWiki.TimeSeries.MDependence
import DeepWiki.TimeSeries.SampleMeanVariance
import DeepWiki.TimeSeries.MultivariateCLT
import DeepWiki.TimeSeries.SampleMeanCLT
import Mathlib.Probability.IdentDistrib

/-! # Central limit theorem for m-dependent sequences (§6.4, Theorem 6.4.2) — foundations
A bottom-up construction of the `m`-dependent central limit theorem via Bernstein's
big-block/small-block method. This file begins with the foundational bricks: the autocovariance of an
`m`-dependent process vanishes beyond lag `m`, hence is summable, and the long-run variance is the
finite sum `∑_{|h| ≤ m} γ(h)` — the variance the standardized sample mean converges to. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [MeasurableSpace Ω] in
/-- A block sum `∑_{t ∈ C} Xₜ` factors through the tuple `(Xₜ)_{t ∈ A}` over any containing index
set `C ⊆ A`, as the coordinate-sum map composed with that tuple. The plumbing that lets
`IndepFun` of block tuples descend to `IndepFun` of block sums. -/
private theorem blockSum_eq_comp_tuple {C A : Finset ℤ} (hCA : C ⊆ A) (X : ℤ → Ω → ℝ) :
    (fun ω => ∑ t ∈ C, X t ω)
      = (fun v : ↥A → ℝ => ∑ t ∈ C.attach, v ⟨↑t, hCA t.2⟩) ∘
        (fun ω (u : ↥A) => X (↑u) ω) := by
  funext ω
  simp only [Function.comp_apply]
  exact (Finset.sum_attach C (fun t => X t ω)).symm

/-- **m-dependent ⟹ the autocovariance vanishes beyond lag `m`**: for `|k| > m`, `Xₖ` and `X₀` are
independent, so `acvfStat X μ k = cov[Xₖ, X₀] = 0`. -/
theorem acvfStat_eq_zero_of_mDependent {m : ℕ} {X : ℤ → Ω → ℝ} (h : IsMDependent m X μ)
    (hmem : ∀ t, MemLp (X t) 2 μ) {k : ℤ} (hk : (m : ℤ) < |k|) : acvfStat X μ k = 0 := by
  rw [acvfStat_apply]
  rcases lt_or_gt_of_ne (show k ≠ 0 by rintro rfl; rw [abs_zero] at hk; omega) with hneg | hpos
  · rw [abs_of_neg hneg] at hk
    exact (h.indepFun (by omega : k + (m : ℤ) < 0)).covariance_eq_zero (hmem k) (hmem 0)
  · rw [abs_of_pos hpos] at hk
    exact ((h.indepFun (by omega : (0 : ℤ) + (m : ℤ) < k)).symm).covariance_eq_zero
      (hmem k) (hmem 0)

/-- **m-dependent ⟹ summable autocovariance**: the autocovariance is supported on `|h| ≤ m`
(`acvfStat_eq_zero_of_mDependent`), hence summable — so the long-run variance `∑' h, γ(h)` is the
finite sum `∑_{|h| ≤ m} γ(h)`. -/
theorem summable_acvfStat_of_mDependent {m : ℕ} {X : ℤ → Ω → ℝ} (h : IsMDependent m X μ)
    (hmem : ∀ t, MemLp (X t) 2 μ) : Summable (acvfStat X μ) :=
  summable_of_ne_finset_zero (s := Finset.Icc (-(m : ℤ)) m) fun k hk =>
    acvfStat_eq_zero_of_mDependent h hmem (by
      rw [Finset.mem_Icc, not_and_or] at hk
      rcases hk with hk | hk
      · exact lt_abs.mpr (Or.inr (by omega))
      · exact lt_abs.mpr (Or.inl (by omega)))

/-- **Mutual independence of block sums** (the engine of the m-dependent CLT's big-block step): for an
`m`-dependent process and finite index blocks `B₀ < B₁ < ⋯` each separated from the next by more than
`m`, the block sums `∑_{t ∈ Bᵢ} Xₜ` are mutually independent. Proved from one-sided `m`-dependence by
induction on the blocks (peeling the largest): the top block is independent of the union of the
earlier ones — all before it — via `IsMDependent` applied to that union, the earlier block sums
factoring through the union's coordinate tuple. -/
theorem IsMDependent.iIndepFun_blockSum {m : ℕ} {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    (h : IsMDependent m X μ) {ι : Type*} [LinearOrder ι] (B : ι → Finset ℤ)
    (hsep : ∀ i j : ι, i < j → ∀ s ∈ B i, ∀ t ∈ B j, s + (m : ℤ) < t) :
    iIndepFun (fun (i : ι) (ω : Ω) => ∑ t ∈ B i, X t ω) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro sets _; simp
  | insert a s ha ih =>
    intro sets hsets
    have has : a ∉ s := fun h' => lt_irrefl a (ha a h')
    have hsep' : ∀ x ∈ s.biUnion B, ∀ t ∈ B a, x + (m : ℤ) < t := fun x hx t ht => by
      rw [Finset.mem_biUnion] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact hsep i a (ha i hi) x hxi t ht
    have hIndep := h (s.biUnion B) (B a) hsep'
    have hmeas_a : MeasurableSet[MeasurableSpace.comap (fun ω (u : ↥(B a)) => X (↑u) ω) inferInstance]
        ((fun ω => ∑ t ∈ B a, X t ω) ⁻¹' sets a) := by
      rw [blockSum_eq_comp_tuple (Finset.Subset.refl (B a))]
      exact ((Finset.measurable_sum (B a).attach fun t _ =>
        measurable_pi_apply (⟨(↑t : ℤ), Finset.Subset.refl (B a) t.2⟩ : ↥(B a))).comp
        (measurable_iff_comap_le.2 le_rfl)) (hsets a (Finset.mem_insert_self a s))
    have hmeas_s : MeasurableSet[MeasurableSpace.comap
          (fun ω (u : ↥(s.biUnion B)) => X (↑u) ω) inferInstance]
        (⋂ i ∈ s, (fun ω => ∑ t ∈ B i, X t ω) ⁻¹' sets i) := by
      refine MeasurableSet.biInter s.countable_toSet fun i hi => ?_
      rw [blockSum_eq_comp_tuple (Finset.subset_biUnion_of_mem B hi)]
      exact ((Finset.measurable_sum (B i).attach fun t _ =>
        measurable_pi_apply (⟨(↑t : ℤ), Finset.subset_biUnion_of_mem B hi t.2⟩ :
          ↥(s.biUnion B))).comp
        (measurable_iff_comap_le.2 le_rfl)) (hsets i (Finset.mem_insert_of_mem hi))
    obtain ⟨Da, hDa, hDaeq⟩ := MeasurableSpace.measurableSet_comap.1 hmeas_a
    obtain ⟨Ds, hDs, hDseq⟩ := MeasurableSpace.measurableSet_comap.1 hmeas_s
    rw [Finset.set_biInter_insert, Finset.prod_insert has, ← hDaeq, ← hDseq, Set.inter_comm,
      hIndep.measure_inter_preimage_eq_mul Ds Da hDs hDa, hDseq, hDaeq,
      ih fun i hi => hsets i (Finset.mem_insert_of_mem hi), mul_comm]

/-- The `i`-th **big block** of the `(p+m)`-spaced big-block/small-block partition: the size-`p`
window `[i(p+m), i(p+m)+p)`, with a size-`m` gap before the next block. -/
noncomputable def bigBlock (p m i : ℕ) : Finset ℤ :=
  Finset.Ico ((i : ℤ) * ((p : ℤ) + m)) ((i : ℤ) * ((p : ℤ) + m) + p)

/-- **Big blocks are gap-`m` separated**: every index of an earlier big block precedes every index of
a later one by more than `m` (the gap is exactly `m`, so the separation is `m+1 > m`). -/
theorem bigBlock_sep {p m : ℕ} {i j : ℕ} (hij : i < j) :
    ∀ s ∈ bigBlock p m i, ∀ t ∈ bigBlock p m j, s + (m : ℤ) < t := by
  intro s hs t ht
  simp only [bigBlock, Finset.mem_Ico] at hs ht
  have hij' : (i : ℤ) + 1 ≤ j := by exact_mod_cast hij
  nlinarith [mul_le_mul_of_nonneg_right hij' (show (0 : ℤ) ≤ (p : ℤ) + m by positivity),
    hs.1, hs.2, ht.1, ht.2]

/-- **The big-block sums of an m-dependent process are mutually independent**: applying
`iIndepFun_blockSum` to the gap-`m`-separated big blocks. The independence input to the big-block
central limit step. -/
theorem IsMDependent.iIndepFun_bigBlockSum {m : ℕ} {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    (h : IsMDependent m X μ) (p : ℕ) :
    iIndepFun (fun (i : ℕ) (ω : Ω) => ∑ t ∈ bigBlock p m i, X t ω) μ :=
  h.iIndepFun_blockSum (bigBlock p m) fun _ _ hij => bigBlock_sep hij

/-- **Strict stationarity ⟹ a shifted finite-block sum is identically distributed**:
`∑_{t ∈ C} X_{t+c}` has the same law as `∑_{t ∈ C} Xₜ`. The finite-marginal shift-invariance of strict
stationarity (`Fin |C|`-indexed) transported to the subtype-indexed block via `C ≃ Fin |C|`, then
pushed through the coordinate-sum map. -/
theorem IsStrictlyStationary.identDistrib_finsetSum {X : ℤ → Ω → ℝ}
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t)) (C : Finset ℤ) (c : ℤ) :
    IdentDistrib (fun ω => ∑ t ∈ C, X (t + c) ω) (fun ω => ∑ t ∈ C, X t ω) μ μ := by
  set e := C.equivFin with he
  have hR : Measurable (fun v : Fin C.card → ℝ => fun i : ↥C => v (e i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have htuple : IdentDistrib (fun ω (i : ↥C) => X (↑i + c) ω) (fun ω (i : ↥C) => X (↑i) ω) μ μ := by
    refine ⟨(measurable_pi_lambda _ fun (i : ↥C) => hmeas (↑i + c)).aemeasurable,
      (measurable_pi_lambda _ fun (i : ↥C) => hmeas ↑i).aemeasurable, ?_⟩
    have ec : (fun ω (i : ↥C) => X (↑i + c) ω)
        = (fun v : Fin C.card → ℝ => fun i : ↥C => v (e i)) ∘
          (fun ω (j : Fin C.card) => X (↑(e.symm j) + c) ω) := by
      funext ω i; simp only [Function.comp_apply, Equiv.symm_apply_apply]
    have e0 : (fun ω (i : ↥C) => X (↑i) ω)
        = (fun v : Fin C.card → ℝ => fun i : ↥C => v (e i)) ∘
          (fun ω (j : Fin C.card) => X (↑(e.symm j)) ω) := by
      funext ω i; simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [ec, e0, ← Measure.map_map hR (measurable_pi_lambda _ fun j => hmeas _),
      ← Measure.map_map hR (measurable_pi_lambda _ fun j => hmeas _)]
    exact congrArg (Measure.map (fun v : Fin C.card → ℝ => fun i : ↥C => v (e i)))
      (hstat C.card (fun j => ↑(e.symm j)) c).symm
  have hconv : (fun ω => ∑ t ∈ C, X (t + c) ω) = fun ω => ∑ i : ↥C, X (↑i + c) ω := by
    funext ω; exact (Finset.sum_coe_sort C (fun t => X (t + c) ω)).symm
  have hconv0 : (fun ω => ∑ t ∈ C, X t ω) = fun ω => ∑ i : ↥C, X (↑i) ω := by
    funext ω; exact (Finset.sum_coe_sort C (fun t => X t ω)).symm
  rw [hconv, hconv0]
  exact htuple.comp (Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i)

/-- **Big-block sums are identically distributed** (strict stationarity): every big-block sum has the
same law as the first, since `bigBlock i` is `bigBlock 0` shifted by `i(p+m)`. -/
theorem IsStrictlyStationary.identDistrib_bigBlockSum {X : ℤ → Ω → ℝ}
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t)) (p m i : ℕ) :
    IdentDistrib (fun ω => ∑ t ∈ bigBlock p m i, X t ω)
      (fun ω => ∑ t ∈ bigBlock p m 0, X t ω) μ μ := by
  have hshift : (fun ω => ∑ t ∈ bigBlock p m i, X t ω)
      = fun ω => ∑ t ∈ bigBlock p m 0, X (t + (i : ℤ) * ((p : ℤ) + m)) ω := by
    funext ω
    refine Finset.sum_nbij' (fun s => s - (i : ℤ) * ((p : ℤ) + m))
      (fun t => t + (i : ℤ) * ((p : ℤ) + m)) ?_ ?_ ?_ ?_ ?_
    · intro s hs
      simp only [bigBlock, Finset.mem_Ico, Nat.cast_zero, zero_mul, zero_add] at hs ⊢; omega
    · intro t ht
      simp only [bigBlock, Finset.mem_Ico, Nat.cast_zero, zero_mul, zero_add] at ht ⊢; omega
    · intro s _; ring
    · intro t _; ring
    · intro s _; rw [sub_add_cancel]
  rw [hshift]
  exact hstat.identDistrib_finsetSum hmeas (bigBlock p m 0) ((i : ℤ) * ((p : ℤ) + m))

/-- For a weakly stationary process the lag covariance is the autocovariance of the lag difference:
`cov[Xₛ, Xₜ] = γ(s − t)`. -/
theorem IsWeaklyStationary.cov_eq_acvfStat_sub {X : ℤ → Ω → ℝ} (hX : IsWeaklyStationary X μ)
    (s t : ℤ) : cov[X s, X t; μ] = acvfStat X μ (s - t) := by
  rw [acvfStat_apply, hX.acvf_shift s t (-t)]
  simp only [← sub_eq_add_neg, sub_self]

/-- **A general variance bound for a block sum**: for a weakly stationary process with summable
autocovariance, `Var(∑_{t ∈ A} Xₜ) ≤ |A| · ∑_h |γ(h)|`. The analytic input for the small-block (gap)
remainder in the m-dependent CLT: the variance of a sum over any finite set is controlled by its
cardinality times the total absolute autocovariance. -/
theorem variance_finsetSum_le {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ] (hX : IsWeaklyStationary X μ)
    (hsum : Summable (acvfStat X μ)) (A : Finset ℤ) :
    variance (fun ω => ∑ t ∈ A, X t ω) μ ≤ (A.card : ℝ) * ∑' h : ℤ, |acvfStat X μ h| := by
  rw [variance_fun_sum' fun t _ => hX.memLp t]
  have hsa := hsum.abs
  calc ∑ s ∈ A, ∑ t ∈ A, cov[X s, X t; μ]
      ≤ ∑ s ∈ A, ∑ t ∈ A, |acvfStat X μ (s - t)| := by
        gcongr with s _ t _; rw [hX.cov_eq_acvfStat_sub]; exact le_abs_self _
    _ ≤ ∑ s ∈ A, ∑' h : ℤ, |acvfStat X μ h| := by
        gcongr with s _
        have himg : ∑ t ∈ A, |acvfStat X μ (s - t)|
            = ∑ h ∈ A.image (fun t => s - t), |acvfStat X μ h| :=
          (Finset.sum_image (g := fun t => s - t) (f := fun h => |acvfStat X μ h|)
            fun a _ b _ hab => by simp only [] at hab; omega).symm
        rw [himg]
        exact Summable.sum_le_tsum _ (fun h _ => abs_nonneg _) hsa
    _ = (A.card : ℝ) * ∑' h : ℤ, |acvfStat X μ h| := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Block-level central limit theorem** (h1 core): for a strictly stationary, centered, `L²`,
`m`-dependent process, the standardized sum of the first `r` big-block sums has characteristic function
converging to `exp(−Var(U₀)/2)` — applying the iid charFun CLT to the big-block sums `(Uᵢ)`, which are
iid (`iIndepFun_bigBlockSum` + `identDistrib_bigBlockSum`). -/
theorem IsMDependent.tendsto_charFun_bigBlockSum {m : ℕ} {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    (hmdep : IsMDependent m X μ) (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    (hmem : ∀ t, MemLp (X t) 2 μ) (hcenter : ∀ t, μ[X t] = 0) (p : ℕ) :
    Tendsto (fun r : ℕ => charFun (μ.map fun ω =>
        (√r)⁻¹ * ∑ k ∈ Finset.range r, ∑ t ∈ bigBlock p m k, X t ω) 1) atTop
      (𝓝 (Complex.exp (Complex.ofReal
        (-(∫ ω, (∑ t ∈ bigBlock p m 0, X t ω) ^ 2 ∂μ) / 2)))) := by
  have hU0 : MemLp (fun ω => ∑ t ∈ bigBlock p m 0, X t ω) 2 μ :=
    memLp_finsetSum _ fun t _ => hmem t
  refine tendsto_charFun_inv_sqrt_mul_sum_one (hmdep.iIndepFun_bigBlockSum p)
    (fun i => hstat.identDistrib_bigBlockSum hmeas p m i) ?_ hU0.integrable_sq
  rw [integral_finsetSum _ fun t _ => (hmem t).integrable one_le_two]
  simp [hcenter]

/-- **The big-block sums obey a central limit theorem in distribution** (h1, distribution form): for a
strictly stationary `L²` `m`-dependent process, `√r (r⁻¹ ∑_{k<r} U_k − E U₀) ⇒ N(0, Var U₀)`, where
`U_k = ∑_{t ∈ bigBlock k} Xₜ`. A direct application of the iid sample-mean CLT (`iidNoise_sampleMean_clt`)
to the big-block sums, which are iid (`iIndepFun_bigBlockSum` + `identDistrib_bigBlockSum`). -/
theorem IsMDependent.tendstoInDistribution_bigBlockSum {m : ℕ} {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (hmdep : IsMDependent m X μ) (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    (hmem : ∀ t, MemLp (X t) 2 μ) (p : ℕ) {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 Var[fun ω => ∑ t ∈ bigBlock p m 0, X t ω; μ].toNNReal) P') :
    TendstoInDistribution (fun (r : ℕ) ω => Real.sqrt r *
        (sampleMean r (fun k => ∑ t ∈ bigBlock p m k, X t ω)
          - μ[fun ω => ∑ t ∈ bigBlock p m 0, X t ω])) atTop Y (fun _ => μ) P' :=
  iidNoise_sampleMean_clt hY (memLp_finsetSum _ fun t _ => hmem t) (hmdep.iIndepFun_bigBlockSum p)
    fun i => hstat.identDistrib_bigBlockSum hmeas p m i

/-- **The long-run variance of an m-dependent process is the finite sum `∑_{|h| ≤ m} γ(h)`**: the
autocovariance series collapses to lags within the dependence range. -/
theorem tsum_acvfStat_eq_sum_of_mDependent {m : ℕ} {X : ℤ → Ω → ℝ} (h : IsMDependent m X μ)
    (hmem : ∀ t, MemLp (X t) 2 μ) :
    ∑' k : ℤ, acvfStat X μ k = ∑ k ∈ Finset.Icc (-(m : ℤ)) m, acvfStat X μ k :=
  tsum_eq_sum fun k hk =>
    acvfStat_eq_zero_of_mDependent h hmem (by
      rw [Finset.mem_Icc, not_and_or] at hk
      rcases hk with hk | hk
      · exact lt_abs.mpr (Or.inr (by omega))
      · exact lt_abs.mpr (Or.inl (by omega)))

/-- **Variance of the sample mean of an m-dependent process** (the limit the CLT identifies):
`n · Var(X̄ₙ) → ∑_h γ(h) = ∑_{|h| ≤ m} γ(h)`. The summability hypothesis is discharged automatically
by `summable_acvfStat_of_mDependent`; this is the variance `v` of the limiting Gaussian. -/
theorem tendsto_nsmul_variance_sampleMean_of_mDependent {m : ℕ} {X : ℤ → Ω → ℝ}
    [IsProbabilityMeasure μ] (hX : IsWeaklyStationary X μ) (h : IsMDependent m X μ) :
    Tendsto (fun n : ℕ => (n : ℝ) * variance (fun ω => sampleMean n (fun t => X t ω)) μ) atTop
      (𝓝 (∑' k : ℤ, acvfStat X μ k)) :=
  tendsto_nsmul_variance_sampleMean hX (summable_acvfStat_of_mDependent h hX.memLp)

end DeepWiki.TimeSeries
