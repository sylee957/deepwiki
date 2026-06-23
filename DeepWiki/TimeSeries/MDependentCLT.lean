import DeepWiki.TimeSeries.MDependence
import DeepWiki.TimeSeries.SampleMeanVariance

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
