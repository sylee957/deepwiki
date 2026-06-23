import DeepWiki.TimeSeries.MDependence
import DeepWiki.TimeSeries.SampleMeanVariance
import DeepWiki.TimeSeries.MultivariateCLT
import DeepWiki.TimeSeries.SampleMeanCLT
import DeepWiki.TimeSeries.DeltaMethod
import DeepWiki.TimeSeries.DoubleLimitDistribution
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

/-- **A sum over `Ico 0 p` in `ℤ` is a sum over `range p`** (reindexing `k ↦ ↑k`). Relates the
`ℤ`-indexed first big block `bigBlock 0 = Ico 0 p` to the `ℕ`-indexed sample mean. -/
theorem sum_Ico_zero_int_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (p : ℕ) :
    ∑ t ∈ Finset.Ico (0 : ℤ) (p : ℤ), f t = ∑ k ∈ Finset.range p, f (k : ℤ) := by
  refine Finset.sum_nbij' (fun t => t.toNat) (fun k => (k : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro t ht; simp only [Finset.mem_Ico] at ht; simp only [Finset.mem_range]; omega
  · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Ico]; omega
  · intro t ht; simp only [Finset.mem_Ico] at ht; omega
  · intro k _; simp
  · intro t ht; simp only [Finset.mem_Ico] at ht; congr 1; omega

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

/-- **A big block has exactly `p` elements**: `bigBlock p m i = [i(p+m), i(p+m)+p)` has `p` integers. -/
theorem bigBlock_card (p m i : ℕ) : (bigBlock p m i).card = p := by
  rw [bigBlock, Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast]

/-- **The big blocks are pairwise disjoint** (consequence of gap-`m` separation `bigBlock_sep`). -/
theorem bigBlock_pairwiseDisjoint (p m r : ℕ) :
    (↑(Finset.range r) : Set ℕ).PairwiseDisjoint (bigBlock p m) := by
  intro i _ j _ hij
  simp only [Function.onFun, Finset.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have := bigBlock_sep h x hxi x hxj; omega
  · have := bigBlock_sep h x hxj x hxi; omega

omit [MeasurableSpace Ω] in
/-- **The first big block sum is `p` times the sample mean over `[0,p)`**: `∑_{t∈[0,p)} Xₜ =
p · X̄_p` (the block `bigBlock 0 = [0,p)` reindexed to `range p`). Bridges the block variance to the
sample-mean variance. -/
theorem sum_bigBlock_zero_eq_mul_sampleMean {X : ℤ → Ω → ℝ} (p m : ℕ) (ω : Ω) :
    ∑ t ∈ bigBlock p m 0, X t ω = (p : ℝ) * sampleMean p (fun t => X (t : ℤ) ω) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [bigBlock]
  · rw [bigBlock]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rw [sum_Ico_zero_int_eq_sum_range (fun t => X t ω) p, sampleMean,
      mul_inv_cancel_left₀ (Nat.cast_pos.mpr hp).ne']

/-- **The first big-block-sum variance is `p²` times the sample-mean variance**:
`Var[∑_{t<p} Xₜ] = p² · Var[X̄_p]` (from `sum_bigBlock_zero_eq_mul_sampleMean` and `variance_const_mul`).
This is the numerator of `vₚ = Var[U₀⁽ᵖ⁾]/(p+m)`. -/
theorem variance_bigBlockSum_zero {X : ℤ → Ω → ℝ} (p m : ℕ) :
    Var[fun ω => ∑ t ∈ bigBlock p m 0, X t ω; μ]
      = (p : ℝ) ^ 2 * Var[fun ω => sampleMean p (fun t => X (t : ℤ) ω); μ] := by
  have h : (fun ω => ∑ t ∈ bigBlock p m 0, X t ω)
      = fun ω => (p : ℝ) * sampleMean p (fun t => X (t : ℤ) ω) := by
    funext ω; exact sum_bigBlock_zero_eq_mul_sampleMean p m ω
  rw [h, variance_const_mul]

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

/-- **A deterministic convergent sequence converges in measure to its limit**: if `cₙ → c₀` in `ℝ`
then the constant-in-`ω` sequence `cₙ` converges in measure to `c₀`. The deterministic `√(r(n)/n)`
factor entering the Slutsky-product rescaling of the block CLT. -/
theorem tendstoInMeasure_const_of_tendsto [IsProbabilityMeasure μ] {c : ℕ → ℝ} {c₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) :
    TendstoInMeasure μ (fun n (_ : Ω) => c n) atTop (fun _ => c₀) := by
  intro ε hε
  have hed : Tendsto (fun n => edist (c n) c₀) atTop (𝓝 0) := by
    simpa using hc.edist (tendsto_const_nhds (x := c₀))
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hed.eventually (eventually_lt_nhds hε)] with n hn
  have hset : {ω : Ω | ε ≤ edist (c n) c₀} = ∅ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]; exact hn
  rw [hset, measure_empty]

/-- **Reparametrizing convergence in distribution by an index map**: if `Xᵢ ⇒ Z` along `l` and
`r → l` along `l'`, then `X_{r(i)} ⇒ Z` along `l'` (for a constant measure family). The index change
that turns the block CLT (indexed by the block count) into one indexed by the sample size via
`r(n) → ∞`. -/
theorem tendstoInDistribution_comp_tendsto {ι ι' α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    {l : Filter ι} {l' : Filter ι'} {X : ι → α → E} {Z : β → E} {ν : Measure α}
    [IsProbabilityMeasure ν] {ν' : Measure β} [IsProbabilityMeasure ν']
    (hY : TendstoInDistribution X l Z (fun _ => ν) ν') {r : ι' → ι} (hr : Tendsto r l' l) :
    TendstoInDistribution (fun i => X (r i)) l' Z (fun _ => ν) ν' where
  forall_aemeasurable := fun i => hY.forall_aemeasurable (r i)
  aemeasurable_limit := hY.aemeasurable_limit
  tendsto := hY.tendsto.comp hr

/-- The number of complete big blocks fitting in `[0, n)`: `⌊n/(p+m)⌋`. Each contributes a size-`p`
block, so `blockCount · p` indices are covered by blocks and the rest (`≈ n·m/(p+m)`) are gaps. -/
def blockCount (p m n : ℕ) : ℕ := n / (p + m)

/-- **The first `blockCount p m n` big blocks lie in `[0, n)`**: each `bigBlock p m i` with
`i < n/(p+m)` is contained in `Ico 0 n` (since `(i+1)(p+m) ≤ n`). -/
theorem bigBlock_subset_Ico {p m n i : ℕ} (hi : i < blockCount p m n) :
    bigBlock p m i ⊆ Finset.Ico (0 : ℤ) n := by
  have hpm : 0 < p + m := by
    rcases Nat.eq_zero_or_pos (p + m) with h | h
    · rw [blockCount, h, Nat.div_zero] at hi; exact absurd hi (Nat.not_lt_zero i)
    · exact h
  have hle : (i + 1) * (p + m) ≤ n := (Nat.le_div_iff_mul_le hpm).mp (Nat.succ_le_of_lt hi)
  have hleZ : ((i : ℤ) + 1) * ((p : ℤ) + m) ≤ n := by exact_mod_cast hle
  intro x hx
  simp only [bigBlock, Finset.mem_Ico] at hx ⊢
  refine ⟨le_trans (by positivity) hx.1, lt_of_lt_of_le hx.2 ?_⟩
  nlinarith [hleZ, (by positivity : (0 : ℤ) ≤ (m : ℤ))]

/-- **The gap `[0,n) ∖ ⋃ blocks` has `n − blockCount·p` elements**: the `blockCount` disjoint blocks of
size `p` cover `blockCount·p` indices in `[0,n)`, leaving the rest as the small-block gap. -/
theorem gap_card (p m n : ℕ) :
    (Finset.Ico (0 : ℤ) n \ (Finset.range (blockCount p m n)).biUnion (bigBlock p m)).card
      = n - blockCount p m n * p := by
  have hsub : (Finset.range (blockCount p m n)).biUnion (bigBlock p m) ⊆ Finset.Ico (0 : ℤ) n :=
    Finset.biUnion_subset.mpr fun i hi => bigBlock_subset_Ico (Finset.mem_range.mp hi)
  rw [Finset.card_sdiff_of_subset hsub,
    Finset.card_biUnion (bigBlock_pairwiseDisjoint p m (blockCount p m n))]
  simp only [bigBlock_card, Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [Int.card_Ico, sub_zero, Int.toNat_natCast]

omit [MeasurableSpace Ω] in
/-- **The standardized sample mean minus the gap-removed partial sum is the gap sum**:
`√n X̄ₙ − Y⁽ᵖ⁾ₙ = (√n)⁻¹ · ∑_{t ∈ [0,n) ∖ ⋃ blocks} Xₜ`. Both standardized sums share the `(√n)⁻¹`
factor; their difference collects exactly the small-block (gap) indices, via `√n·n⁻¹ = (√n)⁻¹`,
`sum_biUnion` (disjoint blocks), and `sum_sdiff` (blocks `⊆ [0,n)`). -/
theorem sqrt_sampleMean_sub_gapRemoved {X : ℤ → Ω → ℝ} (p m n : ℕ) (ω : Ω) :
    Real.sqrt n * sampleMean n (fun t => X (t : ℤ) ω)
      - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range (blockCount p m n), ∑ t ∈ bigBlock p m i, X t ω
    = (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.Ico (0 : ℤ) n \
        (Finset.range (blockCount p m n)).biUnion (bigBlock p m), X t ω := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Real.sqrt_zero, sampleMean]
  · have hsub : (Finset.range (blockCount p m n)).biUnion (bigBlock p m) ⊆ Finset.Ico (0 : ℤ) n :=
      Finset.biUnion_subset.mpr fun i hi => bigBlock_subset_Ico (Finset.mem_range.mp hi)
    have hsqp : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
    have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
    have hsm : Real.sqrt n * sampleMean n (fun t => X (t : ℤ) ω)
        = (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.Ico (0 : ℤ) n, X t ω := by
      rw [sampleMean, ← sum_Ico_zero_int_eq_sum_range (fun t => X t ω) n, ← mul_assoc]
      congr 1
      rw [← div_eq_mul_inv, eq_comm, inv_eq_one_div, div_eq_div_iff hsqp.ne' hn0.ne', one_mul,
        Real.mul_self_sqrt hn0.le]
    rw [hsm, ← Finset.sum_biUnion (bigBlock_pairwiseDisjoint p m (blockCount p m n)), ← mul_sub]
    congr 1
    rw [← Finset.sum_sdiff hsub]
    ring

/-- **The gap-remainder variance is `≤ (|gap|/n)·∑|γ|`**: `Var[√n X̄ₙ − Y⁽ᵖ⁾ₙ] ≤ ((n−blockCount·p)/n)·∑|γ|`.
The difference is `(√n)⁻¹·∑_{gap} X` (`sqrt_sampleMean_sub_gapRemoved`), so its variance is `n⁻¹` times the
gap-sum variance, bounded by `|gap|·∑|γ|` (`variance_finsetSum_le`) with `|gap| = n−blockCount·p`. -/
theorem variance_sqrt_sampleMean_sub_gapRemoved_le {m : ℕ} {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    (hX : IsWeaklyStationary X μ) (hsum : Summable (acvfStat X μ)) (p n : ℕ) :
    variance (fun ω => Real.sqrt n * sampleMean n (fun t => X (t : ℤ) ω)
      - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range (blockCount p m n), ∑ t ∈ bigBlock p m i, X t ω) μ
    ≤ ((n - blockCount p m n * p : ℕ) : ℝ) / n * ∑' h : ℤ, |acvfStat X μ h| := by
  rw [funext fun ω => sqrt_sampleMean_sub_gapRemoved p m n ω, variance_const_mul, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg n)]
  have hvar := variance_finsetSum_le hX hsum
    (Finset.Ico (0 : ℤ) n \ (Finset.range (blockCount p m n)).biUnion (bigBlock p m))
  rw [gap_card] at hvar
  exact le_trans (mul_le_mul_of_nonneg_left hvar (by positivity)) (le_of_eq (by ring))

/-- **The gap remainder `√n X̄ₙ − Y⁽ᵖ⁾ₙ` is `L²`** (a finite linear combination of the `L²` variables
`Xₜ`, via the difference identity). -/
theorem memLp_sqrt_sampleMean_sub_gapRemoved {m : ℕ} {X : ℤ → Ω → ℝ} (hmem : ∀ t, MemLp (X t) 2 μ)
    (p n : ℕ) :
    MemLp (fun ω => Real.sqrt n * sampleMean n (fun t => X (t : ℤ) ω)
      - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range (blockCount p m n), ∑ t ∈ bigBlock p m i, X t ω) 2 μ := by
  rw [funext fun ω => sqrt_sampleMean_sub_gapRemoved p m n ω]
  exact (memLp_finsetSum _ (fun t _ => hmem t)).const_mul _

/-- **The gap remainder `√n X̄ₙ − Y⁽ᵖ⁾ₙ` is centered** (mean `0`, from the centering of `X`). -/
theorem integral_sqrt_sampleMean_sub_gapRemoved {m : ℕ} {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    (hmem : ∀ t, MemLp (X t) 2 μ) (hcenter : ∀ t, μ[X t] = 0) (p n : ℕ) :
    μ[fun ω => Real.sqrt n * sampleMean n (fun t => X (t : ℤ) ω)
      - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range (blockCount p m n), ∑ t ∈ bigBlock p m i, X t ω] = 0 := by
  rw [funext fun ω => sqrt_sampleMean_sub_gapRemoved p m n ω, integral_const_mul,
    integral_finsetSum _ (fun t _ => (hmem t).integrable one_le_two)]
  simp [hcenter]

/-- **The number of big blocks tends to infinity**: `blockCount p m n → ∞` as `n → ∞` (for a positive
block-plus-gap length). The index reparametrization that turns the block CLT (in the block count `r`)
into a statement about the sample size `n`. -/
theorem tendsto_blockCount {p m : ℕ} (hpm : p + m ≠ 0) :
    Tendsto (fun n => blockCount p m n) atTop atTop :=
  Nat.tendsto_div_const_atTop hpm

/-- **Asymptotic block density**: `r(n)/n → 1/(p+m)` — the fraction of the sample covered by complete
big blocks. The deterministic factor in the `√(r(n)/n)` Slutsky rescaling of the block CLT, and what
sends the gap fraction `m/(p+m) → 0` as `p → ∞` (the small-block remainder). -/
theorem tendsto_blockCount_div {p m : ℕ} (hpm : p + m ≠ 0) :
    Tendsto (fun n : ℕ => (blockCount p m n : ℝ) / n) atTop (𝓝 (1 / ((p + m : ℕ) : ℝ))) := by
  have hpos : 0 < p + m := Nat.pos_of_ne_zero hpm
  have hpmR : (0 : ℝ) < ((p + m : ℕ) : ℝ) := by exact_mod_cast hpos
  have herr : Tendsto (fun n : ℕ => ((n % (p + m) : ℕ) : ℝ) / (((p + m : ℕ) : ℝ) * n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (g := fun n : ℕ => 1 / (n : ℝ)) (fun n => ?_)
      tendsto_one_div_atTop_nhds_zero_nat
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      calc ((n % (p + m) : ℕ) : ℝ) / (((p + m : ℕ) : ℝ) * n)
          ≤ ((p + m : ℕ) : ℝ) / (((p + m : ℕ) : ℝ) * n) := by
            gcongr; exact_mod_cast (Nat.mod_lt n hpos).le
        _ = 1 / (n : ℝ) := by field_simp
  have hlim : Tendsto (fun n : ℕ => 1 / ((p + m : ℕ) : ℝ)
      - ((n % (p + m) : ℕ) : ℝ) / (((p + m : ℕ) : ℝ) * n)) atTop (𝓝 (1 / ((p + m : ℕ) : ℝ))) := by
    simpa using tendsto_const_nhds.sub herr
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (n : ℝ) = ((p + m : ℕ) : ℝ) * ((blockCount p m n : ℕ) : ℝ) + ((n % (p + m) : ℕ) : ℝ) := by
    rw [blockCount]; exact_mod_cast (Nat.div_add_mod n (p + m)).symm
  rw [blockCount] at hc ⊢
  field_simp
  nlinarith [hc]

/-- **The Slutsky rescaling factor converges**: `√(r(n)/n) → 1/√(p+m)`. Composing `Real.sqrt`
(continuous) with the block density `tendsto_blockCount_div`; the factor relating the `√r`-scaled block
CLT statistic to the `√n`-scaled gap-removed partial sum. -/
theorem tendsto_sqrt_blockCount_div {p m : ℕ} (hpm : p + m ≠ 0) :
    Tendsto (fun n : ℕ => Real.sqrt ((blockCount p m n : ℝ) / n)) atTop
      (𝓝 (1 / Real.sqrt ((p + m : ℕ) : ℝ))) := by
  have h : (1 : ℝ) / Real.sqrt ((p + m : ℕ) : ℝ) = Real.sqrt (1 / ((p + m : ℕ) : ℝ)) := by
    rw [one_div, ← Real.sqrt_inv, one_div]
  rw [h]
  exact (Real.continuous_sqrt.tendsto _).comp (tendsto_blockCount_div hpm)

/-- **The gap fraction tends to `m/(p+m)`**: `(n − blockCount·p)/n → m/(p+m)` as `n → ∞`. Writing the
fraction as `1 − p·(blockCount/n)`, the block density `blockCount/n → 1/(p+m)` (`tendsto_blockCount_div`)
gives `1 − p/(p+m) = m/(p+m)`. This shrinking gap fraction makes the small-block remainder vanish. -/
theorem tendsto_gapFraction {p m : ℕ} (hpm : p + m ≠ 0) :
    Tendsto (fun n : ℕ => ((n - blockCount p m n * p : ℕ) : ℝ) / n) atTop
      (𝓝 ((m : ℝ) / ((p + m : ℕ) : ℝ))) := by
  have hlim : Tendsto (fun n : ℕ => 1 - (p : ℝ) * ((blockCount p m n : ℝ) / n)) atTop
      (𝓝 (1 - (p : ℝ) * (1 / ((p + m : ℕ) : ℝ)))) :=
    tendsto_const_nhds.sub ((tendsto_blockCount_div hpm).const_mul (p : ℝ))
  have hcast : ((p + m : ℕ) : ℝ) = (p : ℝ) + m := by push_cast; ring
  have hne : (p : ℝ) + m ≠ 0 := hcast ▸ Nat.cast_ne_zero.mpr hpm
  have heq : (1 : ℝ) - (p : ℝ) * (1 / ((p + m : ℕ) : ℝ)) = (m : ℝ) / ((p + m : ℕ) : ℝ) := by
    rw [hcast, mul_one_div]; field_simp; ring
  rw [← heq]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hle : blockCount p m n * p ≤ n := by
    calc blockCount p m n * p ≤ blockCount p m n * (p + m) := by gcongr; omega
      _ = n / (p + m) * (p + m) := rfl
      _ ≤ n := Nat.div_mul_le_self n (p + m)
  rw [Nat.cast_sub hle, Nat.cast_mul]
  field_simp

/-- **A big-block sum of a centered process is centered**: `E[∑_{t ∈ bigBlock 0} Xₜ] = 0`. Lets the
block CLT statistic `√r(X̄ᵤ − E U₀)` drop its mean-subtraction to `(√r)⁻¹ ∑ Uᵢ` in the h1 reparametrization. -/
theorem integral_bigBlockSum_eq_zero [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmem : ∀ t, MemLp (X t) 2 μ) (hcenter : ∀ t, μ[X t] = 0) (p m : ℕ) :
    μ[fun ω => ∑ t ∈ bigBlock p m 0, X t ω] = 0 := by
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

/-- **h1 — the gap-removed big-block partial sum obeys the block CLT**: for a strictly stationary
centered `L²` `m`-dependent process, `Y⁽ᵖ⁾ₙ = (√n)⁻¹ ∑_{i<r(n)} ∑_{t∈bigBlock i} Xₜ ⇒ (1/√(p+m)) Y`,
where `Y ~ N(0, Var U₀)` (so the limit has variance `vₚ = Var U₀/(p+m)`). Reparametrizes the block
CLT by `r(n) = ⌊n/(p+m)⌋ → ∞`, then applies the deterministic `√(r/n) → 1/√(p+m)` Slutsky factor; the
`√` algebra `√(r/n)·√r·r⁻¹ = (√n)⁻¹` reconciles the statistic with `Y⁽ᵖ⁾ₙ` (centering drops `E U₀`). -/
theorem IsMDependent.tendstoInDistribution_gapRemoved {m : ℕ} {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (hmdep : IsMDependent m X μ) (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    (hmem : ∀ t, MemLp (X t) 2 μ) (hcenter : ∀ t, μ[X t] = 0) {p : ℕ} (hp : 0 < p) {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 Var[fun ω => ∑ t ∈ bigBlock p m 0, X t ω; μ].toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹
        * ∑ i ∈ Finset.range (blockCount p m n), ∑ t ∈ bigBlock p m i, X t ω) atTop
      (fun ω => 1 / Real.sqrt ((p + m : ℕ) : ℝ) * Y ω) (fun _ => μ) P' := by
  have hpm : p + m ≠ 0 := by omega
  have hc0 : μ[fun ω => ∑ t ∈ bigBlock p m 0, X t ω] = 0 :=
    integral_bigBlockSum_eq_zero hmem hcenter p m
  have hrep := tendstoInDistribution_comp_tendsto
    (hmdep.tendstoInDistribution_bigBlockSum hstat hmeas hmem p hY) (tendsto_blockCount hpm)
  have hslut := hrep.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun ab : ℝ × ℝ => ab.2 * ab.1) (by fun_prop)
    (tendstoInMeasure_const_of_tendsto (tendsto_sqrt_blockCount_div hpm)) (fun _ => aemeasurable_const)
  have hstat_eq : (fun (n : ℕ) ω => (Real.sqrt n)⁻¹
        * ∑ i ∈ Finset.range (blockCount p m n), ∑ t ∈ bigBlock p m i, X t ω)
      = fun n ω => Real.sqrt ((blockCount p m n : ℝ) / n)
        * (Real.sqrt (blockCount p m n)
          * (sampleMean (blockCount p m n) (fun k => ∑ t ∈ bigBlock p m k, X t ω)
            - μ[fun ω => ∑ t ∈ bigBlock p m 0, X t ω])) := by
    funext n ω
    rw [hc0, sub_zero, sampleMean]
    rcases Nat.eq_zero_or_pos (blockCount p m n) with hr | hr
    · simp [hr]
    · have hrR : (0 : ℝ) < blockCount p m n := by exact_mod_cast hr
      rw [Real.sqrt_div hrR.le]
      field_simp
      rw [Real.sq_sqrt hrR.le]
  rw [hstat_eq]
  exact hslut

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

/-- **The big-block variance `vₚ = Var[U₀⁽ᵖ⁾]/(p+m)` converges to `v = ∑_h γ(h)`** as `p → ∞`.
Writing `vₚ = (p · Var[X̄_p]) · (p/(p+m))`, the first factor tends to `∑_h γ(h)`
(`tendsto_nsmul_variance_sampleMean_of_mDependent`) and the gap-shrinking factor `p/(p+m) → 1`.
This is the limiting variance of the gap-removed CLT, and the input to the `Wₚ ⇒ Z` Gaussian step. -/
theorem tendsto_variance_bigBlockSum_div_of_mDependent {m : ℕ} {X : ℤ → Ω → ℝ}
    [IsProbabilityMeasure μ] (hX : IsWeaklyStationary X μ) (h : IsMDependent m X μ) :
    Tendsto (fun p : ℕ => Var[fun ω => ∑ t ∈ bigBlock p m 0, X t ω; μ] / (p + m : ℝ)) atTop
      (𝓝 (∑' k : ℤ, acvfStat X μ k)) := by
  have ha := tendsto_nsmul_variance_sampleMean_of_mDependent hX h
  have hd : Tendsto (fun p : ℕ => (p : ℝ) + m) atTop atTop :=
    tendsto_atTop_add_const_right atTop (m : ℝ) tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun p : ℕ => (p : ℝ) / (p + m : ℝ)) atTop (𝓝 1) := by
    have hsub : Tendsto (fun p : ℕ => 1 - (m : ℝ) / (p + m)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hd)
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hpm : (p : ℝ) + m ≠ 0 := by positivity
    field_simp
    ring
  have hmain := ha.mul hr
  rw [mul_one] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with p hp
  rw [variance_bigBlockSum_zero]
  have hpm : (p : ℝ) + m ≠ 0 := by positivity
  field_simp

/-- **The Gaussian limits `Wₚ = √vₚ · G` converge in distribution to `Z = √v · G`** as `p → ∞`,
where `G` is a standard normal (`h2` of the double-limit theorem). Since `vₚ → v`, the scale factors
`√vₚ → √v` (continuity of `√`), and `tendstoInDistribution_const_smul_of_tendsto` transports this to the
scaled Gaussians. Realizing the whole `N(0,vₚ)` family as scalings of one fixed `G` puts them on a common
probability space, as the double-limit assembly requires. -/
theorem tendstoInDistribution_gaussianFamily_of_mDependent {m : ℕ} {X : ℤ → Ω → ℝ}
    [IsProbabilityMeasure μ] (hX : IsWeaklyStationary X μ) (h : IsMDependent m X μ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {G : Ω' → ℝ} (hG : AEMeasurable G P') :
    TendstoInDistribution
      (fun p ω => Real.sqrt (Var[fun ω => ∑ t ∈ bigBlock p m 0, X t ω; μ] / (p + m : ℝ)) • G ω) atTop
      (fun ω => Real.sqrt (∑' k : ℤ, acvfStat X μ k) • G ω) (fun _ => P') P' :=
  tendstoInDistribution_const_smul_of_tendsto
    ((Real.continuous_sqrt.tendsto _).comp (tendsto_variance_bigBlockSum_div_of_mDependent hX h)) hG

/-- **The gap-removed partial sum `Y⁽ᵖ⁾ₙ` converges in distribution to `Wₚ = √vₚ · G`** (`h1` of the
double-limit theorem, with the limit realized on the common `G`-space). Instantiating
`tendstoInDistribution_gapRemoved` with `Yₚ = √(Var[U₀⁽ᵖ⁾]) · G ~ N(0, Var[U₀⁽ᵖ⁾])`
(`gaussianReal_const_mul`), its limit `(1/√(p+m)) · √(Var[U₀⁽ᵖ⁾]) · G` equals `√(Var[U₀⁽ᵖ⁾]/(p+m)) · G`
by `√(a/b) = √a/√b` — matching exactly the `Wₚ` of `tendstoInDistribution_gaussianFamily_of_mDependent`. -/
theorem IsMDependent.tendstoInDistribution_gapRemoved_smul {m : ℕ} {X : ℤ → Ω → ℝ}
    [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] (hmdep : IsMDependent m X μ) (hstat : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) (hmem : ∀ t, MemLp (X t) 2 μ) (hcenter : ∀ t, μ[X t] = 0)
    {p : ℕ} (hp : 0 < p) {G : Ω' → ℝ} (hG : HasLaw G (gaussianReal 0 1) P') :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹
        * ∑ i ∈ Finset.range (blockCount p m n), ∑ t ∈ bigBlock p m i, X t ω) atTop
      (fun ω => Real.sqrt (Var[fun ω => ∑ t ∈ bigBlock p m 0, X t ω; μ] / (p + m : ℝ)) • G ω)
      (fun _ => μ) P' := by
  set V := Var[fun ω => ∑ t ∈ bigBlock p m 0, X t ω; μ] with hV
  have hVnn : 0 ≤ V := variance_nonneg _ _
  have hY : HasLaw (fun ω => Real.sqrt V * G ω) (gaussianReal 0 V.toNNReal) P' := by
    have h := gaussianReal_const_mul hG (Real.sqrt V)
    rw [mul_zero] at h
    convert h using 2
    rw [mul_one]
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ hVnn, NNReal.coe_mk, Real.sq_sqrt hVnn]
  have hmain := hmdep.tendstoInDistribution_gapRemoved hstat hmeas hmem hcenter hp hY
  have heq : (fun ω => Real.sqrt (V / (p + m : ℝ)) • G ω)
      = fun ω => 1 / Real.sqrt ((p + m : ℕ) : ℝ) * (Real.sqrt V * G ω) := by
    funext ω
    rw [smul_eq_mul, Real.sqrt_div hVnn]
    push_cast
    ring
  rw [heq]
  exact hmain

/-- **A Lévy–Prokhorov distance bound from an `L²` bound** (general form): if `f − g` has `L²` norm
`≤ B` and `B ≤ δ·√δ`, then the laws of `f` and `g` are within `δ` in Lévy–Prokhorov distance.
Chebyshev (`meas_ge_le_mul_pow_eLpNorm_enorm`) on the `L²` bound controls the tail `μ{δ ≤ |f−g|}`,
fed to the in-measure ⟹ Lévy–Prokhorov estimate `levyProkhorovEDist_map_le`. The general engine for the
double-limit approximation hypothesis `h3`. -/
theorem levyProkhorovDist_le_of_eLpNorm_le [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {B δ : ℝ} (hB0 : 0 ≤ B)
    (hδ : 0 < δ) (heLp : eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal B) (hm : B ≤ δ * Real.sqrt δ) :
    levyProkhorovDist (μ.map f) (μ.map g) ≤ δ := by
  have hcheb : μ {ω | δ ≤ dist (f ω) (g ω)} ≤ ENNReal.ofReal δ := by
    have hset : {ω | δ ≤ dist (f ω) (g ω)} = {ω | ENNReal.ofReal δ ≤ ‖(f - g) ω‖ₑ} := by
      ext ω
      simp only [Set.mem_setOf_eq, Pi.sub_apply, Real.dist_eq, ← Real.norm_eq_abs, ← ofReal_norm]
      exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).symm
    rw [hset]
    refine le_trans (meas_ge_le_mul_pow_eLpNorm_enorm μ two_ne_zero ENNReal.ofNat_ne_top
      (hf.sub hg) (ENNReal.ofReal_pos.mpr hδ).ne'
      (fun h => absurd h ENNReal.ofReal_ne_top)) ?_
    rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.rpow_natCast]
    calc (ENNReal.ofReal δ)⁻¹ ^ 2 * eLpNorm (f - g) 2 μ ^ 2
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
    (le_trans (levyProkhorovEDist_map_le f g hf.aemeasurable hg.aemeasurable hδ)
      (sup_le le_rfl hcheb))).trans_eq (ENNReal.toReal_ofReal hδ.le)

/-- **A Lévy–Prokhorov distance bound from a variance bound** (centered case): if `f − g` is centered
with `variance ≤ δ³`, then the laws of `f` and `g` are within `δ` in Lévy–Prokhorov distance. The
variance-form Chebyshev inequality `meas_ge_le_variance_div_sq` controls `μ{δ ≤ |f−g|} ≤ Var/δ² ≤ δ`,
fed to `levyProkhorovEDist_map_le`. The engine for `h3` of the m-dependent CLT, where the gap-sum
variance bound comes straight from `variance_finsetSum_le`. -/
theorem levyProkhorovDist_le_of_variance_le [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfg : MemLp (f - g) 2 μ) (hc : μ[f - g] = 0)
    {δ : ℝ} (hδ : 0 < δ) (hvar : variance (f - g) μ ≤ δ ^ 3) :
    levyProkhorovDist (μ.map f) (μ.map g) ≤ δ := by
  have hcheb : μ {ω | δ ≤ dist (f ω) (g ω)} ≤ ENNReal.ofReal δ := by
    have hset : {ω | δ ≤ dist (f ω) (g ω)} = {ω | δ ≤ |(f - g) ω - μ[f - g]|} := by
      rw [hc]; ext ω; simp only [Set.mem_setOf_eq, Pi.sub_apply, Real.dist_eq, sub_zero]
    rw [hset]
    refine le_trans (meas_ge_le_variance_div_sq hfg hδ) (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hvar]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (le_trans (levyProkhorovEDist_map_le f g hf hg hδ) (sup_le le_rfl hcheb))).trans_eq
    (ENNReal.toReal_ofReal hδ.le)

end DeepWiki.TimeSeries
