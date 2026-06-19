import DeepWiki.NetworkCalculus.ServersResidualPriority

/-! # Non-preemptive static-priority residual service
A packet server cannot interrupt a packet in service: under
non-preemptive static priority, while the priority-`≤ i` flows are
backlogged, the strictly lower flows still serve — but at most one
maximal packet. With a left-continuous strict aggregate curve `β` (the
same repair as preemptive static priority) and arrival curves on the
higher-priority flows, flow `i` receives the min-plus residual
`[β − ∑_{j<i} αⱼ − max_{j>i} ℓⱼᵘ]⁺↑`: the preemptive residual, one
maximal lower-priority packet cheaper. Under packet exclusivity it
also receives `[β − ∑_{j<i} αⱼ − max_{j≥i} ℓⱼᵘ]⁺↑` as a strict
service curve — the blocking packet may then be of the flow's own
priority class. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Set Topology Filter

/-- **Non-preemptive static priority**: while the priority-`≤ i`
aggregate is backlogged throughout the closed `[s, t]`, the strictly
lower flows jointly serve at most one maximal packet on `(s, t]`
(`j < i` means `j` has higher priority, `lmax j` is flow `j`'s maximal
packet size). -/
def IsNpsp {ι : Type*} [Fintype ι] [LinearOrder ι] (lmax : ι → ℝ≥0)
    (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i : ι, ∀ s t : ℝ≥0, s ≤ t →
    (∀ u ∈ Set.Icc s t,
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), D j u)
        < ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), A j u) →
    (∑ j ∈ Finset.univ.filter (fun j => i < j), D j t)
      ≤ (∑ j ∈ Finset.univ.filter (fun j => i < j), D j s)
        + (Finset.univ.filter (fun j => i < j)).sup lmax

/-- A preemptive static-priority family is non-preemptive for every
packet bound: while the `≤ i` aggregate is backlogged, the strictly
lower flows are frozen outright, so they serve nothing at all. -/
theorem IsStaticPriority.isNpsp {ι : Type*} [Fintype ι] [LinearOrder ι]
    {A D : ι → ℝ≥0 → ℝ≥0} (h : IsStaticPriority A D)
    (hc : ∀ j x, D j x ≤ A j x) (lmax : ι → ℝ≥0) :
    IsNpsp lmax A D := by
  intro i s t hst hbl
  have hfreeze : ∀ k ∈ Finset.univ.filter (fun j => i < j),
      D k t = D k s := by
    intro k hk
    have hik : i < k := (Finset.mem_filter.mp hk).2
    refine h k s t hst fun u hu => ?_
    have hsub : Finset.univ.filter (fun j => j ≤ i)
        ⊆ Finset.univ.filter (fun j => j < k) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        lt_of_le_of_lt (Finset.mem_filter.mp hj).2 hik⟩
    calc (∑ j ∈ Finset.univ.filter (fun j => j < k), D j u)
        = (∑ j ∈ Finset.univ.filter (fun j => j < k)
            \ Finset.univ.filter (fun j => j ≤ i), D j u)
          + ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), D j u :=
          (Finset.sum_sdiff hsub).symm
      _ < (∑ j ∈ Finset.univ.filter (fun j => j < k)
            \ Finset.univ.filter (fun j => j ≤ i), A j u)
          + ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), A j u :=
          add_lt_add_of_le_of_lt
            (Finset.sum_le_sum fun j _ => hc j u) (hbl u hu)
      _ = ∑ j ∈ Finset.univ.filter (fun j => j < k), A j u :=
          Finset.sum_sdiff hsub
  calc (∑ j ∈ Finset.univ.filter (fun j => i < j), D j t)
      = ∑ j ∈ Finset.univ.filter (fun j => i < j), D j s :=
        Finset.sum_congr rfl hfreeze
    _ ≤ (∑ j ∈ Finset.univ.filter (fun j => i < j), D j s)
        + (Finset.univ.filter (fun j => i < j)).sup lmax :=
        le_self_add

/-- **Packet exclusivity**: with the strictly-higher aggregate
backlogged throughout the closed `[u, s]` and flow `i` backlogged on
`(s, t]`, flow `i`'s service since `u` and the strictly lower flows'
service since `u` jointly amount to at most one maximal packet of
priority `≥ i` — at most one such packet was already in service at
`u`, and the server never preempts it. (No `u ≤ s` is required: past
`s` the closed-interval premise is vacuous and the bound still holds
on the backlogged window.) -/
def IsNpspExclusive {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lmax : ι → ℝ≥0) (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i : ι, ∀ u s t : ℝ≥0, s ≤ t →
    (∀ v ∈ Set.Icc u s,
      (∑ j ∈ Finset.univ.filter (fun j => j < i), D j v)
        < ∑ j ∈ Finset.univ.filter (fun j => j < i), A j v) →
    (∀ v ∈ Set.Ioc s t, D i v < A i v) →
    D i s + (∑ j ∈ Finset.univ.filter (fun j => i < j), D j t)
      ≤ (D i u + ∑ j ∈ Finset.univ.filter (fun j => i < j), D j u)
        + (Finset.univ.filter (fun j => i ≤ j)).sup lmax

/-- **NP-SP `n`-server**: every served family obeys the non-preemptive
priority bound and the packet exclusivity. -/
def IsNpspServerN {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lmax : ι → ℝ≥0)
    (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ As Ds, S As Ds →
    IsNpsp lmax (fun j => ⇑(As j)) (fun j => ⇑(Ds j))
      ∧ IsNpspExclusive lmax (fun j => ⇑(As j)) (fun j => ⇑(Ds j))

/-- A preemptive static-priority family of monotone flows satisfies
packet exclusivity for every packet bound: flow `i` and the strictly
lower flows are all frozen on the relevant windows, so the coupled
service is zero. -/
theorem IsStaticPriority.isNpspExclusive {ι : Type*} [Fintype ι]
    [LinearOrder ι] {A D : ι → ℝ≥0 → ℝ≥0} (h : IsStaticPriority A D)
    (hc : ∀ j x, D j x ≤ A j x) (hmono : ∀ j, Monotone (D j))
    (lmax : ι → ℝ≥0) : IsNpspExclusive lmax A D := by
  intro i u s t hst hicc hibl
  -- the `< k` aggregates are backlogged wherever `< i` is or flow `i` is
  have hklt : ∀ k, i < k → ∀ v, (v ∈ Set.Icc u s ∨ v ∈ Set.Ioc s t) →
      (∑ j ∈ Finset.univ.filter (fun j => j < k), D j v)
        < ∑ j ∈ Finset.univ.filter (fun j => j < k), A j v := by
    intro k hik v hv
    rcases hv with hv | hv
    · have hsub : Finset.univ.filter (fun j => j < i)
          ⊆ Finset.univ.filter (fun j => j < k) := by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
          lt_trans (Finset.mem_filter.mp hj).2 hik⟩
      calc (∑ j ∈ Finset.univ.filter (fun j => j < k), D j v)
          = (∑ j ∈ Finset.univ.filter (fun j => j < k)
              \ Finset.univ.filter (fun j => j < i), D j v)
            + ∑ j ∈ Finset.univ.filter (fun j => j < i), D j v :=
            (Finset.sum_sdiff hsub).symm
        _ < (∑ j ∈ Finset.univ.filter (fun j => j < k)
              \ Finset.univ.filter (fun j => j < i), A j v)
            + ∑ j ∈ Finset.univ.filter (fun j => j < i), A j v :=
            add_lt_add_of_le_of_lt
              (Finset.sum_le_sum fun j _ => hc j v) (hicc v hv)
        _ = ∑ j ∈ Finset.univ.filter (fun j => j < k), A j v :=
            Finset.sum_sdiff hsub
    · exact Finset.sum_lt_sum (fun j _ => hc j v)
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hik⟩, hibl v hv⟩
  rcases le_or_gt u s with hus | hus
  · -- flow `i` frozen on `[u, s]`, lower flows frozen on `[u, t]`
    have hDi : D i s = D i u := h i u s hus fun v hv => hicc v hv
    have hDk : ∀ k ∈ Finset.univ.filter (fun j => i < j),
        D k t = D k u := by
      intro k hk
      have hik := (Finset.mem_filter.mp hk).2
      refine h k u t (hus.trans hst) fun v hv => ?_
      rcases le_or_gt v s with hvs | hvs
      · exact hklt k hik v (Or.inl ⟨hv.1, hvs⟩)
      · exact hklt k hik v (Or.inr ⟨hvs, hv.2⟩)
    rw [hDi, Finset.sum_congr rfl hDk]
    exact le_self_add
  · rcases le_or_gt u t with hut | hut
    · -- past `s`: flow `i` by monotonicity, lower flows frozen on `[u, t]`
      have hDk : ∀ k ∈ Finset.univ.filter (fun j => i < j),
          D k t = D k u := by
        intro k hk
        have hik := (Finset.mem_filter.mp hk).2
        refine h k u t hut fun v hv => ?_
        exact hklt k hik v (Or.inr ⟨lt_of_lt_of_le hus hv.1, hv.2⟩)
      rw [Finset.sum_congr rfl hDk]
      exact le_trans (add_le_add (hmono i hus.le) le_rfl) le_self_add
    · -- everything by monotonicity
      refine le_trans (add_le_add (hmono i (hst.trans hut.le))
        (Finset.sum_le_sum fun k _ => hmono k hut.le)) le_self_add

/-- A preemptive static-priority `n`-server is an NP-SP `n`-server for
every packet bound. -/
theorem IsStaticPriorityServerN.isNpspServerN {ι : Type*} [Fintype ι]
    [LinearOrder ι] {S : (ι → Curve) → (ι → Curve) → Prop}
    (hSP : IsStaticPriorityServerN S) (hcaus : IsCausalN S)
    (lmax : ι → ℝ≥0) : IsNpspServerN lmax S := fun As Ds hp =>
  ⟨(hSP As Ds hp).isNpsp (fun j x => hcaus As Ds hp j x) lmax,
    (hSP As Ds hp).isNpspExclusive (fun j x => hcaus As Ds hp j x)
      (fun j => (Ds j).mono) lmax⟩

/-- **Non-preemptive static-priority residual** (min-plus): under NP-SP
with a left-continuous strict aggregate curve `β` and `αⱼ`-constrained
higher-priority arrivals, flow `i` is served at
`[β − ∑_{j<i} αⱼ − max_{j>i} ℓⱼᵘ]⁺↑`. The proof anchors just inside
the `≤ i` busy period — which is exactly what the closed-interval
non-preemption bound needs — and passes `β` through its left limit. -/
theorem minConv_residualCurve_le_of_isNpsp {ι : Type*} [Fintype ι]
    [LinearOrder ι] {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {lmax : ι → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hβlc : IsLeftContinuous β)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    (hnp : IsNpsp lmax (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {i : ι} (harr : ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (Deviation.liftENN (residualCurve β (fun v =>
          (∑ j ∈ Finset.univ.filter (fun j => j < i), α j v)
            + (Finset.univ.filter (fun j => i < j)).sup lmax))) t
      ≤ ((Ds i) t : ℝ≥0∞) := by
  set F : Finset ι := Finset.univ.filter (fun j => j < i) with hF
  set Fi : Finset ι := Finset.univ.filter (fun j => j ≤ i) with hFi
  set cL : ℝ≥0 := (Finset.univ.filter (fun j => i < j)).sup lmax
    with hcL
  have hFsubFi : ∀ j ∈ F, j ∈ Fi := fun j hj =>
    Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, ((Finset.mem_filter.mp hj).2).le⟩
  have hiFi : i ∈ Fi :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, le_refl i⟩
  have hcFi : ∀ x, (∑ j ∈ Fi, (Ds j) x) ≤ ∑ j ∈ Fi, (As j) x :=
    fun x => Finset.sum_le_sum fun j _ => hc j x
  set p : ℝ≥0 := start (fun x => ∑ j ∈ Fi, (As j) x)
    (fun x => ∑ j ∈ Fi, (Ds j) x) t with hpdef
  have hpt : p ≤ t := start_le _ _ t
  have hblFi : IsBacklogged (fun x => ∑ j ∈ Fi, (As j) x)
      (fun x => ∑ j ∈ Fi, (Ds j) x) (Set.Ioc p t) :=
    isBacklogged_Ioc_start hcFi t
  -- per-flow equality at the start of the `≤ i` busy period
  have hpeqagg : (∑ j ∈ Fi, (As j) p) = ∑ j ∈ Fi, (Ds j) p :=
    apply_start_eq
      (isLeftContinuous_sum _ fun j _ => (As j).leftCont)
      (isLeftContinuous_sum _ fun j _ => (Ds j).leftCont)
      (by show (∑ j ∈ Fi, (As j) 0) = ∑ j ∈ Fi, (Ds j) 0
          exact Finset.sum_congr rfl fun j _ =>
            ((As j).zero : (As j) 0 = 0).trans
              ((Ds j).zero : (Ds j) 0 = 0).symm)
      hcFi t
  have hfloweq : ∀ j ∈ Fi, (As j) p = (Ds j) p := fun j hj =>
    ((Finset.sum_eq_sum_iff_of_le (fun j _ => hc j p)).mp
      hpeqagg.symm j hj).symm
  -- higher-priority arrival increments from the start
  have hHinc : ∀ v : ℝ≥0,
      (∑ j ∈ F, (As j) (p + v))
        ≤ (∑ j ∈ F, (As j) p) + ∑ j ∈ F, α j v := by
    intro v
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    exact (isMaximalArrivalBound_iff_increment _ _).mp
      (harr j (Finset.mem_filter.mp hj).2) p v
  -- the `≤ i` backlog transfers to the full aggregate
  have hblF : IsBacklogged (fun x => ∑ j, (As j) x)
      (fun x => ∑ j, (Ds j) x) (Set.Ioc p t) := by
    intro u hu
    have hH := hblFi u hu
    calc (∑ j, (Ds j) u)
        = (∑ j ∈ Finset.univ \ Fi, (Ds j) u) + ∑ j ∈ Fi, (Ds j) u :=
          (Finset.sum_sdiff (Finset.subset_univ Fi)).symm
      _ < (∑ j ∈ Finset.univ \ Fi, (As j) u) + ∑ j ∈ Fi, (As j) u :=
          add_lt_add_of_le_of_lt
            (Finset.sum_le_sum fun j _ => hc j u) hH
      _ = ∑ j, (As j) u := Finset.sum_sdiff (Finset.subset_univ Fi)
  -- the decomposition over `{i} ⊎ F ⊎ (> i)`
  have hFiinsert : Fi = insert i F := by
    ext j
    simp only [hFi, hF, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
    · rintro (rfl | h')
      · exact le_refl j
      · exact h'.le
  have hdecomp : ∀ g : ι → ℝ≥0,
      (∑ j, g j) = (g i + ∑ j ∈ F, g j)
        + ∑ j ∈ Finset.univ.filter (fun j => i < j), g j := by
    intro g
    have h1 : (∑ j ∈ Fi, g j) = g i + ∑ j ∈ F, g j := by
      rw [hFiinsert, Finset.sum_insert (by
        simp only [hF, Finset.mem_filter]
        exact fun h => absurd h.2 (lt_irrefl i))]
    have h2 : Finset.univ.filter (fun j => ¬ j ≤ i)
        = Finset.univ.filter (fun j => i < j) := by
      ext j
      simp [not_le]
    rw [← h1, ← h2,
      Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j => j ≤ i) g]
  -- the key shifted bound
  have hkey : ∀ σ : ℝ≥0, σ ≤ t - p →
      β σ - ((∑ j ∈ F, α j σ) + cL) ≤ (Ds i) t - (Ds i) p := by
    intro σ hσ
    rcases eq_zero_or_pos σ with rfl | hσpos
    · rw [beta_zero_eq_of_strict hstrict, zero_tsub]
      exact zero_le
    set w : ℝ≥0 := p + σ with hw
    have hwt : w ≤ t := by
      calc p + σ ≤ p + (t - p) := add_le_add le_rfl hσ
        _ = t := add_tsub_cancel_of_le hpt
    -- the anchored bound, for every anchor `s' ∈ (p, w]`
    have hanch : ∀ s' : ℝ≥0, p < s' → s' ≤ w →
        β (w - s') ≤ ((∑ j ∈ F, α j σ) + cL)
          + ((Ds i) t - (Ds i) p) := by
      intro s' hps' hs'w
      have hs't : s' ≤ t := hs'w.trans hwt
      have hstr := hstrict s' w hs'w fun u hu =>
        hblF u ⟨lt_trans hps' hu.1, hu.2.trans hwt⟩
      rw [hdecomp (fun j => (Ds j) s'), hdecomp (fun j => (Ds j) w)]
        at hstr
      have hstr' : ((Ds i) s' + ((∑ j ∈ F, (Ds j) s')
            + ∑ j ∈ Finset.univ.filter (fun j => i < j), (Ds j) s'))
            + β (w - s')
          ≤ (Ds i) w + ((∑ j ∈ F, (Ds j) w)
            + ∑ j ∈ Finset.univ.filter (fun j => i < j), (Ds j) w) := by
        rw [← add_assoc ((Ds i) s'), ← add_assoc ((Ds i) w)]
        exact hstr
      -- lower flows: at most one maximal packet on `[s', w]`
      have hLnp : (∑ j ∈ Finset.univ.filter (fun j => i < j), (Ds j) w)
          ≤ (∑ j ∈ Finset.univ.filter (fun j => i < j), (Ds j) s')
            + cL := by
        refine hnp i s' w hs'w fun u hu => ?_
        exact hblFi u ⟨lt_of_lt_of_le hps' hu.1, hu.2.trans hwt⟩
      -- higher flows: arrival increments through the start equality
      have hHbd : (∑ j ∈ F, (Ds j) w)
          ≤ (∑ j ∈ F, (Ds j) s') + ∑ j ∈ F, α j σ := by
        calc (∑ j ∈ F, (Ds j) w) ≤ ∑ j ∈ F, (As j) w :=
              Finset.sum_le_sum fun j _ => hc j w
          _ ≤ (∑ j ∈ F, (As j) p) + ∑ j ∈ F, α j σ := by
              rw [hw]
              exact hHinc σ
          _ = (∑ j ∈ F, (Ds j) p) + ∑ j ∈ F, α j σ := by
              congr 1
              exact Finset.sum_congr rfl fun j hj =>
                hfloweq j (hFsubFi j hj)
          _ ≤ (∑ j ∈ F, (Ds j) s') + ∑ j ∈ F, α j σ :=
              add_le_add (Finset.sum_le_sum fun j _ =>
                (Ds j).mono hps'.le) le_rfl
      have hcross : (∑ j ∈ F, (Ds j) w)
            + ∑ j ∈ Finset.univ.filter (fun j => i < j), (Ds j) w
          ≤ ((∑ j ∈ F, (Ds j) s')
            + ∑ j ∈ Finset.univ.filter (fun j => i < j), (Ds j) s')
            + ((∑ j ∈ F, α j σ) + cL) := by
        calc (∑ j ∈ F, (Ds j) w)
              + ∑ j ∈ Finset.univ.filter (fun j => i < j), (Ds j) w
            ≤ ((∑ j ∈ F, (Ds j) s') + ∑ j ∈ F, α j σ)
              + ((∑ j ∈ Finset.univ.filter (fun j => i < j), (Ds j) s')
                + cL) := add_le_add hHbd hLnp
          _ = ((∑ j ∈ F, (Ds j) s')
              + ∑ j ∈ Finset.univ.filter (fun j => i < j), (Ds j) s')
              + ((∑ j ∈ F, α j σ) + cL) := by ring
      have hcore := tsub_le_of_aggregate_step hstr' hcross
        ((Ds i).mono hwt) ((Ds i).mono hs't)
      have hcore' : β (w - s') - ((∑ j ∈ F, α j σ) + cL)
          ≤ (Ds i) t - (Ds i) p :=
        le_trans hcore (tsub_le_tsub_left ((Ds i).mono hps'.le) _)
      exact tsub_le_iff_left.mp hcore'
    -- pass `β` through its left limit at `σ = w − p`
    have hlim : β σ ≤ ((∑ j ∈ F, α j σ) + cL)
        + ((Ds i) t - (Ds i) p) := by
      have hne : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσpos⟩
      refine le_of_tendsto (hβlc σ).tendsto ?_
      filter_upwards [Ioo_mem_nhdsLT hσpos] with σ' hσ'
      have hσw : σ' ≤ w := le_trans hσ'.2.le le_add_self
      have hps' : p < w - σ' := by
        rw [hw, add_tsub_assoc_of_le hσ'.2.le]
        exact lt_add_of_pos_right p (tsub_pos_of_lt hσ'.2)
      have happ := hanch (w - σ') hps' tsub_le_self
      rwa [tsub_tsub_cancel_of_le hσw] at happ
    exact tsub_le_iff_left.mpr hlim
  -- collect the supremum and split the convolution at `p`
  have hsup : residualCurve β
      (fun v => (∑ j ∈ F, α j v) + cL) (t - p)
      ≤ (Ds i) t - (Ds i) p :=
    ciSup_le fun v => hkey v.1 v.2
  refine le_trans (minConv_le_add _ _ (add_tsub_cancel_of_le hpt)) ?_
  show ((As i) p : ℝ≥0∞)
      + ((residualCurve β (fun v => (∑ j ∈ F, α j v) + cL)
          (t - p) : ℝ≥0) : ℝ≥0∞)
    ≤ ((Ds i) t : ℝ≥0∞)
  rw [show (As i) p = (Ds i) p from hfloweq i hiFi, ← ENNReal.coe_add,
    ENNReal.coe_le_coe]
  calc (Ds i) p + residualCurve β
        (fun v => (∑ j ∈ F, α j v) + cL) (t - p)
      ≤ (Ds i) p + ((Ds i) t - (Ds i) p) := add_le_add le_rfl hsup
    _ = (Ds i) t := add_tsub_cancel_of_le ((Ds i).mono hpt)

/-- Relation form: an NP-SP `n`-server with a left-continuous strict
aggregate curve, restricted to pairs with constrained higher-priority
arrivals, offers `[β − ∑_{j<i} αⱼ − max_{j>i} ℓⱼᵘ]⁺↑` as a min-plus
service curve to the residual server of flow `i`. -/
theorem isMinimalServiceCurve_residualServer_of_isNpsp {ι : Type*}
    [Fintype ι] [LinearOrder ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {lmax : ι → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S) (hβlc : IsLeftContinuous β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hnp : IsNpspServerN lmax S) :
    IsMinimalServiceCurve
      (liftEReal (residualCurve β (fun v =>
        (∑ j ∈ Finset.univ.filter (fun j => j < i), α j v)
          + (Finset.univ.filter (fun j => i < j)).sup lmax)))
      (residualServer (fun As Ds => S As Ds ∧
        ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α j)) i) := by
  rintro Ai Di ⟨As, Ds, ⟨hp, harr⟩, rfl, rfl⟩
  intro t
  have h := minConv_residualCurve_le_of_isNpsp
    (fun j => hcaus As Ds hp j) hβlc (hβ.sum_strict hp)
    ((hnp As Ds hp).1) harr t
  rw [show Deviation.liftENN (residualCurve β (fun v =>
        (∑ j ∈ Finset.univ.filter (fun j => j < i), α j v)
          + (Finset.univ.filter (fun j => i < j)).sup lmax))
      = Deviation.toENN (liftEReal (residualCurve β (fun v =>
        (∑ j ∈ Finset.univ.filter (fun j => j < i), α j v)
          + (Finset.univ.filter (fun j => i < j)).sup lmax)))
    from (Deviation.toENN_liftEReal _).symm] at h
  rw [curveEReal_apply]
  exact (Deviation.minConv_toENN_le_coe_iff (As i)
    (isNonneg_liftEReal _) ((Ds i) t) t).mp h

/-! ## Book restatement (NP-SP residual, min-plus half)
An NP-SP `n`-server taking the natural order as priority, offering an
aggregate minimal strict service curve `β` (left-continuous, the same
repair as preemptive static priority), with arrival curves `αⱼ` on the
higher-priority flows: flow `i` is offered the min-plus service curve
`βᵢ = [β − ∑_{j<i} αⱼ − max_{i<j≤n} ℓⱼᵘ]⁺↑`, and the strict service
curve `βᵢˢ` with the maximum extended to `j = i`
(`add_residualCurve_le_of_isNpspExclusive` below). -/
example {ι : Type*} [Fintype ι] [LinearOrder ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {As Ds : ι → Curve}
    {β : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0} {lmax : ι → ℝ≥0}
    (hSrv : IsServerN S) (hp : S As Ds)
    (hβlc : IsLeftContinuous β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hnp : IsNpspServerN lmax S)
    {i : ι} (harr : ∀ j, j < i → IsMaximalArrivalCurve ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (Deviation.liftENN (residualCurve β (fun v =>
          (∑ j ∈ Finset.univ.filter (fun j => j < i), α j v)
            + (Finset.univ.filter (fun j => i < j)).sup lmax))) t
      ≤ ((Ds i) t : ℝ≥0∞) :=
  minConv_residualCurve_le_of_isNpsp (fun j => hSrv.1 As Ds hp j)
    hβlc (hβ.sum_strict hp) ((hnp As Ds hp).1)
    (fun j hj => (harr j hj).2) t

/-- **Non-preemptive static-priority residual** (strict): under packet
exclusivity with a left-continuous strict aggregate curve `β` and
`αⱼ`-constrained higher-priority arrivals, flow `i` obeys the strict
service inequality for `[β − ∑_{j<i} αⱼ − max_{j≥i} ℓⱼᵘ]⁺↑` on its
backlogged periods — the packet that may block it is now any of
priority `≥ i`, including its own. -/
theorem add_residualCurve_le_of_isNpspExclusive {ι : Type*} [Fintype ι]
    [LinearOrder ι] {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {lmax : ι → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hβlc : IsLeftContinuous β)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    (hnpx : IsNpspExclusive lmax
      (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {i : ι} (harr : ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α j))
    {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s
      + residualCurve β (fun v =>
          (∑ j ∈ Finset.univ.filter (fun j => j < i), α j v)
            + (Finset.univ.filter (fun j => i ≤ j)).sup lmax) (t - s)
      ≤ (Ds i) t := by
  set F : Finset ι := Finset.univ.filter (fun j => j < i) with hF
  set cI : ℝ≥0 := (Finset.univ.filter (fun j => i ≤ j)).sup lmax
    with hcI
  have hcH : ∀ x, (∑ j ∈ F, (Ds j) x) ≤ ∑ j ∈ F, (As j) x :=
    fun x => Finset.sum_le_sum fun j _ => hc j x
  set p : ℝ≥0 := start (fun x => ∑ j ∈ F, (As j) x)
    (fun x => ∑ j ∈ F, (Ds j) x) s with hpdef
  have hps : p ≤ s := start_le _ _ s
  have hpt : p ≤ t := hps.trans hst
  have hblH : IsBacklogged (fun x => ∑ j ∈ F, (As j) x)
      (fun x => ∑ j ∈ F, (Ds j) x) (Set.Ioc p s) :=
    isBacklogged_Ioc_start hcH s
  have hpeqagg : (∑ j ∈ F, (As j) p) = ∑ j ∈ F, (Ds j) p :=
    apply_start_eq
      (isLeftContinuous_sum _ fun j _ => (As j).leftCont)
      (isLeftContinuous_sum _ fun j _ => (Ds j).leftCont)
      (by show (∑ j ∈ F, (As j) 0) = ∑ j ∈ F, (Ds j) 0
          exact Finset.sum_congr rfl fun j _ =>
            ((As j).zero : (As j) 0 = 0).trans
              ((Ds j).zero : (Ds j) 0 = 0).symm)
      hcH s
  have hHinc : ∀ v : ℝ≥0,
      (∑ j ∈ F, (As j) (p + v))
        ≤ (∑ j ∈ F, (As j) p) + ∑ j ∈ F, α j v := by
    intro v
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    exact (isMaximalArrivalBound_iff_increment _ _).mp
      (harr j (Finset.mem_filter.mp hj).2) p v
  -- the higher-priority and flow-`i` backlogs cover `(p, t]`
  have hblF : IsBacklogged (fun x => ∑ j, (As j) x)
      (fun x => ∑ j, (Ds j) x) (Set.Ioc p t) := by
    intro u hu
    rcases le_or_gt u s with hus | hus
    · have hH := hblH u ⟨hu.1, hus⟩
      calc (∑ j, (Ds j) u)
          = (∑ j ∈ Finset.univ \ F, (Ds j) u) + ∑ j ∈ F, (Ds j) u :=
            (Finset.sum_sdiff (Finset.subset_univ F)).symm
        _ < (∑ j ∈ Finset.univ \ F, (As j) u) + ∑ j ∈ F, (As j) u :=
            add_lt_add_of_le_of_lt
              (Finset.sum_le_sum fun j _ => hc j u) hH
        _ = ∑ j, (As j) u := Finset.sum_sdiff (Finset.subset_univ F)
    · exact isBacklogged_sum_of_isBacklogged (fun j _ x => hc j x)
        (Finset.mem_univ i) hbl u ⟨hus, hu.2⟩
  -- the decomposition over `{i} ⊎ F ⊎ (> i)`
  have hFiinsert : Finset.univ.filter (fun j => j ≤ i)
      = insert i F := by
    ext j
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
    · rintro (rfl | h')
      · exact le_refl j
      · exact h'.le
  have hdecomp : ∀ g : ι → ℝ≥0,
      (∑ j, g j) = (g i + ∑ j ∈ F, g j)
        + ∑ j ∈ Finset.univ.filter (fun j => i < j), g j := by
    intro g
    have h1 : (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), g j)
        = g i + ∑ j ∈ F, g j := by
      rw [hFiinsert, Finset.sum_insert (by
        simp only [hF, Finset.mem_filter]
        exact fun h => absurd h.2 (lt_irrefl i))]
    have h2 : Finset.univ.filter (fun j => ¬ j ≤ i)
        = Finset.univ.filter (fun j => i < j) := by
      ext j
      simp [not_le]
    rw [← h1, ← h2,
      Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j => j ≤ i) g]
  -- the key shifted bound
  have hkey : ∀ σ : ℝ≥0, σ ≤ t - p →
      β σ - ((∑ j ∈ F, α j σ) + cI) ≤ (Ds i) t - (Ds i) s := by
    intro σ hσ
    rcases eq_zero_or_pos σ with rfl | hσpos
    · rw [beta_zero_eq_of_strict hstrict, zero_tsub]
      exact zero_le
    set w : ℝ≥0 := p + σ with hw
    have hwt : w ≤ t := by
      calc p + σ ≤ p + (t - p) := add_le_add le_rfl hσ
        _ = t := add_tsub_cancel_of_le hpt
    -- the anchored bound, for every anchor `s' ∈ (p, w]`
    have hanch : ∀ s' : ℝ≥0, p < s' → s' ≤ w →
        β (w - s') ≤ ((∑ j ∈ F, α j σ) + cI)
          + ((Ds i) t - (Ds i) s) := by
      intro s' hps' hs'w
      have hstr := hstrict s' w hs'w fun u hu =>
        hblF u ⟨lt_trans hps' hu.1, hu.2.trans hwt⟩
      rw [hdecomp (fun j => (Ds j) s'), hdecomp (fun j => (Ds j) w)]
        at hstr
      have hHbd : (∑ j ∈ F, (Ds j) w)
          ≤ (∑ j ∈ F, (Ds j) s') + ∑ j ∈ F, α j σ := by
        calc (∑ j ∈ F, (Ds j) w) ≤ ∑ j ∈ F, (As j) w :=
              Finset.sum_le_sum fun j _ => hc j w
          _ ≤ (∑ j ∈ F, (As j) p) + ∑ j ∈ F, α j σ := by
              rw [hw]
              exact hHinc σ
          _ = (∑ j ∈ F, (Ds j) p) + ∑ j ∈ F, α j σ := by
              rw [hpeqagg]
          _ ≤ (∑ j ∈ F, (Ds j) s') + ∑ j ∈ F, α j σ :=
              add_le_add (Finset.sum_le_sum fun j _ =>
                (Ds j).mono hps'.le) le_rfl
      -- packet exclusivity couples flow `i` at `s` with the lower flows
      have hexcl : (Ds i) s
            + (∑ j ∈ Finset.univ.filter (fun j => i < j), (Ds j) w)
          ≤ ((Ds i) s'
            + ∑ j ∈ Finset.univ.filter (fun j => i < j), (Ds j) s')
            + cI := by
        have hicc : ∀ v ∈ Set.Icc s' s,
            (∑ j ∈ F, (Ds j) v) < ∑ j ∈ F, (As j) v := fun v hv =>
          hblH v ⟨lt_of_lt_of_le hps' hv.1, hv.2⟩
        rcases le_or_gt w s with hws | hws
        · have h0 := hnpx i s' s s le_rfl hicc
            (fun v hv => absurd (lt_of_lt_of_le hv.1 hv.2)
              (lt_irrefl s))
          refine le_trans (add_le_add le_rfl
            (Finset.sum_le_sum fun j _ => (Ds j).mono hws)) h0
        · exact hnpx i s' s w hws.le hicc
            (fun v hv => hbl v ⟨hv.1, hv.2.trans hwt⟩)
      -- assemble at `ℝ`: cancel the shared sums
      have hfin : (Ds i) s + β (w - s')
          ≤ (Ds i) t + ((∑ j ∈ F, α j σ) + cI) := by
        rw [← NNReal.coe_le_coe]
        have hstrR : ((Ds i) s' : ℝ)
              + ((∑ j ∈ F, (Ds j) s' : ℝ≥0) : ℝ)
              + ((∑ j ∈ Finset.univ.filter (fun j => i < j),
                  (Ds j) s' : ℝ≥0) : ℝ)
              + (β (w - s') : ℝ)
            ≤ ((Ds i) w : ℝ)
              + ((∑ j ∈ F, (Ds j) w : ℝ≥0) : ℝ)
              + ((∑ j ∈ Finset.univ.filter (fun j => i < j),
                  (Ds j) w : ℝ≥0) : ℝ) := by
          exact_mod_cast hstr
        have h2R : ((∑ j ∈ F, (Ds j) w : ℝ≥0) : ℝ)
            ≤ ((∑ j ∈ F, (Ds j) s' : ℝ≥0) : ℝ)
              + ((∑ j ∈ F, α j σ : ℝ≥0) : ℝ) := by
          exact_mod_cast hHbd
        have h3R : ((Ds i) s : ℝ)
              + ((∑ j ∈ Finset.univ.filter (fun j => i < j),
                  (Ds j) w : ℝ≥0) : ℝ)
            ≤ ((Ds i) s' : ℝ)
              + ((∑ j ∈ Finset.univ.filter (fun j => i < j),
                  (Ds j) s' : ℝ≥0) : ℝ)
              + (cI : ℝ) := by
          exact_mod_cast hexcl
        have h4R : ((Ds i) w : ℝ) ≤ ((Ds i) t : ℝ) := by
          exact_mod_cast (Ds i).mono hwt
        push_cast at hstrR h2R h3R h4R ⊢
        linarith
      refine le_trans (le_tsub_of_add_le_left hfin) (le_of_eq ?_)
      rw [add_comm ((Ds i) t) ((∑ j ∈ F, α j σ) + cI),
        add_tsub_assoc_of_le
          (show (Ds i) s ≤ (Ds i) t from (Ds i).mono hst)]
    -- pass `β` through its left limit at `σ = w − p`
    have hlim : β σ ≤ ((∑ j ∈ F, α j σ) + cI)
        + ((Ds i) t - (Ds i) s) := by
      have hne : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσpos⟩
      refine le_of_tendsto (hβlc σ).tendsto ?_
      filter_upwards [Ioo_mem_nhdsLT hσpos] with σ' hσ'
      have hσw : σ' ≤ w := le_trans hσ'.2.le le_add_self
      have hps' : p < w - σ' := by
        rw [hw, add_tsub_assoc_of_le hσ'.2.le]
        exact lt_add_of_pos_right p (tsub_pos_of_lt hσ'.2)
      have happ := hanch (w - σ') hps' tsub_le_self
      rwa [tsub_tsub_cancel_of_le hσw] at happ
    exact tsub_le_iff_left.mpr hlim
  have hsup : residualCurve β
      (fun v => (∑ j ∈ F, α j v) + cI) (t - s)
      ≤ (Ds i) t - (Ds i) s :=
    ciSup_le fun v => hkey v.1 (v.2.trans (tsub_le_tsub_left hps t))
  calc (Ds i) s + residualCurve β
        (fun v => (∑ j ∈ F, α j v) + cI) (t - s)
      ≤ (Ds i) s + ((Ds i) t - (Ds i) s) := add_le_add le_rfl hsup
    _ = (Ds i) t := add_tsub_cancel_of_le ((Ds i).mono hst)

/-- Relation form: an NP-SP `n`-server with a left-continuous strict
aggregate curve, restricted to pairs with constrained higher-priority
arrivals, offers `[β − ∑_{j<i} αⱼ − max_{j≥i} ℓⱼᵘ]⁺↑` as a strict
service curve to the residual server of flow `i`. -/
theorem isStrictMinimalServiceCurve_residualServer_of_isNpsp
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {lmax : ι → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S) (hβlc : IsLeftContinuous β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hnp : IsNpspServerN lmax S) :
    IsStrictMinimalServiceCurve
      (residualCurve β (fun v =>
        (∑ j ∈ Finset.univ.filter (fun j => j < i), α j v)
          + (Finset.univ.filter (fun j => i ≤ j)).sup lmax))
      (residualServer (fun As Ds => S As Ds ∧
        ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α j)) i) := by
  rintro Ai Di ⟨As, Ds, ⟨hp, harr⟩, rfl, rfl⟩ s t hst hbl
  exact add_residualCurve_le_of_isNpspExclusive (fun j => hcaus As Ds hp j)
    hβlc (hβ.sum_strict hp) ((hnp As Ds hp).2) harr hst hbl

/-! ## Book restatement (NP-SP residual, strict half)
The same NP-SP `n`-server offers flow `i` the strict service curve
`βᵢˢ = [β − ∑_{j<i} αⱼ − max_{i≤j≤n} ℓⱼᵘ]⁺↑` — the blocking packet
may now be of priority `i` itself, so the maximum extends to `j = i`. -/
example {ι : Type*} [Fintype ι] [LinearOrder ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {As Ds : ι → Curve}
    {β : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0} {lmax : ι → ℝ≥0}
    (hSrv : IsServerN S) (hp : S As Ds)
    (hβlc : IsLeftContinuous β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hnp : IsNpspServerN lmax S)
    {i : ι} (harr : ∀ j, j < i → IsMaximalArrivalCurve ⇑(As j) (α j))
    {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s
      + residualCurve β (fun v =>
          (∑ j ∈ Finset.univ.filter (fun j => j < i), α j v)
            + (Finset.univ.filter (fun j => i ≤ j)).sup lmax) (t - s)
      ≤ (Ds i) t :=
  add_residualCurve_le_of_isNpspExclusive (fun j => hSrv.1 As Ds hp j)
    hβlc (hβ.sum_strict hp) ((hnp As Ds hp).2)
    (fun j hj => (harr j hj).2) hst hbl

end DeepWiki
