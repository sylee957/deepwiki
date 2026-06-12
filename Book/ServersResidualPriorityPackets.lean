import Book.ServersResidualPriority

/-! # Non-preemptive static-priority residual service
A packet server cannot interrupt a packet in service: under
non-preemptive static priority, while the priority-`≤ i` flows are
backlogged, the strictly lower flows still serve — but at most one
maximal packet. With a left-continuous strict aggregate curve `β` (the
same repair as preemptive static priority) and arrival curves on the
higher-priority flows, flow `i` receives the min-plus residual
`[β − ∑_{j<i} αⱼ − max_{j>i} ℓⱼᵘ]⁺↑`: the preemptive residual, one
maximal lower-priority packet cheaper. -/

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

/-- **NP-SP `n`-server**: every served family obeys the non-preemptive
priority bound. -/
def IsNpspServerN {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lmax : ι → ℝ≥0)
    (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ As Ds, S As Ds →
    IsNpsp lmax (fun j => ⇑(As j)) (fun j => ⇑(Ds j))

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
      exact zero_le'
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
    (hnp As Ds hp) harr t
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
`βᵢ = [β − ∑_{j<i} αⱼ − max_{i<j≤n} ℓⱼᵘ]⁺↑`. (The strict half, with
the maximum extended to `j = i`, is the remaining piece.) -/
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
    hβlc (hβ.sum_strict hp) (hnp As Ds hp)
    (fun j hj => (harr j hj).2) t

end DeepWiki
