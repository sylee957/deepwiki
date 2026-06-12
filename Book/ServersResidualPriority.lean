import Book.ServersResidual

/-! # Static-priority residual service
A preemptive static-priority server freezes a flow while strictly
higher-priority data is backlogged. With a *left-continuous* strict
aggregate service curve `β` and arrival curves on the higher-priority
flows only, flow `i` receives the strict residual
`[β − ∑_{j<i} αⱼ]⁺↑`. Left-continuity of `β` is the repair this needs:
the book's proof equates the flow's backlog at the start of the
higher-priority busy period, which an instantaneous service burst at
that instant can break; anchoring just inside the period and passing
`β` through its left limit closes the gap (for `β` not left-continuous
the statement fails — refutation ladder deferred). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Set Topology Filter

/-- **Preemptive static priority**: while the strictly-higher-priority
aggregate is backlogged throughout the closed interval `[s, t]`, flow
`i` receives nothing on `(s, t]` (`j < i` means `j` has higher
priority). -/
def IsStaticPriority {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i : ι, ∀ s t : ℝ≥0, s ≤ t →
    (∀ u ∈ Set.Icc s t,
      (∑ j ∈ Finset.univ.filter (fun j => j < i), D j u)
        < ∑ j ∈ Finset.univ.filter (fun j => j < i), A j u) →
    D i t = D i s

/-- **Static-priority residual service**: under preemptive SP with a
left-continuous strict aggregate curve `β` and `αⱼ`-constrained
higher-priority arrivals, flow `i` obeys the strict service inequality
for `[β − ∑_{j<i} αⱼ]⁺↑` on its backlogged periods. -/
theorem add_residualCurve_le_of_staticPriority {ι : Type*} [Fintype ι]
    [LinearOrder ι] {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hβlc : IsLeftContinuous β)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    (hSP : IsStaticPriority (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {i : ι} (harr : ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α j))
    {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s
      + residualCurve β
          (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α j v)
          (t - s)
      ≤ (Ds i) t := by
  set F : Finset ι := Finset.univ.filter (fun j => j < i) with hF
  set L : Finset ι := (Finset.univ.erase i) \ F with hL
  have hcH : ∀ x, (∑ j ∈ F, (Ds j) x) ≤ ∑ j ∈ F, (As j) x := fun x =>
    Finset.sum_le_sum fun j _ => hc j x
  set p : ℝ≥0 := start (fun x => ∑ j ∈ F, (As j) x)
    (fun x => ∑ j ∈ F, (Ds j) x) s with hpdef
  have hps : p ≤ s := start_le _ _ s
  have hpt : p ≤ t := hps.trans hst
  -- the higher-priority aggregate is backlogged on `(p, s]`
  have hblH : IsBacklogged (fun x => ∑ j ∈ F, (As j) x)
      (fun x => ∑ j ∈ F, (Ds j) x) (Set.Ioc p s) :=
    isBacklogged_Ioc_start hcH s
  -- and at equality at `p`
  have hpeq : (∑ j ∈ F, (As j) p) = ∑ j ∈ F, (Ds j) p :=
    apply_start_eq
      (isLeftContinuous_sum _ fun j _ => (As j).leftCont)
      (isLeftContinuous_sum _ fun j _ => (Ds j).leftCont)
      (by show (∑ j ∈ F, (As j) 0) = ∑ j ∈ F, (Ds j) 0
          exact Finset.sum_congr rfl fun j _ =>
            ((As j).zero : (As j) 0 = 0).trans
              ((Ds j).zero : (Ds j) 0 = 0).symm)
      hcH s
  -- higher-priority arrival increments
  have hHinc : ∀ x v : ℝ≥0,
      (∑ j ∈ F, (As j) (x + v)) ≤ (∑ j ∈ F, (As j) x) + ∑ j ∈ F, α j v := by
    intro x v
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    exact (isMaximalArrivalBound_iff_increment _ _).mp
      (harr j (Finset.mem_filter.mp hj).2) x v
  -- a strict prefix transfers to any superset of flows
  have hsplit : ∀ G : Finset ι, F ⊆ G → ∀ u : ℝ≥0,
      (∑ j ∈ F, (Ds j) u) < (∑ j ∈ F, (As j) u) →
      (∑ j ∈ G, (Ds j) u) < ∑ j ∈ G, (As j) u := by
    intro G hFG u hH
    calc (∑ j ∈ G, (Ds j) u)
        = (∑ j ∈ G \ F, (Ds j) u) + ∑ j ∈ F, (Ds j) u :=
          (Finset.sum_sdiff hFG).symm
      _ < (∑ j ∈ G \ F, (As j) u) + ∑ j ∈ F, (As j) u :=
          add_lt_add_of_le_of_lt
            (Finset.sum_le_sum fun j _ => hc j u) hH
      _ = ∑ j ∈ G, (As j) u := Finset.sum_sdiff hFG
  -- the full aggregate is backlogged on `(p, t]`
  have hblF : IsBacklogged (fun x => ∑ j, (As j) x)
      (fun x => ∑ j, (Ds j) x) (Set.Ioc p t) := by
    intro u hu
    rcases le_or_gt u s with hus | hus
    · exact hsplit Finset.univ (Finset.subset_univ F) u (hblH u ⟨hu.1, hus⟩)
    · exact isBacklogged_sum_of_isBacklogged (fun j x => hc j x) i hbl u
        ⟨hus, hu.2⟩
  -- lower-priority flows are frozen on `(p, t]`
  have hfreezeLow : ∀ k ∈ L, ∀ s' w : ℝ≥0, p < s' → s' ≤ w → w ≤ t →
      (Ds k) w = (Ds k) s' := by
    intro k hk s' w hps' hs'w hwt
    have hik : i < k := by
      obtain ⟨hker, hknF⟩ := Finset.mem_sdiff.mp hk
      have hne : k ≠ i := (Finset.mem_erase.mp hker).1
      have hnlt : ¬ k < i := fun hlt => hknF
        (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hlt⟩)
      exact lt_of_le_of_ne (not_lt.mp hnlt) (Ne.symm hne)
    refine hSP k s' w hs'w fun u hu => ?_
    have hFk : F ⊆ Finset.univ.filter (fun j => j < k) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        lt_trans (Finset.mem_filter.mp hj).2 hik⟩
    have hu' : u ∈ Set.Ioc p t :=
      ⟨lt_of_lt_of_le hps' hu.1, hu.2.trans hwt⟩
    rcases le_or_gt u s with hus | hus
    · exact hsplit _ hFk u (hblH u ⟨hu'.1, hus⟩)
    · have hiFk : i ∈ Finset.univ.filter (fun j => j < k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hik⟩
      exact Finset.sum_lt_sum (fun j _ => hc j u)
        ⟨i, hiFk, hbl u ⟨hus, hu'.2⟩⟩
  -- flow `i` is frozen on `(p, s]`, hence `Dᵢ s ≤ Dᵢ s'` on `(p, t]`
  have hDis : ∀ s' : ℝ≥0, p < s' → s' ≤ t → (Ds i) s ≤ (Ds i) s' := by
    intro s' hps' hs't
    rcases le_or_gt s' s with h1 | h1
    · exact le_of_eq (hSP i s' s h1 fun u hu =>
        hblH u ⟨lt_of_lt_of_le hps' hu.1, hu.2⟩)
    · exact (Ds i).mono h1.le
  -- the full-aggregate decomposition over `{i} ∪ F ∪ L`
  have hdecomp : ∀ g : ι → ℝ≥0,
      (∑ j, g j) = (g i + ∑ j ∈ F, g j) + ∑ j ∈ L, g j := by
    intro g
    have hFsub : F ⊆ Finset.univ.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr
        ⟨ne_of_lt (Finset.mem_filter.mp hj).2, Finset.mem_univ j⟩
    rw [← Finset.add_sum_erase _ g (Finset.mem_univ i),
      ← Finset.sum_sdiff hFsub, add_comm
        (∑ j ∈ Finset.univ.erase i \ F, g j) (∑ j ∈ F, g j), ← add_assoc]
  -- every shift up to `t − p` is covered
  have hkey : ∀ σ : ℝ≥0, σ ≤ t - p →
      β σ - (∑ j ∈ F, α j σ) ≤ (Ds i) t - (Ds i) s := by
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
        β (w - s') ≤ (∑ j ∈ F, α j σ) + ((Ds i) t - (Ds i) s) := by
      intro s' hps' hs'w
      have hs't : s' ≤ t := hs'w.trans hwt
      have hstr := hstrict s' w hs'w fun u hu =>
        hblF u ⟨lt_trans hps' hu.1, hu.2.trans hwt⟩
      rw [hdecomp (fun j => (Ds j) s'), hdecomp (fun j => (Ds j) w)] at hstr
      have hstr' : ((Ds i) s'
            + ((∑ j ∈ F, (Ds j) s') + ∑ j ∈ L, (Ds j) s')) + β (w - s')
          ≤ (Ds i) w + ((∑ j ∈ F, (Ds j) w) + ∑ j ∈ L, (Ds j) w) := by
        rw [← add_assoc ((Ds i) s'), ← add_assoc ((Ds i) w)]
        exact hstr
      have hcross : (∑ j ∈ F, (Ds j) w) + ∑ j ∈ L, (Ds j) w
          ≤ ((∑ j ∈ F, (Ds j) s') + ∑ j ∈ L, (Ds j) s')
            + ∑ j ∈ F, α j σ := by
        have hH : (∑ j ∈ F, (Ds j) w) ≤ (∑ j ∈ F, (Ds j) s')
            + ∑ j ∈ F, α j σ := by
          calc (∑ j ∈ F, (Ds j) w) ≤ ∑ j ∈ F, (As j) w := hcH w
            _ ≤ (∑ j ∈ F, (As j) p) + ∑ j ∈ F, α j σ := hHinc p σ
            _ = (∑ j ∈ F, (Ds j) p) + ∑ j ∈ F, α j σ := by rw [hpeq]
            _ ≤ (∑ j ∈ F, (Ds j) s') + ∑ j ∈ F, α j σ :=
                add_le_add (Finset.sum_le_sum fun j _ =>
                  (Ds j).mono hps'.le) le_rfl
        have hLfr : (∑ j ∈ L, (Ds j) w) = ∑ j ∈ L, (Ds j) s' :=
          Finset.sum_congr rfl fun k hk =>
            hfreezeLow k hk s' w hps' hs'w hwt
        calc (∑ j ∈ F, (Ds j) w) + ∑ j ∈ L, (Ds j) w
            = (∑ j ∈ F, (Ds j) w) + ∑ j ∈ L, (Ds j) s' := by rw [hLfr]
          _ ≤ ((∑ j ∈ F, (Ds j) s') + ∑ j ∈ F, α j σ)
              + ∑ j ∈ L, (Ds j) s' := add_le_add hH le_rfl
          _ = ((∑ j ∈ F, (Ds j) s') + ∑ j ∈ L, (Ds j) s')
              + ∑ j ∈ F, α j σ := by ring
      have hcore := tsub_le_of_aggregate_step hstr' hcross
        ((Ds i).mono hwt) ((Ds i).mono hs't)
      have hcore' : β (w - s') - (∑ j ∈ F, α j σ)
          ≤ (Ds i) t - (Ds i) s :=
        le_trans hcore (tsub_le_tsub_left (hDis s' hps' hs't) _)
      exact tsub_le_iff_left.mp hcore'
    -- pass `β` through its left limit at `σ = w − p`
    have hlim : β σ ≤ (∑ j ∈ F, α j σ) + ((Ds i) t - (Ds i) s) := by
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
  -- collect the supremum and conclude
  have hsup : residualCurve β (fun v => ∑ j ∈ F, α j v) (t - s)
      ≤ (Ds i) t - (Ds i) s :=
    ciSup_le fun v => hkey v.1 (v.2.trans (tsub_le_tsub_left hps t))
  calc (Ds i) s + residualCurve β (fun v => ∑ j ∈ F, α j v) (t - s)
      ≤ (Ds i) s + ((Ds i) t - (Ds i) s) := add_le_add le_rfl hsup
    _ = (Ds i) t := add_tsub_cancel_of_le ((Ds i).mono hst)

/-- Relation form: an SP `n`-server with a left-continuous strict
aggregate curve, restricted to pairs with constrained higher-priority
arrivals, offers `[β − ∑_{j<i} αⱼ]⁺↑` as a strict service curve to the
residual server of flow `i`. -/
theorem isStrictMinimalServiceCurve_residualServer_of_staticPriority
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S) (hβlc : IsLeftContinuous β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hSP : ∀ As Ds, S As Ds →
      IsStaticPriority (fun j => ⇑(As j)) (fun j => ⇑(Ds j))) :
    IsStrictMinimalServiceCurve
      (residualCurve β
        (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α j v))
      (residualServer (fun As Ds => S As Ds ∧
        ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α j)) i) := by
  rintro Ai Di ⟨As, Ds, ⟨hp, harr⟩, rfl, rfl⟩ s t hst hbl
  refine add_residualCurve_le_of_staticPriority
    (fun j => hcaus As Ds hp j) hβlc ?_ (hSP As Ds hp) harr hst hbl
  intro s' t' hst' hbl'
  have h := hβ (∑ j, As j) (∑ j, Ds j) (aggregateServer_sum hp) s' t' hst'
    (by rwa [Curve.coe_sum, Curve.coe_sum])
  rwa [Curve.sum_apply, Curve.sum_apply] at h

/-! ## Book restatement (static priority)
A preemptive SP `n`-server offering a (left-continuous) strict service
curve `β` whose higher-priority flows have arrival curves `αⱼ`: flow `i`
receives `βᵢ = [β − ∑_{j<i} αⱼ]⁺↑` as a strict service curve — no
constraint on flow `i` itself or on lower-priority flows is used. (The
book omits the left-continuity of `β`, which its proof needs at the
start of the higher-priority busy period.) -/
example {ι : Type*} [Fintype ι] [LinearOrder ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hSrv : IsServerN S) (hβlc : IsLeftContinuous β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hSP : ∀ As Ds, S As Ds →
      IsStaticPriority (fun j => ⇑(As j)) (fun j => ⇑(Ds j))) :
    IsStrictMinimalServiceCurve
      (residualCurve β
        (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α j v))
      (residualServer (fun As Ds => S As Ds ∧
        ∀ j, j < i → IsMaximalArrivalCurve ⇑(As j) (α j)) i) := by
  have h := isStrictMinimalServiceCurve_residualServer_of_staticPriority
    (α := α) (i := i) hSrv.1 hβlc hβ hSP
  intro Ai Di hpair
  obtain ⟨As, Ds, ⟨hp, harr⟩, hA, hD⟩ := hpair
  exact h Ai Di ⟨As, Ds, ⟨hp, fun j hj => (harr j hj).2⟩, hA, hD⟩

end DeepWiki
