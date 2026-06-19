import Mathlib.Topology.Order.Lattice
import DeepWiki.NetworkCalculus.ServersResidualFifo

/-! # Earliest deadline first
Each flow carries a relative deadline `dᵢ`; the scheduler serves the
data with the smallest absolute deadline. Formally, for every horizon
`T`, while data with absolute deadline by `T` is queued (the aggregate
of the parts arrived by `T − dₖ`, `truncBefore`), the parts arrived
after `T − dⱼ` (`truncAfter`) receive nothing — `IsEdf`. The book
prints the pairwise relation between two derived flows; the aggregate
premise (the shape of its static-priority definition) is what its own
residual proof uses, since the backlogged part alternates across flows.
The residual family `edfResidual`
shifts each cross-flow by `[θ − Δᵢⱼ]⁺` (in `ℝ≥0`: `(θ + dⱼ) − dᵢ`) and
degenerates to the FIFO family when all deadlines agree. Deadline
compatibility (`IsDeadlineCompatible`) forces the aggregate min-plus
curve to dominate the shifted arrival curves; conversely, the pointwise
capacity condition makes an EDF family with a strict left-continuous
aggregate curve meet every deadline. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Set Topology Filter

/-! ## The before/after-`T` parts of a flow -/

/-- The part of a cumulative process arrived by `T`: `t ↦ A (t ⊓ T)`. -/
noncomputable def truncBefore (T : ℝ≥0) (A : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => A (min t T)

/-- The part of a cumulative process arrived after `T`:
`t ↦ A t − A T`. -/
noncomputable def truncAfter (T : ℝ≥0) (A : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => A t - A T

/-- The departures of the data arrived by `T`: `t ↦ D t ⊓ A T` (under
per-flow FIFO, the first `A T` units to leave are the first to have
arrived). -/
noncomputable def truncBeforeD (T : ℝ≥0) (A D : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => min (D t) (A T)

/-- The departures of the data arrived after `T`: `t ↦ D t − A T`. -/
noncomputable def truncAfterD (T : ℝ≥0) (A D : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => D t - A T

/-- `truncBefore T A t = A (t ⊓ T)`. -/
@[simp] theorem truncBefore_apply (T : ℝ≥0) (A : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    truncBefore T A t = A (min t T) := rfl

/-- `truncAfter T A t = A t − A T`. -/
@[simp] theorem truncAfter_apply (T : ℝ≥0) (A : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    truncAfter T A t = A t - A T := rfl

/-- `truncBeforeD T A D t = D t ⊓ A T`. -/
@[simp] theorem truncBeforeD_apply (T : ℝ≥0) (A D : ℝ≥0 → ℝ≥0)
    (t : ℝ≥0) : truncBeforeD T A D t = min (D t) (A T) := rfl

/-- `truncAfterD T A D t = D t − A T`. -/
@[simp] theorem truncAfterD_apply (T : ℝ≥0) (A D : ℝ≥0 → ℝ≥0)
    (t : ℝ≥0) : truncAfterD T A D t = D t - A T := rfl

/-- The two parts recover the flow: `A^{≤T} + A^{>T} = A` (for
non-decreasing `A`). -/
theorem truncBefore_add_truncAfter {A : ℝ≥0 → ℝ≥0} (hmono : Monotone A)
    (T t : ℝ≥0) : truncBefore T A t + truncAfter T A t = A t := by
  rw [truncBefore, truncAfter]
  rcases le_total t T with h | h
  · rw [min_eq_left h, tsub_eq_zero_of_le (hmono h), add_zero]
  · rw [min_eq_right h, add_tsub_cancel_of_le (hmono h)]

/-- The two departure parts recover the departures (for causal pairs:
`D t ≥ A T` or `D t ≤ A T` split). -/
theorem truncBeforeD_add_truncAfterD (T : ℝ≥0) (A D : ℝ≥0 → ℝ≥0)
    (t : ℝ≥0) : truncBeforeD T A D t + truncAfterD T A D t = D t := by
  rw [truncBeforeD, truncAfterD]
  rcases le_total (D t) (A T) with h | h
  · rw [min_eq_left h, tsub_eq_zero_of_le h, add_zero]
  · rw [min_eq_right h, add_tsub_cancel_of_le h]

/-- `truncBefore` is monotone for monotone `A`. -/
theorem truncBefore_mono {A : ℝ≥0 → ℝ≥0} (hmono : Monotone A) (T : ℝ≥0) :
    Monotone (truncBefore T A) :=
  fun _ _ hab => hmono (min_le_min hab le_rfl)

/-- `truncBefore` is left-continuous for left-continuous `A`: below `T`
it is `A`, above it is constant. -/
theorem truncBefore_leftCont {A : ℝ≥0 → ℝ≥0} (hlc : IsLeftContinuous A)
    (T : ℝ≥0) : IsLeftContinuous (truncBefore T A) := by
  intro t
  rcases le_total t T with h | h
  · -- on `(−∞, t] ⊆ (−∞, T]` the function agrees with `A`
    have : Filter.Tendsto (truncBefore T A) (nhdsWithin t (Set.Iio t))
        (nhds (A (min t T))) := by
      rw [min_eq_left h]
      refine Filter.Tendsto.congr' ?_ (hlc t).tendsto
      filter_upwards [self_mem_nhdsWithin] with v hv
      rw [truncBefore, min_eq_left (le_trans (le_of_lt hv) h)]
    exact this
  · -- past `T` the function is eventually the constant `A T`
    have : Filter.Tendsto (truncBefore T A) (nhdsWithin t (Set.Iio t))
        (nhds (A (min t T))) := by
      rcases lt_or_eq_of_le h with hTt | heq
      · rw [min_eq_right h]
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Ioo_mem_nhdsLT hTt] with v hv
        rw [truncBefore, min_eq_right (le_of_lt hv.1)]
      · rw [min_eq_right h]
        rw [← heq]
        refine Filter.Tendsto.congr' ?_ (hlc T).tendsto
        filter_upwards [self_mem_nhdsWithin] with v hv
        rw [truncBefore, min_eq_left (le_of_lt (heq ▸ hv))]
    exact this

/-- `truncBefore T A 0 = 0` for null-at-origin `A`. -/
theorem truncBefore_zero_eq {A : ℝ≥0 → ℝ≥0} (h0 : A 0 = 0) (T : ℝ≥0) :
    truncBefore T A 0 = 0 := by
  rw [truncBefore, min_eq_left zero_le]
  exact h0

/-- The before-`T` departures never exceed the before-`T` arrivals (for
causal pairs). -/
theorem truncBeforeD_le_truncBefore {A D : ℝ≥0 → ℝ≥0}
    (hc : ∀ u, D u ≤ A u) (T u : ℝ≥0) :
    truncBeforeD T A D u ≤ truncBefore T A u := by
  rw [truncBeforeD, truncBefore]
  rcases le_total u T with h | h
  · rw [min_eq_left h]
    exact le_trans (min_le_left _ _) (hc u)
  · rw [min_eq_right h]
    exact min_le_right _ _

/-- `truncBeforeD` is monotone for monotone `D`. -/
theorem truncBeforeD_mono {A D : ℝ≥0 → ℝ≥0} (hmono : Monotone D)
    (T : ℝ≥0) : Monotone (truncBeforeD T A D) :=
  fun _ _ hab => min_le_min (hmono hab) le_rfl

/-- `truncBeforeD` is left-continuous for left-continuous `D`. -/
theorem truncBeforeD_leftCont {A D : ℝ≥0 → ℝ≥0}
    (hlc : IsLeftContinuous D) (T : ℝ≥0) :
    IsLeftContinuous (truncBeforeD T A D) := fun t =>
  ContinuousWithinAt.inf (hlc t) continuousWithinAt_const

/-- `truncBeforeD T A D 0 = 0` for null-at-origin `D`. -/
theorem truncBeforeD_zero_eq {A D : ℝ≥0 → ℝ≥0} (h0 : D 0 = 0) (T : ℝ≥0) :
    truncBeforeD T A D 0 = 0 := by
  rw [truncBeforeD, h0]
  exact min_eq_left zero_le

/-- `truncAfter` is monotone for monotone `A`. -/
theorem truncAfter_mono {A : ℝ≥0 → ℝ≥0} (hmono : Monotone A) (T : ℝ≥0) :
    Monotone (truncAfter T A) :=
  fun _ _ hab => tsub_le_tsub_right (hmono hab) _

/-- `truncAfterD` is monotone for monotone `D`. -/
theorem truncAfterD_mono {A D : ℝ≥0 → ℝ≥0} (hmono : Monotone D)
    (T : ℝ≥0) : Monotone (truncAfterD T A D) :=
  fun _ _ hab => tsub_le_tsub_right (hmono hab) _

/-- `truncAfter T A 0 = 0` for null-at-origin `A`. -/
theorem truncAfter_zero_eq {A : ℝ≥0 → ℝ≥0} (h0 : A 0 = 0) (T : ℝ≥0) :
    truncAfter T A 0 = 0 := by
  rw [truncAfter, h0, zero_tsub]

/-- `truncAfterD T A D 0 = 0` for null-at-origin `D`. -/
theorem truncAfterD_zero_eq {A D : ℝ≥0 → ℝ≥0} (h0 : D 0 = 0) (T : ℝ≥0) :
    truncAfterD T A D 0 = 0 := by
  rw [truncAfterD, h0, zero_tsub]

/-! ## The EDF server -/

/-- **EDF family of trajectories** with deadlines `d`: for every horizon
`T`, while data with absolute deadline by `T` is backlogged throughout
`[s, t]` (the aggregate of the parts arrived by `T − dₖ`), the part of
flow `j` with deadline after `T` (arrived after `T − dⱼ`) receives
nothing on `(s, t]`. (The book prints the pairwise relation between
single derived flows, which is insufficient for the residual-theorem
proof — the backlogged part alternates across flows; the aggregate
premise matches its static-priority definition, and
`isEdf_premise_of_single` recovers the pairwise reading.) -/
def IsEdf {ι : Type*} [Fintype ι] (d : ι → ℝ≥0)
    (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ j, ∀ T s t : ℝ≥0, s ≤ t →
    (∀ u ∈ Set.Icc s t,
      (∑ k, truncBeforeD (T - d k) (A k) (D k) u)
        < ∑ k, truncBefore (T - d k) (A k) u) →
    truncAfterD (T - d j) (A j) (D j) t
      = truncAfterD (T - d j) (A j) (D j) s

/-- A single backlogged deadline-`T` part suffices for the EDF freeze
premise (for causal pairs): the aggregate transfer. -/
theorem isEdf_premise_of_single {ι : Type*} [Fintype ι] {d : ι → ℝ≥0}
    {A D : ι → ℝ≥0 → ℝ≥0} (hc : ∀ k u, D k u ≤ A k u)
    {T u : ℝ≥0} (i : ι)
    (hbl : truncBeforeD (T - d i) (A i) (D i) u
      < truncBefore (T - d i) (A i) u) :
    (∑ k, truncBeforeD (T - d k) (A k) (D k) u)
      < ∑ k, truncBefore (T - d k) (A k) u :=
  Finset.sum_lt_sum
    (fun k _ => truncBeforeD_le_truncBefore (hc k) (T - d k) u)
    ⟨i, Finset.mem_univ i, hbl⟩

/-- **EDF `n`-server**: every served family obeys the deadline-ordered
priority. -/
def IsEdfServerN {ι : Type*} [Fintype ι] (d : ι → ℝ≥0)
    (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ As Ds, S As Ds → IsEdf d (fun j => ⇑(As j)) (fun j => ⇑(Ds j))

/-! ## The EDF residual family -/

/-- The EDF residual curve at offset `θ`: each cross-flow is shifted by
`[θ − Δᵢⱼ]⁺ = (θ + dⱼ) − dᵢ`, and the whole is clamped by `δ_θ` —
`[β − ∑_{j≠i} αⱼ(· − ((θ + dⱼ) − dᵢ))]⁺ ∧ δ_θ`. -/
noncomputable def edfResidual {ι : Type*} [Fintype ι] (β : ℝ≥0 → ℝ≥0∞)
    (α : ι → ℝ≥0 → ℝ≥0) (d : ι → ℝ≥0) (i : ι) (θ : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun v => if v ≤ θ then 0
    else β v - ((∑ j ∈ Finset.univ.erase i,
      α j (v - ((θ + d j) - d i)) : ℝ≥0) : ℝ≥0∞)

/-- `edfResidual` reads off by cases at `θ`. -/
theorem edfResidual_apply {ι : Type*} [Fintype ι] (β : ℝ≥0 → ℝ≥0∞)
    (α : ι → ℝ≥0 → ℝ≥0) (d : ι → ℝ≥0) (i : ι) (θ v : ℝ≥0) :
    edfResidual β α d i θ v = if v ≤ θ then 0
      else β v - ((∑ j ∈ Finset.univ.erase i,
        α j (v - ((θ + d j) - d i)) : ℝ≥0) : ℝ≥0∞) := rfl

/-- `edfResidual β α d i θ 0 = 0`. -/
theorem edfResidual_zero_eq {ι : Type*} [Fintype ι] (β : ℝ≥0 → ℝ≥0∞)
    (α : ι → ℝ≥0 → ℝ≥0) (d : ι → ℝ≥0) (i : ι) (θ : ℝ≥0) :
    edfResidual β α d i θ 0 = 0 := if_pos zero_le

/-- **EDF degenerates to FIFO**: with all deadlines equal, the EDF
residual is the FIFO residual. -/
theorem edfResidual_const_deadline {ι : Type*} [Fintype ι]
    (β : ℝ≥0 → ℝ≥0∞) (α : ι → ℝ≥0 → ℝ≥0) (c : ℝ≥0) (i : ι) (θ : ℝ≥0) :
    edfResidual β α (fun _ => c) i θ
      = fifoResidual β
          (fun v => ((∑ j ∈ Finset.univ.erase i, α j v : ℝ≥0) : ℝ≥0∞)) θ := by
  funext v
  rw [edfResidual_apply, fifoResidual_apply]
  by_cases hv : v ≤ θ
  · rw [if_pos hv, if_pos hv]
  · rw [if_neg hv, if_neg hv]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_tsub_cancel_right]

/-- **The EDF residual family**: an EDF family (deadlines `d`) whose
aggregate obeys a strict service inequality for a left-continuous `β`,
with cross-traffic arrival curves `αⱼ`, is served per flow at
`edfResidual β α d i θ` for every offset `θ`. -/
theorem minConv_edfResidual_le_of_isEdf {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0} {d : ι → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hβlc : IsLeftContinuous β)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    (hedf : IsEdf d (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j))
    (θ τ : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (edfResidual (Deviation.liftENN β) α d i θ) τ
      ≤ ((Ds i) τ : ℝ≥0∞) := by
  set t : ℝ≥0 := τ - θ with htdef
  have htτ : t ≤ τ := tsub_le_self
  by_cases hD : (As i) t ≤ (Ds i) τ
  · -- the data arrived by `t` is served by `τ`: split `(t, τ − t)`
    have hres : edfResidual (Deviation.liftENN β) α d i θ (τ - t) = 0 :=
      if_pos tsub_tsub_le
    refine le_trans (minConv_le_add _ _ (add_tsub_cancel_of_le htτ)) ?_
    rw [hres, add_zero]
    exact_mod_cast hD
  · push Not at hD
    -- the filtered family: data with absolute deadline by `t + dᵢ`
    set X : ι → ℝ≥0 := fun k => (t + d i) - d k with hXdef
    have hXi : X i = t := by
      simp only [hXdef]
      exact tsub_eq_of_eq_add rfl
    set FA : ι → ℝ≥0 → ℝ≥0 := fun k => truncBefore (X k) ⇑(As k) with hFA
    set FD : ι → ℝ≥0 → ℝ≥0 :=
      fun k => truncBeforeD (X k) ⇑(As k) ⇑(Ds k) with hFD
    have hFc : ∀ k u, FD k u ≤ FA k u := fun k u =>
      truncBeforeD_le_truncBefore (fun u => hc k u) (X k) u
    set p : ℝ≥0 := start (fun x => ∑ k, FA k x) (fun x => ∑ k, FD k x) t
      with hpdef
    have hpt : p ≤ t := start_le _ _ t
    have hpτ : p ≤ τ := hpt.trans htτ
    -- per-flow equality at the filtered start
    have hfloweq : ∀ k, FD k p = FA k p :=
      apply_start_sum_eq (fun k x => hFc k x)
        (fun k => truncBefore_leftCont (As k).leftCont (X k))
        (fun k => truncBeforeD_leftCont (Ds k).leftCont (X k))
        (fun k => (truncBefore_zero_eq (As k).zero (X k)).trans
          (truncBeforeD_zero_eq (Ds k).zero (X k)).symm) t
    have hDi_lt : ∀ u, u ≤ τ → (Ds i) u < (As i) t :=
      fun u hu => lt_of_le_of_lt ((Ds i).mono hu) hD
    have hFDi : ∀ u, u ≤ τ → FD i u = (Ds i) u := by
      intro u hu
      show min ((Ds i) u) ((As i) (X i)) = (Ds i) u
      rw [hXi]
      exact min_eq_left (le_of_lt (hDi_lt u hu))
    -- flow i's filtered part is backlogged on the closed `[t, τ]`
    have hbli : ∀ u, u ∈ Set.Icc t τ → FD i u < FA i u := by
      intro u hu
      rw [hFDi u hu.2]
      show (Ds i) u < (As i) (min u (X i))
      rw [hXi, min_eq_right hu.1]
      exact hDi_lt u hu.2
    -- the filtered aggregate is backlogged at every point of `(p, τ]`
    have hblF : ∀ u, u ∈ Set.Ioc p τ →
        (∑ k, FD k u) < ∑ k, FA k u := by
      intro u hu
      rcases le_total u t with hut | htu
      · exact isBacklogged_Ioc_start
          (fun x => Finset.sum_le_sum fun k _ => hFc k x) t u ⟨hu.1, hut⟩
      · exact Finset.sum_lt_sum (fun k _ => hFc k u)
          ⟨i, Finset.mem_univ i, hbli u ⟨htu, hu.2⟩⟩
    -- the full aggregate is backlogged on `(p, τ]`
    have hblFull : IsBacklogged (fun x => ∑ k, (As k) x)
        (fun x => ∑ k, (Ds k) x) (Set.Ioc p τ) := by
      intro u hu
      obtain ⟨k, hk⟩ : ∃ k, FD k u < FA k u := by
        by_contra hcon
        push Not at hcon
        exact absurd (hblF u hu)
          (not_lt.mpr (Finset.sum_le_sum fun k _ => hcon k))
      refine Finset.sum_lt_sum (fun j _ => hc j u) ⟨k, Finset.mem_univ k, ?_⟩
      have hk' : min ((Ds k) u) ((As k) (X k)) < (As k) (min u (X k)) := hk
      rcases le_total u (X k) with h | h
      · rw [min_eq_left h] at hk'
        rcases le_total ((Ds k) u) ((As k) (X k)) with h2 | h2
        · rwa [min_eq_left h2] at hk'
        · rw [min_eq_right h2] at hk'
          exact absurd ((As k).mono h) (not_le.mpr hk')
      · rw [min_eq_right h] at hk'
        rcases le_total ((Ds k) u) ((As k) (X k)) with h2 | h2
        · exact lt_of_lt_of_le (by rwa [min_eq_left h2] at hk')
            ((As k).mono h)
        · rw [min_eq_right h2] at hk'
          exact absurd le_rfl (not_le.mpr hk')
    -- the after-deadline parts are frozen on `(p, τ]`
    have hfreeze : ∀ k, ∀ s' w : ℝ≥0, p < s' → s' ≤ w → w ≤ τ →
        truncAfterD (X k) ⇑(As k) ⇑(Ds k) w
          = truncAfterD (X k) ⇑(As k) ⇑(Ds k) s' := by
      intro k s' w hps' hs'w hwτ
      refine hedf k (t + d i) s' w hs'w fun u hu => ?_
      exact hblF u ⟨lt_of_lt_of_le hps' hu.1, hu.2.trans hwτ⟩
    -- the filtered start is strictly before `t`
    have hplt : p < t := by
      rcases lt_or_eq_of_le hpt with h | heq
      · exact h
      · exact absurd ((heq ▸ hfloweq i : FD i t = FA i t))
          (ne_of_lt (hbli t ⟨le_rfl, htτ⟩))
    -- in this case `t` is positive and `τ = t + θ` exactly
    have ht0 : 0 < t := by
      by_contra hcon
      push Not at hcon
      have ht00 : t = 0 := le_antisymm hcon zero_le
      have hA0 : (As i) 0 = 0 := (As i).zero
      rw [ht00, hA0] at hD
      exact absurd hD (not_lt.mpr zero_le)
    have hθτ : θ ≤ τ := by
      by_contra hcon
      push Not at hcon
      exact absurd (htdef.trans (tsub_eq_zero_of_le hcon.le))
        (ne_of_gt ht0)
    have hτeq : (τ : ℝ) = (t : ℝ) + θ := by
      rw [htdef]
      push_cast [NNReal.coe_sub hθτ]
      ring
    -- cross-flow increments are bounded at the residual shifts
    have hshift : ∀ k, k ≠ i →
        FD k τ ≤ FD k p + α k ((τ - p) - ((θ + d k) - d i)) := by
      intro k hk
      have hbase : FD k p = (As k) (min p (X k)) := hfloweq k
      rcases le_total (X k) p with hXp | hpX
      · -- the filter closed before `p`: no increment at all
        refine le_trans ?_ le_self_add
        rw [hbase, min_eq_right hXp]
        exact le_trans (hFc k τ) ((As k).mono (min_le_right _ _))
      · -- one arrival increment from `p`
        have hkey : min τ (X k) ≤ p + ((τ - p) - ((θ + d k) - d i)) := by
          rcases le_total (θ + d k) (d i) with hsk | hsk
          · rw [tsub_eq_zero_of_le hsk, tsub_zero,
              add_tsub_cancel_of_le hpτ]
            exact min_le_left _ _
          · rcases le_total ((θ + d k) - d i) (τ - p) with hcmp | hcmp
            · rcases le_total (d k) (t + d i) with hdk | hdk
              · refine le_trans (min_le_right τ (X k)) ?_
                rw [← NNReal.coe_le_coe]
                rw [show (X k : ℝ≥0) = (t + d i) - d k from rfl]
                push_cast [NNReal.coe_sub hdk, NNReal.coe_sub hsk,
                  NNReal.coe_sub hcmp, NNReal.coe_sub hpτ]
                linarith [hτeq]
              · rw [show X k = 0 from tsub_eq_zero_of_le hdk,
                  min_eq_right zero_le]
                exact zero_le
            · rw [tsub_eq_zero_of_le hcmp, add_zero]
              rcases le_total (d k) (t + d i) with hdk | hdk
              · refine le_trans (min_le_right τ (X k)) ?_
                rw [← NNReal.coe_le_coe]
                rw [show (X k : ℝ≥0) = (t + d i) - d k from rfl]
                push_cast [NNReal.coe_sub hdk]
                -- from `τ − p ≤ θ + dₖ − dᵢ`: `t + dᵢ − dₖ ≤ p`
                have hcmp' : (τ : ℝ) - p ≤ (θ : ℝ) + d k - d i := by
                  have h1 : ((τ - p : ℝ≥0) : ℝ) ≤ (((θ + d k) - d i : ℝ≥0) : ℝ) := by
                    exact_mod_cast hcmp
                  rwa [NNReal.coe_sub hpτ, NNReal.coe_sub hsk] at h1
                linarith [hτeq]
              · rw [show X k = 0 from tsub_eq_zero_of_le hdk,
                  min_eq_right zero_le]
                exact zero_le
        calc FD k τ ≤ (As k) (min τ (X k)) := hFc k τ
          _ ≤ (As k) (p + ((τ - p) - ((θ + d k) - d i))) :=
              (As k).mono hkey
          _ ≤ (As k) p + α k ((τ - p) - ((θ + d k) - d i)) :=
              (isMaximalArrivalBound_iff_increment _ _).mp (harr k hk) p _
          _ = FD k p + α k ((τ - p) - ((θ + d k) - d i)) := by
              rw [hbase, min_eq_left hpX]
    -- flow i at the filtered start: served exactly its arrivals
    have hAip : FD i p = (As i) p := by
      rw [hfloweq i]
      show (As i) (min p (X i)) = (As i) p
      rw [hXi, min_eq_left hplt.le]
    -- the anchored strict step leaves the residual to flow i
    have hanch : ∀ s' : ℝ≥0, p < s' → s' ≤ τ →
        β (τ - s') ≤ (∑ k ∈ Finset.univ.erase i,
            α k ((τ - p) - ((θ + d k) - d i)))
          + ((Ds i) τ - (As i) p) := by
      intro s' hps' hs'τ
      have hstr := hstrict s' τ hs'τ fun u hu =>
        hblFull u ⟨lt_trans hps' hu.1, hu.2⟩
      have hsplitD : ∀ u : ℝ≥0, (∑ k, (Ds k) u)
          = (∑ k, FD k u)
            + ∑ k, truncAfterD (X k) ⇑(As k) ⇑(Ds k) u := by
        intro u
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ =>
          (truncBeforeD_add_truncAfterD (X k) _ _ u).symm
      rw [hsplitD s', hsplitD τ,
        show (∑ k, truncAfterD (X k) ⇑(As k) ⇑(Ds k) τ)
            = ∑ k, truncAfterD (X k) ⇑(As k) ⇑(Ds k) s' from
          Finset.sum_congr rfl fun k _ =>
            hfreeze k s' τ hps' hs'τ le_rfl] at hstr
      have hstr2 : (∑ k, FD k s') + β (τ - s') ≤ ∑ k, FD k τ := by
        have h2 : ((∑ k, FD k s') + β (τ - s'))
              + ∑ k, truncAfterD (X k) ⇑(As k) ⇑(Ds k) s'
            ≤ (∑ k, FD k τ)
              + ∑ k, truncAfterD (X k) ⇑(As k) ⇑(Ds k) s' := by
          calc ((∑ k, FD k s') + β (τ - s'))
                + ∑ k, truncAfterD (X k) ⇑(As k) ⇑(Ds k) s'
              = ((∑ k, FD k s')
                  + ∑ k, truncAfterD (X k) ⇑(As k) ⇑(Ds k) s')
                + β (τ - s') := by ring
            _ ≤ (∑ k, FD k τ)
                + ∑ k, truncAfterD (X k) ⇑(As k) ⇑(Ds k) s' := hstr
        exact le_of_add_le_add_right h2
      rw [← Finset.add_sum_erase _ (fun k => FD k s') (Finset.mem_univ i),
        ← Finset.add_sum_erase _ (fun k => FD k τ)
          (Finset.mem_univ i)] at hstr2
      have hcross : ∑ k ∈ Finset.univ.erase i, FD k τ
          ≤ (∑ k ∈ Finset.univ.erase i, FD k s')
            + ∑ k ∈ Finset.univ.erase i,
                α k ((τ - p) - ((θ + d k) - d i)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun k hk => ?_
        refine le_trans (hshift k (Finset.ne_of_mem_erase hk)) ?_
        exact add_le_add
          (truncBeforeD_mono (Ds k).mono (X k) hps'.le) le_rfl
      have hcore := tsub_le_of_aggregate_step hstr2 hcross
        (le_of_eq (hFDi τ le_rfl))
        (le_trans (truncBeforeD_mono (Ds i).mono (X i) hs'τ)
          (le_of_eq (hFDi τ le_rfl)))
      have hcore' : β (τ - s')
          - (∑ k ∈ Finset.univ.erase i,
              α k ((τ - p) - ((θ + d k) - d i)))
          ≤ (Ds i) τ - (As i) p := by
        refine le_trans hcore ?_
        refine tsub_le_tsub_left ?_ _
        rw [← hAip]
        exact truncBeforeD_mono (Ds i).mono (X i) hps'.le
      exact tsub_le_iff_left.mp hcore'
    -- pass `β` through its left limit at `τ − p`
    have hτp : 0 < τ - p := tsub_pos_of_lt (lt_of_lt_of_le hplt htτ)
    have hlim : β (τ - p) ≤ (∑ k ∈ Finset.univ.erase i,
          α k ((τ - p) - ((θ + d k) - d i)))
        + ((Ds i) τ - (As i) p) := by
      have hne : (𝓝[<] (τ - p)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτp⟩
      refine le_of_tendsto (hβlc (τ - p)).tendsto ?_
      filter_upwards [Ioo_mem_nhdsLT hτp] with σ' hσ'
      have hσ'τ : σ' ≤ τ := le_trans hσ'.2.le tsub_le_self
      have hps' : p < τ - σ' := by
        have h1 : τ - σ' = p + ((τ - p) - σ') := by
          rw [← NNReal.coe_inj]
          push_cast [NNReal.coe_sub hσ'τ, NNReal.coe_sub hpτ,
            NNReal.coe_sub hσ'.2.le]
          ring
        rw [h1]
        exact lt_add_of_pos_right p (tsub_pos_of_lt hσ'.2)
      have happ := hanch (τ - σ') hps' tsub_le_self
      rwa [tsub_tsub_cancel_of_le hσ'τ] at happ
    -- conclude through the split `(p, τ − p)`
    refine le_trans (minConv_le_add _ _ (add_tsub_cancel_of_le hpτ)) ?_
    have hresneg : ¬ (τ - p ≤ θ) := by
      rw [not_le, ← NNReal.coe_lt_coe]
      push_cast [NNReal.coe_sub hpτ]
      have hpt' : (p : ℝ) < t := by exact_mod_cast hplt
      linarith [hτeq]
    rw [show edfResidual (Deviation.liftENN β) α d i θ (τ - p)
        = Deviation.liftENN β (τ - p)
          - ((∑ k ∈ Finset.univ.erase i,
              α k ((τ - p) - ((θ + d k) - d i)) : ℝ≥0) : ℝ≥0∞) from
      if_neg hresneg]
    show ((As i) p : ℝ≥0∞)
        + (((β (τ - p) : ℝ≥0) : ℝ≥0∞)
          - ((∑ k ∈ Finset.univ.erase i,
              α k ((τ - p) - ((θ + d k) - d i)) : ℝ≥0) : ℝ≥0∞))
      ≤ ((Ds i) τ : ℝ≥0∞)
    rw [← ENNReal.coe_sub, ← ENNReal.coe_add, ENNReal.coe_le_coe]
    have hbS : β (τ - p)
        - (∑ k ∈ Finset.univ.erase i,
            α k ((τ - p) - ((θ + d k) - d i)))
        ≤ (Ds i) τ - (As i) p := tsub_le_iff_left.mpr hlim
    calc (As i) p + (β (τ - p)
          - ∑ k ∈ Finset.univ.erase i,
              α k ((τ - p) - ((θ + d k) - d i)))
        ≤ (As i) p + ((Ds i) τ - (As i) p) := add_le_add le_rfl hbS
      _ = (Ds i) τ := add_tsub_cancel_of_le
          (le_trans (le_of_eq hAip.symm)
            (le_trans (truncBeforeD_mono (Ds i).mono (X i) hpτ)
              (le_of_eq (hFDi τ le_rfl))))

/-- For monotone cross-flow `αⱼ` the EDF residual is the book's wedge
`[β − ∑_{j≠i} αⱼ ∗ δ_{[θ−Δᵢⱼ]⁺}]⁺ ∧ δ_θ`: each summand is a
convolution with the burst-delay at the clamped shift, and the `δ_θ`
clamp absorbs the per-flow shifts below `θ`. -/
theorem edfResidual_eq_min_conv_delayNN {ι : Type*} [Fintype ι]
    {β : ℝ≥0 → ℝ≥0∞} {α : ι → ℝ≥0 → ℝ≥0} {d : ι → ℝ≥0} {i : ι} {θ : ℝ≥0}
    (hαmono : ∀ j, j ≠ i → Monotone (α j)) :
    edfResidual β α d i θ
      = fun v => min (β v
          - ∑ j ∈ Finset.univ.erase i,
              minConv (Deviation.liftENN (α j))
                (delayNN ((θ + d j) - d i)) v)
        (delayNN θ v) := by
  funext v
  rw [edfResidual_apply]
  have hconv : ∀ j ∈ Finset.univ.erase i,
      minConv (Deviation.liftENN (α j)) (delayNN ((θ + d j) - d i)) v
        = ((α j (v - ((θ + d j) - d i)) : ℝ≥0) : ℝ≥0∞) := fun j hj => by
    rw [conv_delayNN _ (Deviation.monotone_liftENN
      (hαmono j (Finset.ne_of_mem_erase hj))) _]
  by_cases hv : v ≤ θ
  · rw [if_pos hv, show delayNN θ v = 0 from delay_eq_zero θ hv,
      min_eq_right zero_le]
  · rw [if_neg hv, show delayNN θ v = ⊤ from delay_eq_top θ (not_le.mp hv),
      min_eq_left le_top, Finset.sum_congr rfl hconv,
      ← ENNReal.ofNNReal_finsetSum]

/-! ## Deadline compatibility -/

/-- **Deadline compatibility**: every flow's arrivals are served within
its relative deadline — `Aᵢ ∗ δ_{dᵢ} ≤ Dᵢ`, pointwise
`Aᵢ(t − dᵢ) ≤ Dᵢ(t)`. -/
def IsDeadlineCompatible {ι : Type*} (d : ι → ℝ≥0)
    (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i t, A i (t - d i) ≤ D i t

/-- Deadline compatibility bounds the shifted arrival curves by the
aggregate output: for curve-realizing arrivals,
`∑ₖ αₖ(t − dₖ) ≤ ∑ⱼ Dⱼ(t)`. -/
theorem sum_apply_tsub_le_sum_of_isDeadlineCompatible {ι : Type*}
    [Fintype ι] {As Ds : ι → Curve} {α : ι → ℝ≥0 → ℝ≥0} {d : ι → ℝ≥0}
    (hA : ∀ i t, (As i) t = α i t)
    (hcompat : IsDeadlineCompatible d
      (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (t : ℝ≥0) :
    (∑ k, α k (t - d k)) ≤ ∑ j, (Ds j) t := by
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← hA k (t - d k)]
  exact hcompat k t

/-- **Deadline compatibility bounds the curve** (the necessary
condition): a greedily served family realizing its arrival curves that
meets every deadline forces the aggregate min-plus curve to dominate
the shifted arrival curves, `∑ᵢ αᵢ(s − dᵢ) ≤ β(s)`. -/
theorem sum_apply_tsub_le_of_isDeadlineCompatible {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0∞} {α : ι → ℝ≥0 → ℝ≥0}
    {d : ι → ℝ≥0}
    (hA : ∀ i t, (As i) t = α i t)
    (hgreedy : ∀ x, ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞)
      ≤ minConv (Deviation.liftENN (fun y => ∑ j, (As j) y)) β x)
    (hcompat : IsDeadlineCompatible d
      (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (s : ℝ≥0) :
    ((∑ i, α i (s - d i) : ℝ≥0) : ℝ≥0∞) ≤ β s := by
  calc ((∑ i, α i (s - d i) : ℝ≥0) : ℝ≥0∞)
      ≤ ((∑ i, (Ds i) s : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_le_coe]
        exact sum_apply_tsub_le_sum_of_isDeadlineCompatible hA hcompat s
    _ ≤ minConv (Deviation.liftENN (fun y => ∑ j, (As j) y)) β s :=
        hgreedy s
    _ ≤ Deviation.liftENN (fun y => ∑ j, (As j) y) 0 + β s :=
        minConv_le_add _ _ (zero_add s)
    _ = β s := by
        show ((∑ j, (As j) 0 : ℝ≥0) : ℝ≥0∞) + β s = β s
        rw [show (∑ j, (As j) 0) = 0 from
            Finset.sum_eq_zero fun j _ => (As j).zero,
          ENNReal.coe_zero, zero_add]

/-- **EDF is deadline compatible under the capacity condition**
(the sufficiency of the book's deadline-compatibility theorem): if the
service curve dominates the shifted arrival curves pointwise,
`∑ₖ αₖ(t − dₖ) ≤ β(t)`, then an EDF family with `αₖ`-constrained
arrivals meets every deadline. The residual at `θ = dᵢ` shifts each
cross-flow by exactly `dⱼ`, and the capacity condition leaves `αᵢ`'s
own share. (The book requires the condition only below the first
crossing of `β` with `∑ αₖ` — the busy-period cap — so the unrestricted
form here is a strictly stronger hypothesis; threading the cap through
the residual theorem is the remaining refinement.) -/
theorem isDeadlineCompatible_of_isEdf {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0}
    {d : ι → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hβlc : IsLeftContinuous β)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    (hedf : IsEdf d (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (harr : ∀ j, IsMaximalArrivalBound ⇑(As j) (α j))
    (hpoint : ∀ t, (∑ k, α k (t - d k)) ≤ β t) :
    IsDeadlineCompatible d (fun j => ⇑(As j)) (fun j => ⇑(Ds j)) := by
  intro i τ
  have h79 := minConv_edfResidual_le_of_isEdf (i := i) hc hβlc hstrict hedf
    (fun j _ => harr j) (d i) τ
  have hlow : ((As i) (τ - d i) : ℝ≥0∞)
      ≤ minConv (Deviation.liftENN ⇑(As i))
          (edfResidual (Deviation.liftENN β) α d i (d i)) τ := by
    refine le_minConv fun u s hus => ?_
    by_cases hs : s ≤ d i
    · -- short shift: the arrival point is already inside the split
      have hu : τ - d i ≤ u := by
        rw [← hus]
        exact tsub_le_iff_right.mpr (add_le_add le_rfl hs)
      refine le_trans ?_ le_self_add
      exact_mod_cast (As i).mono hu
    · -- long shift: the capacity condition leaves `αᵢ`'s share
      have hresge : ((α i (s - d i) : ℝ≥0) : ℝ≥0∞)
          ≤ edfResidual (Deviation.liftENN β) α d i (d i) s := by
        rw [edfResidual_apply, if_neg hs,
          show (∑ j ∈ Finset.univ.erase i,
              α j (s - ((d i + d j) - d i)))
            = ∑ j ∈ Finset.univ.erase i, α j (s - d j) from
            Finset.sum_congr rfl fun j _ => by
              rw [add_tsub_cancel_left (d i) (d j)]]
        refine ENNReal.le_sub_of_add_le_right ENNReal.coe_ne_top ?_
        show ((α i (s - d i) : ℝ≥0) : ℝ≥0∞)
            + ((∑ j ∈ Finset.univ.erase i, α j (s - d j) : ℝ≥0) : ℝ≥0∞)
          ≤ ((β s : ℝ≥0) : ℝ≥0∞)
        rw [← ENNReal.coe_add, ENNReal.coe_le_coe,
          Finset.add_sum_erase _ (fun k => α k (s - d k))
            (Finset.mem_univ i)]
        exact hpoint s
      have hsplit : (τ - d i) = u + (s - d i) := by
        rw [← hus, ← NNReal.coe_inj]
        push_cast [NNReal.coe_sub (not_le.mp hs).le,
          NNReal.coe_sub (show d i ≤ u + s from
            le_trans (not_le.mp hs).le le_add_self)]
        ring
      have hinc : (As i) (τ - d i) ≤ (As i) u + α i (s - d i) := by
        rw [hsplit]
        exact (isMaximalArrivalBound_iff_increment _ _).mp (harr i) u _
      calc ((As i) (τ - d i) : ℝ≥0∞)
          ≤ ((As i) u : ℝ≥0∞) + ((α i (s - d i) : ℝ≥0) : ℝ≥0∞) := by
            rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
            exact hinc
        _ ≤ ((As i) u : ℝ≥0∞)
            + edfResidual (Deviation.liftENN β) α d i (d i) s :=
            add_le_add le_rfl hresge
  have := le_trans hlow h79
  exact_mod_cast this

/-- **Deadline compatibility forces the capacity condition where the
output is within the curve** (the necessity, at the greedy trajectory):
at any point where the aggregate output is dominated by `β`
(`∑ⱼ Dⱼ(t) ≤ β(t)`), compatibility for curve-realizing arrivals yields
`∑ₖ αₖ(t − dₖ) ≤ β(t)`. -/
theorem sum_apply_tsub_le_of_isDeadlineCompatible_of_sum_le {ι : Type*}
    [Fintype ι] {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {d : ι → ℝ≥0}
    (hA : ∀ i t, (As i) t = α i t)
    (hcompat : IsDeadlineCompatible d
      (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {t : ℝ≥0} (hDle : (∑ j, (Ds j) t) ≤ β t) :
    (∑ k, α k (t - d k)) ≤ β t :=
  le_trans
    (sum_apply_tsub_le_sum_of_isDeadlineCompatible hA hcompat t) hDle

/-! ## Book restatement (the EDF residual family)
An EDF `n`-server with deadlines `dᵢ` offering a strict service curve
`β` (left-continuous, per the same repair as static priority) to flows
with arrival curves `αⱼ` offers flow `i` the residual
`βᵢ^θ = [β − ∑_{j≠i} αⱼ ∗ δ_{[θ−Δᵢⱼ]⁺}]⁺ ∧ δ_θ` for every `θ` — the
wedge reduces to `edfResidual` through `conv_delayNN`. (As in the FIFO
family, the book's constraint on flow `i` itself and the monotonicity
of the `αⱼ` beyond the bundles' use here are unnecessary.) -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {As Ds : ι → Curve}
    {β : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0} {d : ι → ℝ≥0}
    (hSrv : IsServerN S) (hS : IsEdfServerN d S) (hp : S As Ds)
    (hβlc : IsLeftContinuous β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalCurve ⇑(As j) (α j))
    (θ τ : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (fun v => min (Deviation.liftENN β v
          - ∑ j ∈ Finset.univ.erase i,
              minConv (Deviation.liftENN (α j))
                (delayNN ((θ + d j) - d i)) v)
          (delayNN θ v)) τ
      ≤ ((Ds i) τ : ℝ≥0∞) := by
  rw [show (fun v => min (Deviation.liftENN β v
        - ∑ j ∈ Finset.univ.erase i,
            minConv (Deviation.liftENN (α j))
              (delayNN ((θ + d j) - d i)) v)
        (delayNN θ v))
      = edfResidual (Deviation.liftENN β) α d i θ from
    (edfResidual_eq_min_conv_delayNN fun j hj => (harr j hj).1).symm]
  refine minConv_edfResidual_le_of_isEdf (fun j => hSrv.1 As Ds hp j)
    hβlc ?_ (hS As Ds hp) (fun j hj => (harr j hj).2) θ τ
  exact hβ.sum_strict hp

/-! ## Book restatement (deadline compatibility, necessary condition)
If an `n`-server whose aggregate offers the min-plus service curve `β`
is deadline compatible for `d₁,…,dₙ` under constraints `α₁,…,αₙ`, then
`β ≥ ∑ᵢ αᵢ ∗ δ_{dᵢ}` — witnessed at the greedy trajectory whose
arrivals realize the constraints and whose aggregate output is
`A ∗ β`. The condition is not sufficient for min-plus aggregates (the
book's two-flow figure); for strict aggregates the EDF scheduler makes
it sufficient (`isDeadlineCompatible_of_isEdf` above, restated below).
The book caps the capacity condition below the first crossing of `β`
with `∑ αₖ`; the busy-period-capped iff is the remaining refinement. -/
example {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0∞} {α : ι → ℝ≥0 → ℝ≥0}
    {d : ι → ℝ≥0}
    (hA : ∀ i t, (As i) t = α i t)
    (hαmono : ∀ i, Monotone (α i))
    (hgreedy : ∀ x, ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞)
      ≤ minConv (Deviation.liftENN (fun y => ∑ j, (As j) y)) β x)
    (hcompat : IsDeadlineCompatible d
      (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (s : ℝ≥0) :
    (∑ i, minConv (Deviation.liftENN (α i)) (delayNN (d i)) s) ≤ β s := by
  calc (∑ i, minConv (Deviation.liftENN (α i)) (delayNN (d i)) s)
      = ∑ i, ((α i (s - d i) : ℝ≥0) : ℝ≥0∞) :=
        Finset.sum_congr rfl fun i _ => by
          rw [conv_delayNN _ (Deviation.monotone_liftENN (hαmono i)) (d i)]
    _ = ((∑ i, α i (s - d i) : ℝ≥0) : ℝ≥0∞) :=
        (ENNReal.ofNNReal_finsetSum _ _).symm
    _ ≤ β s := sum_apply_tsub_le_of_isDeadlineCompatible hA hgreedy
        hcompat s

/-! ## Book restatement (deadline compatibility, sufficient condition)
An EDF `n`-server with deadlines `dᵢ` offering a strict left-continuous
service curve `β` to flows with arrival curves `αᵢ` meets every
deadline when `∑ᵢ αᵢ ∗ δ_{dᵢ} ≤ β` (stated pointwise and unrestricted;
the book caps the condition below the first crossing of `β` with
`∑ αᵢ`). -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {As Ds : ι → Curve}
    {β : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0} {d : ι → ℝ≥0}
    (hSrv : IsServerN S) (hS : IsEdfServerN d S) (hp : S As Ds)
    (hβlc : IsLeftContinuous β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (harr : ∀ j, IsMaximalArrivalCurve ⇑(As j) (α j))
    (hpoint : ∀ s, (∑ i, minConv (Deviation.liftENN (α i))
        (delayNN (d i)) s) ≤ ((β s : ℝ≥0) : ℝ≥0∞)) :
    IsDeadlineCompatible d (fun j => ⇑(As j)) (fun j => ⇑(Ds j)) := by
  refine isDeadlineCompatible_of_isEdf (fun j => hSrv.1 As Ds hp j) hβlc
    ?_ (hS As Ds hp) (fun j => (harr j).2) ?_
  · exact hβ.sum_strict hp
  · intro t
    have h := hpoint t
    rw [show (∑ i, minConv (Deviation.liftENN (α i)) (delayNN (d i)) t)
          = ((∑ i, α i (t - d i) : ℝ≥0) : ℝ≥0∞) from by
        rw [ENNReal.ofNNReal_finsetSum]
        exact Finset.sum_congr rfl fun i _ => by
          rw [conv_delayNN _
            (Deviation.monotone_liftENN (harr i).1) (d i)]] at h
    exact_mod_cast h

end DeepWiki
