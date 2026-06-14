import DeepWiki.NetworkCalculus.ServersResidual
import DeepWiki.NetworkCalculus.ServersJitter
import DeepWiki.NetworkCalculus.ConvolutionMinimum

/-! # FIFO residual service
A FIFO `n`-server serves all data in arrival order across flows: if one
flow's data arrived by `u` has departed by `t`, so has every other
flow's (`IsFifo`, the book's two implications being contrapositives).
Aggregate comparisons then transfer per flow, so an aggregate min-plus
service curve `β` with aggregate arrival curve `α` gives every flow the
pure-delay residual `δ_dM` for any `dM ≥ hDev α β` — and `dM` bounds
every flow's delay. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Set Topology Filter

/-- **FIFO family of trajectories**: if flow `i`'s data arrived by `u`
has departed by `t`, the same holds for every flow `j`. The book's twin
condition is the contrapositive (`isFifo_iff`). -/
def IsFifo {ι : Type*} (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i j, ∀ t u : ℝ≥0, A i u < D i t → A j u ≤ D j t

/-- **FIFO `n`-server**: every served family satisfies the FIFO
trajectory condition. -/
def IsFifoServerN {ι : Type*}
    (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ As Ds, S As Ds → IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j))

/-- The book's second FIFO condition is the contrapositive of the
first: data still queued for one flow is still queued for all. -/
theorem isFifo_iff {ι : Type*} (A D : ι → ℝ≥0 → ℝ≥0) :
    IsFifo A D ↔ ∀ i j, ∀ t u : ℝ≥0, D j t < A j u → D i t ≤ A i u := by
  constructor
  · intro h i j t u hju
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (h i j t u hcon) (not_le.mpr hju)
  · intro h i j t u hiu
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (h i j t u hcon) (not_le.mpr hiu)

/-- **Aggregation of FIFO flows**, served side: an aggregate comparison
`∑ Aⱼ(u) ≤ ∑ Dⱼ(t)` transfers to every flow. -/
theorem forall_le_of_sum_le_of_isFifo {ι : Type*} [Fintype ι]
    {A D : ι → ℝ≥0 → ℝ≥0} (h : IsFifo A D) {t u : ℝ≥0}
    (hsum : ∑ j, A j u ≤ ∑ j, D j t) : ∀ i, A i u ≤ D i t := by
  intro i
  by_contra hcon
  rw [not_le] at hcon
  have hall : ∀ j, D j t ≤ A j u := fun j =>
    (isFifo_iff A D).mp h j i t u hcon
  exact absurd hsum (not_le.mpr (Finset.sum_lt_sum (fun j _ => hall j)
    ⟨i, Finset.mem_univ i, hcon⟩))

/-- **Aggregation of FIFO flows**, queued side: an aggregate comparison
`∑ Dⱼ(t) ≤ ∑ Aⱼ(u)` transfers to every flow. -/
theorem forall_le_of_le_sum_of_isFifo {ι : Type*} [Fintype ι]
    {A D : ι → ℝ≥0 → ℝ≥0} (h : IsFifo A D) {t u : ℝ≥0}
    (hsum : ∑ j, D j t ≤ ∑ j, A j u) : ∀ i, D i t ≤ A i u := by
  intro i
  by_contra hcon
  rw [not_le] at hcon
  have hall : ∀ j, A j u ≤ D j t := fun j => h i j t u hcon
  exact absurd hsum (not_le.mpr (Finset.sum_lt_sum (fun j _ => hall j)
    ⟨i, Finset.mem_univ i, hcon⟩))

/-- **FIFO delay-based residual service**: a FIFO family whose aggregate
is served at min-plus `β` (left-continuous arrivals) with aggregate
arrival curve `α` serves each flow at the pure delay `δ_dM` for any
`dM ≥ hDev α β`: `Aᵢ(t − dM) ≤ Dᵢ(t)`. -/
theorem apply_tsub_le_of_isFifo {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {α β : ℝ≥0 → ℝ≥0∞} {dM : ℝ≥0}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hβmono : Monotone β)
    (harr : IsMaximalArrivalBound
      (Deviation.liftENN (fun x => ∑ j, (As j) x)) α)
    (hserv : ∀ x, minConv (Deviation.liftENN (fun x => ∑ j, (As j) x)) β x
      ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞))
    (hd : (hDev α β : ℝ≥0∞) ≤ (dM : ℝ≥0∞)) (i : ι) (t : ℝ≥0) :
    (As i) (t - dM) ≤ (Ds i) t := by
  have hagg : (∑ j, (As j) (t - dM)) ≤ ∑ j, (Ds j) t :=
    Deviation.apply_tsub_le_of_hDev_le_of_leftCont
      (A := fun x => ∑ j, (As j) x) (D := fun x => ∑ j, (Ds j) x)
      (by show (∑ j, (As j) 0) = 0
          have hA : ∀ j : ι, (As j) 0 = 0 := fun j => (As j).zero
          simp [hA])
      (fun a b hab => Finset.sum_le_sum fun j _ => (As j).mono hab)
      (isLeftContinuous_sum _ fun j _ => (As j).leftCont)
      hβmono
      (fun a b hab => Finset.sum_le_sum fun j _ => (Ds j).mono hab)
      harr hserv hd t
  exact forall_le_of_sum_le_of_isFifo hfifo hagg i

/-- **FIFO transfers delay to the flows**: with no arrival or service
hypotheses at all, each flow's delay is bounded by the aggregate's —
every shift admissible for the aggregate is admissible per flow. -/
theorem delay_le_delay_sum_of_isFifo {ι : Type*} [Fintype ι]
    {A D : ι → ℝ≥0 → ℝ≥0} (h : IsFifo A D) (i : ι) :
    Deviation.delay (A i) (D i)
      ≤ Deviation.delay (fun x => ∑ j, A j x) (fun x => ∑ j, D j x) := by
  refine iSup_mono fun t => ?_
  refine le_iInf fun d => ?_
  exact iInf_le_of_le ⟨d.1, forall_le_of_sum_le_of_isFifo h d.2 i⟩ le_rfl

/-- **FIFO per-flow delay bound**: the aggregate's horizontal deviation
`hDev(α, β)` bounds the delay of every flow. -/
theorem delay_le_hDev_of_isFifo {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {α β : ℝ≥0 → ℝ≥0∞}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hβmono : Monotone β)
    (harr : IsMaximalArrivalBound
      (Deviation.liftENN (fun x => ∑ j, (As j) x)) α)
    (hserv : ∀ x, minConv (Deviation.liftENN (fun x => ∑ j, (As j) x)) β x
      ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞)) (i : ι) :
    Deviation.delay ⇑(As i) ⇑(Ds i) ≤ (hDev α β : ℝ≥0∞) :=
  le_trans (delay_le_delay_sum_of_isFifo hfifo i)
    (Deviation.delay_le_hDev
      (fun _ _ hab => Finset.sum_le_sum fun j _ => (As j).mono hab)
      hβmono harr hserv)

/-! ## Book restatement (FIFO delay-based residual)
A FIFO `n`-server offering a min-plus service curve `β` to flows with
arrival curves `αⱼ` offers each flow the residual service curve
`δ_dM` at any `dM ≥ hDev(∑ⱼ αⱼ, β)` — in convolution form
`Aᵢ ∗ δ_dM ≤ Dᵢ` — and `dM` bounds every flow's delay. (The aggregate
arrival curve `∑ⱼ αⱼ` is supplied by the aggregation chapter; the
hypotheses are per served pair of a FIFO `n`-server,
`IsFifoServerN`.) -/
example {ι : Type*} [Fintype ι] {As Ds : ι → Curve}
    {α β : ℝ≥0 → ℝ≥0∞} {dM : ℝ≥0}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hβmono : Monotone β)
    (harr : IsMaximalArrivalCurve
      (Deviation.liftENN (fun x => ∑ j, (As j) x)) α)
    (hserv : ∀ x, minConv (Deviation.liftENN (fun x => ∑ j, (As j) x)) β x
      ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞))
    (hd : (hDev α β : ℝ≥0∞) ≤ (dM : ℝ≥0∞)) (i : ι) (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i)) (delayNN dM) t
      ≤ ((Ds i) t : ℝ≥0∞) := by
  have hAmonoE : Monotone (Deviation.liftENN ⇑(As i)) :=
    fun u v huv => ENNReal.coe_le_coe.mpr ((As i).mono huv)
  rw [conv_delayNN _ hAmonoE dM]
  show ((As i) (t - dM) : ℝ≥0∞) ≤ ((Ds i) t : ℝ≥0∞)
  exact_mod_cast apply_tsub_le_of_isFifo hfifo hβmono harr.2 hserv hd i t

/-! ## The θ-family of FIFO residual curves -/

/-- The FIFO residual curve at offset `θ`:
`[β − α(· − θ)]⁺ ∧ δ_θ` — zero up to `θ`, then the service left after
the cross-traffic shifted by `θ`. -/
noncomputable def fifoResidual (β α : ℝ≥0 → ℝ≥0∞) (θ : ℝ≥0) :
    ℝ≥0 → ℝ≥0∞ :=
  fun v => if v ≤ θ then 0 else β v - α (v - θ)

/-- `fifoResidual` reads off by cases at `θ`. -/
theorem fifoResidual_apply (β α : ℝ≥0 → ℝ≥0∞) (θ v : ℝ≥0) :
    fifoResidual β α θ v = if v ≤ θ then 0 else β v - α (v - θ) := rfl

/-- `fifoResidual β α θ 0 = 0`. -/
theorem fifoResidual_zero_eq (β α : ℝ≥0 → ℝ≥0∞) (θ : ℝ≥0) :
    fifoResidual β α θ 0 = 0 := if_pos zero_le'

/-- For monotone `α` the FIFO residual is the book's wedge
`[β − α ∗ δ_θ]⁺ ∧ δ_θ` pointwise. -/
theorem fifoResidual_eq_min_conv_delayNN {β α : ℝ≥0 → ℝ≥0∞} {θ : ℝ≥0}
    (hαmono : Monotone α) :
    fifoResidual β α θ
      = fun v => min (β v - minConv α (delayNN θ) v) (delayNN θ v) := by
  funext v
  show (if v ≤ θ then 0 else β v - α (v - θ))
      = min (β v - minConv α (delayNN θ) v) (delayNN θ v)
  have hconv : minConv α (delayNN θ) v = α (v - θ) := by
    rw [conv_delayNN α hαmono θ]
  rw [hconv]
  by_cases hv : v ≤ θ
  · rw [if_pos hv, show delayNN θ v = 0 from delay_eq_zero θ hv,
      min_eq_right zero_le']
  · rw [if_neg hv, show delayNN θ v = ⊤ from delay_eq_top θ (not_le.mp hv),
      min_eq_left le_top]

/-- **The FIFO residual θ-family**: a FIFO family whose aggregate is
served at a non-decreasing left-continuous min-plus `β`, with
cross-traffic arrival curves `αⱼ`, serves flow `i` at
`[β − ∑_{j≠i} αⱼ(· − θ)]⁺ ∧ δ_θ` for every `θ`. (The book also assumes
the `αⱼ` non-decreasing; the increment bound at the exact shift makes
that unnecessary.) -/
theorem minConv_fifoResidual_le_of_isFifo {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0∞} {α : ι → ℝ≥0 → ℝ≥0}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hβmono : Monotone β) (hβlc : IsLeftContinuous β)
    (hserv : ∀ x, minConv (Deviation.liftENN (fun y => ∑ j, (As j) y)) β x
      ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞))
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j))
    (θ t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (fifoResidual β
          (fun v => ((∑ j ∈ Finset.univ.erase i, α j v : ℝ≥0) : ℝ≥0∞)) θ) t
      ≤ ((Ds i) t : ℝ≥0∞) := by
  classical
  by_cases hall : ∀ v, (∑ j, (As j) v) ≤ ∑ j, (Ds j) t
  · -- everything ever arriving is served by `t`: the `(t, 0)` split
    have hit : (As i) t ≤ (Ds i) t :=
      forall_le_of_sum_le_of_isFifo hfifo (hall t) i
    refine le_trans (minConv_le_add _ _ (add_zero t)) ?_
    rw [show fifoResidual β _ θ 0 = 0 from fifoResidual_zero_eq _ _ _,
      add_zero]
    exact_mod_cast hit
  · push Not at hall
    obtain ⟨w, hw⟩ := hall
    have hbdd : BddAbove {v : ℝ≥0 | (∑ j, (As j) v) ≤ ∑ j, (Ds j) t} := by
      refine ⟨w, fun v hv => ?_⟩
      by_contra hcon
      push Not at hcon
      exact absurd (le_trans
        (Finset.sum_le_sum fun j _ => (As j).mono hcon.le) hv) (not_le.mpr hw)
    set u : ℝ≥0 := sSup {v : ℝ≥0 | (∑ j, (As j) v) ≤ ∑ j, (Ds j) t}
      with hudef
    -- the sup itself is served, by left-continuity of the arrivals
    have humem : (∑ j, (As j) u) ≤ ∑ j, (Ds j) t := by
      rcases eq_zero_or_pos u with hu0 | hu0
      · rw [hu0]
        exact le_trans
          (le_of_eq (Finset.sum_eq_zero fun j _ => (As j).zero)) zero_le
      · have hne : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu0⟩
        refine le_of_tendsto
          ((isLeftContinuous_sum Finset.univ
            fun j _ => (As j).leftCont) u).tendsto ?_
        filter_upwards [self_mem_nhdsWithin] with v hv
        have hv' : v < sSup {v : ℝ≥0 |
            (∑ j, (As j) v) ≤ ∑ j, (Ds j) t} := by
          rw [← hudef]
          exact hv
        obtain ⟨v', hv'mem, hvv'⟩ := exists_lt_of_lt_csSup
          ⟨0, show (∑ j, (As j) 0) ≤ ∑ j, (Ds j) t from le_trans
            (le_of_eq (Finset.sum_eq_zero fun j _ => (As j).zero))
            zero_le⟩ hv' 
        exact le_trans
          (Finset.sum_le_sum fun j _ => (As j).mono hvv'.le) hv'mem
    -- beyond the sup nothing is served yet
    have habove : ∀ v, u < v → (∑ j, (Ds j) t) < ∑ j, (As j) v := by
      intro v hv
      by_contra hcon
      push Not at hcon
      exact absurd (le_csSup hbdd hcon) (not_le.mpr hv)
    have htransfer : ∀ j, (As j) u ≤ (Ds j) t :=
      forall_le_of_sum_le_of_isFifo hfifo humem
    by_cases hcase : t - θ ≤ u
    · -- the residual window is empty: split at `min u t`
      set u' : ℝ≥0 := min u t with hu'def
      have hu't : u' ≤ t := min_le_right u t
      have hres0 : t - u' ≤ θ := by
        rcases le_total u t with hut | htu
        · rw [hu'def, min_eq_left hut]
          calc t - u ≤ t - (t - θ) :=
              tsub_le_tsub_left hcase t
            _ ≤ θ := tsub_tsub_le
        · rw [hu'def, min_eq_right htu, tsub_self]
          exact zero_le'
      refine le_trans (minConv_le_add _ _ (add_tsub_cancel_of_le hu't)) ?_
      rw [show fifoResidual β _ θ (t - u') = 0 from if_pos hres0, add_zero]
      have : (As i) u' ≤ (Ds i) t :=
        le_trans ((As i).mono (min_le_left u t)) (htransfer i)
      exact_mod_cast this
    · -- the attainment route: the optimal split is below the sup
      push Not at hcase
      obtain ⟨s, hs, heq⟩ := exists_minConv_eq_split_of_curves_of_contAt
        (Deviation.liftENN (fun y => ∑ j, (As j) y)) β
        (fun a b hab => ENNReal.coe_le_coe.mpr
          (Finset.sum_le_sum fun j _ => (As j).mono hab))
        hβmono
        (fun x => (ENNReal.continuous_coe.continuousAt).comp_continuousWithinAt
          ((isLeftContinuous_sum Finset.univ fun j _ => (As j).leftCont) x))
        hβlc t
        (fun _ => Continuous.continuousAt continuous_add)
      have hkey : ((∑ j, (As j) s : ℝ≥0) : ℝ≥0∞) + β (t - s)
          ≤ ((∑ j, (Ds j) t : ℝ≥0) : ℝ≥0∞) := heq ▸ hserv t
      have hsu : s ≤ u := by
        refine le_csSup hbdd ?_
        have h1 : ((∑ j, (As j) s : ℝ≥0) : ℝ≥0∞)
            ≤ ((∑ j, (Ds j) t : ℝ≥0) : ℝ≥0∞) := le_trans le_self_add hkey
        exact_mod_cast h1
    -- the cross-traffic by `t` is below its arrivals at `t − θ`
      have hcross : ∀ j, (Ds j) t ≤ (As j) (t - θ) :=
        forall_le_of_le_sum_of_isFifo hfifo (habove (t - θ) hcase).le
      have hsθ : s ≤ t - θ := le_of_lt (lt_of_le_of_lt hsu hcase)
      have hθt : θ ≤ t :=
        (tsub_pos_iff_lt.mp (lt_of_le_of_lt zero_le' hcase)).le
      have hθts : θ < t - s := by
        refine lt_tsub_iff_left.mpr ?_
        calc s + θ < (t - θ) + θ :=
            add_lt_add_of_lt_of_le (lt_of_le_of_lt hsu hcase) le_rfl
          _ = t := tsub_add_cancel_of_le hθt
      -- the assembled chain: the split at `s` pays at most the residual
      have hchain : ((As i) s : ℝ≥0∞) + β (t - s)
          ≤ ((Ds i) t : ℝ≥0∞)
            + ((∑ j ∈ Finset.univ.erase i, α j (t - s - θ) : ℝ≥0) : ℝ≥0∞) := by
        have hD : (∑ j ∈ Finset.univ.erase i, (Ds j) t)
            ≤ (∑ j ∈ Finset.univ.erase i, (As j) s)
              + ∑ j ∈ Finset.univ.erase i, α j (t - s - θ) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun j hj => ?_
          have hne : j ≠ i := Finset.ne_of_mem_erase hj
          calc (Ds j) t ≤ (As j) (t - θ) := hcross j
            _ = (As j) (s + (t - θ - s)) := by
                rw [add_tsub_cancel_of_le hsθ]
            _ ≤ (As j) s + α j (t - θ - s) :=
                (isMaximalArrivalBound_iff_increment _ _).mp (harr j hne) s _
            _ = (As j) s + α j (t - s - θ) := by rw [tsub_right_comm]
        have hkey' : (((As i) s : ℝ≥0∞)
              + ((∑ j ∈ Finset.univ.erase i, (As j) s : ℝ≥0) : ℝ≥0∞))
              + β (t - s)
            ≤ ((Ds i) t : ℝ≥0∞)
              + ((∑ j ∈ Finset.univ.erase i, (Ds j) t : ℝ≥0) : ℝ≥0∞) := by
          have h1 := hkey
          rw [show (∑ j, (As j) s) = (As i) s
                + ∑ j ∈ Finset.univ.erase i, (As j) s from
              (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm,
            show (∑ j, (Ds j) t) = (Ds i) t
                + ∑ j ∈ Finset.univ.erase i, (Ds j) t from
              (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm,
            ENNReal.coe_add, ENNReal.coe_add] at h1
          exact h1
        have h2 : (((As i) s : ℝ≥0∞) + β (t - s))
              + ((∑ j ∈ Finset.univ.erase i, (As j) s : ℝ≥0) : ℝ≥0∞)
            ≤ (((Ds i) t : ℝ≥0∞)
                + ((∑ j ∈ Finset.univ.erase i,
                    α j (t - s - θ) : ℝ≥0) : ℝ≥0∞))
              + ((∑ j ∈ Finset.univ.erase i, (As j) s : ℝ≥0) : ℝ≥0∞) := by
          calc (((As i) s : ℝ≥0∞) + β (t - s))
                + ((∑ j ∈ Finset.univ.erase i, (As j) s : ℝ≥0) : ℝ≥0∞)
              = (((As i) s : ℝ≥0∞)
                  + ((∑ j ∈ Finset.univ.erase i, (As j) s : ℝ≥0) : ℝ≥0∞))
                + β (t - s) := by ring
            _ ≤ ((Ds i) t : ℝ≥0∞)
                + ((∑ j ∈ Finset.univ.erase i, (Ds j) t : ℝ≥0) : ℝ≥0∞) :=
                hkey'
            _ ≤ ((Ds i) t : ℝ≥0∞)
                + (((∑ j ∈ Finset.univ.erase i, (As j) s : ℝ≥0) : ℝ≥0∞)
                  + ((∑ j ∈ Finset.univ.erase i,
                      α j (t - s - θ) : ℝ≥0) : ℝ≥0∞)) := by
                refine add_le_add le_rfl ?_
                rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
                exact hD
            _ = (((Ds i) t : ℝ≥0∞)
                  + ((∑ j ∈ Finset.univ.erase i,
                      α j (t - s - θ) : ℝ≥0) : ℝ≥0∞))
                + ((∑ j ∈ Finset.univ.erase i, (As j) s : ℝ≥0) : ℝ≥0∞) := by
                ring
        exact (ENNReal.add_le_add_iff_right ENNReal.coe_ne_top).mp h2
      -- conclude through the split `(s, t − s)`
      refine le_trans (minConv_le_add _ _ (add_tsub_cancel_of_le hs.2)) ?_
      rw [show fifoResidual β
          (fun v => ((∑ j ∈ Finset.univ.erase i, α j v : ℝ≥0) : ℝ≥0∞)) θ
          (t - s)
        = β (t - s)
          - ((∑ j ∈ Finset.univ.erase i, α j (t - s - θ) : ℝ≥0) : ℝ≥0∞)
        from if_neg (not_le.mpr hθts)]
      by_cases hβα : β (t - s)
          ≤ ((∑ j ∈ Finset.univ.erase i, α j (t - s - θ) : ℝ≥0) : ℝ≥0∞)
      · rw [tsub_eq_zero_of_le hβα, add_zero]
        exact_mod_cast le_trans ((As i).mono hsu) (htransfer i)
      · have hle : ((∑ j ∈ Finset.univ.erase i,
            α j (t - s - θ) : ℝ≥0) : ℝ≥0∞) ≤ β (t - s) :=
          le_of_lt (not_le.mp hβα)
        have h4 : (((As i) s : ℝ≥0∞) + (β (t - s)
              - ((∑ j ∈ Finset.univ.erase i,
                  α j (t - s - θ) : ℝ≥0) : ℝ≥0∞)))
              + ((∑ j ∈ Finset.univ.erase i, α j (t - s - θ) : ℝ≥0) : ℝ≥0∞)
            ≤ ((Ds i) t : ℝ≥0∞)
              + ((∑ j ∈ Finset.univ.erase i,
                  α j (t - s - θ) : ℝ≥0) : ℝ≥0∞) := by
          calc (((As i) s : ℝ≥0∞) + (β (t - s)
              - ((∑ j ∈ Finset.univ.erase i,
                  α j (t - s - θ) : ℝ≥0) : ℝ≥0∞)))
                + ((∑ j ∈ Finset.univ.erase i,
                    α j (t - s - θ) : ℝ≥0) : ℝ≥0∞)
              = ((As i) s : ℝ≥0∞) + ((β (t - s)
                  - ((∑ j ∈ Finset.univ.erase i,
                      α j (t - s - θ) : ℝ≥0) : ℝ≥0∞))
                + ((∑ j ∈ Finset.univ.erase i,
                    α j (t - s - θ) : ℝ≥0) : ℝ≥0∞)) := add_assoc _ _ _
            _ = ((As i) s : ℝ≥0∞) + β (t - s) := by
                rw [tsub_add_cancel_of_le hle]
            _ ≤ _ := hchain
        exact (ENNReal.add_le_add_iff_right ENNReal.coe_ne_top).mp h4

/-! ## Book restatement (the FIFO residual θ-family)
A FIFO `n`-server offering a min-plus service curve `β` (non-decreasing,
left-continuous) to flows with arrival curves `αⱼ` offers flow `i` the
residual `β_i^θ = [β − ∑_{j≠i} αⱼ ∗ δ_θ]⁺ ∧ δ_θ` for every `θ` — the
wedge form reduces to `fifoResidual` through `conv_delayNN`, the
bundles' monotonicity carrying the identification. -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {As Ds : ι → Curve}
    {β : ℝ≥0 → ℝ≥0∞} {α : ι → ℝ≥0 → ℝ≥0}
    (hS : IsFifoServerN S) (hp : S As Ds)
    (hβmono : Monotone β) (hβlc : IsLeftContinuous β)
    (hserv : ∀ x, minConv (Deviation.liftENN (fun y => ∑ j, (As j) y)) β x
      ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞))
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalCurve ⇑(As j) (α j))
    (θ t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (fun v => min (β v
          - minConv
              (fun w => ((∑ j ∈ Finset.univ.erase i, α j w : ℝ≥0) : ℝ≥0∞))
              (delayNN θ) v)
          (delayNN θ v)) t
      ≤ ((Ds i) t : ℝ≥0∞) := by
  rw [show (fun v => min (β v
        - minConv
            (fun w => ((∑ j ∈ Finset.univ.erase i, α j w : ℝ≥0) : ℝ≥0∞))
            (delayNN θ) v)
        (delayNN θ v))
      = fifoResidual β
          (fun w => ((∑ j ∈ Finset.univ.erase i, α j w : ℝ≥0) : ℝ≥0∞)) θ
    from (fifoResidual_eq_min_conv_delayNN fun a b hab =>
      ENNReal.coe_le_coe.mpr (Finset.sum_le_sum fun j hj =>
        (harr j (Finset.ne_of_mem_erase hj)).1 hab)).symm]
  exact minConv_fifoResidual_le_of_isFifo (hS As Ds hp) hβmono hβlc hserv
    (fun j hj => (harr j hj).2) θ t

end DeepWiki
