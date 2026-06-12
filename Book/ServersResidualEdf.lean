import Book.ServersResidualFifo

/-! # Earliest deadline first
Each flow carries a relative deadline `dᵢ`; the scheduler serves the
data with the smallest absolute deadline. Formally, for every horizon
`T` the part of flow `i` arrived by `T − dᵢ` (`truncBefore`) has
static-priority precedence over the part of flow `j` arrived after
`T − dⱼ` (`truncAfter`) — `IsEdf`. The residual family `edfResidual`
shifts each cross-flow by `[θ − Δᵢⱼ]⁺` (in `ℝ≥0`: `(θ + dⱼ) − dᵢ`) and
degenerates to the FIFO family when all deadlines agree. Deadline
compatibility (`IsDeadlineCompatible`) forces the aggregate min-plus
curve to dominate the shifted arrival curves. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

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
  rw [truncBefore, min_eq_left zero_le']
  exact h0

/-! ## The EDF server -/

/-- **EDF family of trajectories** with deadlines `d`: for every horizon
`T`, while the part of flow `i` with absolute deadline by `T` (arrived
by `T − dᵢ`) is backlogged throughout `[s, t]`, the part of flow `j`
with deadline after `T` (arrived after `T − dⱼ`) receives nothing on
`(s, t]`. -/
def IsEdf {ι : Type*} (d : ι → ℝ≥0) (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i j, ∀ T s t : ℝ≥0, s ≤ t →
    (∀ u ∈ Set.Icc s t,
      truncBeforeD (T - d i) (A i) (D i) u
        < truncBefore (T - d i) (A i) u) →
    truncAfterD (T - d j) (A j) (D j) t
      = truncAfterD (T - d j) (A j) (D j) s

/-- **EDF `n`-server**: every served family obeys the deadline-ordered
priority. -/
def IsEdfServerN {ι : Type*} (d : ι → ℝ≥0)
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
    edfResidual β α d i θ 0 = 0 := if_pos zero_le'

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

/-! ## Deadline compatibility -/

/-- **Deadline compatibility**: every flow's arrivals are served within
its relative deadline — `Aᵢ ∗ δ_{dᵢ} ≤ Dᵢ`, pointwise
`Aᵢ(t − dᵢ) ≤ Dᵢ(t)`. -/
def IsDeadlineCompatible {ι : Type*} (d : ι → ℝ≥0)
    (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i t, A i (t - d i) ≤ D i t

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
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← hA i (s - d i)]
        exact hcompat i s
    _ ≤ minConv (Deviation.liftENN (fun y => ∑ j, (As j) y)) β s :=
        hgreedy s
    _ ≤ Deviation.liftENN (fun y => ∑ j, (As j) y) 0 + β s :=
        minConv_le_add _ _ (zero_add s)
    _ = β s := by
        show ((∑ j, (As j) 0 : ℝ≥0) : ℝ≥0∞) + β s = β s
        rw [show (∑ j, (As j) 0) = 0 from
            Finset.sum_eq_zero fun j _ => (As j).zero,
          ENNReal.coe_zero, zero_add]

/-! ## Book restatement (deadline compatibility, necessary condition)
If an `n`-server whose aggregate offers the min-plus service curve `β`
is deadline compatible for `d₁,…,dₙ` under constraints `α₁,…,αₙ`, then
`β ≥ ∑ᵢ αᵢ ∗ δ_{dᵢ}` — witnessed at the greedy trajectory whose
arrivals realize the constraints and whose aggregate output is
`A ∗ β`. The condition is not sufficient for min-plus aggregates (the
book's two-flow figure); for strict aggregates it is, via the EDF
scheduler — the sufficiency direction is deferred with the EDF residual
theorem. -/
example {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0∞} {α : ι → ℝ≥0 → ℝ≥0}
    {d : ι → ℝ≥0}
    (hA : ∀ i t, (As i) t = α i t)
    (hgreedy : ∀ x, ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞)
      ≤ minConv (Deviation.liftENN (fun y => ∑ j, (As j) y)) β x)
    (hcompat : IsDeadlineCompatible d
      (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (s : ℝ≥0) :
    ((∑ i, α i (s - d i) : ℝ≥0) : ℝ≥0∞) ≤ β s :=
  sum_apply_tsub_le_of_isDeadlineCompatible hA hgreedy hcompat s

end DeepWiki
