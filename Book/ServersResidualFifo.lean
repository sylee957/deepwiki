import Book.ServersResidual
import Book.ServersJitter

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

/-- **FIFO family of trajectories**: if flow `i`'s data arrived by `u`
has departed by `t`, the same holds for every flow `j`. The book's twin
condition is the contrapositive (`isFifo_iff`). -/
def IsFifo {ι : Type*} (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i j, ∀ t u : ℝ≥0, A i u < D i t → A j u ≤ D j t

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

/-- **FIFO per-flow delay bound**: under the hypotheses of the
delay-based residual, `dM` bounds the delay of every flow. -/
theorem delay_le_of_isFifo {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {α β : ℝ≥0 → ℝ≥0∞} {dM : ℝ≥0}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hβmono : Monotone β)
    (harr : IsMaximalArrivalBound
      (Deviation.liftENN (fun x => ∑ j, (As j) x)) α)
    (hserv : ∀ x, minConv (Deviation.liftENN (fun x => ∑ j, (As j) x)) β x
      ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞))
    (hd : (hDev α β : ℝ≥0∞) ≤ (dM : ℝ≥0∞)) (i : ι) :
    Deviation.delay ⇑(As i) ⇑(Ds i) ≤ (dM : ℝ≥0∞) := by
  refine hDev_le fun t => ?_
  refine hDevAt_le ?_
  have h := apply_tsub_le_of_isFifo hfifo hβmono harr hserv hd i (t + dM)
  rwa [add_tsub_cancel_right] at h

/-! ## Book restatement (FIFO delay-based residual)
A FIFO `n`-server offering a min-plus service curve `β` to flows with
arrival curves `αⱼ` offers each flow the residual service curve
`δ_dM` at any `dM ≥ hDev(∑ⱼ αⱼ, β)` — in convolution form
`Aᵢ ∗ δ_dM ≤ Dᵢ` — and `dM` bounds every flow's delay. (The aggregate
arrival curve `∑ⱼ αⱼ` is supplied by the aggregation chapter.) -/
example {ι : Type*} [Fintype ι] {As Ds : ι → Curve}
    {α β : ℝ≥0 → ℝ≥0∞} {dM : ℝ≥0}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hβmono : Monotone β)
    (harr : IsMaximalArrivalBound
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
  exact_mod_cast apply_tsub_le_of_isFifo hfifo hβmono harr hserv hd i t

end DeepWiki
