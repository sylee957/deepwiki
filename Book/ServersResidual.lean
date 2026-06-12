import Book.ServersMimo
import Book.ServiceCurveStrictMinimal
import Book.ClosuresNd
import Book.DeviationsBoundsServer

/-! # Residual service under blind multiplexing
With no information on the service policy, a *weakly strict* aggregate
service curve already leaves a guarantee to each flow: the residual
server for flow `i` offers the min-plus service curve
`[β − ∑_{j≠i} αⱼ]⁺↑` (`residualCurve`), where the `αⱼ` constrain the
cross-traffic arrivals — the proof anchors at the start of the
aggregate's backlogged period, which is all the start-anchored bound
provides, and the strict hypothesis enters only as a corollary route.
If instead the cross-traffic *departures* are constrained, the
residual curve is strict; that proof runs inside backlogged windows
and genuinely consumes strictness. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The residual (leftover) curve `[β − α]⁺↑`: the non-decreasing closure
of the difference, the `ℝ≥0` truncated subtraction supplying the positive
part. -/
noncomputable def residualCurve (β α : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  ndClosure (fun v => β v - α v)

/-- `residualCurve β α t` is the supremum of the clamped differences up
to `t`. -/
theorem residualCurve_apply (β α : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    residualCurve β α t = ⨆ v : {v : ℝ≥0 // v ≤ t}, (β v.1 - α v.1) := rfl

/-- `residualCurve β α 0 = 0` when `β 0 = 0`. -/
theorem residualCurve_zero_eq {β : ℝ≥0 → ℝ≥0} (α : ℝ≥0 → ℝ≥0)
    (hβ0 : β 0 = 0) : residualCurve β α 0 = 0 := by
  refine le_antisymm (ciSup_le fun v => ?_) zero_le'
  have hv0 : v.1 = 0 := le_antisymm v.2 zero_le'
  show β v.1 - α v.1 ≤ 0
  rw [hv0, hβ0, zero_tsub]

/-- Intro: each clamped difference below `t` bounds `residualCurve β α t`
from below (under prefix-boundedness). -/
theorem tsub_le_residualCurve {β α : ℝ≥0 → ℝ≥0}
    (hbdd : ClosureBddAbove (fun v => β v - α v)) {v t : ℝ≥0} (hvt : v ≤ t) :
    β v - α v ≤ residualCurve β α t :=
  le_ciSup_of_le (hbdd t) ⟨v, hvt⟩ le_rfl

/-- Elim: `residualCurve β α t ≤ x` from the pointwise bounds on `[0, t]`. -/
theorem residualCurve_le {β α : ℝ≥0 → ℝ≥0} {x t : ℝ≥0}
    (h : ∀ v, v ≤ t → β v - α v ≤ x) :
    residualCurve β α t ≤ x :=
  ciSup_le fun v => h v.1 v.2

/-- `residualCurve β α` is monotone (under prefix-boundedness). -/
theorem residualCurve_mono {β α : ℝ≥0 → ℝ≥0}
    (hbdd : ClosureBddAbove (fun v => β v - α v)) :
    Monotone (residualCurve β α) :=
  ndClosure_mono _ hbdd

/-- For non-decreasing `β` the residual differences are prefix-bounded:
`β t` dominates every clamped difference on `[0, t]`. -/
theorem closureBddAbove_tsub_of_monotone {β α : ℝ≥0 → ℝ≥0}
    (hβ : Monotone β) : ClosureBddAbove (fun v => β v - α v) := fun t =>
  ⟨β t, by rintro x ⟨v, rfl⟩; exact le_trans tsub_le_self (hβ v.2)⟩

/-- `residualCurve β α` is monotone for non-decreasing `β`. -/
theorem residualCurve_mono_of_monotone {β α : ℝ≥0 → ℝ≥0}
    (hβ : Monotone β) : Monotone (residualCurve β α) :=
  residualCurve_mono (closureBddAbove_tsub_of_monotone hβ)

/-- The `ℝ≥0` cancellation core of the residual-service proofs: an
aggregate step of at least `b` minus a cross-traffic consumption of at
most `c` leaves the clamped difference to the tagged flow. -/
theorem tsub_le_of_aggregate_step {xs xv xt ys yv c b : ℝ≥0}
    (hstr : (xs + ys) + b ≤ xv + yv) (hcross : yv ≤ ys + c)
    (hxv : xv ≤ xt) (hxs : xs ≤ xt) :
    b - c ≤ xt - xs := by
  have hmain : xs + b ≤ xv + c := by
    have h2 : (xs + b) + ys ≤ (xv + c) + ys := by
      calc (xs + b) + ys = (xs + ys) + b := by ring
        _ ≤ xv + yv := hstr
        _ ≤ xv + (ys + c) := add_le_add le_rfl hcross
        _ = (xv + c) + ys := by ring
    exact le_of_add_le_add_right h2
  refine tsub_le_iff_right.mpr ?_
  calc b ≤ (xv + c) - xs := le_tsub_of_add_le_left hmain
    _ ≤ (xt + c) - xs := tsub_le_tsub_right (add_le_add hxv le_rfl) _
    _ = (xt - xs) + c := (tsub_add_eq_add_tsub hxs).symm

/-- A strict service inequality forces `β 0 = 0`: the empty backlogged
period `(s, s]` serves `β 0` instantly. -/
theorem beta_zero_eq_of_strict {A D β : ℝ≥0 → ℝ≥0}
    (hstrict : ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
      D s + β (t - s) ≤ D t) : β 0 = 0 := by
  have h := hstrict 0 0 le_rfl (fun u hu => absurd hu.2 (not_le.mpr hu.1))
  rw [tsub_zero] at h
  exact le_antisymm (by rwa [add_le_iff_nonpos_right] at h) zero_le'

/-- **Blind multiplexing from weakly strict service**: the aggregate
pair need only gain `β` from the start of each backlogged period —
the start is constant across the window, so the anchored bound covers
every shifted difference. Flow `i` is served at the min-plus residual
`[β − ∑_{j≠i} αⱼ]⁺↑`: `Aᵢ ∗ residualCurve ≤ Dᵢ`. -/
theorem minConv_residualCurve_le_of_wstrict_aggregate {ι : Type*}
    [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hws : ∀ w, (∑ j, (Ds j)
        (start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) w))
      + β (w - start (fun x => ∑ j, (As j) x)
          (fun x => ∑ j, (Ds j) x) w)
      ≤ ∑ j, (Ds j) w)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (Deviation.liftENN (residualCurve β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
      ≤ ((Ds i) t : ℝ≥0∞) := by
  have h0agg : (∑ j, (As j) 0) = ∑ j, (Ds j) 0 := by
    have hA : (∑ j, (As j) 0) = 0 :=
      Finset.sum_eq_zero fun j _ => ((As j).zero : (As j) 0 = 0)
    have hD : (∑ j, (Ds j) 0) = 0 :=
      Finset.sum_eq_zero fun j _ => ((Ds j).zero : (Ds j) 0 = 0)
    rw [hA, hD]
  set s₀ : ℝ≥0 := start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) t
    with hs₀def
  have hs₀t : s₀ ≤ t := start_le _ _ t
  -- per-flow equality at the start of the aggregate backlogged period
  have hfloweq : ∀ j, (Ds j) s₀ = (As j) s₀ :=
    apply_start_sum_eq (fun j x => hc j x)
      (fun j => (As j).leftCont) (fun j => (Ds j).leftCont)
      (fun j => ((As j).zero : (As j) 0 = 0).trans
        ((Ds j).zero : (Ds j) 0 = 0).symm) t
  -- every shifted difference is covered by what flow `i` receives
  have hv : ∀ v : ℝ≥0, v ≤ t - s₀ →
      β v - (∑ j ∈ Finset.univ.erase i, α j v)
        ≤ (Ds i) t - (Ds i) s₀ := by
    intro v hvle
    have hut : s₀ + v ≤ t := by
      calc s₀ + v ≤ s₀ + (t - s₀) := add_le_add le_rfl hvle
        _ = t := add_tsub_cancel_of_le hs₀t
    -- the start is constant across the window, so the anchored bound
    -- applies at `s₀ + v` with anchor `s₀`
    have hstartv : start (fun x => ∑ j, (As j) x)
        (fun x => ∑ j, (Ds j) x) (s₀ + v) = s₀ := by
      rw [hs₀def]
      exact start_eq_start_of_le h0agg
        (by rw [← hs₀def]; exact le_self_add) hut
    have hstr := hws (s₀ + v)
    rw [hstartv, add_tsub_cancel_left,
      ← Finset.add_sum_erase Finset.univ (fun j => (Ds j) s₀)
        (Finset.mem_univ i),
      ← Finset.add_sum_erase Finset.univ (fun j => (Ds j) (s₀ + v))
        (Finset.mem_univ i)] at hstr
    -- the cross-traffic consumed at most its arrival constraint
    have hcross : ∑ j ∈ Finset.univ.erase i, (Ds j) (s₀ + v)
        ≤ (∑ j ∈ Finset.univ.erase i, (Ds j) s₀)
          + ∑ j ∈ Finset.univ.erase i, α j v := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j hj => ?_
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      calc (Ds j) (s₀ + v) ≤ (As j) (s₀ + v) := hc j (s₀ + v)
        _ ≤ (As j) s₀ + α j v :=
          (isMaximalArrivalBound_iff_increment _ _).mp (harr j hne) s₀ v
        _ = (Ds j) s₀ + α j v := by rw [hfloweq j]
    exact tsub_le_of_aggregate_step hstr hcross
      ((Ds i).mono hut) ((Ds i).mono hs₀t)
  -- collect the supremum and split the convolution at `s₀`
  have hkey : (Ds i) s₀
      + residualCurve β (fun v => ∑ j ∈ Finset.univ.erase i, α j v) (t - s₀)
      ≤ (Ds i) t := by
    have hsup : residualCurve β
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v) (t - s₀)
        ≤ (Ds i) t - (Ds i) s₀ :=
      ciSup_le fun v => hv v.1 v.2
    calc (Ds i) s₀ + residualCurve β _ (t - s₀)
        ≤ (Ds i) s₀ + ((Ds i) t - (Ds i) s₀) := add_le_add le_rfl hsup
      _ = (Ds i) t := add_tsub_cancel_of_le ((Ds i).mono hs₀t)
  refine le_trans (minConv_le_add _ _ (add_tsub_cancel_of_le hs₀t)) ?_
  show ((As i) s₀ : ℝ≥0∞)
      + (residualCurve β (fun v => ∑ j ∈ Finset.univ.erase i, α j v)
          (t - s₀) : ℝ≥0∞)
    ≤ ((Ds i) t : ℝ≥0∞)
  rw [← hfloweq i, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  exact hkey

/-- **Blind multiplexing residual** under the strict aggregate
hypothesis — a corollary of the weakly strict form, which is all the
start-anchored argument ever uses. -/
theorem minConv_residualCurve_le_of_strict_aggregate {ι : Type*}
    [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (Deviation.liftENN (residualCurve β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
      ≤ ((Ds i) t : ℝ≥0∞) := by
  refine minConv_residualCurve_le_of_wstrict_aggregate hc ?_ harr t
  intro w
  exact hstrict (start _ _ w) w (start_le _ _ w)
    (isBacklogged_Ioc_start
      (fun x => Finset.sum_le_sum fun j _ => hc j x) w)

/-- **Strict residual service**: if the aggregate pair obeys a strict
service inequality for `β` and the cross-traffic *departures* are
`α`-constrained, then flow `i` obeys the strict service inequality for
`residualCurve β α` on its own backlogged periods (which sit inside the
aggregate's). -/
theorem add_residualCurve_le_of_strict_aggregate {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β α : ℝ≥0 → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    {i : ι}
    (hdep : IsMaximalArrivalBound
      (fun x => ∑ j ∈ Finset.univ.erase i, (Ds j) x) α)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s + residualCurve β α (t - s) ≤ (Ds i) t := by
  -- flow-`i` backlog forces aggregate backlog
  have hblagg : ∀ u, u ∈ Set.Ioc s t →
      (∑ j, (Ds j) u) < ∑ j, (As j) u :=
    isBacklogged_sum_of_isBacklogged (fun j _ x => hc j x) (Finset.mem_univ i) hbl
  have hv : ∀ v : ℝ≥0, v ≤ t - s → β v - α v ≤ (Ds i) t - (Ds i) s := by
    intro v hvle
    have hut : s + v ≤ t := by
      calc s + v ≤ s + (t - s) := add_le_add le_rfl hvle
        _ = t := add_tsub_cancel_of_le hst
    rcases eq_zero_or_pos v with rfl | hvpos
    · rw [beta_zero_eq_of_strict hstrict, zero_tsub]
      exact zero_le'
    · have hbl' : IsBacklogged (fun x => ∑ j, (As j) x)
          (fun x => ∑ j, (Ds j) x) (Set.Ioc s (s + v)) := fun u hu =>
        hblagg u ⟨hu.1, hu.2.trans hut⟩
      have hstr := hstrict s (s + v) le_self_add hbl'
      rw [add_tsub_cancel_left,
        ← Finset.add_sum_erase Finset.univ (fun j => (Ds j) s)
          (Finset.mem_univ i),
        ← Finset.add_sum_erase Finset.univ (fun j => (Ds j) (s + v))
          (Finset.mem_univ i)] at hstr
      have hcross : ∑ j ∈ Finset.univ.erase i, (Ds j) (s + v)
          ≤ (∑ j ∈ Finset.univ.erase i, (Ds j) s) + α v :=
        (isMaximalArrivalBound_iff_increment _ _).mp hdep s v
      exact tsub_le_of_aggregate_step hstr hcross
        ((Ds i).mono hut) ((Ds i).mono hst)
  have hsup : residualCurve β α (t - s) ≤ (Ds i) t - (Ds i) s :=
    ciSup_le fun v => hv v.1 v.2
  calc (Ds i) s + residualCurve β α (t - s)
      ≤ (Ds i) s + ((Ds i) t - (Ds i) s) := add_le_add le_rfl hsup
    _ = (Ds i) t := add_tsub_cancel_of_le ((Ds i).mono hst)

/-- A strict aggregate service curve gives the plain-function sum form
of the strict service inequality on each served family — the `hstrict`
premise of the pair-level residual theorems. -/
theorem IsStrictMinimalServiceCurve.sum_strict {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds) :
    ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t := by
  intro s t hst hbl
  have h := hβ (∑ j, As j) (∑ j, Ds j) (aggregateServer_sum hp) s t hst
    (by rwa [Curve.coe_sum, Curve.coe_sum])
  rwa [Curve.sum_apply, Curve.sum_apply] at h

/-- A min-plus aggregate service curve gives the plain-function sum
form of the service inequality on each served family — the `hserv`
premise of the pair-level warning theorem. -/
theorem IsMinimalServiceCurve.sum_minConv_le {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → EReal}
    (hβ : IsMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds) :
    minConv (liftEReal (fun x => ∑ j, (As j) x)) β
      ≤ liftEReal (fun x => ∑ j, (Ds j) x) := by
  have h := hβ (∑ j, As j) (∑ j, Ds j) (aggregateServer_sum hp)
  rwa [curveEReal_eq_liftEReal, curveEReal_eq_liftEReal,
    Curve.coe_sum, Curve.coe_sum] at h

/-- Relation form of blind multiplexing: an `n`-server offering a strict
aggregate service curve serves each pair's flow `i` at the min-plus
residual of the cross-traffic arrival constraints. -/
theorem minConv_residualCurve_le_of_isStrictMinimalServiceCurve
    {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (Deviation.liftENN (residualCurve β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
      ≤ ((Ds i) t : ℝ≥0∞) := by
  exact minConv_residualCurve_le_of_strict_aggregate
    (fun j => hcaus As Ds hp j) (hβ.sum_strict hp) harr t

/-- Relation form of the strict residual: restricting an `n`-server with
a strict aggregate service curve to pairs whose cross-traffic departures
are `α`-constrained, the residual server for flow `i` offers
`residualCurve β α` as a strict service curve. -/
theorem isStrictMinimalServiceCurve_residualServer {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β α : ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S)) :
    IsStrictMinimalServiceCurve (residualCurve β α)
      (residualServer (fun A D => S A D ∧ IsMaximalArrivalBound
        (fun x => ∑ j ∈ Finset.univ.erase i, (D j) x) α) i) := by
  rintro Ai Di ⟨As, Ds, ⟨hp, hdep⟩, rfl, rfl⟩ s t hst hbl
  exact add_residualCurve_le_of_strict_aggregate
    (fun j => hcaus As Ds hp j) (hβ.sum_strict hp) hdep hst hbl

/-- **The residual server offers the residual curve** (the book's
residual-service-curve reading of blind multiplexing): restricting an
`n`-server with a strict aggregate curve to pairs with `αⱼ`-constrained
cross-traffic, the residual server for flow `i` offers
`[β − ∑_{j≠i} αⱼ]⁺↑` as a min-plus service curve. -/
theorem isMinimalServiceCurve_residualServer {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S)) :
    IsMinimalServiceCurve
      (liftEReal (residualCurve β
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v)))
      (residualServer (fun A D => S A D ∧
        ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(A j) (α j)) i) := by
  rintro Ai Di ⟨As, Ds, ⟨hp, harr⟩, rfl, rfl⟩
  intro t
  have h := minConv_residualCurve_le_of_isStrictMinimalServiceCurve
    hcaus hβ hp harr t
  rw [show Deviation.liftENN (residualCurve β
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v))
      = Deviation.toENN (liftEReal (residualCurve β
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v)))
    from (Deviation.toENN_liftEReal _).symm] at h
  rw [curveEReal_apply]
  exact (Deviation.minConv_toENN_le_coe_iff (As i)
    (isNonneg_liftEReal _) ((Ds i) t) t).mp h

/-- A weakly strict aggregate service curve gives the start-anchored
sum form on each served family — the `hws` premise of the weakly
strict residual theorem. -/
theorem IsWeaklyStrictMinimalServiceCurve.sum_wstrict {ι : Type*}
    [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    (hβ : IsWeaklyStrictMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds) :
    ∀ w, (∑ j, (Ds j)
        (start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) w))
      + β (w - start (fun x => ∑ j, (As j) x)
          (fun x => ∑ j, (Ds j) x) w)
      ≤ ∑ j, (Ds j) w := by
  intro w
  have h := hβ (∑ j, As j) (∑ j, Ds j) (aggregateServer_sum hp) w
  rw [Curve.coe_sum, Curve.coe_sum] at h
  exact h

/-- Relation form of weakly strict blind multiplexing: an `n`-server
offering a weakly strict aggregate service curve serves each pair's
flow `i` at the min-plus residual of the cross-traffic arrival
constraints. -/
theorem minConv_residualCurve_le_of_isWeaklyStrictMinimalServiceCurve
    {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hcaus : IsCausalN S)
    (hβ : IsWeaklyStrictMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (Deviation.liftENN (residualCurve β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
      ≤ ((Ds i) t : ℝ≥0∞) :=
  minConv_residualCurve_le_of_wstrict_aggregate
    (fun j => hcaus As Ds hp j) (hβ.sum_wstrict hp) harr t

/-- **Blind multiplexing needs only weak strictness**: restricting an
`n`-server with a weakly strict aggregate curve to pairs with
`αⱼ`-constrained cross-traffic, the residual server for flow `i`
offers `[β − ∑_{j≠i} αⱼ]⁺↑` as a min-plus service curve. -/
theorem isMinimalServiceCurve_residualServer_of_wstrict {ι : Type*}
    [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsWeaklyStrictMinimalServiceCurve β (aggregateServer S)) :
    IsMinimalServiceCurve
      (liftEReal (residualCurve β
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v)))
      (residualServer (fun A D => S A D ∧
        ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(A j) (α j)) i) := by
  rintro Ai Di ⟨As, Ds, ⟨hp, harr⟩, rfl, rfl⟩
  intro t
  have h := minConv_residualCurve_le_of_isWeaklyStrictMinimalServiceCurve
    hcaus hβ hp harr t
  rw [show Deviation.liftENN (residualCurve β
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v))
      = Deviation.toENN (liftEReal (residualCurve β
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v)))
    from (Deviation.toENN_liftEReal _).symm] at h
  rw [curveEReal_apply]
  exact (Deviation.minConv_toENN_le_coe_iff (As i)
    (isNonneg_liftEReal _) ((Ds i) t) t).mp h

/-! ## Book restatement (blind multiplexing, weakly strict aggregate)
An `n`-server offering a *weakly strict* service curve `β` — the
increment required only from the start of each backlogged period —
whose arrival processes have arrival curves `αᵢ` still serves each
flow `i` at the min-plus residual `βᵢ = [β − ∑_{j≠i} αⱼ]⁺↑`: the
blind-multiplexing proof only ever uses strictness at the start, so
the strict version is a corollary of this one. The book notes, via
its two-flow example, that the residual computed this way is not
necessarily weakly strict. -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hSrv : IsServerN S)
    (hβ : IsWeaklyStrictMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalCurve ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (Deviation.liftENN (residualCurve β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
      ≤ ((Ds i) t : ℝ≥0∞) :=
  minConv_residualCurve_le_of_isWeaklyStrictMinimalServiceCurve
    hSrv.1 hβ hp (fun j hj => (harr j hj).2) t

/-! ## Book restatement (blind multiplexing)
An `n`-server offering a strict service curve `β` whose arrival
processes have arrival curves `αᵢ`: the residual server for flow `i`
offers the min-plus service curve `βᵢ = [β − ∑_{j≠i} αⱼ]⁺↑`, i.e.
`Dᵢ ≥ Aᵢ ∗ βᵢ`. The strict aggregate hypothesis is essential
(`not_forall_minConv_residualCurve_le_of_minimal_aggregate`); the
conclusion also cannot be upgraded to strict
(`not_forall_add_residualCurve_le_of_strict_aggregate_of_arrival_bounds`).
If instead
the aggregate departure process
of the cross-traffic is constrained by `α`, the residual server offers
the *strict* service curve `[β − α]⁺↑`. -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hSrv : IsServerN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalCurve ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (Deviation.liftENN (residualCurve β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
      ≤ ((Ds i) t : ℝ≥0∞) :=
  minConv_residualCurve_le_of_isStrictMinimalServiceCurve
    hSrv.1 hβ hp (fun j hj => (harr j hj).2) t

end DeepWiki
