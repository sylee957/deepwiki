import Book.ServersMimo
import Book.ServiceCurveStrict
import Book.ClosuresNd
import Book.DeviationsBounds

/-! # Residual service under blind multiplexing
With no information on the service policy, a strict aggregate service
curve still leaves a guarantee to each flow: the residual server for
flow `i` offers the min-plus service curve `[β − ∑_{j≠i} αⱼ]⁺↑`
(`residualCurve`), where the `αⱼ` constrain the cross-traffic arrivals.
If instead the cross-traffic *departures* are constrained, the residual
curve is strict. Both proofs run inside a backlogged period of the
aggregate pair: strictness serves `β` there, the cross-traffic can have
consumed at most its constraint, and the leftover is flow `i`'s. -/

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

/-- A strict service inequality forces `β 0 = 0`: the empty backlogged
period `(s, s]` serves `β 0` instantly. -/
theorem beta_zero_eq_of_strict {A D β : ℝ≥0 → ℝ≥0}
    (hstrict : ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
      D s + β (t - s) ≤ D t) : β 0 = 0 := by
  have h := hstrict 0 0 le_rfl (fun u hu => absurd hu.2 (not_le.mpr hu.1))
  rw [tsub_zero] at h
  exact le_antisymm (by rwa [add_le_iff_nonpos_right] at h) zero_le'

/-- **Blind multiplexing**: if the aggregate pair obeys a strict service
inequality for `β` and every cross-traffic arrival is `αⱼ`-constrained,
then flow `i` is served at the min-plus residual `[β − ∑_{j≠i} αⱼ]⁺↑`:
`Aᵢ ∗ residualCurve ≤ Dᵢ`. -/
theorem minConv_residualCurve_le_of_strict_aggregate {ι : Type*} [Fintype ι]
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
  have hcagg : ∀ x, (∑ j, (Ds j) x) ≤ ∑ j, (As j) x := fun x =>
    Finset.sum_le_sum fun j _ => hc j x
  set s₀ : ℝ≥0 := start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) t
    with hs₀def
  have hs₀t : s₀ ≤ t := start_le _ _ t
  -- per-flow equality at the start of the aggregate backlogged period
  have haggeq : (∑ j, (As j) s₀) = ∑ j, (Ds j) s₀ :=
    apply_start_eq
      (isLeftContinuous_sum _ fun j _ => (As j).leftCont)
      (isLeftContinuous_sum _ fun j _ => (Ds j).leftCont)
      (by show (∑ j, (As j) 0) = ∑ j, (Ds j) 0
          have hA : ∀ j : ι, (As j) 0 = 0 := fun j => (As j).zero
          have hD : ∀ j : ι, (Ds j) 0 = 0 := fun j => (Ds j).zero
          simp [hA, hD])
      hcagg t
  have hfloweq : ∀ j, (Ds j) s₀ = (As j) s₀ := fun j =>
    (Finset.sum_eq_sum_iff_of_le (fun j _ => hc j s₀)).mp haggeq.symm j
      (Finset.mem_univ j)
  -- every shifted difference is covered by what flow `i` receives
  have hv : ∀ v : ℝ≥0, v ≤ t - s₀ →
      β v - (∑ j ∈ Finset.univ.erase i, α j v)
        ≤ (Ds i) t - (Ds i) s₀ := by
    intro v hvle
    have hut : s₀ + v ≤ t := by
      calc s₀ + v ≤ s₀ + (t - s₀) := add_le_add le_rfl hvle
        _ = t := add_tsub_cancel_of_le hs₀t
    rcases eq_zero_or_pos v with rfl | hvpos
    · rw [beta_zero_eq_of_strict hstrict, zero_tsub]
      exact zero_le'
    · have hbl : IsBacklogged (fun x => ∑ j, (As j) x)
          (fun x => ∑ j, (Ds j) x) (Set.Ioc s₀ (s₀ + v)) := fun u hu =>
        (isBacklogged_Ioc_start hcagg t) u ⟨hu.1, hu.2.trans hut⟩
      have hstr := hstrict s₀ (s₀ + v) le_self_add hbl
      rw [add_tsub_cancel_left,
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
      -- cancel the cross-traffic backlog at `s₀`
      have hmain : (Ds i) s₀ + β v
          ≤ (Ds i) (s₀ + v) + ∑ j ∈ Finset.univ.erase i, α j v := by
        have h2 : ((Ds i) s₀ + β v)
              + ∑ j ∈ Finset.univ.erase i, (Ds j) s₀
            ≤ ((Ds i) (s₀ + v) + ∑ j ∈ Finset.univ.erase i, α j v)
              + ∑ j ∈ Finset.univ.erase i, (Ds j) s₀ := by
          calc ((Ds i) s₀ + β v) + ∑ j ∈ Finset.univ.erase i, (Ds j) s₀
              = ((Ds i) s₀ + ∑ j ∈ Finset.univ.erase i, (Ds j) s₀) + β v := by
                ring
            _ ≤ (Ds i) (s₀ + v) + ∑ j ∈ Finset.univ.erase i, (Ds j) (s₀ + v) :=
                hstr
            _ ≤ (Ds i) (s₀ + v)
                + ((∑ j ∈ Finset.univ.erase i, (Ds j) s₀)
                  + ∑ j ∈ Finset.univ.erase i, α j v) :=
                add_le_add le_rfl hcross
            _ = ((Ds i) (s₀ + v) + ∑ j ∈ Finset.univ.erase i, α j v)
                + ∑ j ∈ Finset.univ.erase i, (Ds j) s₀ := by
                ring
        exact le_of_add_le_add_right h2
      -- pass to the truncated differences
      have hDi : (Ds i) (s₀ + v) ≤ (Ds i) t := (Ds i).mono hut
      refine tsub_le_iff_right.mpr ?_
      calc β v ≤ ((Ds i) (s₀ + v) + ∑ j ∈ Finset.univ.erase i, α j v)
            - (Ds i) s₀ :=
            le_tsub_of_add_le_left hmain
        _ ≤ ((Ds i) t + ∑ j ∈ Finset.univ.erase i, α j v) - (Ds i) s₀ :=
            tsub_le_tsub_right (add_le_add hDi le_rfl) _
        _ = ((Ds i) t - (Ds i) s₀) + ∑ j ∈ Finset.univ.erase i, α j v :=
            (tsub_add_eq_add_tsub ((Ds i).mono hs₀t)).symm
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
      (∑ j, (Ds j) u) < ∑ j, (As j) u := fun u hu =>
    Finset.sum_lt_sum (fun j _ => hc j u) ⟨i, Finset.mem_univ i, hbl u hu⟩
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
      have hmain : (Ds i) s + β v ≤ (Ds i) (s + v) + α v := by
        have h2 : ((Ds i) s + β v) + ∑ j ∈ Finset.univ.erase i, (Ds j) s
            ≤ ((Ds i) (s + v) + α v)
              + ∑ j ∈ Finset.univ.erase i, (Ds j) s := by
          calc ((Ds i) s + β v) + ∑ j ∈ Finset.univ.erase i, (Ds j) s
              = ((Ds i) s + ∑ j ∈ Finset.univ.erase i, (Ds j) s) + β v := by
                ring
            _ ≤ (Ds i) (s + v)
                + ∑ j ∈ Finset.univ.erase i, (Ds j) (s + v) := hstr
            _ ≤ (Ds i) (s + v)
                + ((∑ j ∈ Finset.univ.erase i, (Ds j) s) + α v) :=
                add_le_add le_rfl hcross
            _ = ((Ds i) (s + v) + α v)
                + ∑ j ∈ Finset.univ.erase i, (Ds j) s := by
                ring
        exact le_of_add_le_add_right h2
      have hDi : (Ds i) (s + v) ≤ (Ds i) t := (Ds i).mono hut
      refine tsub_le_iff_right.mpr ?_
      calc β v ≤ ((Ds i) (s + v) + α v) - (Ds i) s :=
            le_tsub_of_add_le_left hmain
        _ ≤ ((Ds i) t + α v) - (Ds i) s :=
            tsub_le_tsub_right (add_le_add hDi le_rfl) _
        _ = ((Ds i) t - (Ds i) s) + α v :=
            (tsub_add_eq_add_tsub ((Ds i).mono hst)).symm
  have hsup : residualCurve β α (t - s) ≤ (Ds i) t - (Ds i) s :=
    ciSup_le fun v => hv v.1 v.2
  calc (Ds i) s + residualCurve β α (t - s)
      ≤ (Ds i) s + ((Ds i) t - (Ds i) s) := add_le_add le_rfl hsup
    _ = (Ds i) t := add_tsub_cancel_of_le ((Ds i).mono hst)

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
  refine minConv_residualCurve_le_of_strict_aggregate
    (fun j => hcaus As Ds hp j) ?_ harr t
  intro s t' hst hbl
  have h := hβ (∑ j, As j) (∑ j, Ds j) (aggregateServer_sum hp) s t' hst
    (by rwa [Curve.coe_sum, Curve.coe_sum])
  rwa [Curve.sum_apply, Curve.sum_apply] at h

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
  refine add_residualCurve_le_of_strict_aggregate
    (fun j => hcaus As Ds hp j) ?_ hdep hst hbl
  intro s' t' hst' hbl'
  have h := hβ (∑ j, As j) (∑ j, Ds j) (aggregateServer_sum hp) s' t' hst'
    (by rwa [Curve.coe_sum, Curve.coe_sum])
  rwa [Curve.sum_apply, Curve.sum_apply] at h

/-! ## Book restatement (blind multiplexing)
An `n`-server offering a strict service curve `β` whose arrival
processes have arrival curves `αᵢ`: the residual server for flow `i`
offers the min-plus service curve `βᵢ = [β − ∑_{j≠i} αⱼ]⁺↑`, i.e.
`Dᵢ ≥ Aᵢ ∗ βᵢ`. The strictness of the aggregate hypothesis and the
non-strictness of the conclusion are both essential. If instead the
aggregate departure process of the cross-traffic is constrained by `α`,
the residual server offers the *strict* service curve `[β − α]⁺↑`. -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hSrv : IsServerN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (Deviation.liftENN (residualCurve β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
      ≤ ((Ds i) t : ℝ≥0∞) :=
  minConv_residualCurve_le_of_isStrictMinimalServiceCurve
    hSrv.1 hβ hp harr t

end DeepWiki
