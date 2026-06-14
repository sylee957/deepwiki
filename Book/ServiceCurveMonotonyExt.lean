import Book.CurveENN
import Book.ClosuresNdRegularity

/-! # Refined min-plus monotony with extended arrivals (Thm 9.3 item 3)
The book's monotony refinement distinguishes a service curve `β` from its non-decreasing
closure `β↑`: the min-plus inclusion `S_mp(β) ⊇ S_mp(β')` forces only the *closures* to be
ordered, `β↑ ≤ β'↑` (item 3). Its converse fails (item 4, `ServiceCurveMonotony`), and the
inclusion does not force the raw `β ≤ β'` (item 2). The proof rides the instantaneous
infinite burst `δ_0` as the probing arrival: `(δ_0, β'↑) ∈ S_mp(β')`, carried by the
inclusion into `S_mp(β)`, yields `β ≤ β'↑` and hence `β↑ ≤ β'↑`. The departure `β'↑` is the
running-sup closure of `β'`, a genuine `CurveENN` exactly because `ndClosure` preserves the
curve regularity (`ClosuresNdRegularity`). -/

namespace DeepWiki

open Set
open scoped Classical NNReal ENNReal

/-- The non-decreasing closure of a regular `ℝ≥0∞`-valued curve, as a `CurveENN`: `ndClosure`
preserves monotonicity, the origin value, piecewise- and left-continuity. -/
noncomputable def ndClosureCurveENN (β : ℝ≥0 → ℝ≥0∞)
    (hpwc : IsPiecewiseContinuous β) (hlc : IsLeftContinuous β)
    (h0 : IsNullAtOrigin β) : CurveENN where
  toFun := ndClosure β
  mono := monotone_ndClosure_complete β
  zero := by rw [IsNullAtOrigin, ndClosure_zero_eq]; exact h0
  pwc := isPiecewiseContinuous_ndClosure hpwc
  leftCont := isLeftContinuous_ndClosure hlc

/-- `ndClosureCurveENN β … t = ndClosure β t`. -/
@[simp] theorem ndClosureCurveENN_apply {β : ℝ≥0 → ℝ≥0∞}
    {hpwc : IsPiecewiseContinuous β} {hlc : IsLeftContinuous β} {h0 : IsNullAtOrigin β}
    (t : ℝ≥0) : ndClosureCurveENN β hpwc hlc h0 t = ndClosure β t := rfl

/-- **The closure `(δ_0, β'↑)` is min-plus served by `β'`** (over extended arrivals): the
canonical tight pair with the infinite-burst input. Since `δ_0 ∗ β' = β'` and `β' ≤ β'↑ ≤
δ_0`, the pair sits in `S_mp(β')`. -/
theorem minimalServiceRelExt_delay0_ndClosureCurveENN {β : ℝ≥0 → ℝ≥0∞}
    (hpwc : IsPiecewiseContinuous β) (hlc : IsLeftContinuous β) (h0 : IsNullAtOrigin β) :
    minimalServiceRelExt (fun t => (β t : EReal)) delay0ENN
      (ndClosureCurveENN β hpwc hlc h0) := by
  have hnb : IsNeverBot (fun t => (β t : EReal)) := fun t => EReal.coe_ennreal_ne_bot _
  refine ⟨fun t => ?_, ?_⟩
  · -- causality `β'↑ ≤ δ_0`
    rw [curveENNEReal_apply, curveENNEReal_delay0ENN]
    rcases eq_or_ne t 0 with rfl | ht
    · rw [ndClosureCurveENN_apply, ndClosure_zero_eq, h0, convUnitEReal, if_pos rfl,
        EReal.coe_ennreal_zero]
    · rw [convUnitEReal, if_neg ht]; exact le_top
  · -- `δ_0 ∗ β' = β' ≤ β'↑`
    rw [curveENNEReal_delay0ENN, minConv_convUnitEReal_left _ hnb]
    intro t
    rw [curveENNEReal_apply, ndClosureCurveENN_apply]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_ndClosure_apply β le_rfl)

/-- **Thm 9.3 item 3 (refined min-plus monotony, with extended arrivals)**: if every extended
pair min-plus served by `β'` is also served by `β`, then the non-decreasing closures are
ordered, `β↑ ≤ β'↑`. Probing the `β'`-server with the infinite burst `δ_0` recovers `β'↑` as
the departure; the inclusion then forces `β ≤ β'↑`, and `β↑` is the least monotone majorant.
Only the closures are forced — the raw converse (`β ≤ β'`) and the converse implication fail
(items 2, 4). `β'` ranges over regular curves (the book's `ℱ`); `β` is arbitrary. -/
theorem ndClosure_le_of_minimalServiceRelExt_le {β β' : ℝ≥0 → ℝ≥0∞}
    (hpwc : IsPiecewiseContinuous β') (hlc : IsLeftContinuous β') (h0 : IsNullAtOrigin β')
    (h : minimalServiceRelExt (fun t => (β' t : EReal))
      ≤ minimalServiceRelExt (fun t => (β t : EReal))) :
    ndClosure β ≤ ndClosure β' := by
  have hnbβ : IsNeverBot (fun t => (β t : EReal)) := fun t => EReal.coe_ennreal_ne_bot _
  have hmem := h delay0ENN (ndClosureCurveENN β' hpwc hlc h0)
    (minimalServiceRelExt_delay0_ndClosureCurveENN hpwc hlc h0)
  have hle := le_curveENNEReal_of_minimalServiceRelExt_delay0 hnbβ hmem
  refine ndClosure_le (monotone_ndClosure_complete β') (fun t => ?_)
  have ht := hle t
  rw [curveENNEReal_apply, ndClosureCurveENN_apply] at ht
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mp ht

end DeepWiki
