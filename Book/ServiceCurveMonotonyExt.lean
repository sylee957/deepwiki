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

/-! ## Thm 9.3 item 2: the inclusion `S_mp(β) ⊇ S_mp(β')` does not force `β ≤ β'`
The book's witness, over extended arrivals: `β'` is `0` at `0` and on `(1,2]`, `+∞` elsewhere;
`β` is `0` on `[0,1] ∪ (2,∞)`, `+∞` on `(1,2]`. Every extended pair served by `β'` is served
by `β` (`S_mp(β') ⊆ S_mp(β)`), yet `β ≰ β'` (at any `t ∈ (1,2]`, `β t = +∞ > 0 = β' t`). The
closures are ordered, `β↑ ≤ β'↑` (consistent with item 3), but the raw curves are not — the
inclusion sits strictly between `β ≤ β'` and `β↑ ≤ β'↑`. -/

/-- Item-2 witness `β`: `0` on `[0,1] ∪ (2,∞)`, `+∞` on `(1,2]`. -/
noncomputable def mono2Cexβ : ℝ≥0 → EReal := fun t => if t ≤ 1 ∨ 2 < t then 0 else ⊤

/-- Item-2 witness `β'`: `0` at `0` and on `(1,2]`, `+∞` on `(0,1] ∪ (2,∞)`. -/
noncomputable def mono2Cexβ' : ℝ≥0 → EReal :=
  fun t => if t = 0 ∨ (1 < t ∧ t ≤ 2) then 0 else ⊤

/-- `mono2Cexβ` vanishes off the `+∞` band. -/
theorem mono2Cexβ_zero_of {t : ℝ≥0} (h : t ≤ 1 ∨ 2 < t) : mono2Cexβ t = 0 := if_pos h

/-- `mono2Cexβ` is `+∞` on `(1,2]`. -/
theorem mono2Cexβ_top_of {t : ℝ≥0} (h1 : 1 < t) (h2 : t ≤ 2) : mono2Cexβ t = ⊤ :=
  if_neg (not_or.mpr ⟨not_le.mpr h1, not_lt.mpr h2⟩)

/-- `mono2Cexβ'` vanishes at `0` and on `(1,2]`. -/
theorem mono2Cexβ'_zero_of {t : ℝ≥0} (h : t = 0 ∨ (1 < t ∧ t ≤ 2)) : mono2Cexβ' t = 0 :=
  if_pos h

/-- `mono2Cexβ'` is `+∞` off `{0} ∪ (1,2]`. -/
theorem mono2Cexβ'_top_of {t : ℝ≥0} (h0 : t ≠ 0) (h : ¬ (1 < t ∧ t ≤ 2)) :
    mono2Cexβ' t = ⊤ := if_neg (not_or.mpr ⟨h0, h⟩)

/-- **`S_mp(β') ⊆ S_mp(β)` for the item-2 witness.** For `t ∉ (1,2]` the split at the origin
gives `(A ∗ β) t ≤ A 0 + β t = 0`. For `t ∈ (1,2]`, `(A ∗ β) t ≤ A(t−1)`, and the departure
absorbs it: `A(t−1) ≤ (A ∗ β')(t−1) ≤ D(t−1) ≤ D t` — the first step because every split of
`t−1 ≤ 1` either puts the mass at `0` (giving `A(t−1)`) or hits `β'`'s `+∞` band. -/
theorem minimalServiceRelExt_mono2Cex_le :
    minimalServiceRelExt mono2Cexβ' ≤ minimalServiceRelExt mono2Cexβ := by
  intro A D hAD
  rw [mem_minimalServiceRelExt_iff] at hAD ⊢
  obtain ⟨hca, hbnd⟩ := hAD
  have hA0 : (curveENNEReal A) 0 = 0 := by
    rw [curveENNEReal_apply, show A 0 = 0 from A.zero, EReal.coe_ennreal_zero]
  refine ⟨hca, fun t => ?_⟩
  rcases le_or_gt t 1 with ht1 | ht1
  · refine le_trans (minConv_le_add (curveENNEReal A) mono2Cexβ (zero_add t)) ?_
    rw [hA0, mono2Cexβ_zero_of (Or.inl ht1), zero_add, curveENNEReal_apply]
    exact EReal.coe_ennreal_nonneg _
  · rcases le_or_gt t 2 with ht2 | ht2
    · -- 1 < t ≤ 2
      have hub : minConv (curveENNEReal A) mono2Cexβ t ≤ (curveENNEReal A) (t - 1) := by
        refine le_trans (minConv_le_add (curveENNEReal A) mono2Cexβ
          (tsub_add_cancel_of_le ht1.le)) ?_
        rw [mono2Cexβ_zero_of (Or.inl le_rfl), add_zero]
      have hlb : (curveENNEReal A) (t - 1) ≤ minConv (curveENNEReal A) mono2Cexβ' (t - 1) := by
        refine le_minConv (fun u s hus => ?_)
        by_cases hs0 : s = 0
        · rw [hs0, mono2Cexβ'_zero_of (Or.inl rfl), add_zero]
          rw [hs0, add_zero] at hus
          exact le_of_eq (congrArg (curveENNEReal A) hus.symm)
        · have hsle : s ≤ t - 1 := by rw [← hus]; exact le_add_self
          have ht1le : t - 1 ≤ 1 := by rw [tsub_le_iff_right]; exact ht2.trans (by norm_num)
          have hsnt : ¬ (1 < s ∧ s ≤ 2) :=
            fun h => absurd (lt_of_lt_of_le h.1 (hsle.trans ht1le)) (lt_irrefl 1)
          rw [mono2Cexβ'_top_of hs0 hsnt, EReal.add_top_of_ne_bot
            (by rw [curveENNEReal_apply]; exact EReal.coe_ennreal_ne_bot _)]
          exact le_top
      calc minConv (curveENNEReal A) mono2Cexβ t
          ≤ (curveENNEReal A) (t - 1) := hub
        _ ≤ minConv (curveENNEReal A) mono2Cexβ' (t - 1) := hlb
        _ ≤ (curveENNEReal D) (t - 1) := hbnd (t - 1)
        _ ≤ (curveENNEReal D) t := by
            rw [curveENNEReal_apply, curveENNEReal_apply]
            exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (D.mono tsub_le_self)
    · -- t > 2
      refine le_trans (minConv_le_add (curveENNEReal A) mono2Cexβ (zero_add t)) ?_
      rw [hA0, mono2Cexβ_zero_of (Or.inr ht2), zero_add, curveENNEReal_apply]
      exact EReal.coe_ennreal_nonneg _

/-- **Thm 9.3 item 2 (`S_mp(β) ⊇ S_mp(β') ⇏ β ≤ β'`)**: the min-plus inclusion does not force
pointwise domination of the raw service curves — only of their closures (item 3). The witness
`(mono2Cexβ, mono2Cexβ')` satisfies the inclusion yet `β 2 = +∞ > 0 = β' 2`. -/
theorem not_forall_minimalServiceRelExt_le_imp_le :
    ¬ ∀ β β' : ℝ≥0 → EReal, minimalServiceRelExt β' ≤ minimalServiceRelExt β → β ≤ β' := by
  intro h
  have hle := h mono2Cexβ mono2Cexβ' minimalServiceRelExt_mono2Cex_le 2
  rw [mono2Cexβ_top_of one_lt_two le_rfl, mono2Cexβ'_zero_of (Or.inr ⟨one_lt_two, le_rfl⟩)] at hle
  exact absurd hle (by simp)

end DeepWiki
