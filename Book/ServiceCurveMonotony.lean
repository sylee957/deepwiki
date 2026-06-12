import Book.RealCurvesRegularity
import Book.ServiceCurveWeaklyStrict

/-! # Comparison of service curves (monotony refined)
A smaller curve is always offered (the `*_mono` family); when is the
comparison an equivalence? For the min-plus and weakly strict types,
relation inclusion forces pointwise domination against every regular
curve — witnessed by the burst–clip pair: a burst input at a level
just above the target value, served as the curve itself until it
reaches the level. The book's forcing witness rides a `δ₀`-shaped
input; the burst at a large enough constant is the book's own finite
recipe for it. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The clip of `β` at level `M`: `t ↦ min (β t) M`. -/
noncomputable def clipFun (β : ℝ≥0 → ℝ≥0) (M : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => min (β t) M

/-- `clipFun β M t` is the minimum `min (β t) M`. -/
theorem clipFun_apply (β : ℝ≥0 → ℝ≥0) (M t : ℝ≥0) :
    clipFun β M t = min (β t) M := rfl

/-- `clipFun β M 0 = 0` for `β` null at the origin. -/
theorem clipFun_zero_eq {β : ℝ≥0 → ℝ≥0} (M : ℝ≥0) (h0 : β 0 = 0) :
    clipFun β M 0 = 0 := by
  rw [clipFun_apply, h0]
  exact min_eq_left zero_le'

/-- The clip stays below the curve. -/
theorem clipFun_le_apply (β : ℝ≥0 → ℝ≥0) (M t : ℝ≥0) :
    clipFun β M t ≤ β t := min_le_left _ _

/-- The clip stays below its level. -/
theorem clipFun_le (β : ℝ≥0 → ℝ≥0) (M t : ℝ≥0) :
    clipFun β M t ≤ M := min_le_right _ _

/-- Below the level the clip is the curve. -/
theorem clipFun_eq_of_lt {β : ℝ≥0 → ℝ≥0} {M t : ℝ≥0} (h : β t < M) :
    clipFun β M t = β t := min_eq_left h.le

/-- At and beyond the level the clip saturates. -/
theorem clipFun_eq_of_le {β : ℝ≥0 → ℝ≥0} {M t : ℝ≥0} (h : M ≤ β t) :
    clipFun β M t = M := min_eq_right h

/-- `clipFun β M` is monotone when `β` is. -/
theorem clipFun_mono {β : ℝ≥0 → ℝ≥0} (M : ℝ≥0) (hmono : Monotone β) :
    Monotone (clipFun β M) :=
  fun _ _ hab => min_le_min (hmono hab) le_rfl

/-- The burst input as a curve. -/
noncomputable def burstCurve (M : ℝ≥0) : Curve where
  toFun := burstFun M
  mono := burstFun_mono M
  zero := burstFun_zero_eq M
  pwc := burstFun_pwc M
  leftCont := burstFun_leftCont M

/-- `burstCurve M t` is `burstFun M t`. -/
theorem burstCurve_apply (M t : ℝ≥0) :
    burstCurve M t = burstFun M t := rfl

/-- The clipped output as a curve, for a regular `β`. -/
noncomputable def clipCurve (β : ℝ≥0 → ℝ≥0) (M : ℝ≥0)
    (hmono : Monotone β) (hlc : IsLeftContinuous β)
    (hpwc : IsPiecewiseContinuous β) (h0 : β 0 = 0) : Curve where
  toFun := clipFun β M
  mono := clipFun_mono M hmono
  zero := clipFun_zero_eq M h0
  pwc := by
    intro T
    refine Set.Finite.subset (hpwc T) ?_
    rintro t ⟨ht, htm⟩
    refine ⟨fun hc => ht ?_, htm⟩
    exact hc.min continuousAt_const
  leftCont := fun t => (hlc t).min continuousWithinAt_const

/-- `clipCurve β M … t` is `clipFun β M t`. -/
theorem clipCurve_apply {β : ℝ≥0 → ℝ≥0} {M : ℝ≥0}
    (hmono : Monotone β) (hlc : IsLeftContinuous β)
    (hpwc : IsPiecewiseContinuous β) (h0 : β 0 = 0) (t : ℝ≥0) :
    clipCurve β M hmono hlc hpwc h0 t = clipFun β M t := rfl

/-- Below the clip the burst–clip pair has no positive equality
point: the start anchors at the origin. -/
theorem start_burst_clip_eq_zero {β : ℝ≥0 → ℝ≥0} {M : ℝ≥0}
    (hmono : Monotone β) (hlc : IsLeftContinuous β)
    (hpwc : IsPiecewiseContinuous β) (h0 : β 0 = 0) {t : ℝ≥0}
    (hM : β t < M) :
    start ⇑(burstCurve M) ⇑(clipCurve β M hmono hlc hpwc h0) t = 0 := by
  refine le_antisymm (csSup_le ⟨0, zero_le', ?_⟩ fun u hu => ?_) zero_le'
  · show burstFun M 0 = clipFun β M 0
    rw [burstFun_zero_eq, clipFun_zero_eq M h0]
  · by_contra hu0
    rw [not_le] at hu0
    have hβu : β u < M := lt_of_le_of_lt (hmono hu.1) hM
    have h2 : burstFun M u = clipFun β M u := hu.2
    rw [burstFun_apply_of_ne M (ne_of_gt hu0), clipFun_eq_of_lt hβu] at h2
    exact absurd h2.symm (ne_of_lt hβu)

/-- At and beyond the clip `t` itself is an equality point: the start
anchors at `t`. -/
theorem start_burst_clip_eq_self {β : ℝ≥0 → ℝ≥0} {M : ℝ≥0}
    (hmono : Monotone β) (hlc : IsLeftContinuous β)
    (hpwc : IsPiecewiseContinuous β) (h0 : β 0 = 0) {t : ℝ≥0}
    (hM : M ≤ β t) :
    start ⇑(burstCurve M) ⇑(clipCurve β M hmono hlc hpwc h0) t = t := by
  rcases eq_or_ne t 0 with rfl | hne
  · exact le_antisymm (start_le _ _ 0) zero_le'
  · exact start_eq_of_apply_eq (by
      show burstFun M t = clipFun β M t
      rw [burstFun_apply_of_ne M hne, clipFun_eq_of_le hM])

/-- The burst–clip pair is weakly-strictly served at `β`: below the
clip the start anchors at the origin and the output is `β` itself;
at and beyond it the start anchors at `t`. -/
theorem clip_mem_weaklyStrictServiceRel {β : ℝ≥0 → ℝ≥0} (M : ℝ≥0)
    (hmono : Monotone β) (hlc : IsLeftContinuous β)
    (hpwc : IsPiecewiseContinuous β) (h0 : β 0 = 0) :
    weaklyStrictServiceRel β (burstCurve M)
      (clipCurve β M hmono hlc hpwc h0) := by
  constructor
  · intro t
    show clipFun β M t ≤ burstFun M t
    rcases eq_or_ne t 0 with rfl | ht
    · rw [clipFun_zero_eq M h0, burstFun_zero_eq]
    · rw [burstFun_apply_of_ne M ht]
      exact clipFun_le β M t
  · intro t
    rcases lt_or_ge (β t) M with hM | hM
    · rw [start_burst_clip_eq_zero hmono hlc hpwc h0 hM]
      show clipFun β M 0 + β (t - 0) ≤ clipFun β M t
      rw [clipFun_zero_eq M h0, zero_add, tsub_zero]
      exact (clipFun_eq_of_lt hM).symm.le
    · rw [start_burst_clip_eq_self hmono hlc hpwc h0 hM,
        tsub_self, h0, add_zero]

/-- The burst–clip pair is min-plus served at `β`: below the clip the
`(0, t)` split bounds the convolution, at and beyond it the `(t, 0)`
split. -/
theorem clip_mem_minimalServiceRel {β : ℝ≥0 → ℝ≥0} (M : ℝ≥0)
    (hmono : Monotone β) (hlc : IsLeftContinuous β)
    (hpwc : IsPiecewiseContinuous β) (h0 : β 0 = 0) :
    minimalServiceRel (liftEReal β) (burstCurve M)
      (clipCurve β M hmono hlc hpwc h0) := by
  refine ⟨curveEReal_mono
    (clip_mem_weaklyStrictServiceRel M hmono hlc hpwc h0).1,
    fun t => ?_⟩
  rcases lt_or_ge (β t) M with hM | hM
  · refine le_trans (minConv_le_add _ _ (zero_add t)) ?_
    rw [curveEReal_zero, zero_add, curveEReal_apply,
      clipCurve_apply, clipFun_eq_of_lt hM]
  · rcases eq_or_ne t 0 with rfl | ht
    · refine le_trans (minConv_le_add _ _ (zero_add 0)) ?_
      rw [curveEReal_zero, zero_add]
      show ((β 0 : ℝ) : EReal)
          ≤ curveEReal (clipCurve β M hmono hlc hpwc h0) 0
      rw [h0, curveEReal_apply, clipCurve_apply, clipFun_zero_eq M h0]
    · refine le_trans (minConv_le_add _ _ (add_zero t)) ?_
      rw [curveEReal_apply, curveEReal_apply, clipCurve_apply,
        clipFun_eq_of_le hM,
        show burstCurve M t = M from burstFun_apply_of_ne M ht]
      show ((M : ℝ) : EReal) + ((β 0 : ℝ) : EReal) ≤ ((M : ℝ) : EReal)
      rw [h0]
      norm_num

/-- Forcing direction for the weakly strict comparison: relation
inclusion forces pointwise domination, via the burst–clip pair
clipped just above the target value. -/
theorem le_of_weaklyStrictServiceRel_le {β β' : ℝ≥0 → ℝ≥0}
    (hmono : Monotone β') (hlc : IsLeftContinuous β')
    (hpwc : IsPiecewiseContinuous β') (h0 : β' 0 = 0)
    (h : weaklyStrictServiceRel β' ≤ weaklyStrictServiceRel β) :
    β ≤ β' := by
  intro t
  have hM : β' t < β' t + 1 := lt_add_one _
  have hp := h _ _
    (clip_mem_weaklyStrictServiceRel (β' t + 1) hmono hlc hpwc h0)
  have hb : clipFun β' (β' t + 1)
      (start ⇑(burstCurve (β' t + 1))
        ⇑(clipCurve β' (β' t + 1) hmono hlc hpwc h0) t)
      + β (t - start ⇑(burstCurve (β' t + 1))
        ⇑(clipCurve β' (β' t + 1) hmono hlc hpwc h0) t)
      ≤ clipFun β' (β' t + 1) t := hp.2 t
  rw [start_burst_clip_eq_zero hmono hlc hpwc h0 hM,
    clipFun_zero_eq _ h0, zero_add, tsub_zero,
    clipFun_eq_of_lt hM] at hb
  exact hb

/-- Forcing direction for the min-plus comparison: relation inclusion
forces pointwise domination — clip at the target value, against
which the convolution reaches the clip level while the output stays
strictly below it. -/
theorem le_of_minimalServiceRel_le {β β' : ℝ≥0 → ℝ≥0}
    (hmono : Monotone β') (hlc : IsLeftContinuous β')
    (hpwc : IsPiecewiseContinuous β') (h0 : β' 0 = 0)
    (h : minimalServiceRel (liftEReal β')
      ≤ minimalServiceRel (liftEReal β)) :
    β ≤ β' := by
  intro t
  by_contra hlt
  rw [not_le] at hlt
  have hp := h _ _ (clip_mem_minimalServiceRel (β t) hmono hlc hpwc h0)
  have hconv := hp.2 t
  have hlow : ((β t : ℝ) : EReal)
      ≤ minConv (curveEReal (burstCurve (β t))) (liftEReal β) t := by
    refine le_minConv fun u s hus => ?_
    rcases eq_or_ne u 0 with rfl | hu
    · rw [zero_add] at hus
      subst hus
      rw [curveEReal_zero, zero_add]
    · rw [curveEReal_apply,
        show burstCurve (β t) u = β t from burstFun_apply_of_ne _ hu]
      exact le_add_of_nonneg_right (isNonneg_liftEReal β s)
  have hup : curveEReal (clipCurve β' (β t) hmono hlc hpwc h0) t
      = ((β' t : ℝ) : EReal) := by
    rw [curveEReal_apply, clipCurve_apply, clipFun_eq_of_lt hlt]
  have hle : ((β t : ℝ) : EReal) ≤ ((β' t : ℝ) : EReal) :=
    le_trans hlow (le_trans hconv (le_of_eq hup))
  have : β t ≤ β' t := by exact_mod_cast hle
  exact absurd this (not_le.mpr hlt)

/-- **Monotony refined, weakly strict**: against a regular curve,
relation inclusion is exactly pointwise domination. -/
theorem weaklyStrictServiceRel_le_iff {β β' : ℝ≥0 → ℝ≥0}
    (hmono : Monotone β') (hlc : IsLeftContinuous β')
    (hpwc : IsPiecewiseContinuous β') (h0 : β' 0 = 0) :
    weaklyStrictServiceRel β' ≤ weaklyStrictServiceRel β ↔ β ≤ β' :=
  ⟨le_of_weaklyStrictServiceRel_le hmono hlc hpwc h0,
    weaklyStrictServiceRel_mono⟩

/-- **Monotony refined, min-plus**: against a regular curve, relation
inclusion is exactly pointwise domination. -/
theorem minimalServiceRel_le_iff {β β' : ℝ≥0 → ℝ≥0}
    (hmono : Monotone β') (hlc : IsLeftContinuous β')
    (hpwc : IsPiecewiseContinuous β') (h0 : β' 0 = 0) :
    minimalServiceRel (liftEReal β') ≤ minimalServiceRel (liftEReal β)
      ↔ β ≤ β' :=
  ⟨le_of_minimalServiceRel_le hmono hlc hpwc h0,
    fun hle => minimalServiceRel_mono fun t => by
      show ((β t : ℝ) : EReal) ≤ ((β' t : ℝ) : EReal)
      exact_mod_cast hle t⟩

/-! ## Book restatement (monotony refined, the closure criteria)
`S_mp(β↑) ⊇ S_mp(β'↑)` iff `β↑ ≤ β'↑`, and
`S_wstrict(β) ⊇ S_wstrict(β')` iff `β↑ ≤ β'↑` — stated against the
monotone representative: for a monotone `β'` the closure is `β'`
itself (`ndClosure_eq_self`), and the criterion `β↑ ≤ β'↑` is the
pointwise `β ≤ β'` (below, with the closure spelled out under
prefix-boundedness of `β`). The book's forcing witness is the pair
`(δ₀, β'↑)`; the burst–clip pair at a level just above the target
value is its finite stand-in — the book's own remark that `+∞` may
be replaced by a large enough constant. The strict and
variable-capacity items, whose criterion compares super-additive
closures, ride a super-additively closed witness output and are
deferred. -/
example {β β' : ℝ≥0 → ℝ≥0}
    (hmono : Monotone β') (hlc : IsLeftContinuous β')
    (hpwc : IsPiecewiseContinuous β') (h0 : β' 0 = 0)
    (hbdd : ClosureBddAbove β) :
    weaklyStrictServiceRel β' ≤ weaklyStrictServiceRel β ↔
      ndClosure β ≤ ndClosure β' := by
  rw [ndClosure_eq_self hmono,
    weaklyStrictServiceRel_le_iff hmono hlc hpwc h0]
  constructor
  · intro hle t
    exact ndClosure_le hmono hle t
  · intro hle t
    exact le_trans (le_ndClosure β hbdd t) (hle t)
example {β β' : ℝ≥0 → ℝ≥0}
    (hmono : Monotone β') (hlc : IsLeftContinuous β')
    (hpwc : IsPiecewiseContinuous β') (h0 : β' 0 = 0)
    (hbdd : ClosureBddAbove β) :
    minimalServiceRel (liftEReal β') ≤ minimalServiceRel (liftEReal β)
      ↔ ndClosure β ≤ ndClosure β' := by
  rw [ndClosure_eq_self hmono,
    minimalServiceRel_le_iff hmono hlc hpwc h0]
  constructor
  · intro hle t
    exact ndClosure_le hmono hle t
  · intro hle t
    exact le_trans (le_ndClosure β hbdd t) (hle t)

end DeepWiki
