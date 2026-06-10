import Book.DeviationsBoundsServer
import Book.ArrivalCurveShaperGreedy

/-! # Tightness of the delay and backlog bounds
The deviation bounds are attained: for sub-additive `A` the greedy pair
`(A, A ∗ β)` realizes `d(A, A ∗ β) = hDev` and `b(A, A ∗ β) = vDev`. The raw
equalities hold for any `D` realizing the `ℝ≥0∞` convolution exactly. The
greedy output `greedyFun` always realizes it, so the direct form needs only
`A` sub-additive and `β` in `F₀`; left-continuity and the
piecewise-continuity witness only package the output as a `Curve` served in
`minimalServiceRel β`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- Sub-additivity transfers to the `ℝ≥0∞` reading `Deviation.liftENN`. -/
theorem IsSubadditive.liftENN {A : ℝ≥0 → ℝ≥0} (hsub : IsSubadditive A) :
    IsSubadditive (Deviation.liftENN A) :=
  fun u s => by exact_mod_cast hsub u s

namespace Deviation

/-! ## Raw equalities
For `A` null at the origin and `D` realizing the convolution `A ∗ β` exactly,
the deviations of the pair `(A, D)` against `(A, β)` collapse: `D ≤ β` from
the `(0, t)` split, so the monotony of deviations reverses the bounds. -/

/-- A `D` realizing `A ∗ β` lies below `β` when `A 0 = 0` (the `(0, t)`
split). -/
theorem liftENN_le_of_minConv_eq {A D : ℝ≥0 → ℝ≥0} {β : ℝ≥0 → ℝ≥0∞}
    (h0 : IsNullAtOrigin A)
    (hD : ∀ t, (D t : ℝ≥0∞) = minConv (liftENN A) β t) :
    liftENN D ≤ β := by
  intro t
  rw [show liftENN D t = minConv (liftENN A) β t from hD t]
  refine le_trans (minConv_le_add (liftENN A) β (zero_add t)) ?_
  have hA0 : A 0 = 0 := h0
  have htoE : liftENN A 0 = 0 := by
    show ((A 0 : ℝ≥0) : ℝ≥0∞) = 0
    exact_mod_cast hA0
  rw [htoE, zero_add]

/-- `delayAt` agrees with the horizontal deviation of the `ℝ≥0∞` readings:
the admissibility predicates match through the coercion. -/
theorem delayAt_eq_hDevAt_liftENN (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    delayAt A D t = (hDevAt (liftENN A) (liftENN D) t : ℝ≥0∞) := by
  apply le_antisymm
  · exact le_iInf fun d => hDevAt_le (by exact_mod_cast d.2)
  · exact le_iInf fun d => hDevAt_le (by exact_mod_cast d.2)

/-- `delay` is the horizontal deviation of the `ℝ≥0∞` readings. -/
theorem delay_eq_hDev_liftENN (A D : ℝ≥0 → ℝ≥0) :
    delay A D = (hDev (liftENN A) (liftENN D) : ℝ≥0∞) := by
  rw [delay_eq_iSup]
  exact iSup_congr (delayAt_eq_hDevAt_liftENN A D)

/-- **Tightness of the delay bound**: sub-additive `A` is its own arrival
curve, and against a `D` realizing `A ∗ β` exactly the delay attains the
horizontal deviation, `d(A, D) = hDev (liftENN A) β`. -/
theorem delay_eq_hDev_of_minConv_eq {A D : ℝ≥0 → ℝ≥0} {β : ℝ≥0 → ℝ≥0∞}
    (hA : Monotone A) (h0 : IsNullAtOrigin A) (hsub : IsSubadditive A)
    (hβ : Monotone β)
    (hD : ∀ t, (D t : ℝ≥0∞) = minConv (liftENN A) β t) :
    delay A D = (hDev (liftENN A) β : ℝ≥0∞) := by
  have harr : IsMaximalArrivalCurve (liftENN A) (liftENN A) :=
    isMaximalArrivalCurve_self_of_subadditive hsub.liftENN
  apply le_antisymm
  · exact delay_le_hDev hA hβ harr fun t => (hD t).ge
  · calc (hDev (liftENN A) β : ℝ≥0∞)
        ≤ hDev (liftENN A) (liftENN D) :=
          hDev_mono le_rfl (liftENN_le_of_minConv_eq h0 hD)
      _ = delay A D := (delay_eq_hDev_liftENN A D).symm

/-- **Tightness of the backlog bound**: against a `D` realizing `A ∗ β`
exactly, the backlog attains the vertical deviation,
`b(A, D) = vDev (liftENN A) β`. -/
theorem backlog_eq_vDev_of_minConv_eq {A D : ℝ≥0 → ℝ≥0}
    {β : ℝ≥0 → ℝ≥0∞} (h0 : IsNullAtOrigin A) (hsub : IsSubadditive A)
    (hD : ∀ t, (D t : ℝ≥0∞) = minConv (liftENN A) β t) :
    backlog A D = vDev (liftENN A) β := by
  have harr : IsMaximalArrivalCurve (liftENN A) (liftENN A) :=
    isMaximalArrivalCurve_self_of_subadditive hsub.liftENN
  apply le_antisymm
  · exact backlog_le_vDev harr fun t => (hD t).ge
  · calc vDev (liftENN A) β
        ≤ vDev (liftENN A) (liftENN D) :=
          vDev_mono le_rfl (liftENN_le_of_minConv_eq h0 hD)
      _ = backlog A D := (backlog_eq_vDev_liftENN A D).symm

/-- **Tightness of the deviation bounds** (function form): for monotone
sub-additive `alpha` in `F₀` and monotone `β` in `F₀`, some min-plus service
pair `(A, D)` of `β` — `A ≥ D ≥ A ∗ β` in the `ℝ≥0∞` reading — with `A`
having maximal arrival curve `alpha` attains `d(A, D) = hDev(alpha, β)` and
`b(A, D) = vDev(alpha, β)`. The witnesses are `A = alpha` and
`D = alpha ∗ β`; neither left-continuity nor piecewise continuity is
needed — those only package the pair into curves. -/
theorem exists_delay_eq_hDev_backlog_eq_vDev
    {alpha : ℝ≥0 → ℝ≥0} {β : ℝ≥0 → ℝ≥0∞}
    (hmono : Monotone alpha) (h0 : IsNullAtOrigin alpha)
    (hsub : IsSubadditive alpha)
    (hβmono : Monotone β) (hβ0 : β 0 = 0) :
    ∃ A D : ℝ≥0 → ℝ≥0,
      minimalServicePair β (liftENN A) (liftENN D) ∧
      IsMaximalArrivalCurve (liftENN A) (liftENN alpha) ∧
      delay A D = (hDev (liftENN alpha) β : ℝ≥0∞) ∧
      backlog A D = vDev (liftENN alpha) β := by
  have hle : ∀ t, minConv (liftENN alpha) β t ≤ (alpha t : ℝ≥0∞) := by
    intro t
    refine le_trans (minConv_le_add (liftENN alpha) β (add_zero t)) ?_
    rw [hβ0, add_zero]
  have hne : ∀ t, minConv (liftENN alpha) β t ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := alpha t)) (hle t)
  have hD : ∀ t, (((minConv (liftENN alpha) β t).toNNReal : ℝ≥0) : ℝ≥0∞)
      = minConv (liftENN alpha) β t := fun t => ENNReal.coe_toNNReal (hne t)
  exact ⟨alpha, fun t => (minConv (liftENN alpha) β t).toNNReal,
    ⟨fun t => le_trans (hD t).le (hle t), fun t => (hD t).ge⟩,
    isMaximalArrivalCurve_self_of_subadditive hsub.liftENN,
    delay_eq_hDev_of_minConv_eq hmono h0 hsub hβmono hD,
    backlog_eq_vDev_of_minConv_eq h0 hsub hD⟩

/-! ## Server form: the greedy pair attains the bounds
A greedy-served pair `(A, D)` with `D = A ∗ β` realizes the `ℝ≥0∞`
convolution exactly, so for sub-additive `A` the raw equalities apply; the
greedy output curve supplies the served witness in `minimalServiceRel β`. -/

/-- A greedy-served output realizes the `ℝ≥0∞` convolution with the reading
`toENN beta` exactly. -/
theorem coe_eq_minConv_toENN_of_greedyShaperRel {beta : ℝ≥0 → EReal}
    (hnn : IsNonneg beta) {A D : Curve} (hp : greedyShaperRel beta A D)
    (t : ℝ≥0) :
    (D t : ℝ≥0∞) = minConv (liftENN ⇑A) (toENN beta) t := by
  apply EReal.coe_ennreal_injective
  calc ((D t : ℝ≥0∞) : EReal)
      = curveE D t := EReal.coe_nnreal_eq_coe_real (D t)
    _ = minConv (curveE A) beta t := by
        rw [(hp : curveE D = minConv (curveE A) beta)]
    _ = ((minConv (liftENN ⇑A) (toENN beta) t : ℝ≥0∞) : EReal) :=
        (coe_minConv_toENN A hnn t).symm

/-- **Delay-bound tightness for greedy shapers**: a greedy-served pair with
sub-additive arrival attains `d(A, D) = hDev (liftENN A) (toENN beta)`. -/
theorem delay_eq_hDev_of_greedyShaperRel {beta : ℝ≥0 → EReal} {A D : Curve}
    (hsub : IsSubadditive (⇑A : ℝ≥0 → ℝ≥0))
    (hmono : Monotone beta) (h0 : IsNullAtOrigin beta)
    (hp : greedyShaperRel beta A D) :
    delay ⇑A ⇑D = (hDev (liftENN ⇑A) (toENN beta) : ℝ≥0∞) :=
  delay_eq_hDev_of_minConv_eq A.mono A.zero hsub (monotone_toENN hmono)
    (coe_eq_minConv_toENN_of_greedyShaperRel
      (isNonneg_of_monotone_of_nullAtOrigin hmono h0) hp)

/-- **Backlog-bound tightness for greedy shapers**: a greedy-served pair
with sub-additive arrival attains
`b(A, D) = vDev (liftENN A) (toENN beta)`. -/
theorem backlog_eq_vDev_of_greedyShaperRel {beta : ℝ≥0 → EReal}
    {A D : Curve} (hsub : IsSubadditive (⇑A : ℝ≥0 → ℝ≥0))
    (hmono : Monotone beta) (h0 : IsNullAtOrigin beta)
    (hp : greedyShaperRel beta A D) :
    backlog ⇑A ⇑D = vDev (liftENN ⇑A) (toENN beta) :=
  backlog_eq_vDev_of_minConv_eq A.zero hsub
    (coe_eq_minConv_toENN_of_greedyShaperRel
      (isNonneg_of_monotone_of_nullAtOrigin hmono h0) hp)

/-! ## Direct form: no regularity on `beta`
The deviation equalities are function-level facts: the always-defined output
`greedyFun A beta` realizes the convolution for any `beta` in `F₀`, so the
tightness needs only sub-additivity of `A`. Left-continuity of `beta` and the
piecewise-continuity witness matter only for packaging the output as a
`Curve` member of `minimalServiceRel beta` below. -/

/-- The greedy output function realizes the `ℝ≥0∞` convolution with the
reading `toENN beta` exactly, without any curve packaging. -/
theorem coe_greedyFun_eq_minConv_toENN (A : Curve) {beta : ℝ≥0 → EReal}
    (hnn : IsNonneg beta) (h0 : IsNullAtOrigin beta) (t : ℝ≥0) :
    (greedyFun A beta t : ℝ≥0∞) = minConv (liftENN ⇑A) (toENN beta) t := by
  apply EReal.coe_ennreal_injective
  calc ((greedyFun A beta t : ℝ≥0∞) : EReal)
      = ((greedyFun A beta t : ℝ) : EReal) := EReal.coe_nnreal_eq_coe_real _
    _ = minConv (curveE A) beta t := coe_greedyFun A hnn h0 t
    _ = ((minConv (liftENN ⇑A) (toENN beta) t : ℝ≥0∞) : EReal) :=
        (coe_minConv_toENN A hnn t).symm

/-- **Delay-bound tightness, direct form**: for sub-additive `A` and `beta`
in `F₀`, the greedy output attains the delay bound,
`d(A, A ∗ beta) = hDev (liftENN A) (toENN beta)`. -/
theorem delay_greedyFun_eq_hDev (A : Curve) {beta : ℝ≥0 → EReal}
    (hsub : IsSubadditive (⇑A : ℝ≥0 → ℝ≥0))
    (hmono : Monotone beta) (h0 : IsNullAtOrigin beta) :
    delay ⇑A (greedyFun A beta)
      = (hDev (liftENN ⇑A) (toENN beta) : ℝ≥0∞) :=
  delay_eq_hDev_of_minConv_eq A.mono A.zero hsub (monotone_toENN hmono)
    (coe_greedyFun_eq_minConv_toENN A
      (isNonneg_of_monotone_of_nullAtOrigin hmono h0) h0)

/-- **Backlog-bound tightness, direct form**: for sub-additive `A` and
`beta` in `F₀`, the greedy output attains the backlog bound,
`b(A, A ∗ beta) = vDev (liftENN A) (toENN beta)`. -/
theorem backlog_greedyFun_eq_vDev (A : Curve) {beta : ℝ≥0 → EReal}
    (hsub : IsSubadditive (⇑A : ℝ≥0 → ℝ≥0))
    (hmono : Monotone beta) (h0 : IsNullAtOrigin beta) :
    backlog ⇑A (greedyFun A beta) = vDev (liftENN ⇑A) (toENN beta) :=
  backlog_eq_vDev_of_minConv_eq A.zero hsub
    (coe_greedyFun_eq_minConv_toENN A
      (isNonneg_of_monotone_of_nullAtOrigin hmono h0) h0)

/-! ## `C`-membership form
The witnesses below buy only membership: the greedy output as a `Curve`,
served in `minimalServiceRel beta`. The attained equalities are those of the
direct form. -/

/-- The greedy output curve is greedy-served: `D = A ∗ beta` by
construction. -/
theorem greedyShaperRel_greedyCurve (A : Curve) {beta : ℝ≥0 → EReal}
    (hmono : Monotone beta) (h0 : beta 0 = 0)
    (hlc : IsLeftContinuous beta)
    (hpwc : IsPiecewiseContinuous (greedyFun A beta)) :
    greedyShaperRel beta A (greedyCurve A beta hmono h0 hlc hpwc) :=
  curveE_greedyCurve A hmono h0 hlc hpwc

/-- **Tightness of the deviation bounds** (`C`-membership form): for
sub-additive `alpha` and left-continuous `beta`, there exists a pair
`(A, D)` of `minimalServiceRel beta` such that `A` has arrival curve
`alpha`, `d(A, D) = hDev(alpha, beta)` and `b(A, D) = vDev(alpha, beta)`.
The piecewise-continuity witness is the price of `C`-membership (the
equalities themselves are the function form above). -/
theorem exists_minimalServiceRel_delay_eq_hDev_backlog_eq_vDev (alpha : Curve)
    {beta : ℝ≥0 → EReal} (hsub : IsSubadditive (⇑alpha : ℝ≥0 → ℝ≥0))
    (hmono : Monotone beta) (h0 : beta 0 = 0)
    (hlc : IsLeftContinuous beta)
    (hpwc : IsPiecewiseContinuous (greedyFun alpha beta)) :
    ∃ A D : Curve, minimalServiceRel beta A D ∧
      IsMaximalArrivalCurve (liftENN ⇑A) (liftENN ⇑alpha) ∧
      delay ⇑A ⇑D = (hDev (liftENN ⇑alpha) (toENN beta) : ℝ≥0∞) ∧
      backlog ⇑A ⇑D = vDev (liftENN ⇑alpha) (toENN beta) := by
  have hp := greedyShaperRel_greedyCurve alpha hmono h0 hlc hpwc
  exact ⟨alpha, greedyCurve alpha beta hmono h0 hlc hpwc,
    ((mem_greedyShaperRel_iff_minimal_and_maximal h0.le).mp hp).1,
    isMaximalArrivalCurve_self_of_subadditive hsub.liftENN,
    delay_eq_hDev_of_greedyShaperRel hsub hmono h0 hp,
    backlog_eq_vDev_of_greedyShaperRel hsub hmono h0 hp⟩

end Deviation

end DeepWiki
