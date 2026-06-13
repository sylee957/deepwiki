import Book.ServiceCurveWeaklyStrict
import Book.RealCurves
import Book.ServersRate

/-! # Weakly strict is strictly weaker than strict
The middle inclusion of the hierarchy is strict: a server may grant
each `t` its full increment from the start of its backlogged period
while under-serving interior windows. The witness serves a `4/3`
burst at rate `2`, then rate `2/3` — the start-anchored bound holds
against `λ₁`, but the window `(1/2, 3/4]` receives `1/6 < 1/4`.
The chapter also separates the upper inclusion: for every
delayed-start curve the min-plus relation strictly exceeds the
weakly strict one — the rate-line pair witnesses it per curve. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The witness burst function: `4/3` just after the origin. -/
noncomputable def wsBurst : ℝ≥0 → ℝ≥0 := fun t => if t = 0 then 0 else 4 / 3

/-- `wsBurst` is monotone. -/
theorem wsBurst_mono : Monotone wsBurst := by
  intro a b hab
  by_cases ha : a = 0
  · subst ha
    simp only [wsBurst, if_pos]
    exact zero_le'
  · have hb : b ≠ 0 := fun hb =>
      ha (le_antisymm (hb ▸ hab) zero_le')
    simp only [wsBurst, if_neg ha, if_neg hb]
    exact le_rfl

/-- `wsBurst` is left-continuous: the jump at the origin is
right-sided. -/
theorem wsBurst_leftCont : IsLeftContinuous wsBurst := by
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · exact isLeftContinuousAt_zero _
  · refine continuousWithinAt_const.congr_of_eventuallyEq ?_
      (if_neg ht)
    filter_upwards [Ioo_mem_nhdsLT (pos_of_ne_zero ht)] with v hv
    exact if_neg (ne_of_gt hv.1)

/-- The witness arrivals: a `4/3` burst at the origin. -/
noncomputable def wsWitnessArrival : Curve where
  toFun := wsBurst
  mono := wsBurst_mono
  zero := if_pos rfl
  pwc := by
    refine isPiecewiseContinuous_of_monotone_of_finite_image
      wsBurst_mono wsBurst_leftCont (fun T => Set.Finite.subset
        (Set.Finite.insert 0 (Set.finite_singleton (4 / 3))) ?_)
    rintro x ⟨u, -, rfl⟩
    by_cases hu : u = 0
    · exact Set.mem_insert_iff.mpr (Or.inl (if_pos hu))
    · exact Set.mem_insert_iff.mpr (Or.inr (if_neg hu))
  leftCont := wsBurst_leftCont

/-- `wsWitnessArrival t = 4/3` away from the origin. -/
theorem wsWitnessArrival_pos {t : ℝ≥0} (ht : t ≠ 0) :
    wsWitnessArrival t = 4 / 3 := if_neg ht

/-- The witness departures: rate `2`, then rate `2/3`, capped at the
burst. -/
noncomputable def wsWitnessDeparture : Curve where
  toFun := fun t => min (2 * t) (min ((2 * t + 2) / 3) (4 / 3))
  mono := by
    intro a b hab
    refine min_le_min (by gcongr) (min_le_min (by gcongr) le_rfl)
  zero := by
    show min (2 * 0) (min ((2 * 0 + 2) / 3) (4 / 3)) = 0
    rw [mul_zero]
    exact min_eq_left zero_le'
  pwc := by
    refine isPiecewiseContinuous_of_continuous _ ?_
    exact (continuous_const.mul continuous_id).min
      (((continuous_const.mul continuous_id).add
        continuous_const).div_const 3 |>.min continuous_const)
  leftCont := by
    refine isLeftContinuous_of_continuous _ ?_
    exact (continuous_const.mul continuous_id).min
      (((continuous_const.mul continuous_id).add
        continuous_const).div_const 3 |>.min continuous_const)

/-- `wsWitnessDeparture t` unfolds to its three-piece minimum. -/
theorem wsWitnessDeparture_apply (t : ℝ≥0) :
    wsWitnessDeparture t
      = min (2 * t) (min ((2 * t + 2) / 3) (4 / 3)) := rfl

/-- `wsWitnessDeparture 0 = 0`. -/
theorem wsWitnessDeparture_zero_eq : wsWitnessDeparture 0 = 0 :=
  wsWitnessDeparture.zero

/-- Before saturation the departures sit strictly below the burst. -/
theorem wsWitnessDeparture_lt_of_lt_one {u : ℝ≥0} (hu : u < 1) :
    wsWitnessDeparture u < 4 / 3 := by
  rw [wsWitnessDeparture_apply]
  refine lt_of_le_of_lt
    (le_trans (min_le_right _ _) (min_le_left _ _)) ?_
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ≥0) < 3)]
  calc 2 * u + 2 < 2 * 1 + 2 := by gcongr
    _ = 4 := by norm_num

/-- The witness is causal: the departures stay below the burst. -/
theorem wsWitnessDeparture_le_wsWitnessArrival :
    wsWitnessDeparture ≤ wsWitnessArrival := by
  intro t
  by_cases ht : t = 0
  · subst ht
    show min (2 * 0) _ ≤ _
    rw [mul_zero, min_eq_left zero_le']
    exact zero_le'
  · show min (2 * t) (min ((2 * t + 2) / 3) (4 / 3))
      ≤ if t = 0 then 0 else 4 / 3
    rw [if_neg ht]
    exact le_trans (min_le_right _ _) (min_le_right _ _)

/-- The witness's equality points are the origin and the saturated
tail `1 ≤ u`. -/
theorem wsWitness_eq_iff {u : ℝ≥0} :
    wsWitnessArrival u = wsWitnessDeparture u ↔ u = 0 ∨ 1 ≤ u := by
  constructor
  · intro h
    by_cases hu : u = 0
    · exact Or.inl hu
    · refine Or.inr ?_
      by_contra hu1
      push Not at hu1
      have hDlt : wsWitnessDeparture u < 4 / 3 :=
        wsWitnessDeparture_lt_of_lt_one hu1
      rw [← h, wsWitnessArrival_pos hu] at hDlt
      exact lt_irrefl _ hDlt
  · rintro (rfl | hu)
    · exact wsWitnessArrival.zero_eq wsWitnessDeparture
    · have hu0 : u ≠ 0 := by
        intro h
        rw [h] at hu
        exact absurd hu (by norm_num)
      show (if u = 0 then 0 else 4 / 3 : ℝ≥0)
        = min (2 * u) (min ((2 * u + 2) / 3) (4 / 3))
      rw [if_neg hu0]
      rw [min_eq_right, min_eq_right]
      · rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ≥0) < 3)]
        calc (4 : ℝ≥0) = 2 * 1 + 2 := by norm_num
          _ ≤ 2 * u + 2 := by gcongr
      · refine le_trans (min_le_right _ _) ?_
        calc (4 / 3 : ℝ≥0) ≤ 2 * 1 := by
              rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 3)]
              norm_num
          _ ≤ 2 * u := by gcongr

/-- The witness is weakly strict for `λ₁`: before saturation the
start is the origin and the departures dominate the elapsed time;
after saturation the start is the instant itself. -/
theorem wsWitness_mem_weaklyStrictServiceRel :
    weaklyStrictServiceRel (rate 1) wsWitnessArrival wsWitnessDeparture := by
  refine ⟨wsWitnessDeparture_le_wsWitnessArrival, fun t => ?_⟩
  rcases lt_or_ge t 1 with ht | ht
  · -- the start is the origin
    have hstart : start ⇑wsWitnessArrival ⇑wsWitnessDeparture t = 0 := by
      unfold start
      have hset : {u | u ≤ t
          ∧ wsWitnessArrival u = wsWitnessDeparture u} = {0} := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hut, heq⟩
          rcases wsWitness_eq_iff.mp heq with h | h
          · exact h
          · exact absurd (h.trans hut) (not_le.mpr ht)
        · rintro rfl
          exact ⟨zero_le', wsWitness_eq_iff.mpr (Or.inl rfl)⟩
      rw [hset, csSup_singleton]
    have hD0 : wsWitnessDeparture 0 = 0 := wsWitnessDeparture.zero
    rw [hstart, hD0, zero_add, tsub_zero]
    show rate 1 t ≤ min (2 * t) (min ((2 * t + 2) / 3) (4 / 3))
    rw [rate_apply, one_mul]
    refine le_min ?_ (le_min ?_ ?_)
    · rw [two_mul]
      exact le_self_add
    · rw [le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 3)]
      calc t * 3 = 2 * t + t := by ring
        _ ≤ 2 * t + 2 := by
            refine add_le_add le_rfl ?_
            calc t ≤ 1 := le_of_lt ht
              _ ≤ 2 := by norm_num
    · calc t ≤ 1 := le_of_lt ht
        _ ≤ 4 / 3 := by
            rw [le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 3)]
            norm_num
  · -- saturated: the start is `t` itself
    have hstart : start ⇑wsWitnessArrival ⇑wsWitnessDeparture t = t := by
      refine le_antisymm (start_le _ _ t) ?_
      refine le_csSup ⟨t, fun x hx => hx.1⟩ ?_
      exact ⟨le_rfl, wsWitness_eq_iff.mpr (Or.inr ht)⟩
    rw [hstart, tsub_self]
    show wsWitnessDeparture t + rate 1 0 ≤ wsWitnessDeparture t
    rw [rate_zero_eq, add_zero]

/-- The witness is not strict for `λ₁`: the window `(1/2, 3/4]` is
backlogged but receives `1/6 < 1/4`. -/
theorem wsWitness_not_mem_strictServiceRel :
    ¬ strictServiceRel (rate 1) wsWitnessArrival wsWitnessDeparture := by
  rintro ⟨-, hstrict⟩
  have hbl : IsBacklogged ⇑wsWitnessArrival ⇑wsWitnessDeparture
      (Set.Ioc (1 / 2) (3 / 4)) := by
    intro u hu
    have hu0 : u ≠ 0 := by
      intro h
      rw [h] at hu
      exact absurd hu.1 (by norm_num)
    have hu1 : u < 1 :=
      lt_of_le_of_lt hu.2 (by norm_num)
    show wsWitnessDeparture u < wsWitnessArrival u
    rw [wsWitnessArrival_pos hu0]
    exact wsWitnessDeparture_lt_of_lt_one hu1
  have h := hstrict (1 / 2) (3 / 4) (by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)
      (by norm_num : (0 : ℝ≥0) < 4)]
    norm_num) hbl
  have hD12 : wsWitnessDeparture (1 / 2) = 1 := by
    show min ((2 : ℝ≥0) * (1 / 2))
      (min ((2 * (1 / 2) + 2) / 3) (4 / 3)) = 1
    rw [show (2 : ℝ≥0) * (1 / 2) = 1 by norm_num,
      show ((1 : ℝ≥0) + 2) / 3 = 1 by norm_num]
    rw [min_eq_left (le_min le_rfl (by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 3)]
      norm_num))]
  rw [hD12, show (3 / 4 : ℝ≥0) - 1 / 2 = 1 / 4 from
    tsub_eq_of_eq_add (by
      rw [div_add_div _ _ (by norm_num : (4 : ℝ≥0) ≠ 0)
        (by norm_num : (2 : ℝ≥0) ≠ 0)]
      norm_num),
    rate_apply, one_mul] at h
  refine absurd h (not_le.mpr ?_)
  show min (2 * (3 / 4 : ℝ≥0)) (min ((2 * (3 / 4) + 2) / 3) (4 / 3))
    < 1 + 1 / 4
  refine lt_of_le_of_lt
    (le_trans (min_le_right _ _) (min_le_left _ _)) ?_
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ≥0) < 3),
    show (2 : ℝ≥0) * (3 / 4) = 3 / 2 by norm_num,
    show (3 / 2 : ℝ≥0) + 2 = 7 / 2 by norm_num,
    show ((1 : ℝ≥0) + 1 / 4) * 3 = 15 / 4 by norm_num,
    div_lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)
      (by norm_num : (0 : ℝ≥0) < 4)]
  norm_num

/-- Instance level: the weakly strict relation is not contained in the
strict one. -/
theorem not_weaklyStrictServiceRel_le_strictServiceRel_rate :
    ¬ (weaklyStrictServiceRel (rate 1)
      ≤ strictServiceRel (rate 1)) := fun h =>
  wsWitness_not_mem_strictServiceRel
    (h _ _ wsWitness_mem_weaklyStrictServiceRel)

/-- The middle inclusion of the hierarchy is strict at `λ₁`. -/
theorem strictServiceRel_lt_weaklyStrictServiceRel_rate :
    strictServiceRel (rate 1) < weaklyStrictServiceRel (rate 1) :=
  lt_of_le_not_ge (strictServiceRel_le_weaklyStrictServiceRel _)
    not_weaklyStrictServiceRel_le_strictServiceRel_rate

/-- **The converse of the middle inclusion is a non-theorem.** -/
theorem not_forall_weaklyStrictServiceRel_le_strictServiceRel :
    ¬ ∀ beta : ℝ≥0 → ℝ≥0,
      weaklyStrictServiceRel beta ≤ strictServiceRel beta := fun h =>
  not_weaklyStrictServiceRel_le_strictServiceRel_rate (h _)

/-- The converse fails even for monotone left-continuous curves —
the book's standing regularity. -/
theorem not_forall_weaklyStrictServiceRel_le_strictServiceRel_of_monotone :
    ¬ ∀ beta : ℝ≥0 → ℝ≥0, Monotone beta → IsLeftContinuous beta →
      weaklyStrictServiceRel beta ≤ strictServiceRel beta := by
  intro h
  exact not_weaklyStrictServiceRel_le_strictServiceRel_rate
    (h _ (rate_mono 1)
      (isLeftContinuous_of_continuous _ (rate_continuous 1)))


/-! ## The upper inclusion is strict for every delayed-start curve
For monotone `β` vanishing on `[0, t₀)` (`0 < t₀`) and positive at
some `s`, the rate input `λ_ρ` with `ρ = β(s)/s`, served at exactly
the convolution `λ_ρ ∗ β`, is min-plus served at `β` but not weakly
strictly: the pair's only equality point is the origin, and at `s`
the anchored bound demands the full `β(s)` while the convolution
stays strictly below it. The book's rate-line witness for this case
is finite-valued, hence representable here unchanged. -/

/-- Before its start the delayed curve contributes nothing, so the
rate convolution sits strictly below the rate at every positive
time. -/
theorem rateConvCurve_lt_rateCurve {β : ℝ≥0 → ℝ≥0} {t₀ s : ℝ≥0}
    (hmono : Monotone β) (hvan : ∀ u, u < t₀ → β u = 0)
    (ht₀ : 0 < t₀) (hts : t₀ ≤ s) (hβs : 0 < β s) {u : ℝ≥0}
    (hu : 0 < u) :
    rateConvCurve β (β s / s) hmono (hvan 0 ht₀) u
      < rateCurve (β s / s) u := by
  have hs0 : 0 < s := lt_of_lt_of_le ht₀ hts
  have hρ : 0 < β s / s := div_pos hβs hs0
  set w := min (t₀ / 2) u with hw
  have hw0 : 0 < w := lt_min (half_pos ht₀) hu
  have hwu : w ≤ u := min_le_right _ _
  have hwt₀ : w < t₀ := lt_of_le_of_lt (min_le_left _ _)
    (NNReal.half_lt_self (ne_of_gt ht₀))
  have hβw : β w = 0 := hvan w hwt₀
  have hsplit : (u - w) + w = u := tsub_add_cancel_of_le hwu
  calc rateConvCurve β (β s / s) hmono (hvan 0 ht₀) u
      ≤ rate (β s / s) (u - w) + β w := minConvProj_le_add hsplit
    _ = (β s / s) * (u - w) := by rw [hβw, add_zero, rate_apply]
    _ < (β s / s) * u := by
        refine mul_lt_mul_of_pos_left ?_ hρ
        exact tsub_lt_self hu hw0
    _ = rateCurve (β s / s) u := rfl

/-- The pair's only equality point is the origin: the start anchors
there. -/
theorem start_rateCurve_rateConvCurve_eq_zero {β : ℝ≥0 → ℝ≥0}
    {t₀ s : ℝ≥0}
    (hmono : Monotone β) (hvan : ∀ u, u < t₀ → β u = 0)
    (ht₀ : 0 < t₀) (hts : t₀ ≤ s) (hβs : 0 < β s) (t : ℝ≥0) :
    start ⇑(rateCurve (β s / s))
      ⇑(rateConvCurve β (β s / s) hmono (hvan 0 ht₀)) t = 0 := by
  refine le_antisymm (csSup_le ⟨0, zero_le', ?_⟩ fun u hu => ?_)
    zero_le'
  · have hA0 : rateCurve (β s / s) 0 = 0 := (rateCurve _).zero
    have hD0 : rateConvCurve β (β s / s) hmono (hvan 0 ht₀) 0 = 0 :=
      (rateConvCurve β (β s / s) hmono (hvan 0 ht₀)).zero
    show rateCurve (β s / s) 0
      = rateConvCurve β (β s / s) hmono (hvan 0 ht₀) 0
    rw [hA0, hD0]
  · by_contra hu0
    rw [not_le] at hu0
    exact absurd hu.2.symm (ne_of_lt
      (rateConvCurve_lt_rateCurve hmono hvan ht₀ hts hβs hu0))

/-- **For every delayed-start curve the min-plus relation strictly
exceeds the weakly strict one**: the rate pair is min-plus served at
`β` but the anchored bound fails at `s`. -/
theorem exists_minimalServiceRel_not_weaklyStrictServiceRel
    {β : ℝ≥0 → ℝ≥0} {t₀ s : ℝ≥0}
    (hmono : Monotone β) (hvan : ∀ u, u < t₀ → β u = 0)
    (ht₀ : 0 < t₀) (hts : t₀ ≤ s) (hβs : 0 < β s) :
    ∃ A D : Curve, minimalServiceRel (liftEReal β) A D
      ∧ ¬ weaklyStrictServiceRel β A D := by
  have hs0 : 0 < s := lt_of_lt_of_le ht₀ hts
  set A := rateCurve (β s / s) with hA
  set D := rateConvCurve β (β s / s) hmono (hvan 0 ht₀) with hD
  have hcaus : D ≤ A := by
    intro t
    rcases eq_zero_or_pos t with rfl | ht
    · have hA0 : A 0 = 0 := A.zero
      have hD0 : D 0 = 0 := D.zero
      rw [hA0, hD0]
    · exact (rateConvCurve_lt_rateCurve hmono hvan ht₀ hts hβs ht).le
  refine ⟨A, D, mem_minimalServiceRel_iff.mpr ⟨hcaus, fun t => ?_⟩, ?_⟩
  · -- the ε-room between the `ℝ≥0` infimum and the `EReal` convolution
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc1, hc2⟩ := EReal.exists_between_coe_real hcon
    have hεpos : (0 : ℝ) < c - (D t : ℝ) := by
      refine sub_pos.mpr ?_
      have hc1' : (((D t : ℝ≥0) : ℝ) : EReal) < (c : EReal) := hc1
      exact_mod_cast hc1'
    have hlt : (⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        (rate (β s / s) p.1.1 + β p.1.2))
        < D t + (c - (D t : ℝ)).toNNReal := by
      have hDt : D t = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (rate (β s / s) p.1.1 + β p.1.2) := minConvProj_eq _ _ t
      rw [← hDt]
      exact lt_add_of_pos_right _ (Real.toNNReal_pos.mpr hεpos)
    obtain ⟨p, hp⟩ := exists_lt_of_ciInf_lt hlt
    have hpR : ((rate (β s / s) p.1.1 + β p.1.2 : ℝ≥0) : ℝ) < c := by
      have h := (NNReal.coe_lt_coe.mpr hp :
        ((rate (β s / s) p.1.1 + β p.1.2 : ℝ≥0) : ℝ) < _)
      push_cast [Real.coe_toNNReal _ hεpos.le] at h ⊢
      linarith
    have hchain : minConv (curveEReal A) (liftEReal β) t
        ≤ (((rate (β s / s) p.1.1 + β p.1.2 : ℝ≥0) : ℝ) : EReal) := by
      refine le_trans (minConv_le_add _ _ p.2) ?_
      rw [curveEReal_apply]
      push_cast
      exact le_rfl
    exact absurd (lt_of_le_of_lt hchain (by exact_mod_cast hpR))
      (not_lt.mpr hc2.le)
  · rintro ⟨_, hb⟩
    have h := hb s
    have hD0 : D 0 = 0 := D.zero
    rw [start_rateCurve_rateConvCurve_eq_zero hmono hvan ht₀ hts hβs,
      tsub_zero, hD0, zero_add] at h
    have hDs : D s < A s :=
      rateConvCurve_lt_rateCurve hmono hvan ht₀ hts hβs hs0
    have hAs : A s = β s := by
      show β s / s * s = β s
      rw [div_mul_cancel₀ _ (ne_of_gt hs0)]
    rw [hAs] at hDs
    exact absurd h (not_le.mpr hDs)

/-- The strict relation-level separation: for every delayed-start
curve the weakly strict relation is strictly below the min-plus
one. -/
theorem weaklyStrictServiceRel_lt_minimalServiceRel
    {β : ℝ≥0 → ℝ≥0} {t₀ s : ℝ≥0}
    (hmono : Monotone β) (hvan : ∀ u, u < t₀ → β u = 0)
    (ht₀ : 0 < t₀) (hts : t₀ ≤ s) (hβs : 0 < β s) :
    weaklyStrictServiceRel β < minimalServiceRel (liftEReal β) := by
  obtain ⟨A, D, hmp, hnws⟩ :=
    exists_minimalServiceRel_not_weaklyStrictServiceRel
      hmono hvan ht₀ hts hβs
  refine lt_of_le_of_ne (weaklyStrictServiceRel_le_minimalServiceRel β)
    fun heq => ?_
  refine hnws ?_
  rw [heq]
  exact hmp

/-- **The upper inclusion cannot be reversed**: it is not the case
that every monotone curve's min-plus relation refines its weakly
strict one — instantiated at the unit rate-latency curve. -/
theorem not_forall_minimalServiceRel_le_weaklyStrictServiceRel :
    ¬ ∀ β : ℝ≥0 → ℝ≥0, Monotone β →
      minimalServiceRel (liftEReal β) ≤ weaklyStrictServiceRel β := by
  intro h
  have hvan : ∀ u : ℝ≥0, u < 1 → rateLatency (1 : ℝ≥0) 1 u = 0 := by
    intro u hu
    show (1 : ℝ≥0) * (u - 1) = 0
    rw [tsub_eq_zero_of_le (le_of_lt hu), mul_zero]
  have hpos : (0 : ℝ≥0) < rateLatency (1 : ℝ≥0) 1 2 := by
    show (0 : ℝ≥0) < 1 * (2 - 1)
    rw [one_mul]
    norm_num
  obtain ⟨A, D, hmp, hnws⟩ :=
    exists_minimalServiceRel_not_weaklyStrictServiceRel
      (t₀ := 1) (s := 2)
      (rateLatency_mono 1 1) hvan one_pos one_le_two hpos
  exact hnws (h _ (rateLatency_mono 1 1) A D hmp)

end DeepWiki
