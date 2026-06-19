import DeepWiki.NetworkCalculus.ServiceCurveWeaklyStrict
import DeepWiki.NetworkCalculus.RealCurves
import DeepWiki.NetworkCalculus.ServersRate
import DeepWiki.NetworkCalculus.ArrivalCurvesShaperGreedy
import DeepWiki.NetworkCalculus.ServiceCurveMonotony
import DeepWiki.NetworkCalculus.ServiceCurvePackets
import Mathlib.Analysis.Real.Sqrt

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
    exact zero_le
  · have hb : b ≠ 0 := fun hb =>
      ha (le_antisymm (hb ▸ hab) zero_le)
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
    exact min_eq_left zero_le
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
    rw [mul_zero, min_eq_left zero_le]
    exact zero_le
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
          exact ⟨zero_le, wsWitness_eq_iff.mpr (Or.inl rfl)⟩
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
  refine le_antisymm (csSup_le ⟨0, zero_le, ?_⟩ fun u hu => ?_)
    zero_le
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

/-! ## The upper inclusion is strict even for a no-delay curve
The delayed-start witness above needs `t₀ > 0`. For any finite no-delay
rate `λ_b` (`0 < b < 1`), the separation still holds, via a *stalling*
departure: `Dᵗ = max(min(t, 1), b·t)` rises with `λ₁` to the value `1` at
`t = 1`, stalls at `1` through `[1, 1/b]`, then follows the convolution
`λ₁ ∗ λ_b = λ_b`. The stall keeps `D` above `λ₁ ∗ λ_b` (so `(λ₁, D)` is
min-plus served) while a backlogged window `(1, t*]` (`1 < t* < 1/b`) —
whose start is `1` — receives nothing, breaking the start-anchored bound
(the book's no-delay case, the pseudo-inverse made explicit by
`λ_b⁻¹(y) = y / b`). -/

/-- The no-delay witness departure for rate `λ_b`: rate `1` to time `1`, a
stall at `1`, then rate `b`. -/
noncomputable def wsmpDep (b : ℝ≥0) : Curve where
  toFun := fun t => max (min t 1) (b * t)
  mono := fun x y h => max_le_max (min_le_min h le_rfl) (by gcongr)
  zero := by show max (min (0 : ℝ≥0) 1) (b * 0) = 0; simp
  pwc := by
    refine isPiecewiseContinuous_of_continuous _ ?_
    exact (continuous_id.min continuous_const).max (continuous_const.mul continuous_id)
  leftCont := by
    refine isLeftContinuous_of_continuous _ ?_
    exact (continuous_id.min continuous_const).max (continuous_const.mul continuous_id)

/-- `wsmpDep b t` unfolds to the stall expression. -/
theorem wsmpDep_apply (b t : ℝ≥0) : wsmpDep b t = max (min t 1) (b * t) := rfl

/-- The departure dominates the convolution `λ₁ ∗ λ_b = λ_b`. -/
theorem wsmpDep_ge_rate (b t : ℝ≥0) : b * t ≤ wsmpDep b t := le_max_right _ _

/-- The departure stays below the rate-`1` arrival when `b ≤ 1`. -/
theorem wsmpDep_le_arr (b : ℝ≥0) (hb1 : b ≤ 1) (t : ℝ≥0) :
    wsmpDep b t ≤ rateCurve 1 t := by
  show max (min t 1) (b * t) ≤ rateCurve 1 t
  rw [rateCurve_apply, one_mul]
  exact max_le (min_le_left _ _) (mul_le_of_le_one_left zero_le hb1)

/-- The pair's equality points are exactly `[0, 1]` (for `b < 1`). -/
theorem wsmp_eq_iff (b : ℝ≥0) (hb1 : b < 1) {u : ℝ≥0} :
    rateCurve 1 u = wsmpDep b u ↔ u ≤ 1 := by
  rw [rateCurve_apply, one_mul, wsmpDep_apply]
  constructor
  · intro h
    by_contra hu
    rw [not_le] at hu
    have hupos : (0 : ℝ≥0) < u := lt_of_lt_of_le one_pos hu.le
    rw [min_eq_right hu.le] at h
    rcases le_total (b * u) 1 with h2 | h2
    · rw [max_eq_left h2] at h; exact absurd h (ne_of_gt hu)
    · rw [max_eq_right h2] at h
      exact absurd h (ne_of_gt (mul_lt_of_lt_one_left hupos hb1))
  · intro h
    rw [min_eq_left h, max_eq_left (mul_le_of_le_one_left zero_le hb1.le)]

/-- The pair is min-plus served at `λ_b` (`b ≤ 1`): the `(0, t)` split bounds
the convolution by `λ_b(t) ≤ D(t)`. -/
theorem wsmp_mem_minimalServiceRel (b : ℝ≥0) (hb1 : b ≤ 1) :
    minimalServiceRel (liftEReal (rate b)) (rateCurve 1) (wsmpDep b) := by
  refine mem_minimalServiceRel_iff.mpr ⟨fun t => wsmpDep_le_arr b hb1 t, fun t => ?_⟩
  have hbnd : rate b t ≤ wsmpDep b t := by rw [rate_apply]; exact wsmpDep_ge_rate b t
  calc minConv (curveEReal (rateCurve 1)) (liftEReal (rate b)) t
      ≤ curveEReal (rateCurve 1) 0 + liftEReal (rate b) t :=
        minConv_le_add _ _ (zero_add t)
    _ ≤ curveEReal (wsmpDep b) t := by
        rw [curveEReal_apply, curveEReal_apply, rateCurve_apply, mul_zero,
          NNReal.coe_zero, EReal.coe_zero, zero_add]
        show ((rate b t : ℝ) : EReal) ≤ ((wsmpDep b t : ℝ) : EReal)
        exact_mod_cast hbnd

/-- The pair is not weakly strictly served at `λ_b` (`0 < b < 1`): a
backlogged window `(1, t*]` with `1 < t* < 1/b` starts at `1` but receives
nothing while the anchored bound demands growth. -/
theorem wsmp_not_mem_weaklyStrictServiceRel (b : ℝ≥0) (hb0 : 0 < b) (hb1 : b < 1) :
    ¬ weaklyStrictServiceRel (rate b) (rateCurve 1) (wsmpDep b) := by
  rintro ⟨-, hb⟩
  obtain ⟨ts, hts1, hts2⟩ := exists_between ((one_lt_div hb0).mpr hb1)
  have hts1le : (1 : ℝ≥0) ≤ ts := hts1.le
  have htsb : b * ts < 1 :=
    calc b * ts < b * (1 / b) := mul_lt_mul_of_pos_left hts2 hb0
      _ = 1 := by rw [mul_one_div, div_self hb0.ne']
  have hstart : start ⇑(rateCurve 1) ⇑(wsmpDep b) ts = 1 := by
    unfold start
    have hset : {u | u ≤ ts ∧ rateCurve 1 u = wsmpDep b u} = Set.Iic 1 := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_Iic, wsmp_eq_iff b hb1]
      exact ⟨fun h => h.2, fun h => ⟨le_trans h hts1le, h⟩⟩
    rw [hset, csSup_Iic]
  have h := hb ts
  rw [hstart] at h
  have hD1 : wsmpDep b 1 = 1 := by
    rw [wsmpDep_apply, min_eq_left (le_refl 1), max_eq_left (by rw [mul_one]; exact hb1.le)]
  have hDts : wsmpDep b ts = 1 := by
    rw [wsmpDep_apply, min_eq_right hts1le, max_eq_left htsb.le]
  rw [hD1, hDts, rate_apply] at h
  exact absurd h (not_le.mpr (lt_add_of_pos_right 1 (mul_pos hb0 (tsub_pos_of_lt hts1))))

/-- **The upper inclusion is strict for every no-delay rate `λ_b`**
(`0 < b < 1`): its weakly strict relation is strictly below its min-plus
relation, witnessed by the stalling departure. -/
theorem weaklyStrictServiceRel_lt_minimalServiceRel_rate (b : ℝ≥0)
    (hb0 : 0 < b) (hb1 : b < 1) :
    weaklyStrictServiceRel (rate b) < minimalServiceRel (liftEReal (rate b)) := by
  refine lt_of_le_of_ne (weaklyStrictServiceRel_le_minimalServiceRel _) fun heq => ?_
  refine wsmp_not_mem_weaklyStrictServiceRel b hb0 hb1 ?_
  rw [heq]; exact wsmp_mem_minimalServiceRel b hb1.le

/-- The no-delay separation at the representative rate `λ_{1/2}`. -/
theorem weaklyStrictServiceRel_lt_minimalServiceRel_rateHalf :
    weaklyStrictServiceRel (rate (1 / 2 : ℝ≥0))
      < minimalServiceRel (liftEReal (rate (1 / 2 : ℝ≥0))) :=
  weaklyStrictServiceRel_lt_minimalServiceRel_rate (1 / 2) (by positivity)
    (by rw [div_lt_one (by norm_num : (0 : ℝ≥0) < 2)]; norm_num)

/-! ## Case B of the general no-delay separation: a sub-rate curve
The general no-delay case when the rate `λ_ρ` overtakes a
no-delay `β` that stays strictly below it (`∀ u > 0, β u < ρu`) yet is *slow*:
some stall point `s < ts` has `β ts < ρs`. The stalling departure
`D = (λ_ρ ⊓ ρs) ⊔ β` rises with `λ_ρ` to the level `ρs` at `s`, stalls there
through `(s, ts]`, then follows `β`. It is min-plus served by `β` under
`A = λ_ρ` but breaks the start-anchored bound on the stall window. The rate
family `λ_b` above is the instance `ρ = 1`, `s = 1`. -/

/-- The case-B stalling departure `D = (λ_ρ ⊓ ρs) ⊔ β`. -/
noncomputable def wsmpGenDep (β : ℝ≥0 → ℝ≥0) (ρ s : ℝ≥0)
    (hmono : Monotone β) (hlc : IsLeftContinuous β)
    (hpwc : IsPiecewiseContinuous β) (h0 : β 0 = 0) : Curve where
  toFun := fun t => max (min (ρ * t) (ρ * s)) (β t)
  mono := fun _ _ h => max_le_max (min_le_min (by gcongr) le_rfl) (hmono h)
  zero := by show max (min (ρ * 0) (ρ * s)) (β 0) = 0; rw [mul_zero, h0]; simp
  pwc := by
    intro T
    refine Set.Finite.subset (hpwc T) ?_
    rintro t ⟨ht, htm⟩
    exact ⟨fun hc => ht (((continuousAt_const.mul continuousAt_id).min
      continuousAt_const).max hc), htm⟩
  leftCont := fun t => (((continuous_const.mul continuous_id).min
    continuous_const).continuousWithinAt).max (hlc t)

/-- `wsmpGenDep … t = max (min (ρ t) (ρ s)) (β t)`. -/
theorem wsmpGenDep_apply {β : ℝ≥0 → ℝ≥0} {ρ s : ℝ≥0} {hmono hlc hpwc h0} (t : ℝ≥0) :
    wsmpGenDep β ρ s hmono hlc hpwc h0 t = max (min (ρ * t) (ρ * s)) (β t) := rfl

/-- The departure dominates `β`. -/
theorem wsmpGenDep_ge {β : ℝ≥0 → ℝ≥0} {ρ s : ℝ≥0} {hmono hlc hpwc h0} (t : ℝ≥0) :
    β t ≤ wsmpGenDep β ρ s hmono hlc hpwc h0 t := le_max_right _ _

/-- Below the rate, the departure stays under `λ_ρ`. -/
theorem wsmpGenDep_le_arr {β : ℝ≥0 → ℝ≥0} {ρ s : ℝ≥0} {hmono hlc hpwc h0}
    (hle : ∀ t, β t ≤ ρ * t) (t : ℝ≥0) :
    wsmpGenDep β ρ s hmono hlc hpwc h0 t ≤ rateCurve ρ t := by
  rw [wsmpGenDep_apply]; show max (min (ρ * t) (ρ * s)) (β t) ≤ rateCurve ρ t
  rw [rateCurve_apply]
  exact max_le (min_le_left _ _) (hle t)

/-- The pair's equality points are exactly `[0, s]`. -/
theorem wsmpGen_eq_iff {β : ℝ≥0 → ℝ≥0} {ρ s : ℝ≥0} {hmono hlc hpwc h0}
    (hρ : 0 < ρ) (hlt : ∀ u, 0 < u → β u < ρ * u) (hle : ∀ t, β t ≤ ρ * t) {u : ℝ≥0} :
    rateCurve ρ u = wsmpGenDep β ρ s hmono hlc hpwc h0 u ↔ u ≤ s := by
  rw [rateCurve_apply, wsmpGenDep_apply]
  constructor
  · intro h
    by_contra hu
    rw [not_le] at hu
    rw [min_eq_right (le_of_lt (mul_lt_mul_of_pos_left hu hρ))] at h
    rcases le_total (β u) (ρ * s) with h2 | h2
    · rw [max_eq_left h2] at h
      exact absurd h (ne_of_gt (mul_lt_mul_of_pos_left hu hρ))
    · rw [max_eq_right h2] at h
      exact absurd h (ne_of_gt (hlt u (lt_of_le_of_lt zero_le hu)))
  · intro h
    rw [min_eq_left (by gcongr), max_eq_left (hle u)]

/-- The pair is min-plus served at `β`: the `(0, t)` split bounds the
convolution by `β t ≤ D t`. -/
theorem wsmpGen_mem {β : ℝ≥0 → ℝ≥0} {ρ s : ℝ≥0} {hmono hlc hpwc h0}
    (hle : ∀ t, β t ≤ ρ * t) :
    minimalServiceRel (liftEReal β) (rateCurve ρ) (wsmpGenDep β ρ s hmono hlc hpwc h0) := by
  refine mem_minimalServiceRel_iff.mpr ⟨fun t => wsmpGenDep_le_arr hle t, fun t => ?_⟩
  calc minConv (curveEReal (rateCurve ρ)) (liftEReal β) t
      ≤ curveEReal (rateCurve ρ) 0 + liftEReal β t := minConv_le_add _ _ (zero_add t)
    _ ≤ curveEReal (wsmpGenDep β ρ s hmono hlc hpwc h0) t := by
        rw [curveEReal_apply, curveEReal_apply, rateCurve_apply, mul_zero,
          NNReal.coe_zero, EReal.coe_zero, zero_add]
        show ((β t : ℝ) : EReal) ≤ ((wsmpGenDep β ρ s hmono hlc hpwc h0 t : ℝ) : EReal)
        exact_mod_cast wsmpGenDep_ge t

/-- The pair is not weakly strictly served at `β`: the stall window `(s, ts]`
starts at `s` but receives nothing while the anchored bound demands growth. -/
theorem wsmpGen_not_mem {β : ℝ≥0 → ℝ≥0} {ρ s : ℝ≥0} {hmono hlc hpwc h0}
    (hρ : 0 < ρ) (hpos : ∀ u, 0 < u → 0 < β u)
    (hlt : ∀ u, 0 < u → β u < ρ * u) (hle : ∀ t, β t ≤ ρ * t)
    (ts : ℝ≥0) (hts1 : s < ts) (hts2 : β ts < ρ * s) :
    ¬ weaklyStrictServiceRel β (rateCurve ρ) (wsmpGenDep β ρ s hmono hlc hpwc h0) := by
  rintro ⟨-, hb⟩
  have hstart : start ⇑(rateCurve ρ) ⇑(wsmpGenDep β ρ s hmono hlc hpwc h0) ts = s := by
    unfold start
    have hset : {u | u ≤ ts ∧ rateCurve ρ u = wsmpGenDep β ρ s hmono hlc hpwc h0 u}
        = Set.Iic s := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_Iic, wsmpGen_eq_iff hρ hlt hle]
      exact ⟨fun h => h.2, fun h => ⟨le_trans h hts1.le, h⟩⟩
    rw [hset, csSup_Iic]
  have h := hb ts
  rw [hstart] at h
  have hDs : wsmpGenDep β ρ s hmono hlc hpwc h0 s = ρ * s := by
    rw [wsmpGenDep_apply, min_self, max_eq_left (hle s)]
  have hDts : wsmpGenDep β ρ s hmono hlc hpwc h0 ts = ρ * s := by
    rw [wsmpGenDep_apply, min_eq_right (le_of_lt (mul_lt_mul_of_pos_left hts1 hρ)),
      max_eq_left hts2.le]
  rw [hDs, hDts] at h
  exact absurd h (not_le.mpr (lt_add_of_pos_right (ρ * s)
    (hpos (ts - s) (tsub_pos_of_lt hts1))))

/-- **The upper inclusion is strict for a no-delay sub-rate curve** (case B of
the no-delay separation): a no-delay `β` strictly below the rate `ρ`, slow enough to stall
(`β ts < ρs` for some `s < ts`), has `wstrict(β) ⊊ mp(β)`. -/
theorem weaklyStrictServiceRel_lt_minimalServiceRel_subRate
    {β : ℝ≥0 → ℝ≥0} (hmono : Monotone β) (hlc : IsLeftContinuous β)
    (hpwc : IsPiecewiseContinuous β) (h0 : β 0 = 0)
    {ρ s : ℝ≥0} (hρ : 0 < ρ) (hpos : ∀ u, 0 < u → 0 < β u)
    (hlt : ∀ u, 0 < u → β u < ρ * u)
    (ts : ℝ≥0) (hts1 : s < ts) (hts2 : β ts < ρ * s) :
    weaklyStrictServiceRel β < minimalServiceRel (liftEReal β) := by
  have hle : ∀ t, β t ≤ ρ * t := fun t => by
    rcases eq_or_ne t 0 with rfl | ht
    · rw [h0, mul_zero]
    · exact (hlt t (lt_of_le_of_ne zero_le (Ne.symm ht))).le
  refine lt_of_le_of_ne (weaklyStrictServiceRel_le_minimalServiceRel _) fun heq => ?_
  refine wsmpGen_not_mem (hmono := hmono) (hlc := hlc) (hpwc := hpwc) (h0 := h0)
    hρ hpos hlt hle ts hts1 hts2 ?_
  rw [heq]; exact wsmpGen_mem (hmono := hmono) (hlc := hlc) (hpwc := hpwc) (h0 := h0) hle

/-! ## Case C of the general no-delay separation: a superlinear curve
The remaining no-delay case: when `β` overtakes every rate
(no `λ_ρ` stays above it), pick `ρ` with `λ_ρ > β` near the origin but
`β` overtaking at some `t_ov` (`β t_ov > ρ·t_ov`). The departure `D = λ_ρ ∗ β`
(a Curve via the Lipschitz-greedy machinery) is min-plus served by `β`, but
has no positive equality point with `λ_ρ` (so its start is the origin), and the
start-anchored bound then demands `D t_ov ≥ β t_ov` while `D t_ov ≤ ρ·t_ov <
β t_ov`. -/

/-- The case-C departure `λ_ρ ∗ β`, as a Curve (`λ_ρ` is `ρ`-Lipschitz). -/
noncomputable def wsmpSupDep (β : Curve) (ρ : ℝ≥0) : Curve :=
  greedyCurve (rateCurve ρ) (curveEReal β) (monotone_curveEReal β) (curveEReal_zero β)
    (isLeftContinuous_curveEReal β)
    (isPiecewiseContinuous_greedyFun_of_lipschitz (rateCurve ρ) (monotone_curveEReal β)
      (curveEReal_nonneg β) (curveEReal_zero β)
      (fun u v => le_of_eq (by rw [rateCurve_apply, rateCurve_apply]; ring)))

/-- `curveEReal (wsmpSupDep β ρ) = λ_ρ ∗ β`. -/
theorem curveEReal_wsmpSupDep (β : Curve) (ρ : ℝ≥0) :
    curveEReal (wsmpSupDep β ρ) = minConv (curveEReal (rateCurve ρ)) (curveEReal β) :=
  curveEReal_greedyCurve _ _ _ _ _

/-- The case-C departure stays below `λ_ρ`. -/
theorem wsmpSupDep_le (β : Curve) (ρ : ℝ≥0) (t : ℝ≥0) :
    wsmpSupDep β ρ t ≤ rateCurve ρ t := by
  have h : curveEReal (wsmpSupDep β ρ) t ≤ curveEReal (rateCurve ρ) t := by
    rw [curveEReal_wsmpSupDep]
    exact minConv_self_le (curveEReal_zero β).le (rateCurve ρ) t
  rwa [curveEReal_apply, curveEReal_apply, EReal.coe_le_coe_iff, NNReal.coe_le_coe] at h

/-- Case C is min-plus served at `β` (the departure is exactly `λ_ρ ∗ β`). -/
theorem wsmpSup_mem (β : Curve) (ρ : ℝ≥0) :
    minimalServiceRel (curveEReal β) (rateCurve ρ) (wsmpSupDep β ρ) :=
  mem_minimalServiceRel_iff.mpr ⟨fun t => wsmpSupDep_le β ρ t,
    fun t => le_of_eq (congrFun (curveEReal_wsmpSupDep β ρ).symm t)⟩

/-- Below an overtaking, `λ_ρ ∗ β` sits strictly below `λ_ρ`: the equality
points with `λ_ρ` are just the origin, so the start is the origin. -/
theorem wsmpSupDep_lt (β : Curve) {ρ : ℝ≥0}
    (hbelow : ∀ t, 0 < t → ∃ s, 0 < s ∧ s ≤ t ∧ β s < ρ * s) {u : ℝ≥0} (hu : 0 < u) :
    wsmpSupDep β ρ u < rateCurve ρ u := by
  obtain ⟨s, hs0, hsu, hsβ⟩ := hbelow u hu
  have hE : curveEReal (wsmpSupDep β ρ) u < curveEReal (rateCurve ρ) u := by
    rw [curveEReal_wsmpSupDep]
    refine lt_of_le_of_lt (minConv_le_add (curveEReal (rateCurve ρ)) (curveEReal β)
      (tsub_add_cancel_of_le hsu)) ?_
    rw [curveEReal_apply, curveEReal_apply, curveEReal_apply, ← EReal.coe_add,
      EReal.coe_lt_coe_iff, rateCurve_apply, rateCurve_apply]
    have hβs : ((β s : ℝ)) < (ρ : ℝ) * (s : ℝ) := by exact_mod_cast hsβ
    have hdist : (ρ : ℝ) * ((u : ℝ) - (s : ℝ)) + (ρ : ℝ) * (s : ℝ) = (ρ : ℝ) * (u : ℝ) := by
      ring
    push_cast [NNReal.coe_sub hsu]
    linarith
  rwa [curveEReal_apply, curveEReal_apply, EReal.coe_lt_coe_iff, NNReal.coe_lt_coe] at hE

/-- Case C is not weakly strictly served: start at the origin, but the bound
demands `D t_ov ≥ β t_ov` while `D t_ov ≤ ρ·t_ov < β t_ov`. -/
theorem wsmpSup_not_mem (β : Curve) {ρ : ℝ≥0}
    (hbelow : ∀ t, 0 < t → ∃ s, 0 < s ∧ s ≤ t ∧ β s < ρ * s)
    {t_ov : ℝ≥0} (hov : ρ * t_ov < β t_ov) :
    ¬ weaklyStrictServiceRel ⇑β (rateCurve ρ) (wsmpSupDep β ρ) := by
  rintro ⟨-, hb⟩
  have hstart : start ⇑(rateCurve ρ) ⇑(wsmpSupDep β ρ) t_ov = 0 := by
    unfold start
    have hset : {u | u ≤ t_ov ∧ rateCurve ρ u = wsmpSupDep β ρ u} = {0} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, heq⟩
        by_contra hu0
        exact absurd heq.symm (ne_of_lt (wsmpSupDep_lt β hbelow (zero_lt_iff.mpr hu0)))
      · rintro rfl
        refine ⟨zero_le, ?_⟩
        rw [rateCurve_apply, mul_zero]
        exact ((wsmpSupDep β ρ).zero).symm
    rw [hset, csSup_singleton]
  have h := hb t_ov
  have h0D : wsmpSupDep β ρ 0 = 0 := (wsmpSupDep β ρ).zero
  rw [hstart, tsub_zero, h0D, zero_add] at h
  exact absurd (le_trans h (wsmpSupDep_le β ρ t_ov)) (not_le.mpr hov)

/-- **The upper inclusion is strict for a no-delay superlinear curve** (case C of
the no-delay separation): if `β` overtakes the rate `ρ` (`ρ·t_ov < β t_ov`) but `λ_ρ`
exceeds `β` near the origin (`β s < ρ·s` arbitrarily close to `0`), then
`wstrict(β) ⊊ mp(β)`. -/
theorem weaklyStrictServiceRel_lt_minimalServiceRel_superlinear (β : Curve) {ρ : ℝ≥0}
    (hbelow : ∀ t, 0 < t → ∃ s, 0 < s ∧ s ≤ t ∧ β s < ρ * s)
    {t_ov : ℝ≥0} (hov : ρ * t_ov < β t_ov) :
    weaklyStrictServiceRel ⇑β < minimalServiceRel (curveEReal β) := by
  refine lt_of_le_of_ne (weaklyStrictServiceRel_le_minimalServiceRel _) fun heq => ?_
  refine wsmpSup_not_mem β hbelow hov ?_
  rw [heq]; exact wsmpSup_mem β ρ

/-- **The no-delay separation for every sub-linear curve** (the practical case
of the no-delay separation): a no-delay `β` bounded by some rate (`β t ≤ ρ₀·t`) has
`wstrict(β) ⊊ mp(β)` — it is case B with `ρ = 2ρ₀+1`, stalling at `s = 1/2`
below `ts = 1`. Covers rates, rate-latencies (no-delay part), and every
bounded-rate flow; superlinear and infinite-initial-slope curves are the
remaining (case-C / the `√·` witness below) classes. -/
theorem weaklyStrictServiceRel_lt_minimalServiceRel_of_subLinear (β : Curve) {ρ₀ : ℝ≥0}
    (hsub : ∀ t, β t ≤ ρ₀ * t) (hpos : ∀ u, 0 < u → 0 < β u) :
    weaklyStrictServiceRel ⇑β < minimalServiceRel (curveEReal β) := by
  have hρρ : ρ₀ < 2 * ρ₀ + 1 := by
    rw [show 2 * ρ₀ + 1 = ρ₀ + (ρ₀ + 1) from by ring]
    exact lt_add_of_pos_right ρ₀ (by positivity)
  refine weaklyStrictServiceRel_lt_minimalServiceRel_subRate β.mono β.leftCont β.pwc β.zero
    (ρ := 2 * ρ₀ + 1) (s := 1 / 2) (by positivity) hpos
    (fun u hu => (hsub u).trans_lt (mul_lt_mul_of_pos_right hρρ hu)) 1 (by norm_num) ?_
  calc β 1 ≤ ρ₀ * 1 := hsub 1
    _ = ρ₀ := mul_one _
    _ < (2 * ρ₀ + 1) * (1 / 2) := by
        rw [show (2 * ρ₀ + 1) * (1 / 2) = ρ₀ + 1 / 2 from by ring]
        exact lt_add_of_pos_right ρ₀ (by norm_num)

/-! ## The `√·` witness: an infinite-initial-slope curve
The rate-based separations above need a rate `λ_ρ` sitting above `β` near the
origin; a concave curve with infinite initial slope (`β = √·`) admits no such
rate, so those constructions miss it. A direct witness covers it: the arrival
`A = 1_{>0} + 1_{>1}` (two unit bursts) and departure `D = √· ⊓ 2` satisfy
`A ∗ √· ≤ D ≤ A` — so `(A, D)` is min-plus served — yet at `t = 2` the
backlogged period starts at `1` (the convolution harvests the burst at `0`,
not at the start), and the start-anchored bound demands `D 2 ≥ D 1 + √1 = 2`
while `D 2 = √2 < 2`. Hence `wstrict(√·) ⊊ mp(√·)`: the hierarchy is strict for
`√·` too, so `wstrict = mp` fails for every `β↑ ∉ {δ₀, 0}`. -/

/-- The square-root service curve `√·` as a plain function. -/
noncomputable def sqrtFun : ℝ≥0 → ℝ≥0 := fun t => NNReal.sqrt t

/-- `sqrtFun t = √t`. -/
theorem sqrtFun_apply (t : ℝ≥0) : sqrtFun t = NNReal.sqrt t := rfl

/-- `√·` is monotone. -/
theorem sqrtFun_mono : Monotone sqrtFun := fun _ _ h => NNReal.sqrt_le_sqrt.mpr h

/-- `√·` is continuous. -/
theorem sqrtFun_continuous : Continuous sqrtFun := NNReal.continuous_sqrt

/-- `√·` is left-continuous. -/
theorem sqrtFun_leftCont : IsLeftContinuous sqrtFun :=
  isLeftContinuous_of_continuous _ sqrtFun_continuous

/-- `√·` is piecewise continuous. -/
theorem sqrtFun_pwc : IsPiecewiseContinuous sqrtFun :=
  isPiecewiseContinuous_of_continuous _ sqrtFun_continuous

/-- `√0 = 0`. -/
theorem sqrtFun_zero : sqrtFun 0 = 0 := NNReal.sqrt_zero

/-- `√1 = 1`. -/
theorem sqrtFun_one : sqrtFun 1 = 1 := NNReal.sqrt_one

/-- `√2 < 2`. -/
theorem sqrtFun_two_lt_two : sqrtFun 2 < 2 := by
  have h4 : NNReal.sqrt 4 = 2 := by
    rw [show (4 : ℝ≥0) = 2 ^ 2 from by norm_num, NNReal.sqrt_sq]
  calc sqrtFun 2 = NNReal.sqrt 2 := rfl
    _ < NNReal.sqrt 4 := NNReal.sqrt_lt_sqrt.mpr (by norm_num)
    _ = 2 := h4

/-- **The upper inclusion is strict for any strictly-subadditive curve.**
If a regular `β` is strictly subadditive at some split `0 < a < t`
(`β t < β a + β (t − a)`), then `weaklyStrictServiceRel β < minimalServiceRel
(liftEReal β)`. Witness: arrival `A = β a · 1_{>0} + (β t + 1 − β a) · 1_{>a}`
(it empties at `a`) and departure `D = β ⊓ (β t + 1)`. The convolution harvests
the burst at `0`, so `A ∗ β ≤ D ≤ A` (min-plus served); but `t`'s backlogged
period starts at `a`, and the start-anchored bound demands
`β a + β (t − a) ≤ β t`, which strict subadditivity denies. -/
theorem weaklyStrictServiceRel_lt_minimalServiceRel_of_strictSubadditive
    {β : ℝ≥0 → ℝ≥0} (hmono : Monotone β) (hlc : IsLeftContinuous β)
    (hpwc : IsPiecewiseContinuous β) (h0 : β 0 = 0)
    {a t : ℝ≥0} (ha : 0 < a) (hat : a < t)
    (hsub : β t < β a + β (t - a)) :
    weaklyStrictServiceRel β < minimalServiceRel (liftEReal β) := by
  have hβtM : β t < β t + 1 := lt_add_one _
  have hβaM : β a < β t + 1 := (hmono hat.le).trans_lt hβtM
  set A : Curve := stepCurve 0 (β a) + stepCurve a (β t + 1 - β a) with hAdef
  set D : Curve := clipCurve β (β t + 1) hmono hlc hpwc h0 with hDdef
  have hAapp : ∀ u, A u =
      (if (0 : ℝ≥0) < u then β a else 0) + (if a < u then β t + 1 - β a else 0) := by
    intro u
    show (stepCurve 0 (β a) + stepCurve a (β t + 1 - β a)) u = _
    rw [Curve.add_apply, stepCurve_apply, stepCurve_apply]
  have hDapp : ∀ u, D u = min (β u) (β t + 1) := fun _ => rfl
  have hA_zero : A 0 = 0 := by
    rw [hAapp, if_neg (lt_irrefl 0),
      if_neg (not_lt.mpr (zero_le : (0 : ℝ≥0) ≤ a)), add_zero]
  have hA_mid : ∀ u, 0 < u → u ≤ a → A u = β a := fun u h0u hua => by
    rw [hAapp, if_pos h0u, if_neg (not_lt.mpr hua), add_zero]
  have hA_hi : ∀ u, a < u → A u = β t + 1 := fun u hu => by
    rw [hAapp, if_pos (ha.trans hu), if_pos hu, add_tsub_cancel_of_le hβaM.le]
  have hA_le_M : ∀ u, A u ≤ β t + 1 := by
    intro u
    rcases le_or_gt u a with hua | hua
    · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0u | h0u
      · rw [← h0u, hA_zero]; exact zero_le
      · rw [hA_mid u h0u hua]; exact hβaM.le
    · rw [hA_hi u hua]
  have hcaus : D ≤ A := by
    intro u
    rcases le_or_gt u a with hua | hua
    · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0u | h0u
      · rw [← h0u, hDapp, h0, hA_zero, min_eq_left (zero_le : (0 : ℝ≥0) ≤ β t + 1)]
      · rw [hA_mid u h0u hua, hDapp]
        exact (min_le_left _ _).trans (hmono hua)
    · rw [hA_hi u hua, hDapp]; exact min_le_right _ _
  have hmem : minimalServiceRel (liftEReal β) A D := by
    refine mem_minimalServiceRel_iff.mpr ⟨hcaus, fun u => ?_⟩
    rcases le_total (β u) (β t + 1) with h | h
    · calc minConv (curveEReal A) (liftEReal β) u
          ≤ curveEReal A 0 + liftEReal β u := minConv_le_add _ _ (zero_add u)
        _ ≤ curveEReal D u := by
            rw [curveEReal_zero, zero_add, curveEReal_apply]
            exact_mod_cast (show β u ≤ D u by rw [hDapp]; exact le_min le_rfl h)
    · calc minConv (curveEReal A) (liftEReal β) u
          ≤ curveEReal A u + liftEReal β 0 := minConv_le_add _ _ (add_zero u)
        _ ≤ curveEReal D u := by
            have hz : liftEReal β 0 = 0 := by
              show ((β 0 : ℝ) : EReal) = 0
              rw [h0, NNReal.coe_zero, EReal.coe_zero]
            rw [hz, add_zero, curveEReal_apply, curveEReal_apply]
            exact_mod_cast
              (show A u ≤ D u by rw [hDapp, min_eq_right h]; exact hA_le_M u)
  have hstart : start ⇑A ⇑D t = a := by
    have hamem : a ≤ t ∧ A a = D a :=
      ⟨hat.le, by rw [hA_mid a ha le_rfl, hDapp, min_eq_left hβaM.le]⟩
    unfold start
    refine le_antisymm (csSup_le ⟨a, hamem⟩ fun u hu => ?_)
      (le_csSup ⟨t, fun v hv => hv.1⟩ hamem)
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨hut, hAD⟩ := hu
    rw [hA_hi u hcon, hDapp] at hAD
    have hle1 : β t + 1 ≤ β u := by rw [hAD]; exact min_le_left _ _
    exact absurd (hle1.trans (hmono hut)) (not_le.mpr hβtM)
  have hnotmem : ¬ weaklyStrictServiceRel β A D := by
    rintro ⟨-, hb⟩
    have h := hb t
    rw [hstart, show D a = β a from by rw [hDapp, min_eq_left hβaM.le],
      show D t = β t from by rw [hDapp, min_eq_left hβtM.le]] at h
    exact absurd h (not_le.mpr hsub)
  refine lt_of_le_of_ne (weaklyStrictServiceRel_le_minimalServiceRel _) fun heq => hnotmem ?_
  rw [heq]; exact hmem

/-- **Strict is strictly below weakly strict for any strictly-subadditive
curve.** For regular `β` strictly subadditive at some `0 < a < t`
(`β t < β a + β (t − a)`), the burst-clip pair `(M·1_{>0}, β ⊓ M)` (`M = β t + 1`)
is weakly strictly served by `β` — its backlog starts at the origin, where the
anchored bound is `β` itself (`clip_mem_weaklyStrictServiceRel`) — but not
strictly: the interior window `(a, t]` demands `β a + β (t − a) ≤ β t`, which
strict subadditivity denies. (Contrast the rate witness `λ_b`, which is additive,
not strictly subadditive.) -/
theorem strictServiceRel_lt_weaklyStrictServiceRel_of_strictSubadditive
    {β : ℝ≥0 → ℝ≥0} (hmono : Monotone β) (hlc : IsLeftContinuous β)
    (hpwc : IsPiecewiseContinuous β) (h0 : β 0 = 0)
    {a t : ℝ≥0} (ha : 0 < a) (hat : a < t)
    (hsub : β t < β a + β (t - a)) :
    strictServiceRel β < weaklyStrictServiceRel β := by
  have hβtM : β t < β t + 1 := lt_add_one _
  have hβaM : β a < β t + 1 := (hmono hat.le).trans_lt hβtM
  have hnotmem : ¬ strictServiceRel β (burstCurve (β t + 1))
      (clipCurve β (β t + 1) hmono hlc hpwc h0) := by
    rintro ⟨-, hstrict⟩
    have hbl : IsBacklogged (⇑(burstCurve (β t + 1)))
        (⇑(clipCurve β (β t + 1) hmono hlc hpwc h0)) (Set.Ioc a t) := by
      intro u hu
      show clipFun β (β t + 1) u < burstFun (β t + 1) u
      rw [burstFun_apply_of_ne _ (ne_of_gt (ha.trans hu.1)),
        clipFun_eq_of_lt ((hmono hu.2).trans_lt hβtM)]
      exact (hmono hu.2).trans_lt hβtM
    have h := hstrict a t hat.le hbl
    rw [show (clipCurve β (β t + 1) hmono hlc hpwc h0) a = β a from clipFun_eq_of_lt hβaM,
      show (clipCurve β (β t + 1) hmono hlc hpwc h0) t = β t from clipFun_eq_of_lt hβtM] at h
    exact absurd h (not_le.mpr hsub)
  refine lt_of_le_of_ne (strictServiceRel_le_weaklyStrictServiceRel β) fun heq => hnotmem ?_
  rw [heq]; exact clip_mem_weaklyStrictServiceRel (β t + 1) hmono hlc hpwc h0

/-- **The upper inclusion is strict for `√·`** — the infinite-initial-slope
curve missed by the rate constructions. It is the strict-subadditivity instance
at the split `(a, t) = (1, 2)`: `√2 < √1 + √1 = 2`. -/
theorem weaklyStrictServiceRel_lt_minimalServiceRel_sqrt :
    weaklyStrictServiceRel sqrtFun < minimalServiceRel (liftEReal sqrtFun) :=
  weaklyStrictServiceRel_lt_minimalServiceRel_of_strictSubadditive
    (a := 1) (t := 2) sqrtFun_mono sqrtFun_leftCont sqrtFun_pwc sqrtFun_zero
    one_pos (by norm_num)
    (by rw [show (2 : ℝ≥0) - 1 = 1 from tsub_eq_of_eq_add (by norm_num), sqrtFun_one,
          show (1 : ℝ≥0) + 1 = 2 from by norm_num]
        exact sqrtFun_two_lt_two)

/-- `√·` is strictly subadditive, so its strict relation also lies strictly
below its weakly strict relation: both hierarchy inclusions are strict at `√·`
(the `(a, t) = (1, 2)` instance). -/
theorem strictServiceRel_lt_weaklyStrictServiceRel_sqrt :
    strictServiceRel sqrtFun < weaklyStrictServiceRel sqrtFun :=
  strictServiceRel_lt_weaklyStrictServiceRel_of_strictSubadditive
    (a := 1) (t := 2) sqrtFun_mono sqrtFun_leftCont sqrtFun_pwc sqrtFun_zero
    one_pos (by norm_num)
    (by rw [show (2 : ℝ≥0) - 1 = 1 from tsub_eq_of_eq_add (by norm_num), sqrtFun_one,
          show (1 : ℝ≥0) + 1 = 2 from by norm_num]
        exact sqrtFun_two_lt_two)

/-! ## Book restatement (the hierarchy is strict at `√·`)
`√·` is concave with infinite initial slope, so `√·↑ = √· ∉ {δ₀, 0}`, and it is
strictly subadditive (`√2 < √1 + √1`). The two upper inclusions are therefore
both strict at `√·`: `S_strict(√·) ⊊ S_wstrict(√·) ⊊ S_mp(√·)`. The lower
(`strict`) strictness holds for every strictly-subadditive (e.g.
strictly-concave) curve; the upper (`mp`) one additionally covers the
infinite-initial-slope curves the rate constructions miss. (The bottom
`S_vcn`-vs-`S_strict` inclusion is the adjudicated jump-sensitive one — not
asserted here.) -/
example : strictServiceRel sqrtFun < weaklyStrictServiceRel sqrtFun :=
  strictServiceRel_lt_weaklyStrictServiceRel_sqrt
example : weaklyStrictServiceRel sqrtFun < minimalServiceRel (liftEReal sqrtFun) :=
  weaklyStrictServiceRel_lt_minimalServiceRel_sqrt

/-! ## strict ⊊ wstrict for rate-latency (the superadditive practical curve)
Rate-latency `β_{R,T}` is superadditive, so the burst-clip witness above (which
rides strict subadditivity) does not separate it. A *front-loaded* departure
does: banking service above `β` early keeps the start-anchored bound while an
interior window of length `> T` is under-served. Witness at `(R, T) = (2, 1)`
(`β = 2(t−1)₊`): arrival `8·1_{>0}`, departure `min(4t, t+3, 8)` — rate `4` to
height `4` by `t = 1`, then the slow rate `1` to the cap `8` at `t = 5`. The
backlog (`(0, 5)`) starts at the origin, where the anchored bound holds; but the
window `(1, 4]` demands `D 1 + β 3 = 4 + 4 = 8 > 7 = D 4`. -/

/-- The front-loaded rate-latency witness departure `min(4t, t+3, 8)`. -/
noncomputable def rlDep : Curve where
  toFun := fun t => min (min (4 * t) (t + 3)) 8
  mono := fun _ _ h => min_le_min (min_le_min (by gcongr) (by gcongr)) le_rfl
  zero := by
    show min (min (4 * 0) (0 + 3)) 8 = 0
    rw [mul_zero, zero_add, min_eq_left (zero_le : (0 : ℝ≥0) ≤ 3),
      min_eq_left (zero_le : (0 : ℝ≥0) ≤ 8)]
  pwc := isPiecewiseContinuous_of_continuous _
    (((continuous_const.mul continuous_id).min
      (continuous_id.add continuous_const)).min continuous_const)
  leftCont := isLeftContinuous_of_continuous _
    (((continuous_const.mul continuous_id).min
      (continuous_id.add continuous_const)).min continuous_const)

/-- `rlDep t = min (min (4t) (t+3)) 8`. -/
theorem rlDep_apply (t : ℝ≥0) : rlDep t = min (min (4 * t) (t + 3)) 8 := rfl

/-- `rlDep 0 = 0`. -/
theorem rlDep_zero : rlDep 0 = 0 := rlDep.zero

/-- `rlDep 1 = 4` (the banked height at the kink). -/
theorem rlDep_one : rlDep 1 = 4 := by
  rw [rlDep_apply, show (4 : ℝ≥0) * 1 = 4 from by norm_num,
    show (1 : ℝ≥0) + 3 = 4 from by norm_num, min_self,
    min_eq_left (by norm_num : (4 : ℝ≥0) ≤ 8)]

/-- `rlDep 4 = 7` (the under-served interior endpoint). -/
theorem rlDep_four : rlDep 4 = 7 := by
  rw [rlDep_apply, show (4 : ℝ≥0) * 4 = 16 from by norm_num,
    show (4 : ℝ≥0) + 3 = 7 from by norm_num,
    min_eq_right (by norm_num : (7 : ℝ≥0) ≤ 16),
    min_eq_left (by norm_num : (7 : ℝ≥0) ≤ 8)]

/-- `rlDep t = 8` past `t = 5` (the cap, where the backlog clears). -/
theorem rlDep_eq_eight_of_ge {t : ℝ≥0} (h : 5 ≤ t) : rlDep t = 8 := by
  rw [rlDep_apply, min_eq_right (le_min ?_ ?_)]
  · calc (8 : ℝ≥0) ≤ 4 * 5 := by norm_num
      _ ≤ 4 * t := by gcongr
  · rw [show (8 : ℝ≥0) = 5 + 3 from by norm_num]; gcongr

/-- `rlDep t < 8` before `t = 5` (the backlogged region). -/
theorem rlDep_lt_eight_of_lt {t : ℝ≥0} (h : t < 5) : rlDep t < 8 := by
  rw [rlDep_apply]
  calc min (min (4 * t) (t + 3)) 8 ≤ t + 3 :=
        (min_le_left _ _).trans (min_le_right _ _)
    _ < 8 := by rw [show (8 : ℝ≥0) = 5 + 3 from by norm_num]; gcongr

/-- Causality: `rlDep ≤ 8·1_{>0}`. -/
theorem rlDep_le_burst : rlDep ≤ burstCurve 8 := by
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [rlDep_zero]; exact zero_le
  · rw [burstCurve_apply, burstFun_apply_of_ne 8 ht, rlDep_apply]
    exact min_le_right _ _

/-- Before `t = 5` the backlog has not cleared, so the start anchors at the
origin. -/
theorem rl_start_lt_five {t : ℝ≥0} (ht : t < 5) :
    start ⇑(burstCurve 8) ⇑rlDep t = 0 := by
  refine le_antisymm (csSup_le ⟨0, ⟨zero_le, ?_⟩⟩ fun u hu => ?_) zero_le
  · show burstCurve 8 0 = rlDep 0
    rw [burstCurve_apply, burstFun_zero_eq, rlDep_zero]
  · by_contra hu0
    rw [not_le] at hu0
    obtain ⟨hut, hAD⟩ := hu
    rw [burstCurve_apply, burstFun_apply_of_ne 8 (ne_of_gt hu0)] at hAD
    exact absurd hAD.symm (ne_of_lt (rlDep_lt_eight_of_lt (lt_of_le_of_lt hut ht)))

/-- At and past `t = 5` the pair has emptied, so the start anchors at `t`. -/
theorem rl_start_ge_five {t : ℝ≥0} (ht : 5 ≤ t) :
    start ⇑(burstCurve 8) ⇑rlDep t = t := by
  refine start_eq_of_apply_eq ?_
  show burstCurve 8 t = rlDep t
  rw [burstCurve_apply,
    burstFun_apply_of_ne 8 (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 5) ht)),
    rlDep_eq_eight_of_ge ht]

/-- The pair is weakly strictly served at `β_{2,1}`: its backlog starts at the
origin, where the anchored bound `D 0 + β t = 2(t−1)₊ ≤ D t` holds on `[0, 5]`. -/
theorem rl_mem_weaklyStrictServiceRel :
    weaklyStrictServiceRel (rateLatency 2 1) (burstCurve 8) rlDep := by
  refine ⟨rlDep_le_burst, fun t => ?_⟩
  rcases lt_or_ge t 5 with ht | ht
  · rw [rl_start_lt_five ht]
    show rlDep 0 + rateLatency 2 1 (t - 0) ≤ rlDep t
    rw [rlDep_zero, zero_add, tsub_zero, rlDep_apply]
    show (2 : ℝ≥0) * (t - 1) ≤ min (min (4 * t) (t + 3)) 8
    refine le_min (le_min ?_ ?_) ?_
    · exact mul_le_mul' (by norm_num : (2 : ℝ≥0) ≤ 4) tsub_le_self
    · rw [mul_tsub, mul_one, tsub_le_iff_right, two_mul,
        show t + 3 + 2 = t + 5 from by ring]
      exact add_le_add le_rfl ht.le
    · rw [mul_tsub, mul_one, tsub_le_iff_right]
      exact le_trans (by rw [two_mul]; exact add_le_add ht.le ht.le)
        (by norm_num : (5 : ℝ≥0) + 5 ≤ 8 + 2)
  · rw [rl_start_ge_five ht, tsub_self]
    have h0 : rateLatency (2 : ℝ≥0) 1 0 = 0 := by simp [rateLatency]
    rw [h0, add_zero]

/-- The pair is not strictly served at `β_{2,1}`: the interior window `(1, 4]`
demands `D 1 + β 3 = 8 > 7 = D 4`. -/
theorem rl_not_mem_strictServiceRel :
    ¬ strictServiceRel (rateLatency 2 1) (burstCurve 8) rlDep := by
  rintro ⟨-, hstrict⟩
  have hbl : IsBacklogged (⇑(burstCurve 8)) (⇑rlDep) (Set.Ioc 1 4) := by
    intro u hu
    show rlDep u < burstCurve 8 u
    rw [burstCurve_apply, burstFun_apply_of_ne 8 (ne_of_gt (lt_trans one_pos hu.1))]
    exact rlDep_lt_eight_of_lt (lt_of_le_of_lt hu.2 (by norm_num))
  have h := hstrict 1 4 (by norm_num) hbl
  rw [rlDep_one, rlDep_four, show (4 : ℝ≥0) - 1 = 3 from tsub_eq_of_eq_add (by norm_num),
    show rateLatency (2 : ℝ≥0) 1 3 = 4 from by
      simp only [rateLatency]
      rw [show (3 : ℝ≥0) - 1 = 2 from tsub_eq_of_eq_add (by norm_num)]; norm_num] at h
  exact absurd h (by norm_num)

/-- **strict ⊊ wstrict for the rate-latency curve `β_{2,1}`** — the practical
superadditive curve the strict-subadditivity witness cannot reach. -/
theorem strictServiceRel_lt_weaklyStrictServiceRel_rateLatency :
    strictServiceRel (rateLatency 2 1) < weaklyStrictServiceRel (rateLatency 2 1) := by
  refine lt_of_le_of_ne (strictServiceRel_le_weaklyStrictServiceRel _)
    fun heq => rl_not_mem_strictServiceRel ?_
  rw [heq]; exact rl_mem_weaklyStrictServiceRel

/-- **wstrict ⊊ mp for every rate-latency curve `β_{R,T}` (`R, T > 0`)** — the
delayed-start instance of case A (`t₀ = T`, `s = T + 1`: `β_{R,T}` vanishes
below `T` and is positive past it). -/
theorem weaklyStrictServiceRel_lt_minimalServiceRel_rateLatency {R T : ℝ≥0}
    (hR : 0 < R) (hT : 0 < T) :
    weaklyStrictServiceRel (rateLatency R T)
      < minimalServiceRel (liftEReal (rateLatency R T)) :=
  weaklyStrictServiceRel_lt_minimalServiceRel (t₀ := T) (s := T + 1)
    (rateLatency_mono R T)
    (fun u hu => by show R * (u - T) = 0; rw [tsub_eq_zero_of_le hu.le, mul_zero])
    hT le_self_add
    (by show 0 < R * (T + 1 - T); rw [add_tsub_cancel_left, mul_one]; exact hR)

/-! Both upper inclusions are strict for rate-latency: the witness pair lies in
`S_wstrict(β_{2,1}) ∖ S_strict(β_{2,1})` (a front-loaded server grants each `t`
its full increment from the backlog start yet under-serves an interior window),
and `S_wstrict(β_{R,T}) ⊊ S_mp(β_{R,T})` for all `R, T > 0`. So for the practical
rate-latency curve `S_strict ⊊ S_wstrict ⊊ S_mp`. -/
example :
    weaklyStrictServiceRel (rateLatency 2 1) (burstCurve 8) rlDep ∧
      ¬ strictServiceRel (rateLatency 2 1) (burstCurve 8) rlDep :=
  ⟨rl_mem_weaklyStrictServiceRel, rl_not_mem_strictServiceRel⟩
example {R T : ℝ≥0} (hR : 0 < R) (hT : 0 < T) :
    weaklyStrictServiceRel (rateLatency R T)
      < minimalServiceRel (liftEReal (rateLatency R T)) :=
  weaklyStrictServiceRel_lt_minimalServiceRel_rateLatency hR hT

end DeepWiki
