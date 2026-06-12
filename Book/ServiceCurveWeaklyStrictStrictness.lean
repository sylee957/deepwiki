import Book.ServiceCurveWeaklyStrict
import Book.RealCurves

/-! # Weakly strict is strictly weaker than strict
The middle inclusion of the hierarchy is strict: a server may grant
each `t` its full increment from the start of its backlogged period
while under-serving interior windows. The witness serves a `4/3`
burst at rate `2`, then rate `2/3` — the start-anchored bound holds
against `λ₁`, but the window `(1/2, 3/4]` receives `1/6 < 1/4`. -/

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

end DeepWiki
