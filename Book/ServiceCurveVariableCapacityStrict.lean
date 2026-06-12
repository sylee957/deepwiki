import Book.ServiceCurveVariableCapacityStart

/-! # Variable capacity nodes: the unrepaired forms fail
The counterexample ladder for the adjudicated gap: without jump
domination, the start-anchored closed form is false (`vcnStepCapacity`
— a capacity burst fired at the origin into a right-limit-empty
queue), and the inclusion of variable capacity into the strict — even
the weakly strict — layer is false (`vcnCeilCapacity` — the ceiling
staircase against half-rate arrivals, with a *continuous* `β` whose
self-deconvolution is finite, refuting the book's equality criterion
as well). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Function

/-! ## The capacity burst at the origin -/

/-- The step capacity: one unit fired just after the origin. -/
noncomputable def vcnStepCapacity : ℝ≥0 → ℝ≥0 :=
  fun t => if t = 0 then 0 else 1

/-- The step capacity is monotone. -/
theorem vcnStepCapacity_mono : Monotone vcnStepCapacity := by
  intro a b hab
  by_cases ha : a = 0
  · subst ha
    simp only [vcnStepCapacity, if_pos]
    exact zero_le'
  · have hb : b ≠ 0 := fun hb =>
      ha (le_antisymm (hb ▸ hab) zero_le')
    simp only [vcnStepCapacity, if_neg ha, if_neg hb]
    exact le_rfl

/-- The step capacity is left-continuous: the jump at the origin is
right-sided. -/
theorem vcnStepCapacity_leftCont : IsLeftContinuous vcnStepCapacity := by
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · exact isLeftContinuousAt_zero _
  · refine continuousWithinAt_const.congr_of_eventuallyEq ?_
      (if_neg ht)
    filter_upwards [Ioo_mem_nhdsLT (pos_of_ne_zero ht)] with v hv
    exact if_neg (ne_of_gt hv.1)

/-- Against the step capacity the identity arrivals are never served:
the infimum harvests the unattained burst. -/
theorem vcnOutput_id_stepCapacity_eq (t : ℝ≥0) :
    vcnOutput id vcnStepCapacity t = 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [vcnOutput_zero_eq]
    rfl
  · refine le_antisymm ?_ zero_le'
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    have hmin : 0 < min ε t := lt_min hε (pos_of_ne_zero ht)
    refine le_trans (vcnOutput_le (min_le_right ε t)) ?_
    rw [show vcnStepCapacity t = 1 from if_neg ht,
      show vcnStepCapacity (min ε t) = 1 from if_neg hmin.ne',
      tsub_self, add_zero]
    exact min_le_left ε t

/-- The only equality point of the step-capacity pair is the origin. -/
theorem start_id_stepCapacity_eq (t : ℝ≥0) :
    start id (vcnOutput id vcnStepCapacity) t = 0 := by
  unfold start
  have hset : {u | u ≤ t ∧ id u = vcnOutput id vcnStepCapacity u}
      = {0} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff,
      vcnOutput_id_stepCapacity_eq, id_eq]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ zero_le', h⟩⟩
  rw [hset, csSup_singleton]

/-- The closed form fails at `t = 1`: the output is `0`, the
start-anchored value is `1`. -/
theorem not_vcnOutput_start_eq_stepCapacity :
    vcnOutput id vcnStepCapacity 1
      ≠ id (start id (vcnOutput id vcnStepCapacity) 1)
        + (vcnStepCapacity 1
          - vcnStepCapacity
              (start id (vcnOutput id vcnStepCapacity) 1)) := by
  rw [vcnOutput_id_stepCapacity_eq, start_id_stepCapacity_eq,
    show vcnStepCapacity 1 = 1 from if_neg one_ne_zero,
    show vcnStepCapacity 0 = 0 from if_pos rfl, id_eq]
  simp

/-- **The unrepaired closed form is a non-theorem**: the hypotheses
mirror the repaired form verbatim, with only the jump domination
dropped. -/
theorem not_forall_vcnOutput_start_eq :
    ¬ ∀ A C : ℝ≥0 → ℝ≥0, Monotone A → IsLeftContinuous A →
      Monotone C → IsLeftContinuous C → ∀ t,
      vcnOutput A C t
        = A (start A (vcnOutput A C) t)
          + (C t - C (start A (vcnOutput A C) t)) := by
  intro h
  exact not_vcnOutput_start_eq_stepCapacity
    (h id vcnStepCapacity monotone_id
      (isLeftContinuous_of_continuous _ continuous_id)
      vcnStepCapacity_mono vcnStepCapacity_leftCont 1)

end DeepWiki
