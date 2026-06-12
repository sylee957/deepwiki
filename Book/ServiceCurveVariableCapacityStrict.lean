import Book.ServiceCurveVariableCapacityStart
import Book.RealCurvesRegularity

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
theorem variableCapacityOutput_id_stepCapacity_eq (t : ℝ≥0) :
    variableCapacityOutput id vcnStepCapacity t = 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [variableCapacityOutput_zero_eq]
    rfl
  · refine le_antisymm ?_ zero_le'
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    have hmin : 0 < min ε t := lt_min hε (pos_of_ne_zero ht)
    refine le_trans (variableCapacityOutput_le_add (min_le_right ε t)) ?_
    rw [show vcnStepCapacity t = 1 from if_neg ht,
      show vcnStepCapacity (min ε t) = 1 from if_neg hmin.ne',
      tsub_self, add_zero]
    exact min_le_left ε t

/-- The only equality point of the step-capacity pair is the origin. -/
theorem start_id_stepCapacity_eq (t : ℝ≥0) :
    start id (variableCapacityOutput id vcnStepCapacity) t = 0 := by
  unfold start
  have hset : {u | u ≤ t ∧ id u = variableCapacityOutput id vcnStepCapacity u}
      = {0} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff,
      variableCapacityOutput_id_stepCapacity_eq, id_eq]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ zero_le', h⟩⟩
  rw [hset, csSup_singleton]

/-- The closed form fails at `t = 1`: the output is `0`, the
start-anchored value is `1`. -/
theorem not_variableCapacityOutput_start_eq_stepCapacity :
    variableCapacityOutput id vcnStepCapacity 1
      ≠ id (start id (variableCapacityOutput id vcnStepCapacity) 1)
        + (vcnStepCapacity 1
          - vcnStepCapacity
              (start id (variableCapacityOutput id vcnStepCapacity) 1)) := by
  rw [variableCapacityOutput_id_stepCapacity_eq, start_id_stepCapacity_eq,
    show vcnStepCapacity 1 = 1 from if_neg one_ne_zero,
    show vcnStepCapacity 0 = 0 from if_pos rfl, id_eq]
  simp

/-- **The unrepaired closed form is a non-theorem**: the hypotheses
mirror the repaired form verbatim, with only the jump domination
dropped. -/
theorem not_forall_variableCapacityOutput_start_eq :
    ¬ ∀ A C : ℝ≥0 → ℝ≥0, Monotone A → IsLeftContinuous A →
      Monotone C → IsLeftContinuous C → ∀ t,
      variableCapacityOutput A C t
        = A (start A (variableCapacityOutput A C) t)
          + (C t - C (start A (variableCapacityOutput A C) t)) := by
  intro h
  exact not_variableCapacityOutput_start_eq_stepCapacity
    (h id vcnStepCapacity monotone_id
      (isLeftContinuous_of_continuous _ continuous_id)
      vcnStepCapacity_mono vcnStepCapacity_leftCont 1)

/-! ## The ceiling capacity against half-rate arrivals -/

/-- The ceiling capacity: a full unit at the start of every cycle. -/
noncomputable def vcnCeilCapacity : ℝ≥0 → ℝ≥0 := fun t => (⌈t⌉₊ : ℝ≥0)

/-- The ceiling capacity is the unit staircase of the catalog. -/
theorem vcnCeilCapacity_eq_staircaseFun :
    vcnCeilCapacity = staircaseFun 1 1 0 := by
  funext t
  show ((⌈t⌉₊ : ℕ) : ℝ≥0) = 1 * (⌈((t : ℝ) - 0) / 1⌉₊ : ℝ≥0)
  rw [one_mul, sub_zero, div_one]
  congr 1

/-- The ceiling capacity is monotone. -/
theorem vcnCeilCapacity_mono : Monotone vcnCeilCapacity := by
  rw [vcnCeilCapacity_eq_staircaseFun]
  exact staircaseFun_mono 1 1 0

/-- The ceiling capacity is left-continuous. -/
theorem vcnCeilCapacity_leftCont : IsLeftContinuous vcnCeilCapacity := by
  rw [vcnCeilCapacity_eq_staircaseFun]
  exact staircaseFun_leftCont 1 1 0

/-- The closed output value: against the ceiling capacity the
half-rate arrivals receive one half-unit per completed cycle. -/
theorem variableCapacityOutput_half_ceil_eq {t : ℝ≥0} {k : ℕ} (hk : ⌈t⌉₊ = k + 1) :
    variableCapacityOutput (· / 2) vcnCeilCapacity t = (k : ℝ≥0) / 2 := by
  have hkt : (k : ℝ≥0) < t := Nat.lt_ceil.mp (hk ▸ k.lt_succ_self)
  refine le_antisymm ?_ (le_variableCapacityOutput fun s hs => ?_)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hsk : (k : ℝ≥0) < min ((k : ℝ≥0) + ε) t :=
      lt_min (lt_add_of_pos_right _ hε) hkt
    have hsle : min ((k : ℝ≥0) + ε) t ≤ t := min_le_right _ _
    refine le_trans (variableCapacityOutput_le_add hsle) ?_
    have hceil : ⌈min ((k : ℝ≥0) + ε) t⌉₊ = k + 1 := by
      refine le_antisymm (le_trans (Nat.ceil_mono hsle) hk.le) ?_
      exact Nat.lt_ceil.mpr hsk
    show min ((k : ℝ≥0) + ε) t / 2
        + (vcnCeilCapacity t - vcnCeilCapacity (min ((k : ℝ≥0) + ε) t))
      ≤ (k : ℝ≥0) / 2 + ε
    simp only [vcnCeilCapacity, hceil, hk]
    rw [tsub_self, add_zero]
    have hstep : min ((k : ℝ≥0) + ε) t / 2 ≤ ((k : ℝ≥0) + ε) / 2 := by
      gcongr
      exact min_le_left _ _
    refine le_trans hstep ?_
    rw [add_div]
    refine add_le_add le_rfl ?_
    rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    exact le_mul_of_one_le_right zero_le' (by norm_num)
  · show (k : ℝ≥0) / 2 ≤ s / 2 + (vcnCeilCapacity t - vcnCeilCapacity s)
    have hj2 : ⌈s⌉₊ ≤ k + 1 := hk ▸ Nat.ceil_mono hs
    simp only [vcnCeilCapacity, hk]
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub
      (show ((⌈s⌉₊ : ℕ) : ℝ≥0) ≤ (k : ℝ≥0) + 1 from by
        exact_mod_cast hj2)]
    have hj1 : ((⌈s⌉₊ : ℕ) : ℝ) < (s : ℝ) + 1 := by
      exact_mod_cast (Nat.ceil_lt_add_one zero_le' :
        (⌈s⌉₊ : ℝ≥0) < s + 1)
    have hj2R : ((⌈s⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
      exact_mod_cast hj2
    linarith

/-- The witness pair is backlogged on every positive window. -/
theorem isBacklogged_half_ceil (t : ℝ≥0) :
    IsBacklogged (· / 2) (variableCapacityOutput (· / 2) vcnCeilCapacity)
      (Set.Ioc 0 t) := by
  intro u hu
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ⌈u⌉₊ = k + 1 :=
    ⟨⌈u⌉₊ - 1, (Nat.succ_pred_eq_of_pos
      (Nat.ceil_pos.mpr hu.1)).symm⟩
  rw [variableCapacityOutput_half_ceil_eq hk]
  have hku : (k : ℝ≥0) < u := Nat.lt_ceil.mp (hk ▸ k.lt_succ_self)
  show (k : ℝ≥0) / 2 < u / 2
  rw [← NNReal.coe_lt_coe]
  push_cast
  have hkuR : (k : ℝ) < (u : ℝ) := by exact_mod_cast hku
  linarith

/-- The ceiling capacity dominates the unit rate-latency curve. -/
theorem vcnCeilCapacity_dominates :
    ∀ s t : ℝ≥0, s ≤ t →
      rateLatency 1 1 (t - s) ≤ vcnCeilCapacity t - vcnCeilCapacity s := by
  intro s t hst
  show (1 : ℝ≥0) * ((t - s) - 1) ≤ _
  rw [one_mul]
  rcases le_total (t - s) 1 with h1 | h1
  · rw [tsub_eq_zero_of_le h1]
    exact zero_le'
  · have hcle : ⌈s⌉₊ ≤ ⌈t⌉₊ := Nat.ceil_mono hst
    simp only [vcnCeilCapacity]
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub
      (Nat.cast_le.mpr hcle : ((⌈s⌉₊ : ℕ) : ℝ≥0) ≤ ((⌈t⌉₊ : ℕ) : ℝ≥0)),
      NNReal.coe_sub h1, NNReal.coe_sub hst]
    have h2 : (t : ℝ) ≤ ((⌈t⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_ceil t : (t : ℝ≥0) ≤ (⌈t⌉₊ : ℝ≥0))
    have h3 : ((⌈s⌉₊ : ℕ) : ℝ) < (s : ℝ) + 1 := by
      exact_mod_cast (Nat.ceil_lt_add_one zero_le' :
        (⌈s⌉₊ : ℝ≥0) < s + 1)
    linarith

/-- The half-rate arrival curve. -/
noncomputable def vcnWitnessArrival : Curve :=
  ⟨(· / 2), fun a b hab => by show a / 2 ≤ b / 2; gcongr,
    by show (0 : ℝ≥0) / 2 = 0; rw [zero_div],
    isPiecewiseContinuous_of_continuous _ (continuous_id.div_const 2),
    isLeftContinuous_of_continuous _ (continuous_id.div_const 2)⟩

/-- The ceiling capacity as a curve. -/
noncomputable def vcnWitnessCapacity : Curve :=
  ⟨vcnCeilCapacity, vcnCeilCapacity_mono,
    by show vcnCeilCapacity 0 = 0; simp [vcnCeilCapacity],
    by rw [vcnCeilCapacity_eq_staircaseFun]; exact staircaseFun_pwc 1 1 0,
    vcnCeilCapacity_leftCont⟩

/-- The witness departure: the variable-capacity output itself. -/
noncomputable def vcnWitnessDeparture : Curve :=
  ⟨variableCapacityOutput (· / 2) vcnCeilCapacity,
    variableCapacityOutput_mono (fun a b hab => by show a / 2 ≤ b / 2; gcongr) vcnCeilCapacity_mono,
    by
      show variableCapacityOutput (· / 2) vcnCeilCapacity 0 = 0
      rw [variableCapacityOutput_zero_eq]
      show (0 : ℝ≥0) / 2 = 0
      rw [zero_div],
    isPiecewiseContinuous_of_monotone_of_finite_image
      (variableCapacityOutput_mono (fun a b hab => by show a / 2 ≤ b / 2; gcongr) vcnCeilCapacity_mono)
      (isLeftContinuous_variableCapacityOutput (fun a b hab => by show a / 2 ≤ b / 2; gcongr)
        vcnCeilCapacity_mono vcnCeilCapacity_leftCont)
      (fun T => Set.Finite.subset
        ((Set.finite_Iic ⌈T⌉₊).image (fun n : ℕ => (n : ℝ≥0) / 2))
        (by
          rintro x ⟨u, hu, rfl⟩
          rcases eq_or_ne u 0 with rfl | hu0
          · refine ⟨0, Set.mem_Iic.mpr (Nat.zero_le _), ?_⟩
            rw [variableCapacityOutput_zero_eq]
            show ((0 : ℕ) : ℝ≥0) / 2 = (0 : ℝ≥0) / 2
            norm_num
          · obtain ⟨k, hk⟩ : ∃ k : ℕ, ⌈u⌉₊ = k + 1 :=
              ⟨⌈u⌉₊ - 1, (Nat.succ_pred_eq_of_pos
                (Nat.ceil_pos.mpr (pos_of_ne_zero hu0))).symm⟩
            refine ⟨k, Set.mem_Iic.mpr ?_, ?_⟩
            · have : k < ⌈u⌉₊ := hk ▸ k.lt_succ_self
              exact le_trans (Nat.le_of_lt this) (Nat.ceil_mono hu.2)
            · exact (variableCapacityOutput_half_ceil_eq hk).symm)),
    isLeftContinuous_variableCapacityOutput (fun a b hab => by show a / 2 ≤ b / 2; gcongr)
      vcnCeilCapacity_mono vcnCeilCapacity_leftCont⟩

/-- The witness pair is a variable-capacity node for the unit
rate-latency curve. -/
theorem vcnWitness_mem_variableCapacityRel :
    variableCapacityRel (rateLatency 1 1)
      vcnWitnessArrival vcnWitnessDeparture :=
  ⟨vcnWitnessCapacity, fun _ => rfl, vcnCeilCapacity_dominates⟩

/-- `vcnWitnessDeparture 0 = 0`. -/
theorem vcnWitnessDeparture_zero_eq : vcnWitnessDeparture 0 = 0 := by
  show variableCapacityOutput (· / 2) vcnCeilCapacity 0 = 0
  rw [variableCapacityOutput_zero_eq]
  show (0 : ℝ≥0) / 2 = 0
  rw [zero_div]

/-- The witness departure per completed cycle, at the `Curve` level. -/
theorem vcnWitnessDeparture_apply {t : ℝ≥0} {k : ℕ}
    (hk : ⌈t⌉₊ = k + 1) :
    vcnWitnessDeparture t = (k : ℝ≥0) / 2 :=
  variableCapacityOutput_half_ceil_eq hk

/-- `⌈5/2⌉₊ = 3`. -/
theorem ceil_five_halves : (⌈(5 / 2 : ℝ≥0)⌉₊ : ℕ) = 3 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  refine ⟨by norm_num, ?_⟩
  rw [show ((3 : ℕ) : ℝ≥0) = 3 by norm_num,
    div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
  norm_num

/-- The witness escapes the strict layer: on `(0, 5/2]` the increment
falls short. -/
theorem vcnWitness_not_mem_strictServiceRel :
    ¬ strictServiceRel (rateLatency 1 1)
      vcnWitnessArrival vcnWitnessDeparture := by
  rintro ⟨-, hstrict⟩
  have h := hstrict 0 (5 / 2) (by norm_num)
    (isBacklogged_half_ceil (5 / 2))
  rw [show vcnWitnessDeparture (5 / 2 : ℝ≥0) = 1 from by
      rw [vcnWitnessDeparture_apply (k := 2) ceil_five_halves]
      norm_num,
    vcnWitnessDeparture_zero_eq] at h
  rw [show rateLatency (1 : ℝ≥0) 1 ((5 / 2 : ℝ≥0) - 0) = 3 / 2 from by
      show (1 : ℝ≥0) * (((5 / 2 : ℝ≥0) - 0) - 1) = 3 / 2
      rw [one_mul, tsub_zero, tsub_eq_of_eq_add (by norm_num :
        (5 / 2 : ℝ≥0) = 3 / 2 + 1)]] at h
  rw [zero_add] at h
  have hcontra : ¬ ((3 / 2 : ℝ≥0) ≤ 1) := by
    rw [not_le, lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    norm_num
  exact hcontra h

/-- The only equality point of the witness pair is the origin. -/
theorem start_half_ceil_eq (t : ℝ≥0) :
    start (· / 2) (variableCapacityOutput (· / 2) vcnCeilCapacity) t = 0 := by
  unfold start
  have hset : {u | u ≤ t
      ∧ u / 2 = variableCapacityOutput (· / 2) vcnCeilCapacity u} = {0} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hut, heq⟩
      by_contra hu0
      have hbl := isBacklogged_half_ceil t u
        ⟨pos_of_ne_zero hu0, hut⟩
      rw [← heq] at hbl
      exact lt_irrefl _ hbl
    · rintro rfl
      refine ⟨zero_le', ?_⟩
      rw [variableCapacityOutput_zero_eq]
  rw [hset, csSup_singleton]

/-- The witness escapes even the weakly strict layer: its start is the
origin, and the start-anchored increment falls short on `(0, 5/2]`. -/
theorem vcnWitness_not_mem_weaklyStrictServiceRel :
    ¬ weaklyStrictServiceRel (rateLatency 1 1)
      vcnWitnessArrival vcnWitnessDeparture := by
  rintro ⟨-, hws⟩
  have h := hws (5 / 2)
  rw [show start ⇑vcnWitnessArrival ⇑vcnWitnessDeparture (5 / 2) = 0
      from start_half_ceil_eq (5 / 2)] at h
  rw [show vcnWitnessDeparture (5 / 2 : ℝ≥0) = 1 from by
      rw [vcnWitnessDeparture_apply (k := 2) ceil_five_halves]
      norm_num,
    vcnWitnessDeparture_zero_eq] at h
  rw [show rateLatency (1 : ℝ≥0) 1 ((5 / 2 : ℝ≥0) - 0) = 3 / 2 from by
      show (1 : ℝ≥0) * (((5 / 2 : ℝ≥0) - 0) - 1) = 3 / 2
      rw [one_mul, tsub_zero, tsub_eq_of_eq_add (by norm_num :
        (5 / 2 : ℝ≥0) = 3 / 2 + 1)]] at h
  rw [zero_add] at h
  have hcontra : ¬ ((3 / 2 : ℝ≥0) ≤ 1) := by
    rw [not_le, lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    norm_num
  exact hcontra h

/-- Instance level: the variable-capacity relation is not contained in
the strict one. -/
theorem not_variableCapacityRel_le_strictServiceRel_rateLatency :
    ¬ (variableCapacityRel (rateLatency 1 1)
      ≤ strictServiceRel (rateLatency 1 1)) := fun h =>
  vcnWitness_not_mem_strictServiceRel
    (h _ _ vcnWitness_mem_variableCapacityRel)

/-- Instance level: nor in the weakly strict one. -/
theorem not_variableCapacityRel_le_weaklyStrictServiceRel_rateLatency :
    ¬ (variableCapacityRel (rateLatency 1 1)
      ≤ weaklyStrictServiceRel (rateLatency 1 1)) := fun h =>
  vcnWitness_not_mem_weaklyStrictServiceRel
    (h _ _ vcnWitness_mem_variableCapacityRel)

/-- **The unrepaired bottom inclusion is a non-theorem**: without jump
domination, variable capacity does not refine strict service — the
witness `β` is continuous with finite self-deconvolution, so the
book's equality criterion for the two layers is refuted as well. -/
theorem not_forall_variableCapacityRel_le_strictServiceRel :
    ¬ ∀ beta : ℝ≥0 → ℝ≥0,
      variableCapacityRel beta ≤ strictServiceRel beta := fun h =>
  not_variableCapacityRel_le_strictServiceRel_rateLatency (h _)

/-- **Variable capacity escapes even the weakly strict layer**: the
start-anchored form of the inclusion is a non-theorem too. -/
theorem not_forall_variableCapacityRel_le_weaklyStrictServiceRel :
    ¬ ∀ beta : ℝ≥0 → ℝ≥0,
      variableCapacityRel beta ≤ weaklyStrictServiceRel beta := fun h =>
  not_variableCapacityRel_le_weaklyStrictServiceRel_rateLatency (h _)

/-- The ceiling witness is driven by no jump-dominated capacity: a
jump-dominated witness would make it a strict server. -/
theorem vcnWitness_not_mem_variableCapacityJumpRel :
    ¬ variableCapacityJumpRel (rateLatency 1 1)
      vcnWitnessArrival vcnWitnessDeparture := fun hp =>
  vcnWitness_not_mem_strictServiceRel
    (variableCapacityJumpRel_le_strictServiceRel _ _ _ hp)

/-- Jump domination is a genuine restriction: the jump-dominated
relation sits strictly below the plain one. -/
theorem variableCapacityJumpRel_lt_variableCapacityRel_rateLatency :
    variableCapacityJumpRel (rateLatency 1 1)
      < variableCapacityRel (rateLatency 1 1) :=
  lt_of_le_not_ge (variableCapacityJumpRel_le_variableCapacityRel _)
    (fun h => vcnWitness_not_mem_variableCapacityJumpRel
      (h _ _ vcnWitness_mem_variableCapacityRel))

/-- The book-literal closed-form universal also fails: the witnesses
lie in the book's exact cumulative class, null at origin and
piecewise continuous included. -/
theorem not_forall_variableCapacityOutput_start_eq_curve :
    ¬ ∀ A C : ℝ≥0 → ℝ≥0, Monotone A → IsLeftContinuous A →
      IsPiecewiseContinuous A → A 0 = 0 →
      Monotone C → IsLeftContinuous C →
      IsPiecewiseContinuous C → C 0 = 0 → ∀ t,
      variableCapacityOutput A C t
        = A (start A (variableCapacityOutput A C) t)
          + (C t - C (start A (variableCapacityOutput A C) t)) := by
  intro h
  refine not_variableCapacityOutput_start_eq_stepCapacity
    (h id vcnStepCapacity monotone_id
      (isLeftContinuous_of_continuous _ continuous_id)
      (isPiecewiseContinuous_of_continuous _ continuous_id) rfl
      vcnStepCapacity_mono vcnStepCapacity_leftCont ?_ (if_pos rfl) 1)
  refine isPiecewiseContinuous_of_monotone_of_finite_image
    vcnStepCapacity_mono vcnStepCapacity_leftCont (fun T =>
      Set.Finite.subset (Set.Finite.insert 0 (Set.finite_singleton 1)) ?_)
  rintro x ⟨u, -, rfl⟩
  by_cases hu : u = 0
  · subst hu
    exact Set.mem_insert_iff.mpr (Or.inl (if_pos rfl))
  · exact Set.mem_insert_iff.mpr (Or.inr (if_neg hu))

/-- The hierarchy refutation survives the book's regularity on `beta`
as well: the witness curve is monotone and continuous. -/
theorem not_forall_variableCapacityRel_le_strictServiceRel_of_monotone :
    ¬ ∀ beta : ℝ≥0 → ℝ≥0, Monotone beta → IsLeftContinuous beta →
      variableCapacityRel beta ≤ strictServiceRel beta := by
  intro h
  exact not_variableCapacityRel_le_strictServiceRel_rateLatency
    (h _ (rateLatency_mono 1 1)
      (isLeftContinuous_of_continuous _ (rateLatency_continuous 1 1)))

end DeepWiki
