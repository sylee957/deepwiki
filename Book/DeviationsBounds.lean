import Book.Deviations
import Book.ArrivalCurves

/-! # Delay and backlog bounds
For a served pair with maximal arrival curve `α` and min-plus service `β`
(both `ℝ≥0∞`-valued), the delay is bounded by the horizontal deviation
`hDev α β` and the backlog by the vertical deviation `vDev α β`. The service
hypothesis is the raw `ℝ≥0∞` convolution inequality `A ∗ β ≤ D`; the bridge
from the `EReal`-valued `IsMinimalServiceCurve` server stack is in
`DeviationsBoundsServer`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

namespace Deviation

/-- The `ℝ≥0∞` reading of an `ℝ≥0`-valued cumulative function. -/
abbrev liftENN (A : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0∞ := fun u => (A u : ℝ≥0∞)

/-- `liftENN` transports monotonicity. -/
theorem monotone_liftENN {A : ℝ≥0 → ℝ≥0} (hmono : Monotone A) :
    Monotone (liftENN A) :=
  fun _ _ hab => ENNReal.coe_le_coe.mpr (hmono hab)

/-- `liftENN` preserves and reflects maximal arrival curves:
`IsMaximalArrivalBound (liftENN A) (liftENN α) ↔ IsMaximalArrivalBound A α`
(the increment bounds match through the exact embedding). -/
theorem isMaximalArrivalBound_liftENN_iff {A α : ℝ≥0 → ℝ≥0} :
    IsMaximalArrivalBound (liftENN A) (liftENN α)
      ↔ IsMaximalArrivalBound A α := by
  rw [isMaximalArrivalBound_iff_increment, isMaximalArrivalBound_iff_increment]
  exact ⟨fun h t d => by exact_mod_cast h t d,
    fun h t d => by exact_mod_cast h t d⟩

/-- `liftENN` reflects minimal arrival curves unconditionally: the `ℝ≥0∞`
supremum is never junk, so it dominates each increment, which suffices on
`ℝ≥0`. -/
theorem isMinimalArrivalBound_of_liftENN {A α : ℝ≥0 → ℝ≥0}
    (h : IsMinimalArrivalBound (liftENN A) (liftENN α)) :
    IsMinimalArrivalBound A α :=
  isMinimalArrivalBound_of_increment A α fun t d => by
    exact_mod_cast
      ((add_le_maxConv (liftENN A) (liftENN α) rfl).trans (h (t + d)) :
        liftENN A t + liftENN α d ≤ liftENN A (t + d))

/-- `liftENN` preserves minimal arrival curves of non-decreasing curves:
monotonicity bounds the `ℝ≥0` supremum, making its increment bounds
available to the `ℝ≥0∞` reading. -/
theorem isMinimalArrivalBound_liftENN_of_monotone {A α : ℝ≥0 → ℝ≥0}
    (hA : Monotone A) (hα : Monotone α)
    (h : IsMinimalArrivalBound A α) :
    IsMinimalArrivalBound (liftENN A) (liftENN α) := by
  have hincr := (isMinimalArrivalBound_iff_increment_of_monotone A α hA hα).mp h
  intro t
  refine maxConv_le fun u s hus => ?_
  exact hus ▸
    (by exact_mod_cast hincr u s :
      liftENN A u + liftENN α s ≤ liftENN A (u + s))

/-- **Backlog bound.** If `A` has maximal arrival curve `α` and `D` dominates
the convolution `A ∗ β`, then the backlog at every `t` is bounded by the
vertical deviation: `b(A, D)(t) ≤ vDev α β`. -/
theorem coe_backlogAt_le_vDev {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞}
    (harr : IsMaximalArrivalBound (liftENN A) α)
    (hserv : ∀ t, minConv (liftENN A) β t ≤ (D t : ℝ≥0∞)) (t : ℝ≥0) :
    (backlogAt A D t : ℝ≥0∞) ≤ vDev α β := by
  rw [backlogAt_eq, ENNReal.coe_sub]
  refine le_trans (tsub_le_tsub_left (hserv t) _) ?_
  simp only [minConv]
  rw [ENNReal.sub_iInf]
  refine iSup_le ?_
  rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
  have hinc : (A t : ℝ≥0∞) ≤ (A u : ℝ≥0∞) + α s :=
    (harr t).trans (minConv_le_add (liftENN A) α hus)
  calc (A t : ℝ≥0∞) - (liftENN A u + β s)
      = ((A t : ℝ≥0∞) - liftENN A u) - β s := tsub_add_eq_tsub_tsub _ _ _
    _ ≤ α s - β s := tsub_le_tsub_right (tsub_le_iff_left.mpr hinc) _
    _ ≤ vDev α β := vDevAt_le_vDev α β s

/-- **Backlog bound**: `b(A, D) ≤ vDev α β`. -/
theorem backlog_le_vDev {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞}
    (harr : IsMaximalArrivalBound (liftENN A) α)
    (hserv : ∀ t, minConv (liftENN A) β t ≤ (D t : ℝ≥0∞)) :
    backlog A D ≤ vDev α β :=
  iSup_le fun t => coe_backlogAt_le_vDev harr hserv t

/-- `backlog` is the vertical deviation of the `ℝ≥0∞` readings. -/
theorem backlog_eq_vDev_liftENN (A D : ℝ≥0 → ℝ≥0) :
    backlog A D = vDev (liftENN A) (liftENN D) := by
  rw [backlog_eq_iSup, vDev_eq_iSup]
  exact iSup_congr fun t => ENNReal.coe_sub

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

/-- **Delay bound.** If nondecreasing `A` has maximal arrival curve `α` and
`D` dominates the convolution `A ∗ β` for nondecreasing `β`, then the delay
at every `t` is bounded by the horizontal deviation: `d(A, D)(t) ≤ hDev α β`. -/
theorem delayAt_le_hDev {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞}
    (hA : Monotone A) (hβ : Monotone β)
    (harr : IsMaximalArrivalBound (liftENN A) α)
    (hserv : ∀ t, minConv (liftENN A) β t ≤ (D t : ℝ≥0∞)) (t : ℝ≥0) :
    delayAt A D t ≤ (hDev α β : ℝ≥0∞) := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨d, hd1, hd2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hcon
  have hadm : (A t : ℝ≥0∞) ≤ (D (t + d) : ℝ≥0∞) := by
    refine le_trans (le_minConv fun u s hus => ?_) (hserv (t + d))
    by_cases hut : u ≤ t
    · have hs : s = (t - u) + d := by
        have h1 : u + s = u + ((t - u) + d) := by
          rw [hus, ← add_assoc, add_tsub_cancel_of_le hut]
        exact add_left_cancel h1
      have hα : (A t : ℝ≥0∞) ≤ (A u : ℝ≥0∞) + α (t - u) :=
        (harr t).trans
          (minConv_le_add (liftENN A) α (add_tsub_cancel_of_le hut))
      have hβd : α (t - u) ≤ β ((t - u) + d) := by
        have hlt : (hDevAt α β (t - u) : ℝ≥0∞) < (d : ℝ≥0∞) :=
          lt_of_le_of_lt
            (le_iSup (fun x => (hDevAt α β x : ℝ≥0∞)) (t - u)) hd1
        obtain ⟨⟨e, he⟩, hed⟩ := iInf_lt_iff.mp hlt
        have hed' : (e : ℝ≥0∞) < (d : ℝ≥0∞) := hed
        have hede : e ≤ d := by exact_mod_cast hed'.le
        exact le_trans he (hβ (add_le_add le_rfl hede))
      calc (A t : ℝ≥0∞)
          ≤ (A u : ℝ≥0∞) + α (t - u) := hα
        _ ≤ (A u : ℝ≥0∞) + β ((t - u) + d) := add_le_add le_rfl hβd
        _ = liftENN A u + β s := by rw [hs]
    · calc (A t : ℝ≥0∞)
          ≤ (A u : ℝ≥0∞) := by exact_mod_cast hA (not_le.mp hut).le
        _ ≤ liftENN A u + β s := le_self_add
  have hle : delayAt A D t ≤ (d : ℝ≥0∞) :=
    iInf_le _ (⟨d, by exact_mod_cast hadm⟩ : {d : ℝ≥0 // A t ≤ D (t + d)})
  exact absurd (lt_of_le_of_lt hle hd2) (lt_irrefl _)

/-- **Delay bound, sup form**: `d(A, D) ≤ hDev α β`. -/
theorem delay_le_hDev {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞}
    (hA : Monotone A) (hβ : Monotone β)
    (harr : IsMaximalArrivalBound (liftENN A) α)
    (hserv : ∀ t, minConv (liftENN A) β t ≤ (D t : ℝ≥0∞)) :
    delay A D ≤ (hDev α β : ℝ≥0∞) :=
  iSup_le fun t => delayAt_le_hDev hA hβ harr hserv t

end Deviation

end DeepWiki
