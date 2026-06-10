import Book.Deviations
import Book.ArrivalCurves

/-! # Delay and backlog bounds
For a served pair with maximal arrival curve `α` and min-plus service `β`
(both `ℝ≥0∞`-valued), the delay is bounded by the horizontal deviation
`hDev α β` and the backlog by the vertical deviation `vDev α β`. The service
hypothesis is the raw `ℝ≥0∞` convolution inequality `A ∗ β ≤ D`; bridging it
to the `EReal`-valued `IsMinPlusServiceCurve` server stack (for nonnegative
`β` and `Curve` pairs) is future work. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

namespace Deviation

/-- The `ℝ≥0∞` reading of an `ℝ≥0`-valued cumulative function. -/
abbrev toE (A : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0∞ := fun u => (A u : ℝ≥0∞)

/-- **Backlog bound.** If `A` has maximal arrival curve `α` and `D` dominates
the convolution `A ∗ β`, then the backlog at every `t` is bounded by the
vertical deviation: `b(A, D)(t) ≤ vDev α β`. -/
theorem coe_backlogAt_le_vDev {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞}
    (harr : IsMaximalArrivalCurve (toE A) α)
    (hserv : ∀ t, minConv (toE A) β t ≤ (D t : ℝ≥0∞)) (t : ℝ≥0) :
    (backlogAt A D t : ℝ≥0∞) ≤ vDev α β := by
  rw [backlogAt_eq, ENNReal.coe_sub]
  refine le_trans (tsub_le_tsub_left (hserv t) _) ?_
  rw [show minConv (toE A) β t
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t}, toE A p.1.1 + β p.1.2
    from rfl, ENNReal.sub_iInf]
  refine iSup_le ?_
  rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
  have hinc : (A t : ℝ≥0∞) ≤ (A u : ℝ≥0∞) + α s := by
    have h := (isMaximalArrivalCurve_iff_increment (toE A) α).mp harr u s
    rwa [show u + s = t from hus] at h
  calc (A t : ℝ≥0∞) - (toE A u + β s)
      = ((A t : ℝ≥0∞) - toE A u) - β s := tsub_add_eq_tsub_tsub _ _ _
    _ ≤ α s - β s := tsub_le_tsub_right (tsub_le_iff_left.mpr hinc) _
    _ ≤ vDev α β := le_iSup (fun d => vDevAt α β d) s

/-- **Backlog bound, sup form**: `b(A, D) ≤ vDev α β`, read junk-free in
`ℝ≥0∞` as the supremum of the pointwise backlogs. -/
theorem iSup_backlogAt_le_vDev {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞}
    (harr : IsMaximalArrivalCurve (toE A) α)
    (hserv : ∀ t, minConv (toE A) β t ≤ (D t : ℝ≥0∞)) :
    (⨆ t : ℝ≥0, (backlogAt A D t : ℝ≥0∞)) ≤ vDev α β :=
  iSup_le fun t => coe_backlogAt_le_vDev harr hserv t

/-- **Delay bound.** If nondecreasing `A` has maximal arrival curve `α` and
`D` dominates the convolution `A ∗ β` for nondecreasing `β`, then the delay
at every `t` is bounded by the horizontal deviation: `d(A, D)(t) ≤ hDev α β`. -/
theorem delayAt_le_hDev {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞}
    (hA : Monotone A) (hβ : Monotone β)
    (harr : IsMaximalArrivalCurve (toE A) α)
    (hserv : ∀ t, minConv (toE A) β t ≤ (D t : ℝ≥0∞)) (t : ℝ≥0) :
    delayAt A D t ≤ (hDev α β : ℝ≥0∞) := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨d, hd1, hd2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hcon
  have hadm : (A t : ℝ≥0∞) ≤ (D (t + d) : ℝ≥0∞) := by
    refine le_trans ?_ (hserv (t + d))
    refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = t + d)⟩
    by_cases hut : u ≤ t
    · have hs : s = (t - u) + d := by
        have h1 : u + s = u + ((t - u) + d) := by
          rw [hus, ← add_assoc, add_tsub_cancel_of_le hut]
        exact add_left_cancel h1
      have hα : (A t : ℝ≥0∞) ≤ (A u : ℝ≥0∞) + α (t - u) := by
        have h := (isMaximalArrivalCurve_iff_increment (toE A) α).mp
          harr u (t - u)
        rwa [add_tsub_cancel_of_le hut] at h
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
        _ = toE A u + β s := by rw [hs]
    · calc (A t : ℝ≥0∞)
          ≤ (A u : ℝ≥0∞) := by exact_mod_cast hA (not_le.mp hut).le
        _ ≤ toE A u + β s := le_self_add
  have hle : delayAt A D t ≤ (d : ℝ≥0∞) :=
    iInf_le _ (⟨d, by exact_mod_cast hadm⟩ : {d : ℝ≥0 // A t ≤ D (t + d)})
  exact absurd (lt_of_le_of_lt hle hd2) (lt_irrefl _)

/-- **Delay bound, sup form**: `d(A, D) ≤ hDev α β`. -/
theorem delay_le_hDev {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞}
    (hA : Monotone A) (hβ : Monotone β)
    (harr : IsMaximalArrivalCurve (toE A) α)
    (hserv : ∀ t, minConv (toE A) β t ≤ (D t : ℝ≥0∞)) :
    delay A D ≤ (hDev α β : ℝ≥0∞) :=
  iSup_le fun t => delayAt_le_hDev hA hβ harr hserv t

end Deviation

end DeepWiki
