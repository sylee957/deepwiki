import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import DeepWiki.NetworkCalculus.ServersResidualPriority

/-! # Static priority is not preserved by composition
Like GPS, preemptive static priority does not survive tandem composition.
Two flows, the high-priority flow `0` and the low-priority flow `1`, cross
two servers. At the first server flow `0` is backlogged from time `1`
onward, so flow `1` is frozen there (`spM1` stalls at its time-`1` value);
flow `0` passes the second server instantly, so the second server never
freezes flow `1`, which drains the reservoir it built at the second server
before time `1`. End to end, flow `0` is backlogged on `[3/2, 2]` yet
flow `1` keeps departing — the priority freeze fails for the composite.

The trajectory is laid out at the level of the `IsStaticPriority`
predicate: `spArr` (arrivals), `spMid` (first-server departures =
second-server arrivals), `spDep` (final departures). Each server is
`IsStaticPriority` (`isStaticPriority_server1`, `isStaticPriority_server2`)
but the composite is not (`not_isStaticPriority_composite`), refuting the
general "composition preserves static priority" statement
(`not_forall_isStaticPriority_comp`). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Finset

/-! ## The two-flow / two-server trajectory (all continuous) -/

/-- High-priority arrival: silent until time `1`, then rate `4`. -/
noncomputable def spA0 : ℝ≥0 → ℝ≥0 := fun t => 4 * (t - 1)

/-- Low-priority arrival: rate `1` throughout (always queued at server 1). -/
noncomputable def spA1 : ℝ≥0 → ℝ≥0 := fun t => t

/-- High-priority first-server departure: rate `2`, backlogged from `1`. -/
noncomputable def spM0 : ℝ≥0 → ℝ≥0 := fun t => 2 * (t - 1)

/-- Low-priority first-server departure: served at rate `1` until time `1`,
then frozen (flow `0` takes priority once backlogged). -/
noncomputable def spM1 : ℝ≥0 → ℝ≥0 := fun t => min t 1

/-- Low-priority final departure: drains the second-server reservoir at
rate `1/2`, reaching `spM1`'s ceiling `1` at time `2`. -/
noncomputable def spD1 : ℝ≥0 → ℝ≥0 := fun t => min (t / 2) 1

/-- Arrival family `(A₀, A₁)`. -/
noncomputable def spArr : Fin 2 → ℝ≥0 → ℝ≥0 := ![spA0, spA1]

/-- First-server departure family `(M₀, M₁)` — the second server's arrivals. -/
noncomputable def spMid : Fin 2 → ℝ≥0 → ℝ≥0 := ![spM0, spM1]

/-- Final departure family `(D₀, D₁)`; the high-priority flow passes the
second server untouched, so `D₀ = M₀`. -/
noncomputable def spDep : Fin 2 → ℝ≥0 → ℝ≥0 := ![spM0, spD1]

/-- The higher-priority aggregate of flow `1` is just flow `0`:
`∑_{j<1} f j = f 0` over `Fin 2`. -/
theorem sum_lt_one (f : Fin 2 → ℝ≥0) :
    (∑ j ∈ univ.filter (fun j => j < (1 : Fin 2)), f j) = f 0 := by
  rw [Finset.sum_filter, Fin.sum_univ_two, if_pos (by decide), if_neg (by decide),
    add_zero]

/-- No flow has higher priority than flow `0`: `∑_{j<0} f j = 0`. -/
theorem sum_lt_zero (f : Fin 2 → ℝ≥0) :
    (∑ j ∈ univ.filter (fun j => j < (0 : Fin 2)), f j) = 0 := by
  rw [Finset.sum_filter, Fin.sum_univ_two, if_neg (by decide), if_neg (by decide),
    add_zero]

/-- `spM0 s < spA0 s` forces `1 < s`: the high-priority flow is backlogged
at the first server only past time `1`. -/
theorem one_lt_of_spM0_lt_spA0 {s : ℝ≥0} (h : spM0 s < spA0 s) : 1 < s := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s - 1) with h0 | h0
  · exfalso; rw [spM0, spA0, ← h0] at h; simp at h
  · exact tsub_pos_iff_lt.mp h0

/-! ## Each server is static priority, the composite is not -/

/-- **The first server is static priority**: flow `0` is never preempted,
and while flow `0` is backlogged (which forces `s > 1`) flow `1` is frozen
at its ceiling `1`. -/
theorem isStaticPriority_server1 : IsStaticPriority spArr spMid := by
  intro i s t hst hbl
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exfalso
    have h := hbl s ⟨le_rfl, hst⟩
    rw [sum_lt_zero, sum_lt_zero] at h
    exact absurd h (lt_irrefl 0)
  · have h := hbl s ⟨le_rfl, hst⟩
    rw [sum_lt_one, sum_lt_one] at h
    have hs : (1 : ℝ≥0) < s :=
      one_lt_of_spM0_lt_spA0 (by simpa only [spArr, spMid, Matrix.cons_val_zero] using h)
    show spM1 t = spM1 s
    rw [spM1, spM1, min_eq_right hs.le, min_eq_right (hs.le.trans hst)]

/-- **The second server is static priority**: flow `0` passes it untouched
(`spDep 0 = spMid 0`), so the higher-priority aggregate is never strictly
backlogged and the freeze condition is vacuous. -/
theorem isStaticPriority_server2 : IsStaticPriority spMid spDep := by
  intro i s t hst hbl
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exfalso
    have h := hbl s ⟨le_rfl, hst⟩
    rw [sum_lt_zero, sum_lt_zero] at h
    exact absurd h (lt_irrefl 0)
  · exfalso
    have h := hbl s ⟨le_rfl, hst⟩
    rw [sum_lt_one, sum_lt_one] at h
    -- `spDep 0 = spMid 0 = spM0`, so the strict inequality is `spM0 s < spM0 s`
    simp only [spMid, spDep, Matrix.cons_val_zero] at h
    exact absurd h (lt_irrefl _)

/-- **The composite is not static priority**: on `[3/2, 2]` the
high-priority flow is backlogged end to end, yet the low-priority flow
keeps departing (`spD1` rises from `3/4` to `1`), so the priority freeze
fails. -/
theorem not_isStaticPriority_composite : ¬ IsStaticPriority spArr spDep := by
  intro h
  have hbl : ∀ u ∈ Set.Icc (3 / 2 : ℝ≥0) 2,
      (∑ j ∈ univ.filter (fun j => j < (1 : Fin 2)), spDep j u)
        < ∑ j ∈ univ.filter (fun j => j < (1 : Fin 2)), spArr j u := by
    intro u hu
    rw [sum_lt_one, sum_lt_one]
    show spM0 u < spA0 u
    rw [spM0, spA0]
    have hu1 : (1 : ℝ≥0) < u := lt_of_lt_of_le (by norm_num) hu.1
    exact mul_lt_mul_of_pos_right (by norm_num : (2 : ℝ≥0) < 4) (tsub_pos_of_lt hu1)
  have hfreeze := h 1 (3 / 2) 2
    (by rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]; norm_num) hbl
  -- `spDep 1 = spD1`; `spD1 2 = 1 ≠ 3/4 = spD1 (3/2)`
  simp only [spDep, Matrix.cons_val_one, Matrix.cons_val_zero, spD1] at hfreeze
  rw [show (2 : ℝ≥0) / 2 = 1 from by norm_num, min_self,
    show (3 / 2 : ℝ≥0) / 2 = 3 / 4 from by norm_num] at hfreeze
  -- `hfreeze : 1 = min (3/4) 1`, but `min (3/4) 1 ≤ 3/4 < 1`
  have hle : (1 : ℝ≥0) ≤ 3 / 4 := hfreeze.le.trans (min_le_left _ _)
  exact absurd hle (not_le.mpr ((div_lt_one (by norm_num)).mpr (by norm_num)))

/-- **Static priority is not preserved by composition**: there are families
`A`, `M`, `D` with `M` a static-priority image of `A` and `D` a
static-priority image of `M`, yet `D` not a static-priority image of `A`.
Mirrors the (false) "composition preserves static priority" statement. -/
theorem not_forall_isStaticPriority_comp :
    ¬ ∀ {ι : Type} [Fintype ι] [LinearOrder ι] (A M D : ι → ℝ≥0 → ℝ≥0),
        IsStaticPriority A M → IsStaticPriority M D → IsStaticPriority A D :=
  fun hforall => not_isStaticPriority_composite
    (hforall spArr spMid spDep isStaticPriority_server1 isStaticPriority_server2)

/-! ## Book restatement (static priority in tandem is not static priority)
The book deduces this from the tandem of pure-delay servers failing to be a
strict service curve; the explicit two-flow run above gives the same
conclusion directly at the trajectory level — each server preempts the
low-priority flow `1` exactly when the high-priority flow `0` is backlogged,
but the composite backlogs flow `0` while flow `1` is still draining its
second-server reservoir. -/
example :
    IsStaticPriority spArr spMid
      ∧ IsStaticPriority spMid spDep
      ∧ ¬ IsStaticPriority spArr spDep :=
  ⟨isStaticPriority_server1, isStaticPriority_server2,
    not_isStaticPriority_composite⟩

end DeepWiki
