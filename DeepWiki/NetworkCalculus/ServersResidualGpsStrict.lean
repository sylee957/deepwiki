import Mathlib.Tactic.FinCases
import DeepWiki.NetworkCalculus.ServersResidualGps

/-! # GPS is not preserved by composition
Two GPS servers in tandem need **not** form a GPS server. Concretely, with
equal weights `φ₁ = φ₂`, a fast first stage (`β⁽¹⁾ = λ₄`) followed by a
faster second stage (`β⁽²⁾ = λ₅`), and a bursty tagged flow
(`α = γ_{1,10}`, half its burst served instantly), the second stage drains
the tagged flow's reservoir at rate `3` while the cross-flow — never
backlogged at the second stage — leaves at its arrival rate `2`. End to
end both flows are backlogged on the same window, yet the tagged flow is
served strictly faster, so the composite violates the equal-share
guarantee.

The construction is laid out at the level of the cumulative families:
`gpsTandemArr` (arrivals), `gpsTandemMid` (first-stage departures =
second-stage arrivals) and `gpsTandemDep` (final departures), with the
tagged flow `0` carrying a `0⁺` burst in its first-stage output (the
mechanism that seeds the second-stage reservoir). The first stage
(`isGps_server1`) and the second (`isGps_server2`) are each `IsGps`, but
the composite is not (`not_isGps_gpsTandemComposite`), refuting the general
"composition preserves GPS" statement (`not_forall_isGps_comp`). The same
failure afflicts static priority (deduced from the tandem of pure delays
not being a strict service curve, the strict-tandem counterexamples);
blind multiplexing and FIFO are the policies that *do* survive
composition. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## The two-flow / two-stage trajectory
All six cumulatives are piecewise affine. The tagged flow is `0`; the
cross-flow `1` arrives only from time `1`. Rates are chosen so the first
stage shares `2`/`2` while the second serves the tagged flow at `3` and
the cross-flow at `2`. -/

/-- Tagged-flow arrival: burst `10` at `0⁺`, then rate `2`. -/
noncomputable def gtA0 : ℝ≥0 → ℝ≥0 := fun t => if t = 0 then 0 else 10 + 2 * t

/-- Cross-flow arrival: silent until time `1`, then rate `4`. -/
noncomputable def gtA1 : ℝ≥0 → ℝ≥0 := fun t => 4 * (t - 1)

/-- Tagged-flow first-stage departure: `0⁺` burst of `5` (half the burst
served at once), then rate `2`. -/
noncomputable def gtM0 : ℝ≥0 → ℝ≥0 := fun t => if t = 0 then 0 else 5 + 2 * t

/-- Cross-flow first-stage departure: silent until `1`, then rate `2` —
the equal first-stage share. Doubles as the cross-flow's final departure
(never backlogged at the second stage). -/
noncomputable def gtM1 : ℝ≥0 → ℝ≥0 := fun t => 2 * (t - 1)

/-- Tagged-flow final departure: rate `3` while the reservoir lasts
(`t ≤ 5`), then rate `2`. -/
noncomputable def gtD0 : ℝ≥0 → ℝ≥0 := fun t => if t ≤ 5 then 3 * t else 2 * t + 5

/-- Equal GPS weights `φ₀ = φ₁ = 1`. -/
noncomputable def gpsTandemφ : Fin 2 → ℝ≥0 := fun _ => 1

/-- Arrival family `(A₀, A₁)`. -/
noncomputable def gpsTandemArr : Fin 2 → ℝ≥0 → ℝ≥0 := ![gtA0, gtA1]

/-- First-stage departure family `(M₀, M₁)` — the second stage's arrivals. -/
noncomputable def gpsTandemMid : Fin 2 → ℝ≥0 → ℝ≥0 := ![gtM0, gtM1]

/-- Final departure family `(D₀, D₁)`; the cross-flow passes the second
stage untouched, so `D₁ = M₁`. -/
noncomputable def gpsTandemDep : Fin 2 → ℝ≥0 → ℝ≥0 := ![gtD0, gtM1]

/-! ## Increment-domination engine
`IsGps` (at equal weights) is a statement about increment domination on
backlogged periods. The additive converter turns the easy `+`-form
`h t + f s ≤ f t + h s` into the truncated-subtraction increment bound. -/

/-- Increment domination from the additive form: for nondecreasing `f`, `h`
with `h t + f s ≤ f t + h s` the `h`-increment is dominated by the
`f`-increment, `h t - h s ≤ f t - f s`. -/
theorem tsub_incr_le_of_add_le {f h : ℝ≥0 → ℝ≥0} {s t : ℝ≥0}
    (hf : f s ≤ f t) (hh : h s ≤ h t) (hadd : h t + f s ≤ f t + h s) :
    h t - h s ≤ f t - f s := by
  rw [← NNReal.coe_le_coe, NNReal.coe_sub hh, NNReal.coe_sub hf]
  have h2 := NNReal.coe_le_coe.mpr hadd
  push_cast at h2
  linarith

/-- The rate-`2` ramp `M₁`/`D₁` never gains more than rate `2`:
`gtM1 t ≤ gtM1 s + 2·(t−s)`. -/
theorem gtM1_upper {s t : ℝ≥0} (hst : s ≤ t) :
    gtM1 t ≤ gtM1 s + 2 * (t - s) := by
  unfold gtM1
  rcases le_total 1 s with hs | hs
  · have ht : (1 : ℝ≥0) ≤ t := hs.trans hst
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hs, NNReal.coe_sub ht, NNReal.coe_sub hst]
    linarith
  · rw [tsub_eq_zero_of_le hs, mul_zero, zero_add]
    rcases le_total 1 t with ht | ht
    · rw [← NNReal.coe_le_coe]
      push_cast [NNReal.coe_sub ht, NNReal.coe_sub hst]
      have hs1 : (s : ℝ) ≤ 1 := by exact_mod_cast hs
      linarith
    · rw [tsub_eq_zero_of_le ht, mul_zero]
      exact zero_le'

/-- On the cross-flow's active window (`1 ≤ s`) the rate-`2` ramp gains
*exactly* rate `2`: `gtM1 s + 2·(t−s) ≤ gtM1 t`. -/
theorem gtM1_lower_of_one_le {s t : ℝ≥0} (hs : 1 ≤ s) (hst : s ≤ t) :
    gtM1 s + 2 * (t - s) ≤ gtM1 t := by
  have ht : (1 : ℝ≥0) ≤ t := hs.trans hst
  unfold gtM1
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub hs, NNReal.coe_sub ht, NNReal.coe_sub hst]
  linarith

/-- The tagged-flow first-stage output gains at least rate `2` (the `0⁺`
burst only helps): `gtM0 s + 2·(t−s) ≤ gtM0 t`. -/
theorem gtM0_lower {s t : ℝ≥0} (hst : s ≤ t) :
    gtM0 s + 2 * (t - s) ≤ gtM0 t := by
  unfold gtM0
  rcases eq_or_ne s 0 with rfl | hs
  · rw [if_pos rfl, tsub_zero, zero_add]
    rcases eq_or_ne t 0 with rfl | ht
    · rw [if_pos rfl, mul_zero]
    · rw [if_neg ht]; exact self_le_add_left _ _
  · have ht : t ≠ 0 := fun h => hs (le_antisymm (h ▸ hst) zero_le')
    rw [if_neg hs, if_neg ht, ← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hst]
    linarith

/-- On the active window (`0 < s`) the tagged-flow first-stage output gains
*exactly* rate `2`: `gtM0 t ≤ gtM0 s + 2·(t−s)`. -/
theorem gtM0_upper_of_pos {s t : ℝ≥0} (hs : 0 < s) (hst : s ≤ t) :
    gtM0 t ≤ gtM0 s + 2 * (t - s) := by
  have hs0 : s ≠ 0 := hs.ne'
  have ht0 : t ≠ 0 := (hs.trans_le hst).ne'
  unfold gtM0
  rw [if_neg hs0, if_neg ht0, ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub hst]
  linarith

/-- The tagged-flow final output gains at least rate `2` everywhere (rate
`3` then `2`): `gtD0 s + 2·(t−s) ≤ gtD0 t`. -/
theorem gtD0_lower {s t : ℝ≥0} (hst : s ≤ t) :
    gtD0 s + 2 * (t - s) ≤ gtD0 t := by
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  unfold gtD0
  rcases le_or_gt s 5 with hs5 | hs5 <;> rcases le_or_gt t 5 with ht5 | ht5
  · rw [if_pos hs5, if_pos ht5, ← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hst]; linarith
  · rw [if_pos hs5, if_neg (not_le.mpr ht5), ← NNReal.coe_le_coe]
    have hs5' : (s : ℝ) ≤ 5 := by exact_mod_cast hs5
    push_cast [NNReal.coe_sub hst]; linarith
  · exact absurd (hst.trans ht5) (not_le.mpr hs5)
  · rw [if_neg (not_le.mpr hs5), if_neg (not_le.mpr ht5), ← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hst]; linarith

/-- `gtM1` is nondecreasing. -/
theorem gtM1_mono : Monotone gtM1 := fun _ _ h =>
  mul_le_mul_right (tsub_le_tsub_right h 1) 2

/-- `gtM0` is nondecreasing (from its rate-`2` lower bound). -/
theorem gtM0_mono : Monotone gtM0 := fun _ _ h =>
  le_trans (self_le_add_right _ _) (gtM0_lower h)

/-- `gtD0` is nondecreasing (from its rate-`2` lower bound). -/
theorem gtD0_mono : Monotone gtD0 := fun _ _ h =>
  le_trans (self_le_add_right _ _) (gtD0_lower h)

/-- First-stage equal-share additive form: `gtM1 t + gtM0 s ≤ gtM0 t + gtM1 s`
(the tagged flow's first-stage output never falls behind the cross-flow's). -/
theorem addform_M {s t : ℝ≥0} (hst : s ≤ t) :
    gtM1 t + gtM0 s ≤ gtM0 t + gtM1 s :=
  calc gtM1 t + gtM0 s
      ≤ (gtM1 s + 2 * (t - s)) + gtM0 s := add_le_add (gtM1_upper hst) le_rfl
    _ = gtM1 s + (gtM0 s + 2 * (t - s)) := by ring
    _ ≤ gtM1 s + gtM0 t := add_le_add le_rfl (gtM0_lower hst)
    _ = gtM0 t + gtM1 s := add_comm _ _

/-- Second-stage additive form: `gtM1 t + gtD0 s ≤ gtD0 t + gtM1 s` (the
tagged flow's final output never falls behind the cross-flow's). -/
theorem addform_D {s t : ℝ≥0} (hst : s ≤ t) :
    gtM1 t + gtD0 s ≤ gtD0 t + gtM1 s :=
  calc gtM1 t + gtD0 s
      ≤ (gtM1 s + 2 * (t - s)) + gtD0 s := add_le_add (gtM1_upper hst) le_rfl
    _ = gtM1 s + (gtD0 s + 2 * (t - s)) := by ring
    _ ≤ gtM1 s + gtD0 t := add_le_add le_rfl (gtD0_lower hst)
    _ = gtD0 t + gtM1 s := add_comm _ _

/-- First-stage equal-share additive form on the active window (`1 ≤ s`):
`gtM0 t + gtM1 s ≤ gtM1 t + gtM0 s` — there both first-stage outputs gain
exactly rate `2`, so the shares match. -/
theorem eqform_M {s t : ℝ≥0} (hs : 1 ≤ s) (hst : s ≤ t) :
    gtM0 t + gtM1 s ≤ gtM1 t + gtM0 s :=
  calc gtM0 t + gtM1 s
      ≤ (gtM0 s + 2 * (t - s)) + gtM1 s :=
        add_le_add (gtM0_upper_of_pos (lt_of_lt_of_le one_pos hs) hst) le_rfl
    _ = gtM0 s + (gtM1 s + 2 * (t - s)) := by ring
    _ ≤ gtM0 s + gtM1 t := add_le_add le_rfl (gtM1_lower_of_one_le hs hst)
    _ = gtM1 t + gtM0 s := add_comm _ _

/-- A cross-flow backlogged period sits in its active window: if
`gtA1`/`gtM1` is backlogged on `(s, t]` with `s < t`, then `1 ≤ s`
(below `1` both cumulatives vanish, so there is no backlog). -/
theorem one_le_of_backlog_M1 {s t : ℝ≥0} (hlt : s < t)
    (hbl : IsBacklogged gtA1 gtM1 (Set.Ioc s t)) : 1 ≤ s := by
  by_contra h
  rw [not_le] at h
  have hsu : s < min t 1 := lt_min hlt h
  have hut : min t 1 ≤ t := min_le_left _ _
  have hu1 : min t 1 ≤ 1 := min_le_right _ _
  have hcontra := hbl _ ⟨hsu, hut⟩
  unfold gtM1 gtA1 at hcontra
  rw [tsub_eq_zero_of_le hu1, mul_zero, mul_zero] at hcontra
  exact absurd hcontra (lt_irrefl 0)

/-- The cross-flow is never backlogged at the second stage (`D₁ = M₁`), so
`IsBacklogged gtM1 gtM1 (s, t]` forces `s = t`. -/
theorem eq_of_backlog_M1_M1 {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged gtM1 gtM1 (Set.Ioc s t)) : s = t := by
  by_contra hne
  exact absurd (hbl t ⟨lt_of_le_of_ne hst hne, le_rfl⟩) (lt_irrefl _)

/-! ## The two stages are GPS, the composite is not -/

/-- **The first stage is a GPS server**: at equal weights the tagged flow's
first-stage output never falls behind the cross-flow's, and on the
cross-flow's backlogged periods the two outputs match. -/
theorem isGps_server1 : IsGps gpsTandemφ gpsTandemArr gpsTandemMid := by
  intro i j s t hst hbl
  fin_cases i <;> fin_cases j <;>
    simp only [gpsTandemArr, gpsTandemMid, gpsTandemφ, one_mul] at hbl ⊢
  · exact le_rfl
  · exact tsub_incr_le_of_add_le (gtM0_mono hst) (gtM1_mono hst) (addform_M hst)
  · rcases eq_or_lt_of_le hst with rfl | hlt
    · simp
    · exact tsub_incr_le_of_add_le (gtM1_mono hst) (gtM0_mono hst)
        (eqform_M (one_le_of_backlog_M1 hlt hbl) hst)
  · exact le_rfl

/-- **The second stage is a GPS server**: the tagged flow's final output
never falls behind the cross-flow's, and the cross-flow is never
backlogged at the second stage (so its `(1, 0)` obligation is vacuous). -/
theorem isGps_server2 : IsGps gpsTandemφ gpsTandemMid gpsTandemDep := by
  intro i j s t hst hbl
  fin_cases i <;> fin_cases j <;>
    simp only [gpsTandemMid, gpsTandemDep, gpsTandemφ, one_mul] at hbl ⊢
  · exact le_rfl
  · exact tsub_incr_le_of_add_le (gtD0_mono hst) (gtM1_mono hst) (addform_D hst)
  · rcases eq_or_lt_of_le hst with rfl | hlt
    · simp
    · exact absurd (eq_of_backlog_M1_M1 hst hbl) (ne_of_lt hlt)
  · exact le_rfl

/-- **The composite is not GPS**: on `(1, 2]` the cross-flow is backlogged
end to end, yet the tagged flow is served `3` against the cross-flow's `2`,
breaking the equal-share inequality for the cross-flow. -/
theorem not_isGps_gpsTandemComposite :
    ¬ IsGps gpsTandemφ gpsTandemArr gpsTandemDep := by
  intro h
  have hbl : IsBacklogged (gpsTandemArr 1) (gpsTandemDep 1) (Set.Ioc 1 2) := by
    intro u hu
    have hpos : (0 : ℝ≥0) < u - 1 := tsub_pos_of_lt hu.1
    show gtM1 u < gtA1 u
    unfold gtM1 gtA1
    exact mul_lt_mul_of_pos_right (by norm_num : (2 : ℝ≥0) < 4) hpos
  have key := h 1 0 1 2 (by norm_num) hbl
  simp only [gpsTandemφ, gpsTandemDep, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul] at key
  have e1 : gtD0 2 = 6 := by
    unfold gtD0; rw [if_pos (by norm_num : (2 : ℝ≥0) ≤ 5)]; norm_num
  have e2 : gtD0 1 = 3 := by
    unfold gtD0; rw [if_pos (by norm_num : (1 : ℝ≥0) ≤ 5)]; norm_num
  have e3 : gtM1 2 = 2 := by
    unfold gtM1
    rw [show (2 : ℝ≥0) - 1 = 1 from by
      rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num : (1 : ℝ≥0) ≤ 2)]; norm_num]
    norm_num
  have e4 : gtM1 1 = 0 := by unfold gtM1; simp
  rw [e1, e2, e3, e4,
    show ((6 : ℝ≥0) - 3 : ℝ≥0) = 3 from by
      rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num : (3 : ℝ≥0) ≤ 6)]; norm_num,
    tsub_zero] at key
  norm_num at key

/-- **GPS is not preserved by composition**: there are weights `φ` and
families `A`, `M`, `D` with `M` a GPS image of `A` and `D` a GPS image of
`M`, yet `D` not a GPS image of `A`. Mirrors the (false) "composition
preserves GPS" statement verbatim. -/
theorem not_forall_isGps_comp :
    ¬ ∀ {ι : Type} (φ : ι → ℝ≥0) (A M D : ι → ℝ≥0 → ℝ≥0),
        IsGps φ A M → IsGps φ M D → IsGps φ A D :=
  fun hforall => not_isGps_gpsTandemComposite
    (hforall gpsTandemφ gpsTandemArr gpsTandemMid gpsTandemDep
      isGps_server1 isGps_server2)

/-! ## Book restatement (GPS in tandem is not GPS)
With `β⁽¹⁾ = λ₄`, `β⁽²⁾ = λ₅`, `α₁ = α₂ = γ_{1,10}` and `φ₁ = φ₂`, the
first server shares its service equally while the second — where the
cross-flow, arriving at rate `2`, can never be backlogged — serves the
tagged flow at `3` and the cross-flow at `2`. The two servers are GPS yet
their composition is not: the cross-flow is backlogged end to end but
receives strictly less than its equal share. -/
example :
    IsGps gpsTandemφ gpsTandemArr gpsTandemMid
      ∧ IsGps gpsTandemφ gpsTandemMid gpsTandemDep
      ∧ ¬ IsGps gpsTandemφ gpsTandemArr gpsTandemDep :=
  ⟨isGps_server1, isGps_server2, not_isGps_gpsTandemComposite⟩

end DeepWiki
