import DeepWiki.ReactiveSystems.TimedSqrt2BisimulationCross

/-! # The `√2` Mt-bisimulation, step 4b: the asymmetric single-irrational-cut region (Ex 12.12(3))
The dedicated file for the construction that resolves the double-coincidence — the one remaining
delay sub-case (a formula clock on an integer exactly when the process is at `√2`).

**Why the previous couplings fail.** `jointValW` (process compared to `√2` via the integer-shifted
clock `w = p + (2 − √2)`) *conflates* the `√2`-cut with the integer clock cuts, so at the
double-coincidence it rigidly forces B to exactly `√2` (`a`-enabled, against an `a`-disabled A). A
plain symmetric region equivalence has the same defect: it relates *equal* `√2`-positions.

**The fix — an asymmetric coupling on the ordinary integer region.** Couple via
`RegionEqAll (jointVal d u) (jointVal e u')`, where `jointVal` puts the process at `none` with
**ordinary integer cuts** (so `√2 ∈ (1,2)` stays *interior*, with `sqrt2_side_iff_fracPart` giving the
`√2`-side as `fracPart p < fracPart √2`), together with the `a`-regime: A's threshold is *open*
(`d < √2`), B's is *closed* (`e ≤ √2`). Because the process integer-region at `√2` is open, B's
process has wiggle-room; and because the threshold is asymmetric, A-at-`√2` (`a`-disabled) is matched
by B *strictly past* `√2` (`a`-disabled). The single coincidence to handle is a clock hitting integer
`1` exactly at `√2` (reset at `√2 − 1`, the only integer reachable below `√2 < 2`); there B's reset
offset must exceed A's (`s_x > r_x = √2 − 1`), which the cross-ordering of the `jointVal` coupling
carries.

This file establishes the relation `Sq2ARel` on the `jointVal` coupling and its coupling-independent
clauses (guard, reset, both actions, seed). The asymmetric delay clause — matching A's `√2`-crossing
by choosing B's delay inside the integer-region window on the correct `√2`-side (via the
`exists_delay_before/past` placement and the `regionEqAll_add_small` nudge) — is the focused remaining
work. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

/-- The asymmetric `√2` relation: a *past* regime (both `a`-disabled, formula clocks region-equivalent)
and a *live* regime `(A d) ~ (B e)` with the **open/closed** thresholds `d < √2`, `e ≤ √2` and the
ordinary-integer joint-region coupling `RegionEqAll (jointVal d u) (jointVal e u')` (process at `none`
with integer cuts, so `√2` stays interior to `(1,2)`). -/
def Sq2ARel {D : Type*} (p : Sq2) (u : Valuation D) (q : Sq2) (u' : Valuation D) : Prop :=
  (aDisabled sqrt2NN p ∧ aDisabled sqrt2NN q ∧ RegionEqAll u u')
  ∨ (∃ d e : ℝ≥0, p = Sq2.A d ∧ q = Sq2.B e ∧ d < sqrt2NN ∧ e ≤ sqrt2NN ∧
       RegionEqAll (jointVal d u) (jointVal e u'))

/-- Both regimes give region-equivalent formula clocks (the live one via restriction along `some`). -/
theorem Sq2ARel.regionEqAll {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2ARel p u q u') : RegionEqAll u u' := by
  rcases h with ⟨_, _, hr⟩ | ⟨d, e, _, _, _, _, hr⟩
  · exact hr
  · have hu := RegionEqAll.precomp (Option.some_injective D) hr
    rwa [jointVal_comp_some, jointVal_comp_some] at hu

/-- **Guard clause.** Related states satisfy the same formula-clock guards. -/
theorem Sq2ARel.guard {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2ARel p u q u') (g : ClockConstraint D) : satisfies u g ↔ satisfies u' g :=
  regionEqAll_satisfies h.regionEqAll g

/-- **Reset clause.** Resetting the same formula clock on both sides preserves the relation. -/
theorem Sq2ARel.reset {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2ARel p u q u') (x : D) :
    Sq2ARel p (Valuation.reset {x} u) q (Valuation.reset {x} u') := by
  rcases h with ⟨hpd, hqd, hr⟩ | ⟨d, e, hp, hq, hd, he, hr⟩
  · exact Or.inl ⟨hpd, hqd, hr.reset {x}⟩
  · refine Or.inr ⟨d, e, hp, hq, hd, he, ?_⟩
    rw [← jointVal_reset_some, ← jointVal_reset_some]
    exact hr.reset {some x}

/-- **Action clause (forth).** If `p` performs `a`, `q` matches it, landing related (both `End`). -/
theorem Sq2ARel.act_forth {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2ARel p u q u') (α : Sq2Act) (p' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act p α p') :
    ∃ q', (sq2TLTS sqrt2NN).act q α q' ∧ Sq2ARel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨hpd, _, _⟩ | ⟨d, e, hp, hq, hd, he, hr⟩
  · exact absurd hstep (fun hs => hpd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aA _ =>
        refine ⟨Sq2.End, sq2_act.mpr (Sq2Step.aB he), Or.inl ⟨trivial, trivial, ?_⟩⟩
        have hu := RegionEqAll.precomp (Option.some_injective D) hr
        rwa [jointVal_comp_some, jointVal_comp_some] at hu

/-- **Action clause (back).** If `q` performs `a`, `p` matches it, landing related. -/
theorem Sq2ARel.act_back {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2ARel p u q u') (α : Sq2Act) (q' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act q α q') :
    ∃ p', (sq2TLTS sqrt2NN).act p α p' ∧ Sq2ARel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨_, hqd, _⟩ | ⟨d, e, hp, hq, hd, he, hr⟩
  · exact absurd hstep (fun hs => hqd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aB _ =>
        refine ⟨Sq2.End, sq2_act.mpr (Sq2Step.aA hd), Or.inl ⟨trivial, trivial, ?_⟩⟩
        have hu := RegionEqAll.precomp (Option.some_injective D) hr
        rwa [jointVal_comp_some, jointVal_comp_some] at hu

/-- The seed: `(A 0)` and `(B 0)` at the all-zero formula valuation are related (live). -/
theorem sq2ARel_seed {D : Type*} :
    Sq2ARel (Sq2.A 0) (fun _ : D => 0) (Sq2.B 0) (fun _ : D => 0) :=
  Or.inr ⟨0, 0, rfl, rfl, zero_lt_sqrt2NN, le_of_lt zero_lt_sqrt2NN, RegionEqAll.refl _⟩

/-- **Delay clause, past regime.** From two `a`-disabled region-equivalent states, a left delay is
matched by a right delay landing again `a`-disabled and region-equivalent. -/
theorem Sq2ARel.delay_past {D : Type*} [Fintype D] {p q : Sq2} {u u' : Valuation D}
    (hpd : aDisabled sqrt2NN p) (hqd : aDisabled sqrt2NN q) (hr : RegionEqAll u u')
    (d : ℝ≥0) (p' : Sq2) (hstep : (sq2TLTS sqrt2NN).delay p d p') :
    ∃ d' q', (sq2TLTS sqrt2NN).delay q d' q' ∧ Sq2ARel p' (u.add d) q' (u'.add d') := by
  rw [sq2_delay] at hstep
  obtain ⟨d', hr'⟩ := regionEqAll_timeSuccessor hr d
  obtain ⟨q', hqstep, hq'd⟩ := hqd.delay_succ d'
  exact ⟨d', q', sq2_delay.mpr hqstep, Or.inl ⟨hpd.delay_pres hstep, hq'd, hr'⟩⟩

/-- **Delay clause, live and non-crossing into the lower region** (`d + δ ≤ 1`, hence `< √2`). The
integer-region time-successor already keeps B at `≤ 1 < √2` (so B stays live), no `√2`-side window
needed — `√2` is irrelevant below `1`. (The remaining live cases enter the region `(1, √2)`, where the
`√2`-side must be controlled inside the integer-region window — the asymmetric crux.) -/
theorem Sq2ARel.delay_live_lower {D : Type*} [Fintype D] {d e : ℝ≥0} {u u' : Valuation D}
    (hr : RegionEqAll (jointVal d u) (jointVal e u')) (δ : ℝ≥0) (hlow : d + δ ≤ 1) :
    ∃ δ' q', (sq2TLTS sqrt2NN).delay (Sq2.B e) δ' q' ∧
      Sq2ARel (Sq2.A (d + δ)) (u.add δ) q' (u'.add δ') := by
  obtain ⟨δ', hr'⟩ := regionEqAll_timeSuccessor hr δ
  rw [jointVal_add, jointVal_add] at hr'
  have h1lt : (1 : ℝ≥0) < sqrt2NN := by rw [← NNReal.coe_lt_coe]; push_cast; exact one_lt_sqrt2NN
  -- `e + δ' ≤ 1` from the integer-region match on the process clock `none`
  have hle : e + δ' ≤ (1 : ℝ≥0) := by
    have hs := regionEqAll_satisfies hr' (ClockConstraint.atom none Cmp.le 1)
    simp only [satisfies, Cmp.holds, jointVal_none, Nat.cast_one] at hs
    exact hs.mp hlow
  refine ⟨δ', Sq2.B (e + δ'), sq2_delay.mpr Sq2Step.delB,
    Or.inr ⟨d + δ, e + δ', rfl, rfl, lt_of_le_of_lt hlow h1lt, le_of_lt (lt_of_le_of_lt hle h1lt), hr'⟩⟩

/-! ### The delay-invariant "value at the √2-crossing" (the key to the asymmetric region)

Maximum-effort design breakthrough for the `(1,√2)` crux. The reason the integer-region match fails to
control the `√2`-side is that it tracks the cross-ordering of each clock with the *integers*, not with
`√2`. The fix: for a process at `d < √2` and a clock value `v`, the clock's **value at the
`√2`-crossing** is `v + (√2 − d)` (advance everything by `√2 − d` to bring the process to `√2`).

This quantity is **delay-invariant** (`clock_at_sqrt2_delay_invariant`): advancing the process and the
clock together by `δ` leaves it unchanged. So the cross-ordering of every clock with the `√2`-boundary
— in particular *whether a clock hits an integer exactly at `√2`* (`v + (√2 − d) ∈ ℤ`, the
double-coincidence) — is a **static datum that is automatically preserved under delay**. The augmented
single-irrational-cut region is therefore: the standard integer region on the advancing clocks/process,
the `√2`-side, **and** a match on these frozen crossing-values `{v + (√2 − d)}`. The frozen match needs
the open/closed **asymmetry** (A's crossing-value `= m` ↔ B's crossing-value just below `m`), which is
exactly what places B strictly past `√2` at the coincidence. Because the frozen values don't move under
delay, the delay clause only has to drive the standard region + `√2`-side (the existing window/placement
toolkit), with the frozen match carried for free — the structural simplification that makes the
construction tractable. -/

/-- The clock value `v` reaches `v + (√2 − d)` when the process (at `d ≤ √2`) reaches `√2`, and this
"value at the `√2`-crossing" is **delay-invariant**: advancing both the process and the clock by `δ`
(staying `≤ √2`) leaves it unchanged. Hence the cross-ordering of each clock with the `√2`-boundary —
and the double-coincidence `v + (√2 − d) ∈ ℤ` — is a static, auto-preserved datum. -/
theorem clock_at_sqrt2_delay_invariant {d δ v : ℝ≥0} (h : d + δ ≤ sqrt2NN) :
    (v + δ) + (sqrt2NN - (d + δ)) = v + (sqrt2NN - d) := by
  have hd : d ≤ sqrt2NN := le_trans le_self_add h
  rw [← NNReal.coe_inj]
  push_cast [NNReal.coe_sub h, NNReal.coe_sub hd]
  ring

end TLTS

end DeepWiki.ReactiveSystems
