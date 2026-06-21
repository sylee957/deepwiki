import DeepWiki.ReactiveSystems.TimedSqrt2Bisimulation

/-! # The `√2` Mt-bisimulation, step 2: the non-crossing delay clauses (Ex 12.12(3))
Continues `TimedSqrt2Bisimulation`. The delay clause is matched against the *coupled* relation
`Sq2Rel` (`TimedBisimulationHmlRefined`), whose live regime carries the augmented-clock region
equivalence `RegionEqAll (jointValW d u) (jointValW e u')` — exactly the coupling that lets B's delay
track A's √2-position. Here we discharge the two delay situations that do **not** cross `√2`:

* **past regime** — both `a`-disabled: matched by the formula-clock region time-successor.
* **live, non-crossing** (`d + δ < √2`) — matched by the augmented-clock time-successor
  `jointValW_delay_match`; the open condition `· < √2` is preserved through the region (no boundary
  subtlety), so B lands strictly below `√2` again, staying live.

What remains (later steps) is the **crossing** `d + δ ≥ √2`: the strict case `d + δ > √2` and the
exact case `d + δ = √2`. The latter, when a formula clock simultaneously hits an integer (the
double-coincidence), is the irreducible core — `jointValW` there forces B to exactly `√2`
(`a`-enabled) against an `a`-disabled A, so it needs the looser single-irrational-cut coupling. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

/-- The augmented clock's `√2`-side is a region invariant: region-equivalent augmented joint
valuations agree on whether the process is below `√2`. -/
theorem jointValW_sqrt2_side {D : Type*} {T T' : ℝ≥0} {u u' : Valuation D}
    (h : RegionEqAll (jointValW T u) (jointValW T' u')) : T < sqrt2NN ↔ T' < sqrt2NN := by
  rw [← jointValW_none_lt_two_iff (u := u), ← jointValW_none_lt_two_iff (u := u')]
  have hs := regionEqAll_satisfies h (ClockConstraint.atom none Cmp.lt 2)
  simp only [satisfies, Cmp.holds, Nat.cast_ofNat] at hs
  exact hs

/-- The process crosses `√2` exactly when the augmented clock equals integer `2`. -/
theorem jointValW_none_eq_two_iff {D : Type*} (T : ℝ≥0) (u : Valuation D) :
    jointValW T u none = 2 ↔ T = sqrt2NN := by
  rw [jointValW, jointVal_none]
  constructor
  · intro h
    have hr : (T : ℝ) + (2 - Real.sqrt 2) = 2 := by
      have := congrArg NNReal.toReal h; push_cast [coe_twoSubSqrt2NN] at this; linarith
    rw [← NNReal.coe_inj, coe_sqrt2NN]; linarith
  · rintro rfl
    rw [← NNReal.coe_inj]; push_cast [coe_twoSubSqrt2NN, coe_sqrt2NN]; ring

/-- Region-equivalent augmented joint valuations agree on whether the process is exactly `√2`. -/
theorem jointValW_sqrt2_eq_side {D : Type*} {T T' : ℝ≥0} {u u' : Valuation D}
    (h : RegionEqAll (jointValW T u) (jointValW T' u')) : T = sqrt2NN ↔ T' = sqrt2NN := by
  rw [← jointValW_none_eq_two_iff T u, ← jointValW_none_eq_two_iff T' u']
  have hs := regionEqAll_satisfies h (ClockConstraint.atom none Cmp.eq 2)
  simp only [satisfies, Cmp.holds, Nat.cast_ofNat] at hs
  exact hs

/-- **Delay clause, past regime.** From two `a`-disabled region-equivalent states, a left delay is
matched by a right delay landing again `a`-disabled and region-equivalent. -/
theorem Sq2Rel.delay_past {D : Type*} [Fintype D] {p q : Sq2} {u u' : Valuation D}
    (hpd : aDisabled sqrt2NN p) (hqd : aDisabled sqrt2NN q) (hr : RegionEqAll u u')
    (d : ℝ≥0) (p' : Sq2) (hstep : (sq2TLTS sqrt2NN).delay p d p') :
    ∃ d' q', (sq2TLTS sqrt2NN).delay q d' q' ∧ Sq2Rel p' (u.add d) q' (u'.add d') := by
  rw [sq2_delay] at hstep
  obtain ⟨d', hr'⟩ := regionEqAll_timeSuccessor hr d
  obtain ⟨q', hqstep, hq'd⟩ := hqd.delay_succ d'
  exact ⟨d', q', sq2_delay.mpr hqstep, Or.inl ⟨hpd.delay_pres hstep, hq'd, hr'⟩⟩

/-- **Delay clause, live and non-crossing.** A live left delay that stays strictly below `√2` is
matched by a right delay staying strictly below `√2` (so both remain live), via the augmented-clock
time-successor. -/
theorem Sq2Rel.delay_live_stay {D : Type*} [Fintype D] {d e : ℝ≥0} {u u' : Valuation D}
    (hr : RegionEqAll (jointValW d u) (jointValW e u')) (δ : ℝ≥0) (hstay : d + δ < sqrt2NN) :
    ∃ δ' q', (sq2TLTS sqrt2NN).delay (Sq2.B e) δ' q' ∧
      Sq2Rel (Sq2.A (d + δ)) (u.add δ) q' (u'.add δ') := by
  obtain ⟨δ', hr'⟩ := jointValW_delay_match hr δ
  have he' : e + δ' < sqrt2NN := (jointValW_sqrt2_side hr').mp hstay
  exact ⟨δ', Sq2.B (e + δ'), sq2_delay.mpr Sq2Step.delB,
    Or.inr ⟨d + δ, e + δ', rfl, rfl, hstay, he', hr'⟩⟩

/-- **Delay clause, live and strictly crossing.** A live left delay that lands strictly *above* `√2`
is matched by a right delay also strictly above `√2` — region equivalence forbids B landing exactly
on `√2` when A does not (`jointValW_sqrt2_eq_side`), so both become `a`-disabled (the past regime). -/
theorem Sq2Rel.delay_live_cross_strict {D : Type*} [Fintype D] {d e : ℝ≥0} {u u' : Valuation D}
    (hr : RegionEqAll (jointValW d u) (jointValW e u')) (δ : ℝ≥0) (hcross : sqrt2NN < d + δ) :
    ∃ δ' q', (sq2TLTS sqrt2NN).delay (Sq2.B e) δ' q' ∧
      Sq2Rel (Sq2.A (d + δ)) (u.add δ) q' (u'.add δ') := by
  obtain ⟨δ', hr'⟩ := jointValW_delay_match hr δ
  have hge : sqrt2NN ≤ e + δ' := by
    by_contra hlt
    exact absurd ((jointValW_sqrt2_side hr').mpr (not_le.mp hlt)) (not_lt.mpr (le_of_lt hcross))
  have hne : e + δ' ≠ sqrt2NN := fun heq =>
    absurd ((jointValW_sqrt2_eq_side hr').mpr heq).symm (ne_of_lt hcross)
  have he' : sqrt2NN < e + δ' := lt_of_le_of_ne hge (Ne.symm hne)
  have hregf : RegionEqAll (u.add δ) (u'.add δ') := by
    have hp := RegionEqAll.precomp (Option.some_injective D) hr'
    rwa [jointValW_comp_some, jointValW_comp_some] at hp
  exact ⟨δ', Sq2.B (e + δ'), sq2_delay.mpr Sq2Step.delB,
    Or.inl ⟨le_of_lt hcross, he', hregf⟩⟩

end TLTS

end DeepWiki.ReactiveSystems
