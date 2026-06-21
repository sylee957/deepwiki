import DeepWiki.ReactiveSystems.TimedBisimulationHmlRefined

/-! # The `√2` Mt-bisimulation, step 1: the relation and its non-crossing clauses (Ex 12.12(3))
This is the start of the dedicated construction closing Ex 12.12(3): `(A,0)` and `(B,0)` of the `√2`
TLTS satisfy the same *full* `Mt` formulae. The device is an `IsMtBisimulation` (then `.mtSat`).

**The relation** `Sq2MtRel` has two regimes:
* *past* — both states `a`-disabled (`A d` with `√2 ≤ d`, `B e` with `√2 < e`, or `End`), with the
  formula clocks region-equivalent. Behaviour here is duration-blind (only delays), so plain
  `RegionEqAll` suffices and is closed under delay (region time-successor) and reset.
* *live* — `(A d) ~ (B e)` with `d < √2`, `e ≤ √2` (both can still do `a`; note `A`'s threshold is
  *open* `< √2`, `B`'s is *closed* `≤ √2`), and `RegionEqAll` on the formula clocks.

This file proves every `IsMtBisimulation` clause that does **not** need the live delay-crossing:
the guard, reset, both action clauses, the seed, and the entire **past-regime delay** clause (matched
by the formula-clock region time-successor). What remains — assembled in later steps — is the **live
delay clause**, whose crossing of `√2` is the genuine crux: it needs the process clock placed on the
correct side of `√2` *inside* the formula-clock region-window (the `exists_delay_past`/`before` +
`regionEqAll_timeSuccessor_frac_Ioo` toolkit of `TimedBisimulationHmlRefined`), and at the
double-coincidence (a formula clock at an integer exactly when the process is at `√2`) the single
irrational cut must be tracked per clock. That is the dedicated region-theory work to follow. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

/-- The candidate `Mt`-bisimulation for the `√2` example: a *past* regime (both `a`-disabled, formula
clocks region-equivalent) and a *live* regime (`(A d) ~ (B e)` with `d < √2`, `e ≤ √2`, formula clocks
region-equivalent). -/
def Sq2MtRel {D : Type*} (p : Sq2) (u : Valuation D) (q : Sq2) (u' : Valuation D) : Prop :=
  (aDisabled sqrt2NN p ∧ aDisabled sqrt2NN q ∧ RegionEqAll u u')
  ∨ (∃ d e : ℝ≥0, p = Sq2.A d ∧ q = Sq2.B e ∧ d < sqrt2NN ∧ e ≤ sqrt2NN ∧ RegionEqAll u u')

/-- Both regimes give region-equivalent formula clocks. -/
theorem Sq2MtRel.regionEqAll {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2MtRel p u q u') : RegionEqAll u u' := by
  rcases h with ⟨_, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ <;> exact hr

/-- **Guard clause.** Related states satisfy the same formula-clock guards. -/
theorem Sq2MtRel.guard {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2MtRel p u q u') (g : ClockConstraint D) : satisfies u g ↔ satisfies u' g :=
  regionEqAll_satisfies h.regionEqAll g

/-- **Reset clause.** Resetting the same formula clock on both sides preserves the relation. -/
theorem Sq2MtRel.reset {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2MtRel p u q u') (x : D) :
    Sq2MtRel p (Valuation.reset {x} u) q (Valuation.reset {x} u') := by
  rcases h with ⟨hpd, hqd, hr⟩ | ⟨d, e, hp, hq, hd, he, hr⟩
  · exact Or.inl ⟨hpd, hqd, hr.reset {x}⟩
  · exact Or.inr ⟨d, e, hp, hq, hd, he, hr.reset {x}⟩

/-- **Action clause (forth).** If `p` performs `a`, `q` matches it, landing related (both `End`). -/
theorem Sq2MtRel.act_forth {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2MtRel p u q u') (α : Sq2Act) (p' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act p α p') :
    ∃ q', (sq2TLTS sqrt2NN).act q α q' ∧ Sq2MtRel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨hpd, _, _⟩ | ⟨d, e, hp, hq, hd, he, hr⟩
  · exact absurd hstep (fun hs => hpd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aA _ => exact ⟨Sq2.End, sq2_act.mpr (Sq2Step.aB he), Or.inl ⟨trivial, trivial, hr⟩⟩

/-- **Action clause (back).** If `q` performs `a`, `p` matches it, landing related. -/
theorem Sq2MtRel.act_back {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2MtRel p u q u') (α : Sq2Act) (q' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act q α q') :
    ∃ p', (sq2TLTS sqrt2NN).act p α p' ∧ Sq2MtRel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨_, hqd, _⟩ | ⟨d, e, hp, hq, hd, he, hr⟩
  · exact absurd hstep (fun hs => hqd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aB _ => exact ⟨Sq2.End, sq2_act.mpr (Sq2Step.aA hd), Or.inl ⟨trivial, trivial, hr⟩⟩

/-- **Delay clause, past regime.** From two `a`-disabled, region-equivalent states, a left delay is
matched by a right delay (the formula-clock region time-successor), landing again `a`-disabled and
region-equivalent. (The live-regime delay — with its `√2`-crossing — is the remaining crux.) -/
theorem Sq2MtRel.delay_past {D : Type*} [Fintype D] {p q : Sq2} {u u' : Valuation D}
    (hpd : aDisabled sqrt2NN p) (hqd : aDisabled sqrt2NN q) (hr : RegionEqAll u u')
    (d : ℝ≥0) (p' : Sq2) (hstep : (sq2TLTS sqrt2NN).delay p d p') :
    ∃ d' q', (sq2TLTS sqrt2NN).delay q d' q' ∧ Sq2MtRel p' (u.add d) q' (u'.add d') := by
  rw [sq2_delay] at hstep
  obtain ⟨d', hr'⟩ := regionEqAll_timeSuccessor hr d
  obtain ⟨q', hqstep, hq'd⟩ := hqd.delay_succ d'
  refine ⟨d', q', sq2_delay.mpr hqstep, Or.inl ⟨?_, hq'd, hr'⟩⟩
  exact hpd.delay_pres hstep

/-- The seed: `(A 0)` and `(B 0)` at the all-zero formula valuation are related (live). -/
theorem sq2MtRel_seed {D : Type*} :
    Sq2MtRel (Sq2.A 0) (fun _ : D => 0) (Sq2.B 0) (fun _ : D => 0) :=
  Or.inr ⟨0, 0, rfl, rfl, zero_lt_sqrt2NN, le_of_lt zero_lt_sqrt2NN, RegionEqAll.refl _⟩

end TLTS

end DeepWiki.ReactiveSystems
