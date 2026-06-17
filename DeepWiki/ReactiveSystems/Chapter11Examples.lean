import DeepWiki.ReactiveSystems.TimedAutomata
import DeepWiki.ReactiveSystems.TimedTraces

/-! # Exercise 11.2 — two timed-language-inequivalent automata
The two single-location automata of Example 11.2 (one clock `x`, one action `a`,
self-loops resetting `x`): automaton (a) has guard `x ≤ 1`, automaton (b) has guard
`x = 1`. The timed trace `(0, a)` is afforded by (a) but not by (b) — at time `0`
the clock reads `0`, which satisfies `x ≤ 1` but not `x = 1` — so the two are **not**
timed-language equivalent. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal
open TLTS

/-- Automaton (a): a single location with a `x ≤ 1`-guarded `a`-self-loop. -/
def taA : TimedAutomaton Unit Unit Unit where
  initial := ()
  edge _ g _ r _ := g = ClockConstraint.atom () Cmp.le 1 ∧ r = {()}
  inv _ := ClockConstraint.true_

/-- Automaton (b): a single location with a `x = 1`-guarded `a`-self-loop. -/
def taB : TimedAutomaton Unit Unit Unit where
  initial := ()
  edge _ g _ r _ := g = ClockConstraint.atom () Cmp.eq 1 ∧ r = {()}
  inv _ := ClockConstraint.true_

/-- Automaton (a) affords the timed trace `(0, a)`: at time `0` the clock is `0`,
which satisfies the guard `x ≤ 1`. -/
theorem taA_trace : TimedTrace taA.tlts (taA.initial, fun _ => (0 : ℝ≥0)) [(0, ())] := by
  refine ⟨((), Valuation.add (fun (_ : Unit) => (0 : ℝ≥0)) (0 - 0)),
    ((), Valuation.reset {()} (Valuation.add (fun (_ : Unit) => (0 : ℝ≥0)) (0 - 0))),
    le_refl _, ⟨rfl, rfl, trivial, trivial⟩, ?_, trivial⟩
  refine ⟨ClockConstraint.atom () Cmp.le 1, {()}, ⟨rfl, rfl⟩, ?_, rfl, trivial⟩
  simp [satisfies, Cmp.holds, Valuation.add_apply]

/-- Automaton (b) does **not** afford `(0, a)`: at time `0` the clock is `0`, which
fails the guard `x = 1`. -/
theorem taB_no_trace : ¬ TimedTrace taB.tlts (taB.initial, fun _ => (0 : ℝ≥0)) [(0, ())] := by
  rintro ⟨⟨ℓ1, v1⟩, ⟨ℓ2, v2⟩, _, hd, ha, _⟩
  rw [TimedAutomaton.tlts_delay_iff] at hd
  rw [TimedAutomaton.tlts_act_iff] at ha
  obtain ⟨_, rfl, _, _⟩ := hd
  obtain ⟨_, _, ⟨rfl, _⟩, hsat, _⟩ := ha
  simp [satisfies, Cmp.holds, Valuation.add_apply] at hsat

/-- **Exercise 11.2** (§11.1, p.195). The automata (a) and (b) of Example 11.2 are not
timed-language equivalent: `(0, a)` is a timed trace of (a) but not of (b). -/
theorem ex_11_2 :
    taA.tlts.timedLang (taA.initial, fun _ => (0 : ℝ≥0)) ≠
      taB.tlts.timedLang (taB.initial, fun _ => (0 : ℝ≥0)) := by
  intro h
  apply taB_no_trace
  have hmem : [(0, ())] ∈ taA.tlts.timedLang (taA.initial, fun _ => (0 : ℝ≥0)) := taA_trace
  rw [h] at hmem
  exact hmem

end DeepWiki.ReactiveSystems
