import DeepWiki.ReactiveSystems.TimedAutomata
import DeepWiki.ReactiveSystems.TimedTraces

/-! # Two timed automata: untimed-language equivalent but not timed-equivalent
Two single-location automata (one clock `x`, one action `a`,
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

/-- The automata (a) and (b) are not
timed-language equivalent: `(0, a)` is a timed trace of (a) but not of (b). -/
theorem taA_not_timedLangEq_taB :
    taA.tlts.timedLang (taA.initial, fun _ => (0 : ℝ≥0)) ≠
      taB.tlts.timedLang (taB.initial, fun _ => (0 : ℝ≥0)) := by
  intro h
  apply taB_no_trace
  have hmem : [(0, ())] ∈ taA.tlts.timedLang (taA.initial, fun _ => (0 : ℝ≥0)) := taA_trace
  rw [h] at hmem
  exact hmem

/-! ## The untimed-language-equivalence half (the converse fails) -/

/-- Resetting the single clock yields the all-zero valuation. -/
theorem reset_unit (v : Valuation Unit) : Valuation.reset {()} v = fun _ => (0 : ℝ≥0) := by
  funext x; exact Valuation.reset_mem (by simp) v

/-- Automaton (a) affords every untimed trace (it can do `a` at any time, looping back
to the initial state). -/
theorem taA_real : ∀ u : List Unit,
    ∃ w, w ∈ taA.tlts.timedLang (taA.initial, fun _ => (0 : ℝ≥0)) ∧ w.map Prod.snd = u := by
  intro u
  induction u with
  | nil => exact ⟨[], trivial, rfl⟩
  | cons hd tl ih =>
      obtain ⟨w', hw', hmap'⟩ := ih
      refine ⟨((0 : ℝ≥0), ()) :: w', ⟨(taA.initial, Valuation.add (fun (_ : Unit) => (0 : ℝ≥0)) (0 - 0)),
        (taA.initial, fun _ => 0), le_refl _, ⟨rfl, rfl, trivial, trivial⟩,
        ⟨ClockConstraint.atom () Cmp.le 1, {()}, ⟨rfl, rfl⟩,
          by simp [satisfies, Cmp.holds, Valuation.add_apply], (reset_unit _).symm, trivial⟩,
        hw'⟩, ?_⟩
      cases hd; simp [hmap']

/-- Automaton (b) affords every untimed trace too (it does `a` after waiting one unit,
looping back to the initial state). -/
theorem taB_real : ∀ (now : ℝ≥0) (u : List Unit),
    ∃ w, TimedTraceFrom taB.tlts (taB.initial, fun _ => (0 : ℝ≥0)) now w ∧ w.map Prod.snd = u := by
  intro now u
  induction u generalizing now with
  | nil => exact ⟨[], trivial, rfl⟩
  | cons hd tl ih =>
      obtain ⟨w', hw', hmap'⟩ := ih (now + 1)
      refine ⟨(now + 1, ()) :: w',
        ⟨(taB.initial, Valuation.add (fun (_ : Unit) => (0 : ℝ≥0)) ((now + 1) - now)),
        (taB.initial, fun _ => 0), le_self_add, ⟨rfl, rfl, trivial, trivial⟩,
        ⟨ClockConstraint.atom () Cmp.eq 1, {()}, ⟨rfl, rfl⟩, ?_, (reset_unit _).symm, trivial⟩,
        hw'⟩, ?_⟩
      · show Cmp.holds Cmp.eq _ 1
        simp only [Cmp.holds, Valuation.add_apply, Nat.cast_one, zero_add, add_tsub_cancel_left]
      · cases hd; simp [hmap']

/-- Automaton (a) accepts every untimed trace. -/
theorem taA_untimed_univ : taA.tlts.untimedLang (taA.initial, fun _ => (0 : ℝ≥0)) = Set.univ :=
  Set.eq_univ_iff_forall.mpr taA_real

/-- Automaton (b) accepts every untimed trace. -/
theorem taB_untimed_univ : taB.tlts.untimedLang (taB.initial, fun _ => (0 : ℝ≥0)) = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun u => taB_real 0 u

/-- The automata (a) and (b) **are** untimed-language equivalent (both accept every
untimed trace, differing only in *when* the `a`s happen). -/
theorem taA_untimedLangEq_taB :
    taA.tlts.untimedLang (taA.initial, fun _ => (0 : ℝ≥0)) =
      taB.tlts.untimedLang (taB.initial, fun _ => (0 : ℝ≥0)) :=
  taA_untimed_univ.trans taB_untimed_univ.symm

/-- Untimed-language
equivalence does **not** imply timed-language equivalence: (a) and (b) are
untimed-language equivalent yet not timed-language equivalent. -/
theorem taA_taB_untimedEq_not_timedEq :
    (taA.tlts.untimedLang (taA.initial, fun _ => (0 : ℝ≥0)) =
      taB.tlts.untimedLang (taB.initial, fun _ => (0 : ℝ≥0))) ∧
    (taA.tlts.timedLang (taA.initial, fun _ => (0 : ℝ≥0)) ≠
      taB.tlts.timedLang (taB.initial, fun _ => (0 : ℝ≥0))) :=
  ⟨taA_untimedLangEq_taB, taA_not_timedLangEq_taB⟩

end DeepWiki.ReactiveSystems
