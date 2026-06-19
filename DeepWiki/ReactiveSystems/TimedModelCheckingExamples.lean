import DeepWiki.ReactiveSystems.TimedRegionSuccessorComplete
import DeepWiki.ReactiveSystems.SymbolicModelCheckingExample

/-! # Worked timed model-checking, discharged by the executable decision procedure
The unconditional executable checker `satisfiesMt_iff_decideFull_delaySucc` turns a concrete
timed model-checking question `A ⊨ F` into a `decide` goal: rewrite by the bridge and let the
kernel evaluate the region-based Bool computation `SymSatCodeFull … regionCodeDelaySucc …`.

Here it discharges the running model-checking example — the one-location loop automaton
`demoAuto` (the `FinAutomaton` form of `boundedLoopAuto`) against `y in ∃∃(y = 2 ∧ [a]ff)` and
several delay-quantified variants — *by kernel computation* rather than the hand region argument
of `boundedLoop_symSat`. These are full-logic formulae (delay quantifiers `∃∃`/`∀∀`), so they go
through `satisfiesMt_iff_decideFull_delaySucc`, not the delay-free `satisfiesMt_iff_decide`. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The running model-checking example, by the **executable decision procedure**: `demoAuto`
(the `FinAutomaton` form of `boundedLoopAuto`) satisfies `y in ∃∃(y = 2 ∧ [a]ff)`. Proved by
`decide` through the verified bridge `satisfiesMt_iff_decideFull_delaySucc` — no hand region
argument (contrast `boundedLoop_symSat`). -/
theorem demoAuto_satisfies_boundedLoopFormula :
    demoAuto.toTimedAutomaton.SatisfiesMt boundedLoopFormula := by
  rw [satisfiesMt_iff_decideFull_delaySucc]; decide

/-- `∃∃[a]ff`: after *some* delay the `a`-loop is disabled (once `x > 1`). True, by decision. -/
theorem demoAuto_satisfies_existsDelay_box_ff :
    demoAuto.toTimedAutomaton.SatisfiesMt
      (Mt.existsDelay (Mt.box () Mt.ff) : Mt Unit (Fin 1)) := by
  rw [satisfiesMt_iff_decideFull_delaySucc]; decide

/-- `∀∀⟨a⟩tt`: the `a`-loop is enabled after *every* delay. False (fails once `x > 1`), by
decision — the dual of `demoAuto_satisfies_existsDelay_box_ff`. -/
theorem demoAuto_not_satisfies_forallDelay_dia_tt :
    ¬ demoAuto.toTimedAutomaton.SatisfiesMt
      (Mt.forallDelay (Mt.dia () Mt.tt) : Mt Unit (Fin 1)) := by
  rw [satisfiesMt_iff_decideFull_delaySucc]; decide

/-- `[a]⟨a⟩tt`: after an `a`-step (which resets `x`), the `a`-loop is enabled again. True, by
decision. -/
theorem demoAuto_satisfies_box_dia_tt :
    demoAuto.toTimedAutomaton.SatisfiesMt
      (Mt.box () (Mt.dia () Mt.tt) : Mt Unit (Fin 1)) := by
  rw [satisfiesMt_iff_decideFull_delaySucc]; decide

/-- `∀∀[a]⟨a⟩tt`: after every delay, any `a`-step leaves the loop re-enabled. True, by decision —
each `a`-edge resets `x`, so the post-state always satisfies the guard. -/
theorem demoAuto_satisfies_forallDelay_box_dia_tt :
    demoAuto.toTimedAutomaton.SatisfiesMt
      (Mt.forallDelay (Mt.box () (Mt.dia () Mt.tt)) : Mt Unit (Fin 1)) := by
  rw [satisfiesMt_iff_decideFull_delaySucc]; decide

/-! ## §12.4 running example: the `TwoAs` property by decision -/

/-- The §12.4 running automaton: one location, clock `x`, a single `a`-self-loop guarded `x ≤ 1`
resetting `x`, with the trivial invariant (the location may delay freely). The `FinAutomaton`
form, so the decision procedure applies. -/
def loopAuto : FinAutomaton (Fin 1) Unit (Fin 1) where
  initial := 0
  edges := [(0, ClockConstraint.atom 0 Cmp.le 1, (), [0], 0)]
  inv := fun _ => ClockConstraint.true_

/-- The §12.4 formula `TwoAs := [a](y in ∀∀[a](y ≤ 1))` (eq. 12.2): no matter how the automaton
performs two `a`-actions in a row, the delay between them is at most one time unit. -/
def twoAsFormula : Mt Unit (Fin 1) :=
  .box () (.reset 0 (.forallDelay (.box () (.guard (.atom 0 Cmp.le 1)))))

/-- **§12.4 running example (eq. 12.2), by the executable decision procedure.** The running
automaton satisfies `TwoAs = [a](y in ∀∀[a](y ≤ 1))` — between two consecutive `a`-actions at
most one time unit elapses — proved by `decide` through `satisfiesMt_iff_decideFull_delaySucc`
(the book encourages checking this directly from the satisfaction relation). -/
theorem loopAuto_satisfies_twoAs : loopAuto.toTimedAutomaton.SatisfiesMt twoAsFormula := by
  rw [satisfiesMt_iff_decideFull_delaySucc]; decide

end DeepWiki.ReactiveSystems
