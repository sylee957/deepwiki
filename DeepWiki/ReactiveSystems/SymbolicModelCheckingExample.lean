import DeepWiki.ReactiveSystems.SymbolicModelChecking

/-! # A worked symbolic model-checking example (Exercise 12.8)
The one-location timed automaton with clock `x`, invariant `x ≤ 2`, and a single
`a`-self-loop guarded `x ≤ 1` resetting `x`. Its initial symbolic state satisfies
`y in ∃∃(y = 2 ∧ [a]ff)`: reset the formula clock `y`, delay `2` (legal, `x ≤ 2`)
so that `y = 2`, and there `[a]ff` holds vacuously because `a` is disabled
(`x = 2 > 1`). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- Exercise 12.8's timed automaton: one location, clock `x`, invariant `x ≤ 2`, a
single `a`-edge guarded `x ≤ 1` resetting `x`. -/
def boundedLoopAuto : TimedAutomaton Unit Unit Unit where
  initial := ()
  edge _ g _ r _ := g = ClockConstraint.atom () .le 1 ∧ r = {()}
  inv _ := ClockConstraint.atom () .le 2

/-- Exercise 12.8's formula `y in ∃∃(y = 2 ∧ [a]ff)`. -/
def boundedLoopFormula : Mt Unit Unit :=
  .reset () (.existsDelay (.and (.guard (.atom () .eq 2)) (.box () .ff)))

/-- **Exercise 12.8.** The initial symbolic state of `boundedLoopAuto` satisfies
`y in ∃∃(y = 2 ∧ [a]ff)`: delaying `2` reaches `y = 2` with `x = 2`, where the
`a`-edge (guard `x ≤ 1`) is disabled, so `[a]ff` holds vacuously. -/
theorem boundedLoop_symSat :
    SymSat boundedLoopAuto () (combineVal (fun _ => 0) (fun _ => 0)) boundedLoopFormula := by
  refine ⟨2, ?_, ?_, ?_, ?_⟩
  · -- pre-invariant: x = 0 ≤ 2
    norm_num [boundedLoopAuto, satisfies, Cmp.holds, Valuation.reset, combineVal,
      Set.mem_singleton_iff]
  · -- post-invariant: x = 0 + 2 ≤ 2
    norm_num [boundedLoopAuto, satisfies, Cmp.holds, Valuation.reset, combineVal,
      Set.mem_singleton_iff]
  · -- y = 2: the formula clock, reset then delayed by 2
    norm_num [SymSat, boundedLoopAuto, satisfies, Cmp.holds, Valuation.reset, combineVal,
      Set.mem_singleton_iff]
  · -- [a]ff: the only a-edge has guard x ≤ 1, but x = 2 > 1, so the guard fails
    rintro _ g r ⟨rfl, rfl⟩ hgsat _
    norm_num [satisfies, Cmp.holds, Valuation.reset, combineVal, Set.mem_singleton_iff] at hgsat

end DeepWiki.ReactiveSystems
