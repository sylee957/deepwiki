import DeepWiki.ReactiveSystems.TimedAutomata
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 10: Timed automata
Book-numbered restatements for the syntax (§10.2) and semantics (§10.3) of timed
automata, discharged by the `DeepWiki.ReactiveSystems` library. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems

/-! ## §10.2 Syntax of timed automata -/

/-- **Definition 10.1** (§10.2, p.176). Clock constraints / guards
`g ::= tt ∣ x ⋈ n ∣ g₁ ∧ g₂`. The library's `ClockConstraint`. -/
abbrev def_10_1 := @ClockConstraint

/-- **§10.2** (p.176), the increment `v + d` of a clock valuation by a delay. -/
abbrev valuation_add := @Valuation.add

/-- **§10.2** (p.176), the reset `v[r]` of the clocks in `r` to zero. -/
noncomputable def valuation_reset := @Valuation.reset

/-- **Definition 10.2** (§10.2, p.177). Evaluation of a clock constraint under a
valuation. The library's `satisfies`. -/
abbrev def_10_2 := @satisfies

/-- **Definition 10.4** (§10.2, p.179). A timed automaton: locations, an edge
relation carrying guard/action/reset, and location invariants. The library's
`TimedAutomaton`. -/
abbrev def_10_4 := @TimedAutomaton

/-! ## §10.3 Semantics of timed automata -/

/-- **Definition 10.5** (§10.3, p.180). The timed LTS `T(A)` denoted by a timed
automaton — guarded action transitions with clock resets, and delay transitions
that advance all clocks within the location invariant. The library's
`TimedAutomaton.tlts`. -/
noncomputable def def_10_5 := @TimedAutomaton.tlts

/-- **Definition 10.5** (§10.3, p.180). The semantics of a timed automaton has
deterministic delay transitions (time-determinism axiom 9.2). -/
theorem def_10_5_timeDeterministic {Loc Act C : Type*} (A : TimedAutomaton Loc Act C) :
    A.tlts.TimeDeterministic := A.timeDeterministic

end DeepWiki.Rs
