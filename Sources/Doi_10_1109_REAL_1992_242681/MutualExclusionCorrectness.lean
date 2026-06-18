import DeepWiki.ReactiveSystems.FischerMutualExclusion
import Sources.Doi_10_1109_REAL_1992_242681.Source

/-! # Lynch–Shavit — timing-based mutual exclusion — catalog
Pointers to the `DeepWiki.ReactiveSystems` formalization of Fischer's timing-based mutual-exclusion
protocol, whose correctness framework the Reactive Systems book's Chapter 13 (Theorem 13.1) defers
to this paper. These are the paper-side ("double reference") pointers complementing the book
catalog's `Chapter13`; the protocol's *essential* dependence on timing — the correctness the paper
analyses — is witnessed by the erroneous (wrong-guard) variant violating safety. -/

namespace DeepWiki.Ls

open DeepWiki.ReactiveSystems

/-- **The timing-based mutual-exclusion algorithm** modeled as a timed automaton (one clock and a
shared register per process, folded into the global location). The library's `fischer`. -/
abbrev mutualExclusionProtocol := @DeepWiki.ReactiveSystems.fischer

/-- **The mutual-exclusion safety property**: at most one process is in its critical section. The
library's `FischerLoc.MutualExclusion`. -/
abbrev mutualExclusion := @DeepWiki.ReactiveSystems.FischerLoc.MutualExclusion

/-- **Initial-configuration safety**: the initial global location satisfies mutual exclusion. The
library's `fischer_initial_mutualExclusion`. -/
alias initial_mutualExclusion := DeepWiki.ReactiveSystems.fischer_initial_mutualExclusion

/-- **Timing is essential** (the paper's point): with the *wrong* guard the protocol breaks — a
reachable configuration of the erroneous variant violates mutual exclusion (both processes enter
their critical sections), so the timing constraints are necessary for correctness. The library's
`not_fischerErroneous_mutualExclusion`. -/
alias erroneous_violates_mutualExclusion :=
  DeepWiki.ReactiveSystems.not_fischerErroneous_mutualExclusion

end DeepWiki.Ls
