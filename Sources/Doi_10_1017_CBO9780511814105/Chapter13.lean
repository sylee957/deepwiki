import DeepWiki.ReactiveSystems.FischerMutualExclusion
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 13: Fischer's algorithm
Book-numbered restatements for the timing-based mutual-exclusion model of §13.2,
discharged by the `DeepWiki.ReactiveSystems` library. Correctness (Lynch–Shavit,
Theorem 4.6) rests on the timing assumptions and is proved here directly for every `n`
(`thm_4_6`), via an inductive invariant on reachable configurations.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
(none) -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems

/-! ## §13.2 Modelling Fischer's algorithm -/

/-- **§13.2** (Figure 13.1, p.251). The control locations `L → 1 → 2 → CS` of
Fischer's per-process automaton `Aᵢ`. The library's `FischerCtrl`. -/
abbrev fischerCtrl := @FischerCtrl

/-- **§13.2** (Figure 13.1, p.251). Fischer's algorithm for `n` processes with
bound `c`, modelled as a network of timed automata: one clock per process and the
shared register `id` folded into the global location. The library's `fischer`. -/
abbrev fig_13_1 := @fischer

/-- **§13.1** (p.250). Mutual exclusion: no two distinct processes are in their
critical sections simultaneously. The library's `FischerLoc.MutualExclusion`. -/
abbrev mutualExclusion := @FischerLoc.MutualExclusion

/-- **§13.2** (p.251). The Fischer network is safe when mutual exclusion holds at
every reachable global location (Theorem 4.6 of Lynch–Shavit; proof delegated to
external verification). The library's `FischerSafe`. -/
abbrev fischerSafe := @FischerSafe

/-- **§13.2.** The initial configuration trivially satisfies mutual exclusion. -/
theorem fischer_initial_mutex (n c : ℕ) :
    (fischer n c).initial.MutualExclusion :=
  fischer_initial_mutualExclusion n c

/-- **Theorem 4.6** (Lynch–Shavit; §13.2). Fischer's algorithm guarantees mutual
exclusion for every number of processes `n` and bound `c`: at every reachable global
location, no two distinct processes are in their critical sections. Proved directly (not
delegated to UPPAAL) via the inductive invariant `FischerInv`, whose load-bearing clause
— a critical process owns the register `id` — forces two critical processes to coincide;
the strict re-check guard `xᵢ > c` is what keeps that clause inductive. The library's
`fischer_safe`. -/
theorem thm_4_6 (n c : ℕ) : FischerSafe n c :=
  fischer_safe n c

/-- **§13.2** (Figure 13.2, p.256). The *erroneous* version of Fischer's
algorithm, whose node-`2` re-check guard is weakened from `xᵢ > c` to `xᵢ ≥ c`.
The library's `fischerErroneous`. -/
abbrev fig_13_2 := @fischerErroneous

/-- **Exercise 13.3** (p.257). The erroneous version does **not** preserve mutual
exclusion: the two-process network reaches a global location where both processes
are in their critical sections (each having entered after a delay of *exactly*
`c`, which the correct strict guard would forbid). -/
theorem ex_13_3 (c : ℕ) :
    ∃ s, (fischerErroneous 2 c).tlts.Reachable
        ((fischerErroneous 2 c).initial, fun _ => 0) s ∧ ¬ s.1.MutualExclusion :=
  not_fischerErroneous_mutualExclusion c

end DeepWiki.Rs
