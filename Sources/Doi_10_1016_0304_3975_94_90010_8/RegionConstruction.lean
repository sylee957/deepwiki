import DeepWiki.ReactiveSystems.TimedRegions
import DeepWiki.ReactiveSystems.TimedRegionGraph
import DeepWiki.ReactiveSystems.SymbolicModelCheckingExecutableFull
import Sources.Doi_10_1016_0304_3975_94_90010_8.Source

/-! # Alur–Dill region construction — catalog
Pointers to the `DeepWiki.ReactiveSystems` region machinery formalizing Alur–Dill §4.2–4.3.
The library defines region equivalence as a one-field fingerprint (clamped floors, frac-zero
bits, frac-order), matching Definition 4.3 verbatim, and builds the finite region quotient
and region automaton on it. The **time-successor** (Definition 4.6) is the chain
`α → β → …` of clock regions reachable as time elapses; the library has its *classical
existence* (`timeSuccessor_of_fintype`) and isolates the constructive enumeration as
`SuccSound`/`SuccComplete` (the §4.3 construction). -/

namespace DeepWiki.Ad

open DeepWiki.ReactiveSystems

/-- **Definition 4.3** (§4.2, p.202): region equivalence `v ∼ v'` — equal clamped integer
parts, agreement on which clocks are integral, and the same fractional ordering. The
library's `RegionEq` (at clamp `cmax`), whose fingerprint matches the three conditions. -/
abbrev def_4_3 := @DeepWiki.ReactiveSystems.RegionEq

/-- **Lemma 4.5** (§4.2, p.203): there are finitely many clock regions. The library's
`Region.finite`. -/
abbrev lemma_4_5 := @DeepWiki.ReactiveSystems.Region.finite

/-- **Definition 4.6** (§4.3, p.203): the time-successor relation on clock regions —
`α'` is a time-successor of `α` iff every `v ∈ α` reaches `α'` after some delay. The
library's relational `TimeSuccessor` (delays match into region-equivalent valuations). -/
abbrev def_4_6 := @DeepWiki.ReactiveSystems.TimeSuccessor

/-- **Definition 4.6**, existence (§4.3, p.203–204): for finitely many clocks the
time-successor delay always exists. The library's `timeSuccessor_of_fintype` (classical;
the *constructive* §4.3 enumeration is isolated as `SuccSound`/`SuccComplete`). -/
abbrev thm_timeSuccessor_of_fintype := @DeepWiki.ReactiveSystems.timeSuccessor_of_fintype

/-- **Definition 4.8** (§4.3, p.204): the region automaton `R(𝒜)` — the quotient of the
untimed transition system by region equivalence on configurations. The library's
`TimedAutomaton.regionGraph`. -/
noncomputable abbrev def_4_8 := @DeepWiki.ReactiveSystems.TimedAutomaton.regionGraph

/-- **§4.3 construction** (p.204): soundness of an enumerated time-successor — every region
code listed by `succ` is realized by some delay. The library's `SuccSound` (the obligation
the constructive Alur–Dill successor must satisfy). -/
abbrev succSound := @DeepWiki.ReactiveSystems.SuccSound

/-- **§4.3 construction** (p.204): completeness of an enumerated time-successor — every
region code reachable by a delay is listed by `succ`. The library's `SuccComplete`. -/
abbrev succComplete := @DeepWiki.ReactiveSystems.SuccComplete

end DeepWiki.Ad
