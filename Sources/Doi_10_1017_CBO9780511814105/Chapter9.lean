import DeepWiki.ReactiveSystems.TimedTransitionSystems
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 9: CCS with time delays
Book-numbered restatements for the timed transition-system model of §9.2,
discharged by the `DeepWiki.ReactiveSystems` library. (§9.3–9.5, the syntax and
SOS rules of timed CCS, are a concrete extension of the CCS model and are noted
but not catalogued here as single declarations.) -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems

/-! ## §9.2 Timed labelled transition systems -/

/-- **Definition 9.1** (§9.2, p.164). A timed labelled transition system: an LTS
with label set `Lab = Act ∪ ℝ≥0` (ordinary actions and time delays). The
library's `TLTS` (over the combined label type `Act ⊕ ℝ≥0`). -/
abbrev def_9_1 := @TLTS

/-- **(9.2)** (§9.2, p.164), time determinism: a delay transition leads to a
unique state. The library's `TLTS.TimeDeterministic`. -/
abbrev eq_9_2 := @TLTS.TimeDeterministic

/-- **(9.3)** (§9.2, p.164), zero delay: every state reaches itself with a zero
delay. The library's `TLTS.ZeroDelay`. -/
abbrev eq_9_3 := @TLTS.ZeroDelay

/-- **(9.4)** (§9.2, p.165), time additivity / continuity: a delay of `d₁ + d₂`
is exactly a delay `d₁` followed by a delay `d₂`. The library's
`TLTS.TimeAdditive`. -/
abbrev eq_9_4 := @TLTS.TimeAdditive

end DeepWiki.Rs
