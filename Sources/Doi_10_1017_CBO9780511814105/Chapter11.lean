import DeepWiki.ReactiveSystems.TimedTransitionSystems
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 11: Timed behavioural equivalences
Book-numbered restatements for §11.2 (timed bisimilarity), discharged by the
`DeepWiki.ReactiveSystems` library. (§11.4–11.5, region and zone graphs, are
future work.) -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems

variable {Proc Act : Type*}

/-! ## §11.2 Timed and untimed bisimilarity -/

/-- **Definition 11.5** (§11.2, p.195). Timed bisimilarity: a timed bisimulation
matches both visible actions and time-delay steps. The library's
`TLTS.TimedBisimilar` (bisimilarity over the combined action/delay labels). -/
abbrev def_11_5 := @TLTS.TimedBisimilar

/-- **Definition 11.5** (§11.2, p.195), the transfer property: timed bisimilarity
matches both action transitions and time-delay transitions on each side. -/
theorem def_11_5_transfer (T : TLTS Proc Act) (p q : Proc) :
    TLTS.TimedBisimilar T p q ↔
      (∀ a p', T.act p a p' → ∃ q', T.act q a q' ∧ TLTS.TimedBisimilar T p' q') ∧
      (∀ a q', T.act q a q' → ∃ p', T.act p a p' ∧ TLTS.TimedBisimilar T p' q') ∧
      (∀ d p', T.delay p d p' → ∃ q', T.delay q d q' ∧ TLTS.TimedBisimilar T p' q') ∧
      (∀ d q', T.delay q d q' → ∃ p', T.delay p d p' ∧ TLTS.TimedBisimilar T p' q') :=
  TLTS.timedBisimilar_iff T p q

/-- **§11.2** (p.195). Timed bisimilarity is an equivalence relation. -/
theorem timedBisimilar_equivalence (T : TLTS Proc Act) :
    Equivalence (TLTS.TimedBisimilar T) := TLTS.timedBisimilar_equivalence T

end DeepWiki.Rs
