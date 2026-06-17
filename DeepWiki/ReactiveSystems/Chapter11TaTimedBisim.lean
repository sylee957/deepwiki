import DeepWiki.ReactiveSystems.TimedAutomata
import DeepWiki.ReactiveSystems.TimedTransitionSystems
import DeepWiki.ReactiveSystems.BisimulationQuotient

/-! # Definition 11.6 — timed bisimilarity of timed automata
Lifting timed bisimilarity (Definition 11.5, on TLTS states) to whole automata: two
timed automata are timed bisimilar iff their initial states (all clocks zero) are
timed bisimilar in the *union* of the timed transition systems they generate. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- **Definition 11.6** (§11.2, p.196). Timed automata `A₁` and `A₂` are *timed
bisimilar* iff their initial states are timed bisimilar in the union (disjoint sum)
of the TLTSs `A₁.tlts` and `A₂.tlts`. -/
def TimedAutomaton.TimedBisimilar {Loc₁ Loc₂ Act C₁ C₂ : Type*}
    (A₁ : TimedAutomaton Loc₁ Act C₁) (A₂ : TimedAutomaton Loc₂ Act C₂) : Prop :=
  TLTS.TimedBisimilar (LTS.sum A₁.tlts A₂.tlts)
    (Sum.inl (A₁.initial, fun _ => 0)) (Sum.inr (A₂.initial, fun _ => 0))

end DeepWiki.ReactiveSystems
