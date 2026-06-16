import DeepWiki.ReactiveSystems.TimedHennessyMilner
import DeepWiki.ReactiveSystems.TimedHennessyMilnerClocks
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 12: Hennessy–Milner logic with time
Book-numbered restatements for the timed logic `Mt` with formula clocks (§12.1,
Definitions 12.1–12.3) and the soundness half of the timed Hennessy–Milner
characterisation (§12.3), discharged by the `DeepWiki.ReactiveSystems` library.
(The completeness half via regions is future work.) -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems

variable {Proc Act D : Type*}

/-! ## §12.1 Hennessy–Milner logic with time (`Mt`) -/

/-- A simplified fragment of timed HML — actions plus the delay quantifiers
`∃∃`/`∀∀`, without formula clocks. The library's `TimedHML`. -/
abbrev timedHML := @TimedHML

/-- Satisfaction of the simplified fragment in a TLTS. The library's
`TLTS.TSat`. -/
abbrev tsat := @TLTS.TSat

/-- **Definition 12.1** (§12.1, p.223). Hennessy–Milner formulae with time `Mt`
over actions `Act` and formula clocks `D`: action modalities `⟨a⟩`/`[a]`, delay
quantifiers `∃∃`/`∀∀`, the reset `x in F`, and atomic clock constraints
`g ∈ B(D)`. The library's `Mt`. -/
abbrev def_12_1 := @Mt

/-- **Definition 12.2** (§12.1, p.224). Semantics of `Mt`: satisfaction at an
extended state `(p, u)` (process plus formula-clock valuation); delay steps
advance the formula clocks `u`, `x in F` resets `x`, and `g` reads `u`. The
library's `TLTS.MtSat`. -/
abbrev def_12_2 := @TLTS.MtSat

/-- **Definition 12.3** (§12.1, p.225). A state satisfies `F` when the extended
state with every formula clock zero does: `(p, u₀) ⊨ F`. The library's
`TLTS.MtSatState`. -/
abbrev def_12_3 := @TLTS.MtSatState

/-! ## §12.3 Timed bisimilarity versus HML with time -/

/-- **§12.3** (soundness; the timed analogue of Theorem 5.1, simplified
fragment). Timed-bisimilar states satisfy the same fragment formulae. (This
direction holds for every TLTS; the converse uses the region abstraction of
§11.4, as delay-branching is uncountable.) -/
theorem timed_hm_soundness (T : TLTS Proc Act) {p q : Proc}
    (h : TLTS.TimedBisimilar T p q) : TLTS.TimedHMLEquiv T p q :=
  TLTS.timedBisimilar_timedHmlEquiv h

/-- **§12.3** (soundness for the full logic `Mt`). Timed-bisimilar states satisfy
the same `Mt` formulae (Definition 12.3 satisfaction). The reset and guard
constructs touch only the formula clocks, so soundness extends from the modal
fragment for free. -/
theorem mt_soundness (T : TLTS Proc Act) {p q : Proc}
    (h : TLTS.TimedBisimilar T p q) (F : Mt Act D) :
    TLTS.MtSatState T p F ↔ TLTS.MtSatState T q F :=
  TLTS.timedBisimilar_mtSatState h F

end DeepWiki.Rs
