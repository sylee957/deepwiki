import DeepWiki.ReactiveSystems.TimedHennessyMilner
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 12: Hennessy–Milner logic with time
Book-numbered restatements for the basic timed logic (§12.1) and the soundness
half of the timed Hennessy–Milner characterisation (§12.3), discharged by the
`DeepWiki.ReactiveSystems` library. (§12.2's full logic `Mt` with formula clocks,
and the completeness half via regions, are future work.) -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems

variable {Proc Act : Type*}

/-! ## §12.1 Basic Hennessy–Milner logic with time -/

/-- **§12.1** (p.220). Basic Hennessy–Milner logic with time: HML over actions
together with the delay quantifiers `∃∃` and `∀∀`. The library's `TimedHML`. -/
abbrev timedHML := @TimedHML

/-- **§12.1** (p.221). Satisfaction of a basic timed formula in a TLTS: `⟨a⟩`/`[a]`
range over action transitions, `∃∃`/`∀∀` over time-delay transitions. The
library's `TLTS.TSat`. -/
abbrev tsat := @TLTS.TSat

/-! ## §12.3 Timed bisimilarity versus HML with time -/

/-- **§12.3** (soundness; the timed analogue of Theorem 5.1). Timed-bisimilar
states satisfy the same basic timed formulae. (This direction holds for every
TLTS; the converse uses the region abstraction of §11.4, as delay-branching is
uncountable.) -/
theorem timed_hm_soundness (T : TLTS Proc Act) {p q : Proc}
    (h : TLTS.TimedBisimilar T p q) : TLTS.TimedHMLEquiv T p q :=
  TLTS.timedBisimilar_timedHmlEquiv h

end DeepWiki.Rs
