import DeepWiki.ReactiveSystems.TimedTransitionSystems
import DeepWiki.ReactiveSystems.TimedRegions
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 11: Timed behavioural equivalences
Book-numbered restatements for §11.2 (timed bisimilarity) and §11.4 (the region
construction), discharged by the `DeepWiki.ReactiveSystems` library. (§11.5, zone
graphs, and the substantive halves of Theorem 11.3 — finite index and
same-region/timed-bisimilarity — are future work.) -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems

variable {Proc Act : Type*} {C : Type*}

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

/-! ## §11.4 The region construction -/

/-- **Definition 11.11** (§11.4, p.205). Integer part `⌊d⌋` of a clock value. -/
noncomputable abbrev intPart := @DeepWiki.ReactiveSystems.intPart

/-- **Definition 11.11** (§11.4, p.205). Fractional part `frac(d) = d − ⌊d⌋`. -/
noncomputable abbrev fracPart := @DeepWiki.ReactiveSystems.fracPart

/-- **Definition 11.12** (§11.4, p.207), verbatim. Two clock valuations are
equivalent when their integer parts agree up to `cₓ`, they agree on which clocks
have a zero fractional part, and the ordering of fractional parts agrees. The
library's `RegionEquiv`. -/
abbrev def_11_12 := @DeepWiki.ReactiveSystems.RegionEquiv

/-- **Definition 11.12** is **not** symmetric as literally stated (the asymmetric
guard `v x ≤ cₓ` only catches differing fractional parts at an integer boundary
in one direction); the genuine region equivalence underlying Theorem 11.3 uses
the clamped floor `RegionEq`. -/
theorem def_11_12_not_symmetric :
    ¬ Symmetric (DeepWiki.ReactiveSystems.RegionEquiv (C := Unit) (fun _ => 0)) :=
  DeepWiki.ReactiveSystems.not_symmetric_regionEquiv

/-- **Theorem 11.3** (§11.4, p.209), equivalence-relation part. Region
equivalence partitions the clock valuations — here the corrected `RegionEq` is a
genuine `Equivalence`. -/
theorem thm_11_3_equivalence (cmax : C → ℕ) :
    Equivalence (DeepWiki.ReactiveSystems.RegionEq cmax) :=
  DeepWiki.ReactiveSystems.regionEq_equivalence cmax

/-- **Theorem 11.3** (§11.4, p.209), finite-index part. Over a finite clock set,
region equivalence has finitely many classes — the region quotient is finite.
(The remaining same-region/timed-bisimilarity claim of Theorem 11.3 is future
work.) -/
theorem thm_11_3_finite [Finite C] (cmax : C → ℕ) :
    Finite (DeepWiki.ReactiveSystems.Region cmax) :=
  DeepWiki.ReactiveSystems.Region.finite cmax

/-- **Definition 11.13** (§11.4, p.209). A *region* is an `≡`-equivalence class
`[v]_≡` of clock valuations. The library's `Region`. -/
abbrev def_11_13 := @DeepWiki.ReactiveSystems.Region

end DeepWiki.Rs
