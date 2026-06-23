import DeepWiki.RelationalDatabases.HorizontalDecompositions
import Sources.Doi_10_1007_978_3_642_69956_6.Source

/-! # Relational Database Model catalog — Chapter 5: Horizontal Decompositions
Chapter 5 splits a relation into the tuples satisfying a functional dependency and the
"exceptions", governed by an *afunctional dependency* (ad). It treats horizontal decomposition
by goals (§5.1), the membership and inference problem for fds and ads (§5.2), the inheritance of
dependencies (§5.3) and normal forms for horizontal decompositions (§5.4). The
`DeepWiki.RelationalDatabases` library formalizes the ad definition and the sound mixed
inference rules FA1, FA2 and A1.

## NOT YET FORMALIZED (audit 2026-06-23; subtractive — delete each item once it is formalized)
§5.1: Def 5.2 (the selection for `X → Y`), Def 5.3 (a goal and the horizontal decomposition),
  Def 5.5 (the selection for an ad), Def 5.6 (a conflicting set of fds and ads), Def 5.7 / 5.8
  (Armstrong and strong Armstrong relations) and Theorem 5.1 (a strong Armstrong relation always
  exists, via the direct-product construction) [infra/research].
§5.2: Lemma 5.1 / 5.2 (conflict via Armstrong relations), Algorithm 5.1 (conflict detection),
  Theorem 5.2 and Corollary 5.1 (the rules I/FA1/FA2/A1 are complete for mixed fds and ads),
  Algorithm 5.2 (ad membership) [infra/research].
§5.3: Theorem 5.3 (fds are always inherited), Lemmas 5.4 / 5.5 / 5.6 and the inheritance of ads
  under horizontal decomposition [research].
§5.4: the normal forms for horizontal decompositions and their interaction with vertical
  decomposition [research].
§5.5: Exercises [deferred: not yet transcribed]. -/

open DeepWiki

namespace DeepWiki.Rdb

/-! ## §5.1 Horizontal Decompositions -/

/-- **Definition 5.1** (§5.1, p.133): a set of tuples is *X-complete* when its tuples have
different `X`-values from those outside it. -/
abbrev def_5_1_xcomplete := @DeepWiki.IsXComplete

/-- **Definition 5.1** (§5.1, p.133): a set of tuples is *X-unique* when all its tuples share one
`X`-value. -/
abbrev def_5_1_xunique := @DeepWiki.IsXUnique

/-- **Definition 5.4** (§5.1, p.135): a row set satisfies the *afunctional dependency* `X ↛ Y`
when every tuple has another tuple agreeing on `X` but differing on `Y`. -/
abbrev def_5_4_ad := @DeepWiki.SatisfiesAd

/-! ## §5.2 The Membership and Inference Problem -/

/-- **Lemma 5.3, rule FA1** (§5.2, p.139): a functional dependency `X → Y` and an ad `X ↛ Z`
yield the ad `Y ↛ Z`. -/
abbrev lemma_5_3_fa1 := @DeepWiki.satisfiesAd_fa1

/-- **Lemma 5.3, rule FA2** (§5.2, p.139): a functional dependency `Y → Z` and an ad `X ↛ Z`
yield the ad `X ↛ Y`. -/
abbrev lemma_5_3_fa2 := @DeepWiki.satisfiesAd_fa2

/-- **Lemma 5.3, rule A1** (§5.2, p.139): from the ad `X ∪ V ↛ Y ∪ W` with `W ⊆ V`, the ad
`X ↛ Y`. -/
abbrev lemma_5_3_a1 := @DeepWiki.satisfiesAd_a1

end DeepWiki.Rdb
