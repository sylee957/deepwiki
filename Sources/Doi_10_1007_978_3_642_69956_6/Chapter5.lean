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
§5.1: Def 5.2 (the selection for `X → Y`), Def 5.3 (a goal and the horizontal decomposition) and
  Def 5.5 (the selection for an ad) [infra]. (Def 5.6 conflict, Def 5.7 / 5.8 Armstrong and strong
  Armstrong relations, and Theorem 5.1 — strong-Armstrong existence via the direct product — are
  done.)
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

/-- **Definition 5.6** (§5.1, p.136): a set of fds `F` and ads `A` is *in conflict* when the empty
instance is the only one satisfying all of them. -/
abbrev def_5_6_conflict := @DeepWiki.InConflict

/-- **Example (§5.1, p.136)**: `{X → Y, X ↛ Y}` is in conflict — any relation satisfying both is
empty. -/
abbrev conflict_fd_ad := @DeepWiki.eq_empty_of_satisfiesFd_satisfiesAd

/-- **Definition 5.7** (§5.1, p.136): an *Armstrong relation* for `F` — the fds holding in it are
exactly the consequences of `F`. -/
abbrev def_5_7_armstrong := @DeepWiki.IsArmstrongRelation

/-- **Definition 5.8** (§5.1, p.137): a *strong Armstrong relation* for `F` — every consequence fd
holds, and every non-consequence fd `X → Y` carries its ad `X ↛ Y`. -/
abbrev def_5_8_strong_armstrong := @DeepWiki.IsStrongArmstrong

/-- A nonempty strong Armstrong relation is an Armstrong relation (§5.1). -/
abbrev armstrong_of_strong := @DeepWiki.isArmstrongRelation_of_isStrongArmstrong

/-- **Theorem 5.1** (§5.1, p.137): for every set of functional dependencies over `Ω` there exists a
strong Armstrong relation — Fagin's direct product `⊗_Z r_Z` of the two-tuple factors. -/
abbrev thm_5_1 := @DeepWiki.exists_strongArmstrong

end DeepWiki.Rdb
