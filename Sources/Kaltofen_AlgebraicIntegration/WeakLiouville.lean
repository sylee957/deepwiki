import DeepWiki.SymbolicIntegration.LiouvilleStructure
import Sources.Kaltofen_AlgebraicIntegration.Source

/-! # Kaltofen §3 (Weak Liouville Theorem + degree lemmas) — catalog
Pointers to the `DeepWiki.SymbolicIntegration` Liouville-structure machinery formalizing Kaltofen's
**Theorem 3.2** (the Weak Liouville Theorem) and the monomial degree **Lemmas 3.1a/3.1b** that drive its
tower-induction pole analysis.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
Case 2.2 of the Thm 3.2 induction (`θ = exp η`, the transcendental exponential layer) [research]: the
  per-layer Liouville instance `K(exp η)/K` is the one open residual; its local degree engine
  (Lemma 3.1b, `coeff_natDegree_expMonomialDeriv`) is proved, the layer-Liouville statement is not.
-/

namespace DeepWiki.Kal

open DeepWiki.SymbolicIntegration.LiouvilleStructure

/-- **Theorem 3.2 — the Weak Liouville Theorem** (descent form): if `L/F` is an elementary (Liouville)
extension with no new constants and `g ∈ L` has `g′ ∈ F`, then `g′ = v₀′ + Σ cᵢ·vᵢ′/vᵢ` with `vᵢ, v₀ ∈ F`,
`cᵢ ∈ C_F` — Kaltofen's tower induction realized as iterated `IsLiouville.trans`. The library's
`weakLiouville_of_isLiouville`. -/
abbrev thm_3_2 := @weakLiouville_of_isLiouville

/-- **Lemma 3.1a — the log monomial degree drop** (`θ′ ∈ K`, i.e. `θ = log η`): the top coefficient sees
only `K`'s derivation, `(D p).coeff (deg p) = (lc p)′`, so `p(θ)′` has degree `deg p` or `deg p − 1`. The
library's `coeff_natDegree_logMonomialDeriv`. -/
abbrev lemma_3_1a := @coeff_natDegree_logMonomialDeriv

/-- **Lemma 3.1b — the exp monomial is degree-preserving** (`θ′/θ ∈ K`, i.e. `θ = exp η`): the monomial
coupling does not vanish at the top, `(D p).coeff (deg p) = (lc p)′ + c·(deg p)·(lc p)`, so `p(θ)′` keeps
the degree `deg p` (on a non-cancelling top). The library's `coeff_natDegree_expMonomialDeriv`. -/
abbrev lemma_3_1b := @coeff_natDegree_expMonomialDeriv

end DeepWiki.Kal
