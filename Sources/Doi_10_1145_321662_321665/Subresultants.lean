import DeepWiki.SymbolicIntegration.Subresultants
import Sources.Doi_10_1145_321662_321665.Source

/-! # Brown–Traub subresultant theory — catalog
Pointers to the `DeepWiki.SymbolicIntegration` subresultant machinery formalizing this paper's
**Lemma 1** (§4, p.509) — the single-division-step relation between the subresultants of `(F,G)`
and `(G,H)` for `F + B·G = H`. Equation (12) (the case `0 ≤ j < deg H`) is fully proved; the
remaining equations of Lemma 1 and the Fundamental Theorem are tracked below.

## NOT YET FORMALIZED
- Lemma 1, equation (13) [research]: `Sη(F,G) = (-1)^((φ-η)(γ-η))·g₀^(φ-η)·h₀^(γ-η-1)·H` (`j = deg H`).
- Lemma 1, equation (14) [research]: `Sⱼ(F,G) = 0` for `deg H < j < deg G - 1`.
- Lemma 2 [research]: the subresultant chain of a full PRS.
- Fundamental Theorem [research]: each `Sⱼ(F₁,F₂)` (`0 ≤ j < n₂`) is similar to some `Fᵢ` or zero. -/

namespace DeepWiki.Btr

open DeepWiki.SymbolicIntegration

/-- **Lemma 1**, equation (12) (§4, p.509): for `F + B·G = H` with `deg F ≥ deg G > deg H`,
`Sⱼ(F,G) = (-1)^((φ-j)(γ-j))·(lc G)^(φ-η)·Sⱼ(G,H)` for `0 ≤ j < deg H`. The library's
`subresultant_rem_lt` (with `F = A`, `G = B`, `H = Rem`, `B = Q`). -/
abbrev lemma_1_eq_12 := @subresultant_rem_lt

/-- **Lemma 1**, equation (15) (§4, p.509): for `F + B·G = H` with `deg F ≥ deg G > deg H`,
`S_{γ-1}(F,G) = (-1)^(φ-γ+1)·(lc G)^(φ-γ+1)·H` (`j = deg G − 1`) — the `(deg G−1)`-th subresultant is
the remainder `H` up to sign and a power of `lc G`. The library's `subresultant_rem_eq_15`
(`F = A`, `G = B`, `H = Rem`, `B = Q`, `φ = deg A`, `γ = deg B`). -/
abbrev lemma_1_eq_15 := @subresultant_rem_eq_15

end DeepWiki.Btr
