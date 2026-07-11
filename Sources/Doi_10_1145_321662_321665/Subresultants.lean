import DeepWiki.ComputableAlgebra.PolySubresultantSpec
import DeepWiki.SymbolicIntegration.SubresultantPRS
import Sources.Doi_10_1145_321662_321665.Source

/-! # Brown–Traub subresultant theory — catalog
Pointers to the `DeepWiki.SymbolicIntegration` subresultant machinery formalizing this paper's
**Lemma 1** (§4, p.509) — the single-division-step relation between the subresultants of `(F,G)`
and `(G,H)` for `F + B·G = H`. Equation (12) (the case `0 ≤ j < deg H`) is fully proved; the
remaining equations of Lemma 1 and the Fundamental Theorem are tracked below.

## NOT YET FORMALIZED
-/

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

/-- **Lemma 1**, equation (14) (§4, p.509): for `F + B·G = H` with `deg F ≥ deg G > deg H`,
`Sⱼ(F,G) = 0` for `deg H < j < deg G − 1` — the defective ("gap") subresultants vanish. The library's
`subresultant_rem_eq_14`. -/
abbrev lemma_1_eq_14 := @subresultant_rem_eq_14

/-- **Lemma 1**, equation (13) (§4, p.509): for `F + B·G = H` with `deg F ≥ deg G > deg H`,
`S_η(F,G) = (-1)^((φ-η)(γ-η))·(lc G)^(φ-η)·(lc H)^(γ-η-1)·H` (`j = deg H = η`). The library's
`subresultant_rem_eq_13`. -/
abbrev lemma_1_eq_13 := @subresultant_rem_eq_13

/-- **Lemma 2**, equation (21) (§5, p.510): a single PRS division step `α·F_{i-2} = Q·F_{i-1} + β·Fᵢ`
relates consecutive subresultants — `α^(n_{i-1}-j)·Sⱼ(F_{i-2},F_{i-1}) =
(-1)^((n_{i-2}-j)(n_{i-1}-j))·(lc F_{i-1})^(δ_{i-2}+δ_{i-1})·β^(n_{i-1}-j)·Sⱼ(F_{i-1},Fᵢ)` for
`0 ≤ j < nᵢ`. The library's `subresultant_prs_step` (`F_{i-2}=A`, `F_{i-1}=B`, `Fᵢ=C`). -/
abbrev lemma_2_eq_21 := @subresultant_prs_step

/-- **Lemma 2**, equation (22) (§5, p.510): the single PRS step at `j = nᵢ`. `subresultant_prs_step_deg`. -/
abbrev lemma_2_eq_22 := @subresultant_prs_step_deg

/-- **Lemma 2**, equation (23) (§5, p.510): the vanishing single PRS step for `nᵢ < j < nᵢ₋₁−1`.
`subresultant_prs_step_gap`. -/
abbrev lemma_2_eq_23 := @subresultant_prs_step_gap

/-- **Lemma 2**, equation (24) (§5, p.510): the single PRS step at `j = nᵢ₋₁−1`.
`subresultant_prs_step_top`. -/
abbrev lemma_2_eq_24 := @subresultant_prs_step_top

/-- **Fundamental Theorem** (§5, p.510, eqs 30–31): for a PRS `F₁,…,Fₖ`, the subresultant `Sⱼ(F₁,F₂)`
is similar to `Sⱼ(Fₘ,F_{m+1})` for every step `m` (and hence to a later PRS element or zero). The
library's `subresultant_prs_telescope`, telescoping the per-step similarity `subresultant_prs_similar`. -/
abbrev fundamental_theorem := @subresultant_prs_telescope

/-- **Fundamental Theorem, explicit product form** (§5, p.510, eq 30): the exact-constant telescoping —
`Sⱼ(F₀,F₁)·∏ αₗ^(n_{l+1}-j) = Sⱼ(Fₘ,F_{m+1})·∏[(-1)^…·(lc F_{l+1})^…·βₗ^…]`, from which the explicit
`ηᵢ/τᵢ` coefficients (eq 1.9) are read off. The library's `subresultant_prs_telescope_explicit`. -/
abbrev fundamental_theorem_explicit := @subresultant_prs_telescope_explicit

end DeepWiki.Btr
