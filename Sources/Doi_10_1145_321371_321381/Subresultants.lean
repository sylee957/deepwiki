import DeepWiki.SymbolicIntegration.Subresultants
import DeepWiki.SymbolicIntegration.SubresultantPRS
import Sources.Doi_10_1145_321371_321381.Source

/-! # Collins subresultant theory — catalog
Pointers to the `DeepWiki.SymbolicIntegration` subresultant machinery formalizing this paper.
The single-division-step **Lemma 1** and its telescoped iterate **Lemma 2** (the engine of the
paper) are formalized; the closed-form **Theorem 1** and the generalized **Lemma 3 / Theorem 2**
(the subresultant-p.r.s. result, = Bronstein's Thm 1.5.3) rest on elementary `(-1)`-exponent
arithmetic over those, and are tracked below.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
Theorem 1(a) (§p.133): `S_{nₖ}(P₁,P₂) = (-1)^σₖ·[∏ᵢ cᵢ^(-δᵢ₋₁(δᵢ-1))]·cₖ^(δₖ₋₁-1)·Pₖ` for a reduced
  p.r.s. [external]: combine the telescoped Lemma 2 (`subresultant_prs_telescope_explicit`) with
  Lemma 1(a) (`subresultant_rem_eq_13`) and reduce the exponent `α ≡ σₖ (mod 2)`.
Theorem 1(b) (§p.133): `S_{n_{k-1}-1}(P₁,P₂) = (-1)^τₖ·[∏ᵢ cᵢ^(-δᵢ₋₁(δᵢ-1))]·Pₖ` for a reduced p.r.s.
  [external]: Lemma 2 + Lemma 1(c) (`subresultant_rem_eq_15`), `β₁ ≡ τₖ (mod 2)`. (= Bronstein Thm 1.5.3,
  the `ηᵢ = 1` content; the `DeepWiki` base case is `subresultant_eq_pseudoRem`.)
Theorem 1(c) (§p.134): `Sⱼ(P₁,P₂) = 0` for `nₖ < j < n_{k-1}-1` (reduced p.r.s.) [external]: Lemma 2 +
  Lemma 1(d) (`subresultant_prs_step_gap`). (The abstract analog is `subresultant_prs_vanish`.)
Corollary 1.1 (§p.134); Corollary 1.2 (§p.135); Corollary 1.3 (§p.135); Corollary 1.4 (§p.135) [external].
Lemma 3 (§p.135): for an *arbitrary* p.r.s. (coefficient choices `eᵢ, fᵢⱼ`), `Pₖ = (-1)^gₖ·[∏ᵢ cᵢ^hᵢₖ]·Sₖ`
  [external]: generalizes Lemma 1 to an arbitrary p.r.s. (eq 2) and iterates.
Theorem 2 (§p.136): the direct subresultant-p.r.s. algorithm [external/infra]: needs the operational form.
-/

namespace DeepWiki.Col

open DeepWiki.SymbolicIntegration

/-- **Lemma 1**, the single-division-step relation (§p.131): for `P_{i+2} = R(Pᵢ,P_{i+1})` the remainder,
the subresultants `Sⱼ(Pᵢ,P_{i+1})` are expressed through `S(P_{i+1},P_{i+2})` and powers of leading
coefficients. The case `0 ≤ j < deg P_{i+2}` — the library's `subresultant_rem_lt` (also Brown–Traub's
Lemma 1, eq 12). -/
abbrev lemma_1 := @subresultant_rem_lt

/-- **Lemma 1(c)** at `j = deg P_{i+1} − 1` (§p.131): `S_{γ-1} = (-1)^…·(lc)^…·P_{i+2}`. The library's
`subresultant_rem_eq_15`. -/
abbrev lemma_1_top := @subresultant_rem_eq_15

/-- **Lemma 1(a)** at `j = deg P_{i+2}` (§p.131): the regular-index value. The library's
`subresultant_rem_eq_13`. -/
abbrev lemma_1_reg := @subresultant_rem_eq_13

/-- **Lemma 1(d)**, the vanishing (gap) subresultants (§p.131): `Sⱼ = 0` for the defective range.
The library's `subresultant_rem_eq_14`. -/
abbrev lemma_1_gap := @subresultant_rem_eq_14

/-- **Lemma 2**, the telescoped iterate of Lemma 1 (§p.132): the exact-constant relation between
`Sⱼ(P₁,P₂)` and `Sⱼ(Pᵣ,P_{r+1})` along the p.r.s. The library's `subresultant_prs_telescope_explicit`
(stated for an abstract PRS with coefficients `αₗ, βₗ`; Collins specializes to the reduced p.r.s.). -/
abbrev lemma_2 := @subresultant_prs_telescope_explicit

end DeepWiki.Col
