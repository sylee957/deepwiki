import DeepWiki.SymbolicIntegration.SubresultantPRS
import Sources.Doi_10_1007_978_3_7091_7551_4_9.Source

/-! # Loos subresultant-PRS theory — catalog
Pointers to the `DeepWiki.SymbolicIntegration` machinery formalizing Loos's subresultant chain ↔ p.r.s.
correspondence (Habicht's Theorem, the Subresultant Theorem). These are the engine of the
Rothstein–Trager / Lazard–Rioboo–Trager logarithmic-part algorithms and of Bronstein's Thm 2.5.1. -/

namespace DeepWiki.Loos

open DeepWiki.SymbolicIntegration

/-- **Habicht's Theorem** (the telescope form): each subresultant relates to its chain neighbours as an
iterated remainder up to similarity — `subresultant_prs_telescope` / `_explicit` over the abstract p.r.s.,
with the single-step `subresultant_prs_similar`. -/
abbrev habicht_telescope := @subresultant_prs_telescope

/-- **Habicht's Theorem** (explicit similarity coefficients). -/
abbrev habicht_telescope_explicit := @subresultant_prs_telescope_explicit

/-- **Subresultant Theorem** (9), the gap/vanishing: subresultants between a regular and a defective
element vanish — `subresultant_prs_vanish` / `subresultant_prs_gap_zero`. -/
abbrev subresultant_theorem_vanish := @subresultant_prs_vanish

/-- **Subresultant Theorem** (10), the defective-element value `R_{j+1}^{j−r}·S_r = lc(S_j)^{j−r}·S_j` —
`subresultant_prs_defective_eq`. -/
abbrev subresultant_theorem_defective := @subresultant_prs_defective_eq

/-- The subresultant ↔ p.r.s.-element correspondence (a subresultant is similar to the p.r.s. element of
the same degree): `subresultant_prs_similar_elt` / `_top`. -/
abbrev subresultant_prs_correspondence := @subresultant_prs_similar_elt

/-- The subresultant as a pseudo-remainder (`subresultant_eq_pseudoRem`) and the normal/closed forms
(`subresultant_prs_normal_eq`, `subresultant_prs_closed_top`). -/
abbrev subresultant_pseudoRem := @subresultant_eq_pseudoRem

/- ## NOT YET FORMALIZED (subtractive — delete each item once formalized)
The subresultant ↔ gcd connection that Bronstein's **Theorem 2.5.1** (Lazard–Rioboo–Trager correctness)
needs: the subresultant of `x`-degree `i = deg(gcd(A,B))` is *similar to* `gcd(A, B)` (the last nonzero
p.r.s. element), obtained from `subresultant_prs_correspondence` + `IsPRS.isSimilar_gcd` (Thm 1.5.1) with
the degree/index bookkeeping; and its degree-preserving *specialization* (`t ↦ α`) connecting LRT's
`lrtSubresultant A D i` at a residue `α` to Rothstein–Trager's `gcd(D, A−αD')` (using
`lrtSubresultant_eval` for the specialization and `thm_2_4_1_ii` for `deg gcd(D, A−αD') = i`). -/

end DeepWiki.Loos
