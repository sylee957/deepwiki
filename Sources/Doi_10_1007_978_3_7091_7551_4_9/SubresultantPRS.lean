import DeepWiki.SymbolicIntegration.SubresultantPRS
import DeepWiki.SymbolicIntegration.PseudoRemainderSequence
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

/-- **Subresultant ↔ gcd connection** (the abstract link, Loos's Subresultant Theorem applied to gcd
computation): for a p.r.s. `F` terminating with `F_{m+2} ~ gcd(F₀, F₁)`, the subresultant of degree
`deg F_{m+2} = deg gcd` is similar to `gcd(F₀, F₁)`. The library's `subresultant_isSimilar_gcd`. -/
abbrev subresultant_gcd_connection := @subresultant_isSimilar_gcd

/-- **Subresultant ↔ gcd, concretely**: the abstract connection instantiated on the Euclidean p.r.s.
`euclideanPRS A B` — for `A ≠ 0`, `deg B ≤ deg A`, with last nonzero element `R_k` (`k ≥ 2`), the
subresultant of `A, B` of degree `deg R_k = deg gcd` is similar to `gcd(A, B)`. The library's
`subresultant_euclideanPRS_isSimilar_gcd` (constructs the p.r.s. via `euclideanPRS`, proves termination, and
discharges the degree-decreasing / non-vanishing hypotheses of the abstract connection). -/
abbrev subresultant_euclideanPRS_gcd_connection := @subresultant_euclideanPRS_isSimilar_gcd

/-- **Degree-padding similarity** (Geddes §7.3 Lemma 7.1's leading-coefficient correction, as a similarity):
raising the second polynomial's formal degree from its true degree `k` to `n` scales the subresultant by the
nonzero constant `C(lc B)^(n−k)`, so the two are similar. The library's `isSimilar_subresultant_padding` —
the bridge matching a formal-degree subresultant (the LRT `deg D − 1`) to an actual-degree p.r.s.
computation, which makes Bronstein's Thm 2.5.1(ii) hold for the degenerate residue too. -/
abbrev subresultant_padding_similarity := @isSimilar_subresultant_padding

/- ## NOT YET FORMALIZED (subtractive — delete each item once formalized)
Bronstein's **Theorem 2.5.1** (Lazard–Rioboo–Trager correctness): the mathematical content is COMPLETE — the
concrete subresultant ↔ gcd connection (`subresultant_euclideanPRS_isSimilar_gcd`) and its `t ↦ α`
specialization to *every* residue (`isSimilar_lrtSubresultant_eval_gcd`, the degenerate
`deg(A − α·D') < deg D − 1` handled via `subresultant_padding_similarity`), plus the multiplicity
identification `deg_x R_m = i` (`rootMultiplicity_rtResultant_eq_natDegree_gcd`, via residue-counting in
`ResidueMultiplicity`). Only the algorithm-level bookkeeping capstone remains (discharge the p.r.s.-
termination hypotheses + rewrite the index to `i = rootMultiplicity α R`); tracked in the Bronstein
`Chapter2` §2.5 marker, not here. -/

end DeepWiki.Loos
