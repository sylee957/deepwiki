import DeepWiki.Algebra.SubresultantSpec
import Sources.Doi_10_1007_b102438.Source

/-! # Geddes–Czapor–Labahn §7.3 — subresultants and the PRS theorem (catalog)
Pointers to the `DeepWiki.SymbolicIntegration` subresultant machinery formalizing §7.3. The
`j`-th subresultant is the determinant polynomial of Definition 7.3 (= Bronstein's Definition
1.4.2); Lemma 7.1 relates the subresultants of `(A,B)` to those of `(B, rem(A,B))`, the engine of
the Fundamental Theorem of PRS (Theorem 7.4). The library proves both halves of Lemma 7.1 (the
scaling-free row reduction and the swap-with-sign) and the degree-padding correction, assembling
its case `0 ≤ j < deg(rem)`.

## NOT YET FORMALIZED
- Theorem 7.4 [research]: the degenerate cases `j = k`, `k < j < n-1`, `j = n-1` of the Fundamental
  Theorem of PRS (where the reduced determinant is upper-triangular), and the full PRS iteration. -/

namespace DeepWiki.Gcl

open DeepWiki.SymbolicIntegration

/-- **Definition 7.3** (§7.3): the `j`-th subresultant `Sⱼ(A,B)` of `A` (degree `n`) and `B`
(degree `m`) — the polynomial `∑_{i=0}^{j} det(ⱼSᵢ)·xⁱ` built from the Sylvester matrix. The
library's `subresultant`. -/
noncomputable abbrev def_7_3 := @subresultant

/-- **Equation 7.12** (§7.3): the single polynomial-column determinant form of the subresultant —
`Sⱼ(A,B)` is the determinant of the matrix whose last column carries the shifted copies of `A` and
`B` as polynomial entries. The library's `subresultant_eq_det_polyCol`. -/
abbrev eq_7_12 := @subresultant_eq_det_polyCol

/-- **Lemma 7.1** (§7.3, p.292), swap-with-sign half: `Sⱼ(A,B) = (-1)^((m-j)(n-j))·Sⱼ(B,A)`. The
library's `subresultant_swap`. -/
abbrev lemma_7_1_swap := @subresultant_swap

/-- **Lemma 7.1** (§7.3, p.292), row-reduction half: subresultants are invariant under
`A ↦ A + B·p` — `Sⱼ(A + B·p, B) = Sⱼ(A,B)`. The library's `subresultant_add_mul`. -/
abbrev lemma_7_1_reduce := @subresultant_add_mul

/-- **Lemma 7.1** (§7.3, p.292), Euclidean-step engine: for a division step `A = rem + B·Q`,
`Sⱼ(A,B) = (-1)^((m-j)(n-j))·Sⱼ(B,rem)`. The library's `subresultant_rem`. -/
abbrev lemma_7_1_engine := @subresultant_rem

/-- **Lemma 7.1** (§7.3, p.292), case `0 ≤ j < deg(rem)`: the full Euclidean-step relation with the
leading-coefficient correction — `Sⱼ(A,B) = (-1)^((m-j)(n-j))·(lc B)^(n-k)·Sⱼ(B,rem)` at `rem`'s
true degree `k`. The library's `subresultant_rem_lt`. -/
abbrev lemma_7_1 := @subresultant_rem_lt

end DeepWiki.Gcl
