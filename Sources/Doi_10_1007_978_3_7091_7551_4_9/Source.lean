/-! # Source (paper): Generalized Polynomial Remainder Sequences
Rüdiger Loos's chapter — the canonical reference for the **subresultant-PRS theory** that underlies the
Rothstein–Trager and Lazard–Rioboo–Trager logarithmic-part algorithms (Bronstein's reference [62]).
Following Habicht, it relates the subresultant *chain* `S_{n+1}=A, S_n=B, …, S_0` to the polynomial
remainder sequence:

* **Habicht's Theorem** — `R_{j+1}^{2(j−r)}·S_r = sres_r(S_{j+1}, S_j)` and `R_{j+1}²·S_{j−1} =
  prem(S_{j+1}, S_j)` (each `k`-th subresultant is the `(n−k)`-th iterated remainder up to similarity).
* **Subresultant Theorem** — the gap structure: if `S_{j+1}` is regular and `S_j` defective of degree
  `r < j`, then `S_{j−1} = … = S_{r+1} = 0`, `R_{j+1}^{j−r}·S_r = lc(S_j)^{j−r}·S_j`, and
  `(−1)^{j−r}·R_{j+1}^{j−r+2}·S_{r−1} = prem(S_{j+1}, S_j)`.

The `DeepWiki.SymbolicIntegration` development formalizes much of this chain (the telescope, the
subresultant ↔ p.r.s.-element correspondence, the gap/defective structure). This catalog points at that
machinery; the remaining subresultant ↔ gcd connection (used by Bronstein's Thm 2.5.1, the LRT
correctness) is tracked below. Builds on Collins (DOI 10.1145/321371.321381) and Brown–Traub
(DOI 10.1145/321662.321665), both cataloged. -/

namespace DeepWiki.Loos

/-- DOI of the source paper (chapter in *Computer Algebra: Symbolic and Algebraic Computation*,
Computing Supplementum 4). -/
def doi : String := "10.1007/978-3-7091-7551-4_9"

/-- Title of the source paper. -/
def title : String := "Generalized Polynomial Remainder Sequences"

/-- Reference of the source paper. -/
def reference : String :=
  "In B. Buchberger, G.E. Collins, R. Loos (eds.), Computer Algebra: Symbolic and Algebraic " ++
  "Computation, Computing Supplementum 4, Springer, 1982, pp. 115–137"

/-- Author of the source paper. -/
def authors : List String := ["Rüdiger Loos"]

end DeepWiki.Loos
