/-! # Source (paper): Subresultants and Reduced Polynomial Remainder Sequences
George E. Collins' foundational paper relating subresultants to polynomial remainder sequences.
Bronstein's *Symbolic Integration I* cites this paper (ref. [23]) for **Theorem 1.5.3** — the
subresultant-PRS specialization `Sⱼ(A,B) = Rᵢ` (`ηᵢ = 1`). The proof of that result is this paper's
**Theorem 1** (closed form of the subresultants of a reduced p.r.s.) and its generalization **Lemma 3 /
Theorem 2** (the direct subresultant-p.r.s. method) — both built on this paper's **Lemma 1** (the
single-division-step relation, also Brown–Traub's Lemma 1, DOI 10.1145/321662.321665) iterated as
**Lemma 2**. The catalog file here points at the `DeepWiki.SymbolicIntegration` machinery that already
formalizes Lemma 1 and the telescoped Lemma 2, and tracks Theorem 1 / Lemma 3 / Theorem 2. -/

namespace DeepWiki.Col

/-- DOI of the source paper. -/
def doi : String := "10.1145/321371.321381"

/-- Title of the source paper. -/
def title : String := "Subresultants and Reduced Polynomial Remainder Sequences"

/-- Journal reference of the source paper. -/
def reference : String := "Journal of the ACM 14(1):128–142, 1967"

/-- Authors of the source paper. -/
def authors : List String := ["George E. Collins"]

end DeepWiki.Col
