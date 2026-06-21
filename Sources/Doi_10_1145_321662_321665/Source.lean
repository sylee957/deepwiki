/-! # Source (paper): On Euclid's Algorithm and the Theory of Subresultants
The original elementary treatment of the subresultant theory and its relationship to the
polynomial remainder sequence. Bronstein's *Symbolic Integration I* and Geddes–Czapor–Labahn's
§7.3 (DOI 10.1007/b102438) both rest on this paper's results; Geddes' Lemma 7.1 is this paper's
**Lemma 1** (the single-division-step subresultant relation). The catalog file here points at the
`DeepWiki.SymbolicIntegration` subresultant machinery formalizing Lemma 1. -/

namespace DeepWiki.Bt

/-- DOI of the source paper. -/
def doi : String := "10.1145/321662.321665"

/-- Title of the source paper. -/
def title : String := "On Euclid's Algorithm and the Theory of Subresultants"

/-- Journal reference of the source paper. -/
def reference : String := "Journal of the ACM 18(4):505–514, 1971"

/-- Authors of the source paper. -/
def authors : List String := ["W. S. Brown", "J. F. Traub"]

end DeepWiki.Bt
