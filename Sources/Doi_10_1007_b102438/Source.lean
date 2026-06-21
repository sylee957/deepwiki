/-! # Source (book): Algorithms for Computer Algebra
The standard computer-algebra textbook. Bronstein's *Symbolic Integration I* defers the
subresultant↔PRS similarity theory (Theorems 1.5.2/1.5.3, which it states without proof) to
this book's §7.3 — the **Fundamental Theorem of Polynomial Remainder Sequences** (its Theorem
7.4, built on Lemma 7.1). The catalog files here point at the `DeepWiki.SymbolicIntegration`
subresultant machinery formalizing §7.3 (the determinant subresultant of Definition 7.3, and the
Euclidean-step relation of Lemma 7.1). The book in turn follows Brown–Traub
(DOI 10.1145/321662.321665) for the proof. -/

namespace DeepWiki.Gcl

/-- DOI of the source book. -/
def doi : String := "10.1007/b102438"

/-- Title of the source book. -/
def title : String := "Algorithms for Computer Algebra"

/-- Publication reference of the source book. -/
def reference : String := "Kluwer Academic Publishers, Boston, 1992"

/-- Authors of the source book. -/
def authors : List String := ["Keith O. Geddes", "Stephen R. Czapor", "George Labahn"]

end DeepWiki.Gcl
