/-! # Source (book): Synchronization and Linearity
Baccelli–Cohen–Olsder–Quadrat, the foundational monograph on the **(max,plus) / (min,plus)
dioid** and its spectral theory. The `DeepWiki.MinPlusMatrix` chapter formalizes the (min,plus)
dual of its Chapter 3 matrix theory: the eigenvalue as the (min) mean cycle (Thm 3.23), the
Kleene-star finiteness for circuit-sign-definite matrices (Thm 3.20), and the cyclicity of
matrix powers (Thm 3.112, partially — the recurrence realized at a critical vertex).

The 1992 Wiley edition carries no DOI; it is keyed here by ISBN. -/

namespace DeepWiki.Bcoq

/-- ISBN of the source book (1992 Wiley edition; freely re-released by the authors). -/
def isbn : String := "0-471-93609-X"

/-- Title of the source book. -/
def title : String := "Synchronization and Linearity: An Algebra for Discrete Event Systems"

/-- Publication reference of the source book. -/
def reference : String := "Wiley, 1992 (ISBN 0-471-93609-X); freely re-released by the authors"

/-- Authors of the source book. -/
def authors : List String :=
  ["François Baccelli", "Guy Cohen", "Geert Jan Olsder", "Jean-Pierre Quadrat"]

end DeepWiki.Bcoq
