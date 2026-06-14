/-! # Source: Deterministic Network Calculus
Metadata for the source book that the `DeepWiki.NetworkCalculus` library
formalizes. Its catalog files (`Sources.Dnc.*`) restate each book item —
named by its book number — and discharge it with the library. -/

namespace DeepWiki.Dnc

/-- DOI of the source book (verify against the publisher record). -/
def doi : String := "10.1002/9781119440284"

/-- Title of the source book. -/
def title : String :=
  "Deterministic Network Calculus: From Theory to Practical Implementation"

/-- Authors of the source book. -/
def authors : List String :=
  ["Anne Bouillard", "Marc Boyer", "Euriell Le Corronc"]

end DeepWiki.Dnc
