/-! # Source: Reactive Systems
Metadata for the source book that the `DeepWiki.ReactiveSystems` library
formalizes. Its catalog files (`Sources.Doi_10_1017_CBO9780511814105.*`) restate each
book item — named by its book number — and discharge it with the library. -/

namespace DeepWiki.Rs

/-- DOI of the source book (verify against the publisher record). -/
def doi : String := "10.1017/CBO9780511814105"

/-- Title of the source book. -/
def title : String :=
  "Reactive Systems: Modelling, Specification and Verification"

/-- Authors of the source book. -/
def authors : List String :=
  ["Luca Aceto", "Anna Ingólfsdóttir", "Kim G. Larsen", "Jiří Srba"]

end DeepWiki.Rs
