/-! # Source (book): Symbolic Integration I — Transcendental Functions
Manuel Bronstein's monograph on the algorithmic theory of integration in finite terms (the
Risch algorithm) over differential fields. The `DeepWiki.SymbolicIntegration` library
formalizes the differential-algebra foundation (Ritt's program: derivations as purely
algebraic objects) and the integration algorithms; several of the latter are procedural and
get an operational-semantics treatment.

Metadata for the source book that `DeepWiki.SymbolicIntegration` formalizes. Its catalog files
(`Sources.Doi_10_1007_b138171.*`) restate each book item — named by its book number — and
discharge it with the library. The book numbering lives here in the catalog, never in the
library. -/

namespace DeepWiki.Si

/-- DOI of the source book (Springer, *Algorithms and Computation in Mathematics* Vol. 1,
2nd ed., 2005). -/
def doi : String := "10.1007/b138171"

/-- Title of the source book. -/
def title : String := "Symbolic Integration I: Transcendental Functions"

/-- Publication reference of the source book (2nd ed.; ISBN 3-540-21493-3). -/
def reference : String := "Springer, 2nd edition, 2005 (ISBN 3-540-21493-3)"

/-- Author of the source book. -/
def authors : List String := ["Manuel Bronstein"]

end DeepWiki.Si
