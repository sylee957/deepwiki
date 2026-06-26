/-! # Source (paper): Integration of Elementary Functions
Manuel Bronstein's paper (J. Symbolic Computation 9(2):117–173, 1990), the **decision procedure**
for integration in finite terms of an elementary function built up over a *liouvillian* ground
field by algebraic, logarithmic, and exponential extensions — extending Trager's algebraic-function
integration to combined elementary towers. It proves: if integration in finite terms is solvable on
an elementary function field, it is solvable in any algebraic extension with logarithmic or
exponential elements.

Per the project's "double reference" rule, this **per-paper** catalog marks the axis of the
combined elementary-over-algebraic integration arc even though `DeepWiki.SymbolicIntegration` has
not yet formalized any of it — the algebraic arc realized so far (`ComputableRadical*` /
`ComputableAlgebraicResidues`) follows **Trager's thesis** (handle `1721.1/15391`); this paper is
the next axis. Nothing here is an `alias`/`abbrev`; the coverage is the `## NOT YET FORMALIZED`
block in `Sources.Doi_10_1016_S0747_7171_08_80027_2.Coverage`. -/

namespace DeepWiki.Bie

/-- DOI of the source paper (J. Symbolic Computation 9(2):117–173, Elsevier, 1990). -/
def doi : String := "10.1016/S0747-7171(08)80027-2"

/-- Title of the source paper. -/
def title : String := "Integration of Elementary Functions"

/-- Publication reference of the source paper. -/
def reference : String := "Journal of Symbolic Computation 9(2):117-173, 1990"

/-- Author of the source paper. -/
def authors : List String := ["Manuel Bronstein"]

end DeepWiki.Bie
