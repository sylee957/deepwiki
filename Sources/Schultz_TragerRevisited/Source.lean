/-! # Source (manuscript): Trager's Algorithm for Integration of Algebraic Functions Revisited
Daniel Schultz's manuscript filling in the gaps of Trager's algorithm for deciding elementary
integrability of algebraic functions, with a partial Mathematica implementation and several
extensions (remedies for points of failure; the zero-divisor / function-algebra case). The
`DeepWiki.SymbolicIntegration` library takes from it: the §4.3 Hermite degree bound (eq.4.9), the
§7.1 function-algebra (zero-divisor) integration, and the §4 general-curve / infinite-places decision.

**No DOI.** This is an unpublished manuscript (typeset 2016; references the Axiom computer-algebra
wiki), with no journal or DOI. The catalog folder is named by a descriptive slug
(`Schultz_TragerRevisited`) rather than a sanitized DOI, per the no-stable-identifier convention
(analogous to the Trager-thesis `Hdl_…` folder, but no DSpace handle exists). The author's short slug is
the declaration namespace (`DeepWiki.Sch`); the §/page of each cataloged item lives in the catalog
docstrings, never in the library. -/

namespace DeepWiki.Sch

/-- No DOI: unpublished manuscript (no journal/DOI; typeset 2016). The descriptive slug is the stable
identifier used for the catalog folder. -/
def doi : Option String := none

/-- Title of the source manuscript. -/
def title : String := "Trager's Algorithm for Integration of Algebraic Functions Revisited"

/-- Publication reference of the source manuscript. -/
def reference : String := "Unpublished manuscript (no DOI), 2016"

/-- Author of the source manuscript. -/
def authors : List String := ["Daniel Schultz"]

end DeepWiki.Sch
