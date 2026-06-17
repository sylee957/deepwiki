/-! # Source (paper): Timing-Based Mutual Exclusion
Reference paper for the correctness framework of timing-based mutual-exclusion
algorithms, to which the Reactive Systems book's Chapter 13 (Fischer's protocol)
defers the correctness theorem. Its catalog files point at the
`DeepWiki.ReactiveSystems` library theorems derived from it. -/

namespace DeepWiki.Ls

/-- DOI of the source paper (Real-Time Systems Symposium 1992, IEEE, pp. 2–11). -/
def doi : String := "10.1109/REAL.1992.242681"

/-- Title of the source paper. -/
def title : String := "Timing-Based Mutual Exclusion"

/-- Authors of the source paper. -/
def authors : List String := ["Nancy A. Lynch", "Nir Shavit"]

end DeepWiki.Ls
