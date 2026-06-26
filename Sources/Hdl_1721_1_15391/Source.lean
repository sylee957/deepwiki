/-! # Source (thesis): Integration of Algebraic Functions
Barry M. Trager's MIT PhD thesis (1984), the algorithmic theory of integrating *algebraic*
functions in finite terms — the algebraic-extension companion to Risch's transcendental
algorithm. Its **Appendix A** gives the practical reductions for **simple radical extensions**
`F(y)` with `yⁿ = f` (the diagonal derivation, the `Tᵢ` decoupling, the Hermite-style
rational-part cases), and **Chapter 5 §2** the residue resultant (eq. 7) that computes the
constants of the logarithmic part. The `DeepWiki.SymbolicIntegration` library renders these as
**computable** algorithms (the `ComputableRadical*` / `ComputableAlgebraicResidues` files)
validated by `native_decide`.

Metadata for the source thesis that `DeepWiki.SymbolicIntegration` formalizes the algebraic
arc of. Its catalog files (`Sources.Hdl_1721_1_15391.*`) restate each thesis item — named by
its section — and discharge it with the library. The section numbering lives here in the
catalog, never in the library.

**No journal DOI.** A PhD thesis has no DOI; the stable identifier is the MIT DSpace handle
`hdl.handle.net/1721.1/15391`. The catalog folder is named by the sanitized handle
(`Hdl_1721_1_15391`, `/` and `.` becoming `_`, `Hdl_` prefix analogous to the `Doi_`
convention), since Lean module names cannot start with a digit. -/

namespace DeepWiki.Tiaf

/-- MIT DSpace handle of the source thesis (no journal DOI; the stable repository identifier). -/
def handle : String := "1721.1/15391"

/-- Title of the source thesis. -/
def title : String := "Integration of Algebraic Functions"

/-- Publication reference of the source thesis (MIT PhD, Dept. of EECS; advisors Moses, Zippel). -/
def reference : String := "PhD thesis, Massachusetts Institute of Technology, 1984"

/-- Author of the source thesis. -/
def authors : List String := ["Barry M. Trager"]

end DeepWiki.Tiaf
