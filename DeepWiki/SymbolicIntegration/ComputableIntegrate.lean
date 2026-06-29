import DeepWiki.SymbolicIntegration.GenericPolyEngine

/-! # Horner polynomial evaluation `cevalG`
`cevalG p c = p(c)` over a `CField` — the generic Horner evaluation of a dense `CPolyG` at a field
point, used by the Rothstein–Trager rational-residue root scan.

This file formerly held the historical ℚ(x)-only `cIntegrate` / `cIntegrateReduced` capstone (Bronstein
Ch. 5, assembled). That pair was **superseded** by the generic tower integrators `cIntegrateGFull` /
`cIntegrateReducedG` (and the unified driver), with the call graph confirming nothing but their own
examples depended on them, so it was removed — only the reusable `cevalG` helper remains here. -/

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Horner evaluation** `cevalG p c = p(c)`: evaluate the dense coefficient list `p` (index = degree,
low→high) at `c ∈ α` by Horner's rule (`p₀ + c·(p₁ + c·(…))`). Generic over `[CField α]`. -/
def cevalG (p : CPolyG α) (c : α) : α :=
  (p : List α).foldr (fun coeff acc => CField.add coeff (CField.mul c acc)) CField.zero

end CPolyG

end DeepWiki.SymbolicIntegration
