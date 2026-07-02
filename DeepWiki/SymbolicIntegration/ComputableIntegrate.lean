import DeepWiki.SymbolicIntegration.GenericPolyEngine

/-! # Horner polynomial evaluation `cevalG`
`cevalG p c = p(c)` over a `CField` — generic Horner evaluation of a dense `CPolyG` at a field
point, used by the Rothstein–Trager rational-residue root scan. -/

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-- Horner evaluation `cevalG p c = p(c)`: evaluate the dense coefficient list `p` (index = degree,
low→high) at `c ∈ α` by Horner's rule (`p₀ + c·(p₁ + c·(…))`). Generic over `[CField α]`. -/
def cevalG (p : CPolyG α) (c : α) : α :=
  (p : List α).foldr (fun coeff acc => CField.add coeff (CField.mul c acc)) CField.zero

end CPolyG

end DeepWiki.SymbolicIntegration
