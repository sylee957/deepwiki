import DeepWiki.SymbolicIntegration.Computable.GenericPolyEngine

/-! # Horner polynomial evaluation `cevalG`
`cevalG p c = p(c)` over a `CField` — generic Horner evaluation of a dense `CPolyG` at a field
point, used by residue-root scans and algebraic evaluation helpers. -/

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-- Horner evaluation `cevalG p c = p(c)` for a dense coefficient list, low degree first. -/
def cevalG (p : CPolyG α) (c : α) : α :=
  (p : List α).foldr (fun coeff acc => CField.add coeff (CField.mul c acc)) CField.zero

end CPolyG

end DeepWiki.SymbolicIntegration
