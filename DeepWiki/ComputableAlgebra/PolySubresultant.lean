import DeepWiki.ComputableAlgebra.PolyEngine

/-! # Representation-selected polynomial subresultants

`CPolySubresultant` selects an executable subresultant algorithm for a computable polynomial
representation. Its denotation law lives with the abstract subresultant theory in SymbolicIntegration.
-/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Executable subresultant polynomial selected by a computable polynomial representation. -/
class CPolySubresultant (P : Type u → Type u) [CPoly P] where
  /-- Compute the `j`-th subresultant at the supplied formal degrees `n` and `m`. -/
  compute : {α : Type u} → [CField α] → P α → P α → ℕ → ℕ → ℕ → P α

end DeepWiki.SymbolicIntegration
