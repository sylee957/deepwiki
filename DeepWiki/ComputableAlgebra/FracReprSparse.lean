import DeepWiki.ComputableAlgebra.FracRepr
import DeepWiki.ComputableAlgebra.PolyEngine

/-! # Sparse computable-fraction representation

`SparseFrac α` is the `CFrac` specialization whose numerator and denominator use
`CPoly.SparsePoly α`. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Fractions represented by sparse numerator and denominator polynomials. -/
abbrev SparseFrac (α : Type u) [CField α] := PolyFrac CPoly.SparsePoly α

end DeepWiki.SymbolicIntegration
