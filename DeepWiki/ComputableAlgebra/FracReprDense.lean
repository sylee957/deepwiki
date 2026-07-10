import DeepWiki.ComputableAlgebra.FracRepr

/-! # Dense computable-fraction representation

`DenseFrac α` is the `CFrac` specialization whose numerator and denominator use `DensePoly α`. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Fractions represented by dense numerator and denominator polynomials. -/
abbrev DenseFrac (α : Type u) [CField α] := PolyFrac DensePoly α

end DeepWiki.SymbolicIntegration
