import DeepWiki.ComputableAlgebra.FracRepr

/-! # Sparse computable-fraction representation

`SparseFrac α` is the `CFrac` specialization whose numerator and denominator use
`CPoly.SparsePoly α`. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Fractions represented by sparse numerator and denominator polynomials. -/
abbrev SparseFrac (α : Type u) [CField α] := PolyFrac CPoly.SparsePoly α

example :
    let num : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, 1), (4, 7)]
    let den : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, 1)]
    CPoly.coeff (CFrac.num (CFrac.ofFraction (F := SparseFrac) num den (by native_decide))) 4 = 7 := by
  native_decide

end DeepWiki.SymbolicIntegration
