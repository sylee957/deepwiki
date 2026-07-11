import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.FracReprSparse

/-! # Representation validation for computable fractions

Sparse fraction examples exercising the representation-independent `CFrac` operations and denotation
bridges. -/

namespace DeepWiki.SymbolicIntegration

example :
    let p : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, 1), (1, 1)]
    CFrac.eval (CFrac.ofPoly (F := SparseFrac) p) 2 = 3 := by
  ccompute

example :
    CFieldSpec.toK (CFrac.ofPoly (F := SparseFrac)
      (CPoly.SparsePoly.ofList [(0, 1), (1, 2)] : CPoly.SparsePoly ℚ))
      = CFrac.am ℚ (CPoly.toPoly (CPoly.SparsePoly.ofList [(0, 1), (1, 2)] : CPoly.SparsePoly ℚ)) := by
  exact CFrac.toRatFunc_ofPoly _

end DeepWiki.SymbolicIntegration
