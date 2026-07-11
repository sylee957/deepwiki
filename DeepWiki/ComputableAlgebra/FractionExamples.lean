import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.FracLinearAlgebraSparse

/-! # Denotation validation for computable fractions

Sparse fraction validation through the representation-independent `CFrac` denotation bridge. -/

namespace DeepWiki.SymbolicIntegration

example :
    CFieldSpec.toK (CFrac.ofPoly (F := SparseFrac)
      (CPoly.SparsePoly.ofList [(0, 1), (1, 2)] : CPoly.SparsePoly ℚ))
      = CFrac.am ℚ (CPoly.toPoly (CPoly.SparsePoly.ofList [(0, 1), (1, 2)] : CPoly.SparsePoly ℚ)) := by
  exact CFrac.toRatFunc_ofPoly _

end DeepWiki.SymbolicIntegration
