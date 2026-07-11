import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.FracLinearAlgebra
import DeepWiki.ComputableAlgebra.FracReprDense
import DeepWiki.ComputableAlgebra.FracReprSparse

/-! # Validation for computable fractions

Dense and sparse fraction validation through the representation-independent `CFrac` interfaces. -/

namespace DeepWiki.SymbolicIntegration

example :
    CFieldSpec.toK (CFrac.ofPoly (F := SparseFrac)
      (CPoly.SparsePoly.ofList [(0, 1), (1, 2)] : CPoly.SparsePoly ℚ))
      = CFrac.am ℚ (CPoly.toPoly (CPoly.SparsePoly.ofList [(0, 1), (1, 2)] : CPoly.SparsePoly ℚ)) := by
  exact CFrac.toRatFunc_ofPoly _

example : Nonempty (CLinearSolve (DenseFrac ℚ)) := ⟨inferInstance⟩

example : Nonempty (CLinearSolve (SparseFrac ℚ)) := ⟨inferInstance⟩

end DeepWiki.SymbolicIntegration
