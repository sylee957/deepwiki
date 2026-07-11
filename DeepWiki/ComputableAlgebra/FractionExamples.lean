import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.FracLinearAlgebraSparse

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

example :
    (match kernelVector 2 [[(CCommRing.one : SparseFrac ℚ), CCommRing.one]] with
      | some [a, b] =>
          CCommRing.isZero (CCommRing.add a CCommRing.one) &&
            CCommRing.isZero (CCommRing.add b (CCommRing.neg CCommRing.one))
      | _ => false) = true := by
  ccompute

end DeepWiki.SymbolicIntegration
