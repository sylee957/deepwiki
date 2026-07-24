import DeepWiki.SymbolicIntegration.Engine.FunctionAlgebraIntegrate.Soundness

/-! # Function-algebra integration examples

Worked checks for `∫y dx` on the reducible curve `(y²−x)(y³−x) = 0`, and checks for the
abstract recombination API. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace DensePoly

/-- The square-root component curve `T₁ = y² − x ∈ ℚ(x)[y]`. -/
def sqrtComponentCurve : DensePoly (DenseFrac ℚ) := [CFrac.ofPoly [0, -1], CCommRing.zero, CCommRing.one]

/-- The square-root component integral `F₁ = (2/3)·x·y`. -/
def sqrtComponentIntegral : DensePoly (DenseFrac ℚ) := [CCommRing.zero, CFrac.ofPoly [0, 2/3]]

/-- The cube-root component curve `T₂ = y³ − x ∈ ℚ(x)[y]`. -/
def cubeRootComponentCurve : DensePoly (DenseFrac ℚ) := [CFrac.ofPoly [0, -1], CCommRing.zero, CCommRing.zero, CCommRing.one]

/-- The cube-root component integral `F₂ = (3/4)·x·y`. -/
def cubeRootComponentIntegral : DensePoly (DenseFrac ℚ) := [CCommRing.zero, CFrac.ofPoly [0, 3/4]]

/-- The integrand `y = [0, 1]` (`CPoly.afBasisElem 1`) of `∫y dx`. -/
def componentIntegrandY : DensePoly (DenseFrac ℚ) := CPoly.afBasisElem 1

/-- Component 1 (`native_decide`): `∫y dx = (2/3)·x·y` on `y² − x = 0`, checked by
`cisZero (afDerivWf (y²−x) F₁ − y)`. -/
theorem sqrtComponentIntegral_deriv :
    cisZero (csub (afDerivWf sqrtComponentCurve sqrtComponentIntegral) componentIntegrandY) = true := by
  native_decide

/-- Component 2 (`native_decide`): `∫y dx = (3/4)·x·y` on `y³ − x = 0`, checked by
`cisZero (afDerivWf (y³−x) F₂ − y)`. -/
theorem cubeRootComponentIntegral_deriv :
    cisZero (csub (afDerivWf cubeRootComponentCurve cubeRootComponentIntegral) componentIntegrandY)
      = true := by
  native_decide

end DensePoly

end DeepWiki.SymbolicIntegration
