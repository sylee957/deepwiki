import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # Shared hyperexponential tower example data

Common `DenseFrac ℚ` constants used by hyperexponential `native_decide` examples and tower-reduction demos.
-/

namespace DeepWiki.SymbolicIntegration

/-- The base variable `x ∈ DenseFrac ℚ = ℚ(x)`, represented as the fraction `x/1`. -/
def nLvl1X : DenseFrac ℚ := CFrac.ofPoly [CCommRing.zero, CCommRing.one]

/-- The base value `x² ∈ DenseFrac ℚ = ℚ(x)`, represented as `x * x`. -/
def nLvl1XSq : DenseFrac ℚ := CCommRing.mul nLvl1X nLvl1X

/-- The base value `2x ∈ DenseFrac ℚ = ℚ(x)`. -/
def nLvl1TwoX : DenseFrac ℚ := CCommRing.mul (CCommRing.add CCommRing.one CCommRing.one) nLvl1X

end DeepWiki.SymbolicIntegration
