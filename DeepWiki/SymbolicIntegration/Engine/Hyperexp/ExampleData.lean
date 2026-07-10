import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # Shared hyperexponential tower example data

Common `CFrac ℚ` constants used by hyperexponential `native_decide` examples and tower-reduction demos.
-/

namespace DeepWiki.SymbolicIntegration

/-- The base variable `x ∈ CFrac ℚ = ℚ(x)`, represented as the fraction `x/1`. -/
def nLvl1X : CFrac ℚ := CFrac.ofPoly [CCommRing.zero, CCommRing.one]

/-- The base value `x² ∈ CFrac ℚ = ℚ(x)`, represented as `x * x`. -/
def nLvl1XSq : CFrac ℚ := CCommRing.mul nLvl1X nLvl1X

/-- The base value `2x ∈ CFrac ℚ = ℚ(x)`. -/
def nLvl1TwoX : CFrac ℚ := CCommRing.mul (CCommRing.add CCommRing.one CCommRing.one) nLvl1X

end DeepWiki.SymbolicIntegration
