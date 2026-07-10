import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # Shared hyperexponential tower example data

Common `CFrac ℚ` constants used by hyperexponential `native_decide` examples and tower-reduction demos.
-/

namespace DeepWiki.SymbolicIntegration


/-- The base field `NLvl1 = CFrac ℚ = ℚ(x)` used by hyperexponential tower examples. -/
abbrev NLvl1 : Type := CFrac ℚ

/-- The base variable `x ∈ NLvl1 = ℚ(x)`, represented as the fraction `x/1`. -/
def nLvl1X : NLvl1 := CFrac.ofPoly [CCommRing.zero, CCommRing.one]

/-- The base value `x² ∈ NLvl1 = ℚ(x)`, represented as `x * x`. -/
def nLvl1XSq : NLvl1 := CCommRing.mul nLvl1X nLvl1X

/-- The base value `2x ∈ NLvl1 = ℚ(x)`. -/
def nLvl1TwoX : NLvl1 := CCommRing.mul (CCommRing.add CCommRing.one CCommRing.one) nLvl1X

end DeepWiki.SymbolicIntegration
