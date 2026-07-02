import DeepWiki.SymbolicIntegration.Computable.Tower.WellFounded

/-! # Shared hyperexponential tower example data

Common `QFunNZG ℚ` constants used by hyperexponential `native_decide` examples and tower-reduction demos.
-/

namespace DeepWiki.SymbolicIntegration

open Compute

/-- The base field `NLvl1 = QFunNZG ℚ = ℚ(x)` used by hyperexponential tower examples. -/
abbrev NLvl1 : Type := QFunNZG ℚ

/-- The base variable `x ∈ NLvl1 = ℚ(x)`, represented as the fraction `x/1`. -/
def nLvl1X : NLvl1 := ⟨([CField.zero, CField.one], [CField.one]), by native_decide⟩

/-- The base value `x² ∈ NLvl1 = ℚ(x)`, represented as `x * x`. -/
def nLvl1XSq : NLvl1 := CField.mul nLvl1X nLvl1X

/-- The base value `2x ∈ NLvl1 = ℚ(x)`. -/
def nLvl1TwoX : NLvl1 := CField.mul (CField.add CField.one CField.one) nLvl1X

end DeepWiki.SymbolicIntegration
