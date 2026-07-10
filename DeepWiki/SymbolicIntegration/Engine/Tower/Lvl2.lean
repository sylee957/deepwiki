import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant

/-! # The level-2 tower carrier `Lvl2 = DenseFrac (DenseFrac ℚ) ≅ ℚ(x)(t₁)`
The concrete ℚ tower at depth 2 (`DensePoly Lvl2 = ℚ(x)(t₁)[t₂]`), a shared readable alias used across the
level-2 tower examples, benchmarks, and integration tests. The generic fraction field `CFrac` itself
lives in `ComputableAlgebra.Fraction`; the fuel-free resultant/gcd engine (`FuelFreeResultant`) is
re-exported here as part of the level-2 API surface. -/

namespace DeepWiki.SymbolicIntegration

/-- Tower level 2: `Lvl2 = DenseFrac (DenseFrac ℚ)`, the field ℚ(x)(t₁); `DensePoly Lvl2 = ℚ(x)(t₁)[t₂]`. -/
abbrev Lvl2 : Type := DenseFrac (DenseFrac ℚ)

end DeepWiki.SymbolicIntegration
