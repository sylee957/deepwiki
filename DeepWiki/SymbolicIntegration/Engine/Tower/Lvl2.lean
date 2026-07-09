import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.SymbolicIntegration.Engine.ConcreteCoherence
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant

/-! # The level-2 tower carrier `Lvl2 = CFrac (CFrac ℚ) ≅ ℚ(x)(t₁)`
The concrete ℚ tower at depth 2 (`CPoly Lvl2 = ℚ(x)(t₁)[t₂]`), a shared readable alias used across the
level-2 tower examples, benchmarks, and integration tests. The generic fraction field `CFrac` itself
lives in `ComputableAlgebra.Fraction`; the concrete-ℚ coherence (`ConcreteCoherence`) and the
fuel-free resultant/gcd engine (`FuelFreeResultant`) are re-exported here as the level-2 API surface. -/

namespace DeepWiki.SymbolicIntegration

/-- Tower level 2: `Lvl2 = CFrac (CFrac ℚ)`, the field ℚ(x)(t₁); `CPoly Lvl2 = ℚ(x)(t₁)[t₂]`. -/
abbrev Lvl2 : Type := CFrac (CFrac ℚ)

end DeepWiki.SymbolicIntegration
