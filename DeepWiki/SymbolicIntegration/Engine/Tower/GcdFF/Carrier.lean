import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Bivariate dense carrier for fraction-free tower gcd

The `GBPoly B = List (CPoly B)` (`(B[s])[t]`) carrier used by the denominator-clearing helpers. The
bivariate arithmetic and pseudo-division live in `GcdFFCore` as the generic `gb*Core` operations
(over `GBPolyCore B`, the same `List (CPoly B)`); the fraction-free gcd correctness is proven there.
-/

namespace DeepWiki.SymbolicIntegration

/-! ### The generic bivariate carrier `GBPoly B = List (CPoly B)` (`(B[s])[t]`) -/

/-- Generic bivariate dense carrier `GBPoly B := List (CPoly B)`: a `t`-polynomial with coefficients in
`CPoly B = B[s]` (index = `t`-degree, low→high). -/
abbrev GBPoly (B : Type*) [CField B] := List (CPoly B)

end DeepWiki.SymbolicIntegration
