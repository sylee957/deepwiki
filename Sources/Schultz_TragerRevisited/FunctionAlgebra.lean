import DeepWiki.SymbolicIntegration.Engine.FunctionAlgebraIntegrate
import Sources.Schultz_TragerRevisited.Source

/-! # Schultz §7.1 (function algebras / zero divisors) — catalog
Pointers to the `DeepWiki.SymbolicIntegration` machinery for integrating over a **reducible** curve — a
function algebra (étale algebra with zero divisors, Schultz Def 7.1) — removing the irreducible-curve
caveat: the derivation kills the CRT idempotent indicators, so the component integrals recombine into
`D(∫f) = f` over a curve with zero divisors.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized) -/

namespace DeepWiki.Sch

open DeepWiki.SymbolicIntegration

/-- **§7.1 keystone — a derivation kills an idempotent** (the CRT indicators are constants): for any
`Derivation R Q Q` and idempotent `e` (`e*e = e`), `D e = 0`. The engine of the function-algebra
soundness (the partition-of-unity indicators pass through `D` as constants). The library's
`FunctionAlgebra.derivation_idempotent_eq_zero`. -/
abbrev derivation_idempotent_eq_zero := @FunctionAlgebra.derivation_idempotent_eq_zero

/-- **§7.2 recombination integrator** (combining the component-wise results using the indicator
functions): the recombined integral `F = Σᵢ eᵢ·Fᵢ` over a function algebra `K(x)[y]/(T)`, from the CRT
indicators `es = [eᵢ]` and per-component integrals `Fs = [Fᵢ]`. The library's
`DensePoly.afIntegrateFunctionAlgebra`. -/
abbrev afIntegrateFunctionAlgebra := @DensePoly.afIntegrateFunctionAlgebra

/-- **★ §7.1–7.2 zero-divisor soundness** `D(∫f) = f` over a REDUCIBLE curve (irreducible-curve caveat
removed): for a separable (possibly reducible) curve `T` with CRT idempotent indicators forming a
partition of unity and component integrals each per-component sound, the recombined integral
differentiates to the integrand in the carrier quotient. The library's
`DensePoly.afIntegrateFunctionAlgebra_sound`. -/
abbrev afIntegrateFunctionAlgebra_sound := @DensePoly.afIntegrateFunctionAlgebra_sound

end DeepWiki.Sch
