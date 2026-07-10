# Remove the `Compute` dense-polynomial wrappers — DONE

The concrete `ℚ` computation layer now reuses the canonical `DensePoly` representation and
operations from `DeepWiki.ComputableAlgebra.PolyReprDense`. `LogToAtan.lean` exports
`cnorm`, `cadd`, `cneg`, `csub`, `cscale`, `cshift`, `cmul`, `clead`, `cisZero`, `cdeg`,
`cderiv`, and `cmonic` into `Compute`, preserving existing qualified and unqualified names
without separate wrapper definitions.

## Denotation

`Compute.toPoly` remains as a one-line specialization of `DensePoly.toPoly` to `ℚ[X]`. A
bare export leaves the abstract `CRingSpec.R ℚ` codomain underconstrained at concrete call
sites, while an `abbrev` exposes that ambiguity during simplification. The opaque wrapper
pins the codomain. `Compute.toPoly_eq_dense` is the sole bridge back to the generic
denotation; operation laws are used directly from the `DensePoly.toPolyG_*` family rather
than repeated as concrete `Compute.toPoly_*` specializations.

The fold-over-multiplication theorem was moved to `PolyReprDense.lean` as
`DensePoly.toPolyG_foldl_range_cmulG`, and concrete consumers use it through the same single
denotation bridge.

## Remaining concrete definitions

Only algorithms genuinely specific to the concrete computation remain:

- interpolation algorithms: `cC`, `clagNum`, `cinterpolate`;
- composed entry points and example data such as `logToAtanCompute`, `rtResultantCompute`,
  `csqfreePart`, `cX3m3X`, and `cX2m2`.

The local scalar-power helper was removed in favor of `DensePoly.cfpow`.
Division, gcd, divisibility, and resultant consumers now call the `CPoly` or fuel-free
`DensePoly` APIs directly; no concrete compatibility wrappers remain for those operations.

## Coherence layer

`Engine/ConcreteCoherence.lean` was deleted. Once the concrete operations and denotation
reuse the canonical dense API, its three remaining bridge lemmas had no reverse dependencies
and no longer represented a distinct abstraction boundary. Consumers now import their actual
dependencies directly.

## Verification

The affected `Compute` and `Engine` module closures are checked with `scripts/check.sh`,
followed by the full repository gate.
