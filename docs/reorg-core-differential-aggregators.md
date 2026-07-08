# Core Differential Aggregators Reorg

## Target module

`DeepWiki.SymbolicIntegration.Core.Differential`

## Theme

The root differential aggregator imports every differential support leaf directly.
For random access, the entry points should expose the main conceptual areas:
derivation extension, fraction-field derivations, gcd/special-factor formulas,
implicit-derivative linear factors, differential polynomials, normal/special
transport, polynomial derivative identities, and Wronskians.

## Decls to move

None. This is an aggregator-only reorganization. All declaration meanings and
declaration modules remain unchanged.

## Impact

- Direct users of leaf modules are unchanged.
- The root `Core.Differential` module remains the umbrella import.
- The new aggregators are additive entry points and do not alter the import DAG
  of executable/native-decision code.

## Unify list

- `DeepWiki.SymbolicIntegration.Core.Differential.Derivation`
  - `DerivationBasic`
  - `DerivationExt`
- `DeepWiki.SymbolicIntegration.Core.Differential.FractionDeriv`
  - `PolynomialFractionDeriv`
  - `DiffPolyFractionDeriv`
- `DeepWiki.SymbolicIntegration.Core.Differential.Gcd`
  - `Gcd.Derivative`
  - `Gcd.PrimeFactors`
- Existing aggregators stay as conceptual entry points:
  - `DifferentialPolynomials`
  - `ImplicitDerivLinearFactors`
  - `NormalSpecial`
- Standalone leaves stay direct root imports:
  - `ImplicitDerivDegree`
  - `LinearRootEvaluation`
  - `PolynomialDerivatives`
  - `Wronskian`

## Steps

1. Add `Derivation`, `FractionDeriv`, and `Gcd` aggregators.
2. Replace the flat `Core/Differential.lean` import wall with semantic entry points.
3. Gate `DeepWiki.SymbolicIntegration.Core.Differential`, then full `scripts/check.sh`.
4. Rebuild the wiki graph and commit the pure aggregator split.
