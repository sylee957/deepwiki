# Rational-Function Partial-Fraction Reorg

## Target module

Move the generic rational-function partial-fraction API into the core
polynomial/rational-function support file:

- `DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncFractions`

Delete the now-empty consumer-oriented module:

- `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.Diophantine`

## Declarations to move

- `ratFunc_partialFraction_coprime`
- `ratFunc_partialFraction_prod`

## `wiki rdeps` impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.ratFunc_partialFraction_prod --depth 2`
reported direct users in:

- `RationalIntegrationAlgorithms.Hermite`
- `Sources.Doi_10_1007_b138171.Chapter2`

and downstream use through:

- `RationalIntegrationAlgorithms.PolynomialPart`
- the Chapter 2 Hermite catalog alias.

## Unify list

- `RationalIntegrationAlgorithms.Hermite` should import the core
  rational-function fractions module plus `HermitePower`.
- `RationalIntegrationAlgorithms` should no longer import the deleted
  Diophantine wrapper.
- The theorem names and statements remain unchanged.

## Steps

1. Add the partial-fraction theorems to `Core/Polynomial/RatFuncFractions.lean`.
2. Remove `RationalIntegrationAlgorithms/Diophantine.lean`.
3. Update the Hermite and rational-algorithm aggregator imports.
4. Gate the core module, Hermite, the Chapter 2 catalog, and the full library.
