# Polynomial Diophantine Solver Reorg

## Target module

Move the generic extended-Euclidean polynomial Diophantine solver API from the
consumer-oriented rational-integration algorithm layer into:

- `DeepWiki.SymbolicIntegration.Core.Polynomial.Diophantine`

Keep rational-function partial-fraction theorems in:

- `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.Diophantine`

## Declarations to move

- `diophantineSolve`
- `diophantineSolve_spec`
- `diophantineSolveReduced`
- `diophantineSolveReduced_spec`
- `diophantineSolveReduced_fst_degree_lt`

Declarations intentionally staying in the rational-integration layer:

- `ratFunc_partialFraction_coprime`
- `ratFunc_partialFraction_prod`

## `wiki rdeps` impact

`scripts/wiki rdeps diophantineSolve --depth 1` reported direct users in:

- `LaurentCoefficients.Cofactors.Basic`
- `Core.Polynomial.LocalPrincipalParts`
- `RationalIntegrationAlgorithms.RothsteinTrager.CzichowskiNormalPosition`
- `RationalIntegrationAlgorithms.Diophantine`
- `Compute.Diophantine`
- source aliases in `Sources.Doi_10_1007_b138171.Chapter2`

## Unify list

- Core/local-principal and Laurent cofactor users should import the new core
  polynomial Diophantine module directly.
- Rational-integration algorithm files that need the reduced solver should also
  import the new core module directly.
- The old `RationalIntegrationAlgorithms.Diophantine` module remains as the
  partial-fraction module and imports the new core solver.
- `Core.Polynomial` aggregator imports the new module.

## Steps

1. Add `Core/Polynomial/Diophantine.lean` with the solver declarations unchanged.
2. Remove those declarations from `RationalIntegrationAlgorithms/Diophantine.lean`,
   leaving partial-fraction theorems in place.
3. Update imports for direct solver users.
4. Gate the new core module, direct downstream users, and the full library.
