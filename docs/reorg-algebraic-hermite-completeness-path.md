# Algebraic Hermite Completeness Path Reorg

## Target module

`DeepWiki.SymbolicIntegration.AlgebraicHermiteCompleteness`

## Declarations to move

Move the whole current module without changing declarations:

- `IsProperAtInfinity`
- `pole_condition_finite_iff_squarefree`
- `pole_condition_infinite_iff_degree`
- `isUnit_mk_of_isCoprime`
- `hermiteCongruence_exists_unique`
- `hermiteCongruence_unique`
- `hermiteMultiplier_isCoprime`
- `isAlgebraicElementary_self_iff`
- `purelyLog_of_form_const_deriv`
- `HermiteDerivativePartResidual`
- `rationalPartExhaustiveness_of_residual`
- `hermiteDerivativePartResidual_iff_frontier`
- `ratPartExhaustiveness_reduces_to_residual`

## Impact check

- `rg "AlgebraicHermiteCompleteness" -n`
  - imported by `Computable/Algebraic.lean` and `Sources/Schultz_TragerRevisited/HermiteDegreeBound.lean`.
- `scripts/wiki rdeps rationalPartExhaustiveness_of_residual --depth 2`
  - consumed by the Schultz-Trager source catalog and local equivalence theorem.
- `scripts/wiki rdeps HermiteDerivativePartResidual --depth 2`
  - consumed by the same source catalog and local frontier reductions.

## Unify list

- No declaration unification in this commit.
- This is a path-only correction: the file is abstract `AlgebraicHermite` theory and should not live under the executable `Computable/Algebraic` engine tree.

## Steps

1. `git mv` the file to `DeepWiki/SymbolicIntegration/AlgebraicHermiteCompleteness.lean`.
2. Update imports in `DeepWiki/SymbolicIntegration/Computable/Algebraic.lean`, `DeepWiki/SymbolicIntegration.lean`, and the Schultz-Trager source catalog.
3. Gate the moved module, the computable algebraic aggregator, the source catalog, then the full project.
4. Rebuild the wiki graph and commit the pure module-path reorg.
