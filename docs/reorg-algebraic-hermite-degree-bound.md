# Algebraic Hermite degree-bound reorg

## Target module

`DeepWiki.SymbolicIntegration.AlgebraicCompleteness.HermiteDegreeBound`

## Declarations to move

Move the whole module currently at
`DeepWiki.SymbolicIntegration.AlgebraicHermiteDegreeBound`:

- `AlgebraicHermite.hermiteBoundN`
- `AlgebraicHermite.hermiteCandTopDegree`
- `AlgebraicHermite.natDegree_le_hermiteCandTopDegree`
- `AlgebraicHermite.natDegree_hermiteNum_le_of_topCoeff_ne_zero`
- `AlgebraicHermite.natDegree_hermiteNum_le`
- `AlgebraicHermite.implicitDeriv_X2_X`
- `AlgebraicHermite.hermite_degree_bound_witness`

## Impact

`scripts/wiki rdeps AlgebraicHermite.natDegree_hermiteNum_le --depth 2` reports a
source-catalog use through `Sources.Schultz_TragerRevisited.HermiteDegreeBound`.
The main library consumer is `AlgebraicCompleteness/HermiteReduction.lean`.

## Unify list

- Keep the namespace `DeepWiki.SymbolicIntegration.AlgebraicHermite`.
- Move only the module/file path so the degree-bound API sits beside the
  algebraic Hermite completeness reduction that consumes it.
- Update aggregators/imports mechanically.

## Steps

1. `git mv` the root topic file into `AlgebraicCompleteness/HermiteDegreeBound.lean`.
2. Rewrite imports from `DeepWiki.SymbolicIntegration.AlgebraicHermiteDegreeBound`
   to `DeepWiki.SymbolicIntegration.AlgebraicCompleteness.HermiteDegreeBound`.
3. Gate the moved module, the algebraic-completeness aggregator, and the full checker.
4. Rebuild the wiki graph and commit the pure module relocation.
