# Algebraic Hermite degree-bound relocation

## Target module

`DeepWiki.SymbolicIntegration.AlgebraicHermiteDegreeBound`

The current module
`DeepWiki.SymbolicIntegration.Computable.Algebraic.HermiteDegreeBound`
contains generic polynomial degree estimates in namespace
`DeepWiki.SymbolicIntegration.AlgebraicHermite`. It is not an executable
engine module, so the `Computable/Algebraic` placement hides source-neutral
theorem API behind a computable path.

## Declarations to move

- `AlgebraicHermite.hermiteBoundN`
- `AlgebraicHermite.hermiteCandTopDegree`
- `AlgebraicHermite.natDegree_le_hermiteCandTopDegree`
- `AlgebraicHermite.natDegree_hermiteNum_le_of_topCoeff_ne_zero`
- `AlgebraicHermite.natDegree_hermiteNum_le`
- `AlgebraicHermite.implicitDeriv_X2_X`
- `AlgebraicHermite.hermite_degree_bound_witness`

## Impact from `scripts/wiki rdeps`

- `AlgebraicHermite.natDegree_hermiteNum_le` is used by:
  - `Sources.Schultz_TragerRevisited.HermiteDegreeBound.eq_4_9_degreeBound`
- `AlgebraicHermite.natDegree_hermiteNum_le_of_topCoeff_ne_zero` is used by:
  - `Sources.Schultz_TragerRevisited.HermiteDegreeBound.hermite_degreeBound_topCoeff`
  - `AlgebraicHermite.hermite_degree_bound_witness`
- `Computable.Algebraic.AlgebraicHermiteCompleteness` imports the current file
  directly and should import the root theorem module instead.

## Unify list

- Keep source-neutral degree estimates in the root SymbolicIntegration theory
  layer.
- Leave executable/computable algebraic Hermite modules in
  `Computable/Algebraic`.
- Do not change declaration names, statements, proofs, or namespace.

## Steps

1. `git mv` the file to `DeepWiki/SymbolicIntegration/AlgebraicHermiteDegreeBound.lean`.
2. Update direct imports in `Computable/Algebraic.lean`,
   `Computable/Algebraic/AlgebraicHermiteCompleteness.lean`, and the Schultz
   catalog file.
3. Gate the moved module, the computable algebraic consumer, the catalog target,
   and the full library with `scripts/check.sh`.
4. Rebuild the wiki graph and commit the relocation.
