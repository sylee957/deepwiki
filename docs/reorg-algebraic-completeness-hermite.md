# Algebraic completeness Hermite reorganization

Superseded note: the import-only `AlgebraicHermiteCompleteness.lean`
compatibility wrapper was later retired; import
`AlgebraicCompleteness.HermiteReduction` directly.

## Target module

Move the root-level `DeepWiki.SymbolicIntegration.AlgebraicHermiteCompleteness`
content into `DeepWiki.SymbolicIntegration.AlgebraicCompleteness.HermiteReduction`,
keeping the old module as a compatibility aggregator.

## Declarations to move

- `AlgebraicHermite.IsProperAtInfinity`
- `AlgebraicHermite.pole_condition_finite_iff_squarefree`
- `AlgebraicHermite.pole_condition_infinite_iff_degree`
- `AlgebraicHermite.isUnit_mk_of_isCoprime`
- `AlgebraicHermite.hermiteCongruence_exists_unique`
- `AlgebraicHermite.hermiteCongruence_unique`
- `AlgebraicHermite.hermiteMultiplier_isCoprime`
- `AlgebraicHermite.isAlgebraicElementary_self_iff`
- `AlgebraicHermite.purelyLog_of_form_const_deriv`
- `AlgebraicHermite.HermiteDerivativePartResidual`
- `AlgebraicHermite.rationalPartExhaustiveness_of_residual`
- `AlgebraicHermite.hermiteDerivativePartResidual_iff_frontier`
- `AlgebraicHermite.ratPartExhaustiveness_reduces_to_residual`

## `wiki rdeps` impact

- `RationalPartExhaustivenessFrontier`: used by the Hermite residual equivalence and the
  Schultz-Trager source catalog alias `DeepWiki.Sch.rationalPartExhaustiveness`.
- Direct imports of the old root module: topic root, `Computable.Algebraic`, and
  `Sources.Schultz_TragerRevisited.HermiteDegreeBound`.

## Unify list

- Keep the public namespace `DeepWiki.SymbolicIntegration.AlgebraicHermite`.
- Put the frontier-discharge API under `AlgebraicCompleteness/`.
- Keep `AlgebraicHermiteCompleteness.lean` as an import-only compatibility module.

## Steps

1. Move the root file to `AlgebraicCompleteness/HermiteReduction.lean` and narrow its imports.
2. Import the new leaf from `AlgebraicCompleteness.lean`.
3. Replace the old root file with a compatibility import.
4. Gate the new leaf, the compatibility module, source catalog consumer, full library, and wiki graph.
