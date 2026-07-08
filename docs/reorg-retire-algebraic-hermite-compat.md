# Retire algebraic Hermite compatibility wrapper

## Theme

`DeepWiki.SymbolicIntegration.AlgebraicHermiteCompleteness` is now an
import-only root compatibility wrapper. The Hermite completeness declarations
live under `DeepWiki.SymbolicIntegration.AlgebraicCompleteness.HermiteReduction`,
which is the predictable path for a newcomer.

## Target Module

Use `DeepWiki.SymbolicIntegration.AlgebraicCompleteness.HermiteReduction`
directly.

## Decls To Move

None. This is wrapper retirement only; declaration names and statements stay
unchanged.

## Impact

Text import search shows three Lean import sites:

- `DeepWiki/SymbolicIntegration.lean`
- `DeepWiki/SymbolicIntegration/Computable/Algebraic.lean`
- `Sources/Schultz_TragerRevisited/HermiteDegreeBound.lean`

`scripts/wiki show AlgebraicHermite.ratPartExhaustiveness_reduces_to_residual`
confirms the public theorem already lives in
`AlgebraicCompleteness/HermiteReduction.lean`.

## Unify List

- Remove the stale root wrapper.
- Replace imports with the real Hermite reduction module.
- Add supersession notes to older reorg docs that still mention the wrapper.

## Steps

1. Update the three Lean imports.
2. Delete `AlgebraicHermiteCompleteness.lean`.
3. Gate the source catalog and `Computable.Algebraic`, then full `scripts/check.sh`.
4. Rebuild `scripts/wiki build`.
5. Commit the wrapper retirement.
