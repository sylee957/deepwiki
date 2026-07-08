# Polynomial root-evaluation helpers

## Target module

Create `DeepWiki.SymbolicIntegration.Core.Polynomial.RootEvaluation` for generic
polynomial root-evaluation facts that are currently hidden under Laurent
cofactor evaluation.

## Declarations to move

- `DeepWiki.SymbolicIntegration.eval_modByMonic_of_root`

## Impact

`scripts/wiki rdeps eval_modByMonic_of_root --depth 2` reports direct users in:

- `DeepWiki/SymbolicIntegration/LaurentCoefficients/Cofactors/Evaluation.lean`
- `DeepWiki/SymbolicIntegration/LaurentCoefficients/RootEvaluation.lean`

Downstream source aliases flow through `Sources/Doi_10_1007_b138171/Chapter2.lean`.

## Unify list

- Generic `%ₘ` root-evaluation facts belong under `Core.Polynomial`.
- Laurent-specific Bezout evaluation remains under
  `LaurentCoefficients.Cofactors`.
- Laurent engine root evaluation continues to import the Laurent cofactor bridge.

## Steps

1. Add `Core/Polynomial/RootEvaluation.lean` with the generic lemma.
2. Import it in `LaurentCoefficients/Cofactors/Evaluation.lean`.
3. Import the new core module from `DeepWiki/SymbolicIntegration.lean`.
4. Gate the new module, Laurent cofactor/root consumers, Chapter 2 catalog, then
   the full library.
