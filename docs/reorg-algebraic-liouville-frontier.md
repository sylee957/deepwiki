# Algebraic Liouville Frontier Reorg

## Target module

`DeepWiki.SymbolicIntegration.AlgebraicCompleteness.LiouvilleFrontier`

## Declarations to move

- `LiouvilleStructure.hasWeakLiouvilleForm_iff_isAlgebraicElementary`
- `LiouvilleStructure.algebraicLiouvilleFrontier_proved`
- `LiouvilleStructure.isAlgebraicElementary_finiteDimensional_discharge`

## Impact

- `scripts/wiki rdeps DeepWiki.SymbolicIntegration.LiouvilleStructure.algebraicLiouvilleFrontier_proved --depth 2`
  - `Sources.Doi_10_1007_978_3_030_98767_1.Rosenlicht.algebraicLiouvilleFrontier`
- Text import search:
  - `Sources/Doi_10_1007_978_3_030_98767_1/Rosenlicht.lean`
  - `DeepWiki/SymbolicIntegration/Computable/Algebraic.lean`

## Unify list

- Keep the bridge from `HasWeakLiouvilleForm` to
  `AlgebraicCompleteness.IsAlgebraicElementary` next to the
  `AlgebraicLiouvilleFrontier` predicates.
- Remove the proof-only frontier bridge from the `Computable/Algebraic` engine
  aggregator.

## Steps

1. `git mv` `Computable/Algebraic/LiouvilleFrontier.lean` to
   `AlgebraicCompleteness/LiouvilleFrontier.lean`.
2. Update `AlgebraicCompleteness.lean` to import the new leaf.
3. Remove the old import from `Computable/Algebraic.lean`.
4. Update the Rosenlicht source catalog import.
5. Gate the moved module, aggregators, source catalog, and full project.
6. Rebuild the wiki graph and commit.
