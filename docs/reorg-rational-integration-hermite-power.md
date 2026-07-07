# Rational Integration Hermite Power Reorg

## Target module

`DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.HermitePower`

## Declarations to move

- `hermiteReduce_step_ratFunc`
- `hermiteReducePower`
- `hermiteReducePower_spec`
- `degree_lt_of_mul_degree_lt`
- `degree_le_pred_of_lt`
- `hermiteReducePower_remainder_degree`

## Impact

- `scripts/wiki rdeps DeepWiki.SymbolicIntegration.hermiteReducePower --depth 2`
  - Source aliases in `Sources.Doi_10_1007_b138171.Chapter2`.
  - Parent Hermite sum/full reductions.
  - `integrateRationalFunction_reduction_proper`.
  - Downstream `RationalIntegrationLogForm` through the parent reductions.

## Unify list

- Keep the single-prime-power Hermite recurrence, its differential identity,
  and its properness proof together.
- Leave partial fractions, full squarefree-power reduction, polynomial-part
  integration, and Horowitz-Ostrogradsky splitting in the parent for later
  extractions.

## Steps

1. Add `RationalIntegrationAlgorithms/HermitePower.lean`.
2. Import the new leaf from `RationalIntegrationAlgorithms.lean`.
3. Delete the moved prime-power Hermite block from the parent.
4. Gate the new leaf, parent, source catalog, and downstream log-form module.
5. Run the full gate, rebuild the wiki graph, and commit.
