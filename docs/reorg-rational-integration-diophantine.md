# Rational Integration Diophantine Reorg

## Target module

`DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.Diophantine`

## Declarations to move

- `diophantineSolve`
- `diophantineSolve_spec`
- `diophantineSolveReduced`
- `diophantineSolveReduced_spec`
- `diophantineSolveReduced_fst_degree_lt`
- `ratFunc_partialFraction_coprime`
- `ratFunc_partialFraction_prod`

## Impact check

- `scripts/wiki rdeps diophantineSolve --depth 2`
  - used by rational partial fractions, Hermite reduction, local principal parts, Laurent coefficients, Czichowski normal position, and the source catalog.
- `scripts/wiki rdeps diophantineSolveReduced_spec --depth 2`
  - used by Hermite reduction and the computable `cdiophantine` correctness bridge.
- `rg "diophantineSolve" -n DeepWiki Sources`
  - confirms the solver is a standalone shared kernel, not just a local helper for `RationalIntegrationAlgorithms.lean`.
- `scripts/wiki rdeps ratFunc_partialFraction_coprime --depth 2`
  - used by the source catalog, `ratFunc_partialFraction_prod`, and the full Hermite reduction.
- `scripts/wiki rdeps ratFunc_partialFraction_prod --depth 2`
  - used by the source catalog and `hermiteReduce_full`.

## Unify list

- Keep both unreduced and reduced Bézout solvers in the same Diophantine leaf.
- Keep partial-fraction decompositions built directly from `diophantineSolve` in the same leaf.
- Leave `RationalIntegrationAlgorithms.lean` as the public re-exporting parent for downstream compatibility.
- No declaration renames or semantic changes.

## Steps

1. Add `RationalIntegrationAlgorithms/Diophantine.lean` with the moved solver declarations.
2. Import the new leaf from `RationalIntegrationAlgorithms.lean` and remove the moved block.
3. Gate the new leaf, parent, computable Diophantine bridge, relevant source catalog, and full project.
4. Rebuild the wiki graph and commit.
