# Rational Integration RT/LRT Reorg

## Target module

`DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager`

## Declarations to move

- `rtResultant`
- `rtResultant_eval`
- `rtLogGcd`
- `rtLogGcd_isRoot_iff`
- `rtResultant_eval_eq_zero_iff`
- `rtResultant_eval_eq_prod_roots`
- `lrtSubresultant`
- `lrtSubresultant_eval`
- `lazardRiobooTrager`

## Impact

- `scripts/wiki rdeps rtResultant --depth 2`
  - Broad downstream use in residue multiplicity, Czichowski normal position,
    RT-resultant correctness, LRT monic logs, source catalogs, and the
    `lazardRiobooTrager` wrapper.
- `scripts/wiki rdeps lazardRiobooTrager --depth 2`
  - Catalog-facing only, through `DeepWiki.Si.lazardRiobooTrager_algorithm`.

## Unify list

- Keep all Rothstein-Trager resultants, residue gcds, LRT subresultants, and
  Lazard-Rioboo-Trager output assembly together.
- Leave Hermite reduction, partial fractions, polynomial part, and
  Horowitz-Ostrogradsky splitting in the parent until their own extraction.

## Steps

1. Add `RationalIntegrationAlgorithms/RothsteinTrager.lean`.
2. Import the new leaf from `RationalIntegrationAlgorithms.lean`.
3. Delete the moved RT/LRT block from the parent module.
4. Gate the new leaf, parent aggregator, known downstream RT/LRT users, source
   catalogs, and the full project.
5. Rebuild the wiki graph and commit.
