# Subresultant Chain Endpoint Reorg

## Target module

`DeepWiki.SymbolicIntegration.SubresultantCorrectness.ChainEndpoint`

## Declarations to move

- `isSimilar_subresPRS_telescope`
- `IsSubresPRSChainInput`
- `isSimilar_subresPRS_elt`
- `isSimilar_lrtSubresultant_subresPRS_elt`

## Impact check

- `scripts/wiki rdeps isSimilar_subresPRS_telescope --depth 2`
  - no dependents outside its declaration.
- `scripts/wiki rdeps IsSubresPRSChainInput --depth 2`
  - consumed by the endpoint theorem, the remaining `SubresultantCorrectness` bridges, and the two source examples.
- `scripts/wiki rdeps isSimilar_lrtSubresultant_subresPRS_elt --depth 2`
  - consumed by `isSimilar_lrtSubresultant_bsubresultantGcd`, then the later compute bridges.

## Unify list

- Keep the PRS-chain input structure and its two endpoint theorems beside the telescope theorem.
- Let `SubresultantCorrectness.lean` begin with the `bsubresultantGcd` filter identity section.
- Reuse the existing `DividedStep` import as the only local proof dependency for the moved endpoint module.

## Steps

1. Add `SubresultantCorrectness/ChainEndpoint.lean` with the moved chain telescope and endpoint declarations.
2. Import the new leaf from `SubresultantCorrectness.lean` and remove the moved block from the parent.
3. Gate `DeepWiki.SymbolicIntegration.SubresultantCorrectness.ChainEndpoint`, the parent, affected source examples, then the full project.
4. Rebuild the wiki graph and commit the extraction.
