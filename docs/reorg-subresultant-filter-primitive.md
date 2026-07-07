# Subresultant Filter Primitive Reorg

## Target module

`DeepWiki.SymbolicIntegration.SubresultantCorrectness.FilterPrimitive`

## Declarations to move

- `getLast?_getD_filter_eq_of_singleton`
- `bsubresultantGcd_eq_of_filter_singleton`
- `toBPoly_bsubresultantGcd_eq_of_filter_singleton`
- `isSimilar_lrtSubresultant_bsubresultantGcd`
- `isSimilar_lrtSubresultant_bsubresultantGcd_real`
- `IsPrimitivePartXInput`
- `isSimilar_toBPoly_bprimitivePartX`
- `isSimilar_lrtSubresultant_lrtSubresultantCompute`

## Impact check

- `scripts/wiki rdeps bsubresultantGcd_eq_of_filter_singleton --depth 2`
  - local filter bridge, concrete chain filter, and two source example filter proofs.
- `scripts/wiki rdeps isSimilar_lrtSubresultant_bsubresultantGcd --depth 2`
  - local real/filter variant, primitive-part compute bridge, later residue-ring bridge, and source examples.
- `scripts/wiki rdeps isSimilar_lrtSubresultant_lrtSubresultantCompute --depth 2`
  - later residue-ring bridge, concrete specialization, and source examples.

## Unify list

- Keep the filter singleton identity, `bsubresultantGcd` bridge, primitive-content input, and `lrtSubresultantCompute` similarity in one layer.
- Let `SubresultantCorrectness.lean` begin with the mod-`R` unit bridge from `lrtSubresultantCompute` to `lrtGcdCompute`.
- Reuse `ChainEndpoint` and `DividedStep` through the new leaf imports.

## Steps

1. Add `SubresultantCorrectness/FilterPrimitive.lean` with the moved declarations.
2. Import the new leaf from `SubresultantCorrectness.lean` and remove the moved block from the parent.
3. Gate the new leaf, parent, affected source examples, and full project.
4. Rebuild the wiki graph and commit.
