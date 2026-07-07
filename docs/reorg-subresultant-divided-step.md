# Subresultant divided-step reorganization

## Target module

`DeepWiki.SymbolicIntegration.SubresultantCorrectness.DividedStep`

## Declarations to move

- `toBPoly_map_cdiv_exact`
- `toBPoly_bdivC_exact`
- `toBPoly_bdivC_exact_of_dvd`
- `toBPoly_bprimitivePartX_exact`
- `IsBdivCExactStep`
- `subresultant_C_mul_eq_bdivC_of_bpsremainder`
- `lrtSubresultant_C_mul_eq_bdivC_of_bpsremainder`
- `isSimilar_lrtSubresultant_subresultant_bdivC`
- `isSimilar_subresultant_bdivC_step`
- `toBPoly_prs_rel`

## `wiki rdeps` impact

- `toBPoly_bdivC_exact` feeds the divided-step theorem, `toBPoly_prs_rel`,
  the exact-division wrapper, and concrete source examples.
- `IsBdivCExactStep` feeds the parent chain-input structure, the divided-step
  theorems, concrete source examples, and the final LRT agreement theorem.
- `subresultant_C_mul_eq_bdivC_of_bpsremainder` is local to the one-step
  similarity layer.
- `toBPoly_prs_rel` feeds the parent telescope and endpoint bridge.

## Unify list

- Keep the generic first pseudo-remainder step in `PseudoRemainderStep`.
- Keep LRT operand realization in `LrtOperands`.
- Group exact scalar division, β-divided pseudo-remainder reduction, one-step
  similarity, and the per-step `toBPoly` relation in one leaf.
- Leave chain telescoping, endpoint, filter, primitive-part, residue, and
  concrete-chain sections in the parent for later thematic extraction.

## Steps

1. Add the new leaf importing `LrtOperands`.
2. Move the divided-step declarations unchanged.
3. Import the leaf from `SubresultantCorrectness`.
4. Gate the leaf, parent, concrete source examples, and full library.
5. Rebuild the wiki graph and commit.
