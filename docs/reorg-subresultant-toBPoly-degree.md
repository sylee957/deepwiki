# Subresultant `toBPoly` degree bridge reorg

## Target module

`DeepWiki.SymbolicIntegration.SubresultantCorrectness.ToBPolyDegree`

## Declarations to move

- `toBPoly_coeff`
- `natDegree_toBPoly_le`
- `bnorm_getLast?_toPoly_ne_zero`
- `toPoly_blc_eq_coeff`
- `bisZero_iff_toBPoly_eq_zero`
- `toPoly_blc_ne_zero`
- `bdeg_eq_natDegree`
- `length_bnorm_of_ne`
- `toPoly_blc_eq_leadingCoeff`
- `subresultant_C_mul_right`

## Impact from `wiki rdeps`

- `bdeg_eq_natDegree` is used by the remaining subresultant-correctness chain proofs and by
  the Bronstein subresultant example/exercise catalogs.
- `subresultant_C_mul_right` is used by the later divided pseudo-remainder PRS steps.

## Unify list

- Keep the executable `BPoly` and PRS definitions in `Compute`.
- Move only the semantic bridge facts about `toBPoly`, `bdeg`, `blc`, and the abstract
  subresultant scaling lemma.
- Leave pseudo-remainder, LRT operand, PRS telescope, residue-map, and concrete-chain agreement
  sections in `SubresultantCorrectness.lean` for later passes.

## Steps

1. Add `SubresultantCorrectness/ToBPolyDegree.lean` with the moved declarations.
2. Import it from `SubresultantCorrectness.lean`.
3. Remove the moved initial bridge section from the parent.
4. Gate the new module, parent module, relevant source catalog/example targets, full gate, then
   rebuild the wiki graph.
