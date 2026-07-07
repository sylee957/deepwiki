# Subresultant LRT operands reorganization

## Target module

`DeepWiki.SymbolicIntegration.SubresultantCorrectness.LrtOperands`

## Declarations to move

- `toPoly_cC`
- `toBPoly_liftCtoBPoly`
- `toPoly_ctVar`
- `toBPoly_bArgAmtD'`
- `lrtSubresultant_eq_subresultant_toBPoly`
- `lrtSubresultant_C_mul_eq_rem_of_bpsremainder`

## `wiki rdeps` impact

- `toPoly_cC` has only local operand dependents within depth 2: `toBPoly_liftCtoBPoly`,
  `toBPoly_bArgAmtD'`, and `lrtSubresultant_eq_subresultant_toBPoly`.
- `toBPoly_liftCtoBPoly` feeds the LRT operand identity and later LRT bridge
  theorems in `SubresultantCorrectness`.
- `lrtSubresultant_eq_subresultant_toBPoly` feeds the first LRT remainder step,
  the divided-remainder step, and later similarity bridge theorems.
- `lrtSubresultant_C_mul_eq_rem_of_bpsremainder` has no dependents at depth 2.

## Unify list

- Keep the generic `toBPoly` degree and pseudo-remainder algebra in
  `ToBPolyDegree` and `PseudoRemainderStep`.
- Group the LRT-specific operand realization (`liftCtoBPoly D`, `bArgAmtD' A D`)
  and the first LRT specialization of the generic pseudo-remainder theorem in
  one random-access leaf.
- Leave β-division, similarity, telescoping, residue, and concrete-chain stages
  in the parent for later thematic extraction.

## Steps

1. Add the new leaf importing `PseudoRemainderStep`.
2. Move the six LRT operand/first-remainder declarations unchanged.
3. Import the leaf from `SubresultantCorrectness`.
4. Gate the leaf, the parent, and the full library.
5. Rebuild the wiki graph and commit this logical extraction.
