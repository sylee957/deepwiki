# Subresultant pseudo-remainder step reorg

## Target module

`DeepWiki.SymbolicIntegration.SubresultantCorrectness.PseudoRemainderStep`

## Declarations to move

- `subresultant_C_mul_eq_rem_of_bpsremainder`
- `exists_subresultant_C_mul_eq_rem_of_bpsremainder`

## Impact from `wiki rdeps`

- These lemmas are used by the later LRT pseudo-remainder reduction and divided PRS steps.
- They depend on the `toBPoly` bridge and abstract subresultant scaling helper already split into
  `ToBPolyDegree`.

## Unify list

- Keep the low-level `toBPoly` degree bridge in `ToBPolyDegree`.
- Put the one-step pseudo-division/subresultant reduction in this leaf.
- Leave LRT operand identification, divided β steps, telescoping, concrete chain data, and
  residue-map agreement in the parent for later passes.

## Steps

1. Add `SubresultantCorrectness/PseudoRemainderStep.lean` with the moved declarations.
2. Import it from `SubresultantCorrectness.lean`.
3. Remove the moved one-step pseudo-remainder section from the parent.
4. Gate the new module, parent module, full gate, then rebuild the wiki graph.
