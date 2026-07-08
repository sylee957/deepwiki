# Differential Wronskian core reorganization

## Target module

Move the Wronskian and iterated-derivative kernel from
`DeepWiki.SymbolicIntegration.Constants` to
`DeepWiki.SymbolicIntegration.Core.Differential.Wronskian`.

## Declarations to move

- `iterDeriv`
- `iterDeriv_zero`
- `iterDeriv_succ`
- `iterDeriv_zero_right`
- `iterDeriv_add`
- `iterDeriv_const_mul`
- `iterDeriv_sum`
- `iterDeriv_mul`
- `wronskian`
- `wronskian_eq_zero_of_linearDependent`
- `wronskian_eq_zero_of_eq`
- `wronskian_fin_two`
- `wronskian_two_linearDependent`
- `wronskian_eq_zero_imp_linearDependent`
- `wronskian_eq_zero_dependent_iterDeriv`
- `deriv_dependent_iterDeriv`
- `linearDependent_of_div_deriv_dependent`

## `wiki rdeps` impact

- `iterDeriv`: used by the Wronskian kernel itself and
  `AlgebraicConstants.Wronskian`.
- `wronskian`: used by the source catalog Chapter 3 Wronskian aliases and
  `AlgebraicConstants.Wronskian`.

## Unify list

- Keep constants-extension facts in `Constants.lean`.
- Put iterated derivatives and Wronskians in `Core.Differential.Wronskian`.
- Keep `Constants.lean` importing the new leaf so existing imports and source catalogs stay stable.

## Steps

1. Add `Core/Differential/Wronskian.lean` with the moved kernel.
2. Replace the moved section in `Constants.lean` with an import-only compatibility path plus
   the remaining constants-extension theorem.
3. Add the new leaf to the topic root import list.
4. Gate the new leaf, `Constants`, `AlgebraicConstants.Wronskian`, source catalog consumer, full
   library, and wiki graph.
