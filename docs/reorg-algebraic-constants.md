# Algebraic constants reorg

## Target modules

Split `DeepWiki.SymbolicIntegration.AlgebraicConstants` into:

- `DeepWiki.SymbolicIntegration.AlgebraicConstants.Wronskian`
- `DeepWiki.SymbolicIntegration.AlgebraicConstants.Algebraic`
- `DeepWiki.SymbolicIntegration.AlgebraicConstants.Subfield`

Keep `DeepWiki.SymbolicIntegration.AlgebraicConstants` as an import-only compatibility aggregator.

## Decls to move

Wronskian:

- `linearDependentOverConst`
- `linearDependentOverConst_succAbove`
- `dependent_iterDeriv_smul`
- `linearDependentOverConst_of_dependent_iterDeriv`
- `linearDependentOverConst_of_wronskian_eq_zero`
- `wronskian_eq_zero_iff_linearDependentOverConst`
- `wronskian_ne_zero_iff_not_linearDependentOverConst`
- `iterDeriv_algebraMap`
- `wronskian_algebraMap`
- `not_linearDependentOverConst_algebraMap`

Algebraic:

- `coeff_mapCoeffs_eq_zero_of_monic`
- `degree_mapCoeffs_lt`
- `minpoly_coeff_deriv_eq_zero_of_deriv_eq_zero`
- `isAlgebraicOverConst_of_deriv_eq_zero`
- `isAlgebraicOverConst_map_of_deriv_eq_zero`

Subfield:

- `constantsSubfield`
- `mem_constantsSubfield`
- `subfieldClosure_subset_constants`

## `wiki rdeps` impact

- Wronskian declarations are used internally and by Chapter 3 source catalog aliases.
- Algebraic-over-constants declarations are used by Chapter 3 and
  `ConstantsAlgebraicClosure`.
- `constantsSubfield` is used by Chapter 3 and `ConstantsAlgebraicClosure`.

Direct imports of the root are preserved by keeping the root aggregator.

## Unify list

- Keep all Wronskian dependence criteria together.
- Keep minimal-polynomial coefficient facts for algebraic constants together.
- Keep the constants subfield API separate from both proof families.

## Steps

1. Add the three leaf modules with moved declarations.
2. Replace `AlgebraicConstants.lean` with an import-only aggregator.
3. Gate each leaf, the root, `ConstantsAlgebraicClosure`, Chapter 3, and the full project.
