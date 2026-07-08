# Algebraic constants closure reorganization

## Target module

Move the root-level `DeepWiki.SymbolicIntegration.ConstantsAlgebraicClosure`
content into the existing `DeepWiki.SymbolicIntegration.AlgebraicConstants`
area, keeping the old module as a compatibility aggregator.

## Declarations to move

- `IsAlgebraicOverConst`
- `deriv_eq_zero_of_separable_algebraic_const`
- `isAlgebraicOverConst_of_deriv_eq_zero_of_integral`
- `deriv_eq_zero_of_isAlgebraicOverConst`
- `deriv_eq_zero_of_base_constant_polynomial`
- `deriv_eq_zero_iff_isAlgebraicOverConst_separable_base`
- `deriv_eq_zero_iff_isAlgebraicOverConst_separable`
- `mapCoeffs_eq_zero_of_coprime_of_relation`
- `coeff_deriv_eq_zero_of_coprime_of_relation`
- `charZero_constantsSubfield`
- `isAlgClosed_constantsSubfield`
- `exists_const_point_of_exists_extension_point`

## `wiki rdeps` impact

- `IsAlgebraicOverConst`: only `isAlgebraicOverConst_of_deriv_eq_zero_of_integral`
  at depth 2.
- `exists_const_point_of_exists_extension_point`: source catalog alias
  `DeepWiki.Si.lem_3_3_6`.

## Unify list

- Place separable algebraic constant closure facts in
  `AlgebraicConstants/Closure.lean`.
- Place rational-extension numerator/denominator constant-coefficient facts in
  `AlgebraicConstants/RationalExtension.lean`.
- Place the Nullstellensatz transfer theorem in
  `AlgebraicConstants/NullstellensatzTransfer.lean`.
- Keep `ConstantsAlgebraicClosure.lean` as an import-only compatibility module.

## Steps

1. Add the three concept leaves under `AlgebraicConstants/`.
2. Update `AlgebraicConstants.lean` and `ConstantsAlgebraicClosure.lean` imports.
3. Gate the new leaves, compatibility module, source catalog consumer, and full library.
4. Rebuild the wiki graph, then commit the logical reorganization.
