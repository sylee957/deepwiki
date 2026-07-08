# Algebraic constants separable-root wrapper reorganization

## Target module

Move the separable-root constant wrappers from
`DeepWiki.SymbolicIntegration.DifferentialAlgebraExamples` to
`DeepWiki.SymbolicIntegration.AlgebraicConstants.Closure`.

## Declarations to move

- `deriv_eq_zero_of_separable_root_const_coeffs`
- `deriv_eq_zero_iff_separable_root_const_coeffs`

## `wiki rdeps` impact

- `deriv_eq_zero_iff_separable_root_const_coeffs`: no dependents at depth 2.
- The declarations are wrappers over the existing algebraic-constants closure API.

## Unify list

- Keep separable root and constant-coefficient algebraicity criteria together in
  `AlgebraicConstants/Closure.lean`.
- Keep `DifferentialAlgebraExamples.lean` focused on polynomial derivation and
  differential-ideal examples.

## Steps

1. Add the wrappers to `AlgebraicConstants/Closure.lean`.
2. Remove the duplicate section from `DifferentialAlgebraExamples.lean`.
3. Gate the closure leaf, examples module, full library, and wiki graph.
