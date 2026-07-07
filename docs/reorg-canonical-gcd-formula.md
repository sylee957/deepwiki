# CanonicalRepresentation gcd formula split

## Target module

`DeepWiki.SymbolicIntegration.CanonicalRepresentation.GcdFormula`

This module holds the prime-factor and gcd-with-derivative formulas used by
canonical split-factor correctness. The parent `CanonicalRepresentation` file
should keep the staged split/canonical representation story, while the generic
gcd algebra lives in a reusable foundation module.

## Declarations to move

- `associated_prod_primeFactors_pow`
- `associated_gcd_deriv_of_associated`
- `associated_gcd_deriv_prod_primeFactors`
- `associated_prod_gcd_deriv_primeFactors`
- `associated_gcd_deriv_special_part`
- `isUnit_natCast_count_primeFactors`
- `not_isSpecial_derivative_of_irreducible`

## Impact from `scripts/wiki rdeps`

- `associated_prod_primeFactors_pow` is used by:
  - `associated_gcd_deriv_prod_primeFactors`
  - `associated_gcd_deriv_special_part`
- `associated_gcd_deriv_special_part` is used by:
  - `Computable/SplitFactorHelpers.lean`
  - `splitFactorStep_associated_prod_special`
  - `Sources/Doi_10_1007_b138171/Chapter3.lean`
  - downstream split-factor correctness wrappers
  - `Computable/SplitFactorWfCorrect.lean`
- `not_isSpecial_derivative_of_irreducible` has the same downstream footprint
  through the split-factor correctness layer.

## Unify list

- Keep all generic UFD/gcd-with-derivative formulas together.
- Keep `splitFactorStep_associated_prod_special` and later algorithmic
  split-factor correctness in the parent for the next extraction step.
- Keep declaration statements and proofs unchanged.

## Steps

1. Add `CanonicalRepresentation/GcdFormula.lean` importing the existing
   prerequisites.
2. Import the new module from `CanonicalRepresentation.lean`.
3. Delete the moved declarations from the parent.
4. Gate the child, parent, and full library with `scripts/check.sh`.
5. Rebuild the wiki graph and commit the logical split.
