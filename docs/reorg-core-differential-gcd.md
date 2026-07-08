# Core differential gcd reorg

## Target modules

Keep `DeepWiki.SymbolicIntegration.Core.Differential.Gcd` as the aggregator, and move the two
root-level gcd leaves into a predictable subdirectory:

- `DeepWiki.SymbolicIntegration.Core.Differential.Gcd.Derivative`
- `DeepWiki.SymbolicIntegration.Core.Differential.Gcd.PrimeFactors`

The declarations are generic gcd-with-derivative API. The current `GcdDeriv` / `GcdPrimeFactors`
root leaves are historical names; the aggregator already says this is the gcd sub-theory.

## Declarations to move

From `GcdDeriv.lean` to `Gcd/Derivative.lean`:

- `associated_gcd_deriv_mul`
- `associated_gcd_deriv_pow`
- `associated_gcd_deriv_prod`
- `associated_gcd_deriv_of_associated`
- `isSpecial_iff_associated_gcd`
- `IsNormal.isUnit_gcd`

From `GcdPrimeFactors.lean` to `Gcd/PrimeFactors.lean`:

- `associated_prod_primeFactors_pow`
- `associated_gcd_deriv_prod_primeFactors`
- `associated_prod_gcd_deriv_primeFactors`
- `associated_gcd_deriv_special_part`
- `isUnit_natCast_count_primeFactors`
- `not_isSpecial_derivative_of_irreducible`

## `wiki rdeps` impact

- `associated_gcd_deriv_mul`: used by `lem_3_4_4_base`,
  `associated_gcd_deriv_of_associated`, `associated_gcd_deriv_prod`,
  `isSpecial_of_prime_dvd`.
- `isSpecial_iff_associated_gcd`: used by `def_3_4_2_gcd`,
  `gcd_prod_X_sub_C_implicitDeriv`, `gcd_prod_X_sub_C_pow_implicitDeriv`,
  `isSpecial_of_prime_dvd`.
- `associated_gcd_deriv_special_part`: used by
  `gcd_derivative_dvd_gcd_implicitDeriv`, `splitFactorStep_associated_prod_special`.
- `not_isSpecial_derivative_of_irreducible`: used by
  `gcd_derivative_dvd_gcd_implicitDeriv`, `splitFactorStep_associated_prod_special`.

## Unify list

- Keep generic gcd product/coprimality lemmas in `Core.Algebra.GcdBasics`.
- Keep gcd-with-derivative formulas in `Core.Differential.Gcd.*`.
- Keep normal/special closure and factor-inheritance lemmas in `Core.Differential.NormalSpecial.*`.
- Delete the old `GcdDeriv` and `GcdPrimeFactors` module paths; update internal imports directly.

## Steps

1. `git mv` `GcdDeriv.lean` to `Gcd/Derivative.lean`.
2. `git mv` `GcdPrimeFactors.lean` to `Gcd/PrimeFactors.lean`.
3. Update the `Core.Differential.Gcd` aggregator and all direct imports to the new paths.
4. Gate the new gcd aggregator, downstream normal/special and implicit-derivative gcd consumers,
   then the full library.
5. Rebuild the wiki graph and commit.
