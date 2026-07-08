# Implicit-derivative linear-factor reorganization

## Target modules

- `DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors.Basic`
- `DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors.Products`
- `DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors.Gcd`
- `DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors` as the aggregator

## Declarations to move

`Basic` keeps the single-factor and elementary product API:

- `implicitDeriv_X_sub_C`
- `isCoprime_X_sub_C_iff`
- `prod_X_sub_C_pow_eq_squarefree_factorization`
- `squarefree_prod_X_sub_C`
- `isCoprime_prod_X_sub_C_of_disjoint`
- `squarefree_factorization_pairwise_coprime`
- `isCoprime_X_sub_C_implicitDeriv_iff`
- `dvd_X_sub_C_implicitDeriv_iff`
- `dvd_X_sub_C_pow_implicitDeriv_iff`

`Products` keeps product-level normal/special and splitting API:

- `isCoprime_prod_X_sub_C_implicitDeriv_iff`
- `dvd_prod_X_sub_C_implicitDeriv_iff`
- `dvd_prod_X_sub_C_pow_implicitDeriv_iff`
- `splittingFactorization_prod_X_sub_C`
- `isSpecial_special_part`
- `isCoprime_splitting_parts`

`Gcd` keeps gcd, radical, and derivative companion formulas:

- `gcd_prod_X_sub_C_implicitDeriv`
- `gcd_prod_X_sub_C_pow_implicitDeriv`
- `gcd_prod_X_sub_C_pow_derivative`
- `prod_X_sub_C_pow_associated_gcd_mul_radical`
- `gcd_implicitDeriv_associated_gcd_derivative_mul_special`

## `wiki rdeps` impact

- `dvd_X_sub_C_implicitDeriv_iff` is used by source restatements and the product/splitting formulas.
- `associated_gcd_deriv_prod` / `associated_gcd_deriv_pow` from `GcdDeriv` feed the gcd formulas in this file.
- Downstream imports currently use the parent module, so the parent aggregator should preserve public import compatibility.

## Unify list

- Keep basic linear-factor criteria discoverable before product criteria.
- Keep splitting/product API separate from gcd/radical identities.
- Keep the old module name as an aggregator to avoid changing downstream import meaning.

## Steps

1. Move the existing file to `ImplicitDerivLinearFactors/Basic.lean` and leave only the basic declarations there.
2. Add `Products.lean` importing `Basic` and `NormalSpecial`.
3. Add `Gcd.lean` importing `Products` and `GcdDeriv`.
4. Recreate `ImplicitDerivLinearFactors.lean` as an aggregator.
5. Gate each new leaf, the parent aggregator, known direct consumers, and the full repository.
6. Rebuild the wiki graph and commit the split.
