# Reorg: implicit-derivative linear factors

## Target module

`DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors`

This module should hold polynomial linear-factor facts for the monomial derivation
`Differential.implicitDeriv v` on `K[X]`: degree bounds, the `X - C a` calculation,
normal/special criteria for products of linear factors, and the corresponding
gcd formulas. The current root file `MonomialExtensions.lean` hides this concrete
theme behind an old topic-era name.

## Decls to move

Move the existing declarations unchanged from `DeepWiki.SymbolicIntegration.MonomialExtensions`:

- `natDegree_implicitDeriv_le`
- `natDegree_implicitDeriv_eq`
- `implicitDeriv_X_sub_C`
- `isCoprime_X_sub_C_iff`
- `prod_X_sub_C_pow_eq_squarefree_factorization`
- `squarefree_prod_X_sub_C`
- `isCoprime_prod_X_sub_C_of_disjoint`
- `squarefree_factorization_pairwise_coprime`
- `isCoprime_X_sub_C_implicitDeriv_iff`
- `dvd_X_sub_C_implicitDeriv_iff`
- `dvd_X_sub_C_pow_implicitDeriv_iff`
- `isCoprime_prod_X_sub_C_implicitDeriv_iff`
- `dvd_prod_X_sub_C_implicitDeriv_iff`
- `dvd_prod_X_sub_C_pow_implicitDeriv_iff`
- `splittingFactorization_prod_X_sub_C`
- `isSpecial_special_part`
- `gcd_prod_X_sub_C_implicitDeriv`
- `gcd_prod_X_sub_C_pow_implicitDeriv`
- `gcd_prod_X_sub_C_pow_derivative`
- `prod_X_sub_C_pow_associated_gcd_mul_radical`
- `gcd_implicitDeriv_associated_gcd_derivative_mul_special`
- `isCoprime_splitting_parts`

## Impact from `scripts/wiki rdeps`

- `gcd_prod_X_sub_C_pow_implicitDeriv` is used by:
  - `Sources.Doi_10_1007_b138171.Chapter3.thm_3_5_1_gcd_mult`
  - `gcd_implicitDeriv_associated_gcd_derivative_mul_special`
  - `Sources.Doi_10_1007_b138171.Chapter3.thm_3_5_1`
  - `CanonicalRepresentation.SplitFactorCorrect.splitFactorStep_prod_X_sub_C_pow_associated`
- `dvd_X_sub_C_implicitDeriv_iff` is used by:
  - source catalog restatements in `Sources/Doi_10_1007_b138171/Chapter3.lean`
  - `CanonicalRepresentation.RootCharacterization`
  - `MonomialConstants.ConstantField`
  - the product and gcd formulas in this moved module
  - `CanonicalRepresentation.SplitSquarefreeFactor`
- Text import impact from `rg "MonomialExtensions"`:
  - root topic aggregator
  - rational integration/log-form users
  - monomial constants
  - canonical representation modules and aggregator
  - algebraic Hermite degree bound
  - computable residue/monomial-derivative users
  - source catalog chapters

## Unify list

- Keep generic derivative-gcd algebra in `Core.Differential.GcdDeriv`.
- Keep normal/special predicates in `Core.Differential.NormalSpecial`.
- Move the split-linear-factor `implicitDeriv` applications into the new
  `Core.Differential.ImplicitDerivLinearFactors` module.
- Do not change declaration names, statements, proofs, or namespaces.

## Steps

1. `git mv` `MonomialExtensions.lean` to the target module.
2. Update imports from `DeepWiki.SymbolicIntegration.MonomialExtensions` to the new module.
3. Add the target module to the topic aggregator near the other `Core.Differential` imports.
4. Gate the new module, affected downstream modules, catalog targets, and the full library.
5. Rebuild the wiki graph and commit the pure module move.
