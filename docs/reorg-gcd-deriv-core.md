# Gcd-derivative core extraction

## Target module

`DeepWiki.SymbolicIntegration.Core.Differential.GcdDeriv`

This module should hold generic gcd-with-derivation lemmas over a differential
ring. The current declarations are split between `MonomialExtensions` and
`CanonicalRepresentation/GcdFormula`, even though they do not depend on
monomial extensions, special/normal predicates, or canonical representations.

## Declarations to move

- `deriv_mul_eq`
- `associated_gcd_deriv_mul`
- `associated_gcd_deriv_pow`
- `associated_gcd_deriv_prod`
- `associated_gcd_deriv_of_associated`

## Impact from `scripts/wiki rdeps`

- `associated_gcd_deriv_mul` is used by:
  - source catalog aliases in `Sources/Doi_10_1007_b138171/Chapter3.lean`
  - `associated_gcd_deriv_prod`
  - `isSpecial_of_prime_dvd`
  - `CanonicalRepresentation.GcdFormula.associated_gcd_deriv_of_associated`
- `associated_gcd_deriv_pow` is used by:
  - source catalog aliases in `Sources/Doi_10_1007_b138171/Chapter3.lean`
  - `CanonicalRepresentation.GcdFormula.associated_gcd_deriv_prod_primeFactors`
  - monomial-extension split-product gcd formulas
- `associated_gcd_deriv_prod` is used by:
  - source catalog aliases in `Sources/Doi_10_1007_b138171/Chapter3.lean`
  - `CanonicalRepresentation.GcdFormula.associated_gcd_deriv_prod_primeFactors`
  - monomial-extension split-product gcd formulas

## Unify list

- Keep generic gcd-with-derivative algebra in `Core/Differential`.
- Keep `IsNormal`/`IsSpecial` and monomial `implicitDeriv` product/root
  formulas in `MonomialExtensions`.
- Keep prime-factor formulas in `CanonicalRepresentation.GcdFormula`.
- Do not change declaration names, statements, proofs, or namespaces.

## Steps

1. Add `Core/Differential/GcdDeriv.lean` with the generic declarations.
2. Import it from `MonomialExtensions`, `CanonicalRepresentation/GcdFormula`,
   and the topic aggregator.
3. Delete the moved declarations from their old modules.
4. Gate the new core module, affected old modules, catalog target, and full
   library with `scripts/check.sh`.
5. Rebuild the wiki graph and commit the extraction.
