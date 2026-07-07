# Normal and special core reorganization

## Target module

`DeepWiki.SymbolicIntegration.Core.Differential.NormalSpecial`

## Declarations to move

- `IsNormal`
- `IsSpecial`
- `IsSpecial.isDifferentialIdeal`
- `IsSpecial.mul`
- `isSpecial_one`
- `IsSpecial.prod`
- `isNormal_one`
- `IsNormal.mul`
- `IsNormal.prod`
- `IsNormal.of_mul_left`
- `IsNormal.of_mul_right`
- `IsNormal.of_dvd`
- `IsNormal.squarefree`
- `isSpecial_iff_associated_gcd`
- `IsNormal.isUnit_gcd`
- `isSpecial_of_prime_dvd`
- `isSpecial_of_dvd`
- `IsSpecial.of_mul_coprime`
- `isUnit_of_isNormal_of_isSpecial`
- `isNormal_of_isUnit`
- `isNormal_and_isSpecial_iff_isUnit`
- `IsSpecial.unit_mul_iff`
- `IsNormal.unit_mul_iff`
- `IsSpecial.of_associated`
- `IsNormal.of_associated`
- `IsSplittingFactorization`
- `IsSpecial.splittingFactorization`
- `IsNormal.splittingFactorization`

## `wiki rdeps` impact

- `IsNormal` has direct users in source catalogs, canonical representation,
  differential algebra facts, special-normal coprimality, and the old
  `MonomialExtensions` file.
- `IsSpecial` has direct users across the same areas plus monomial constants and
  split-factor correctness.
- `IsSplittingFactorization` is used by the source catalog and canonical
  representation split-factor API.
- `isSpecial_iff_associated_gcd` feeds source catalog restatements and the
  monomial linear-factor gcd computations.

## Unify list

- Move the generic differential-ring predicates and their gcd/unit/splitting API
  to `Core.Differential`.
- Keep monomial derivation degree bounds, linear-factor criteria, products of
  `X - C a`, and implicit-derivative specializations in `MonomialExtensions`.
- Preserve declaration names and theorem statements.

## Steps

1. Add `Core/Differential/NormalSpecial.lean` importing the existing gcd-derivative
   API.
2. Move the generic block unchanged from `MonomialExtensions`.
3. Import the new module from `MonomialExtensions` and the topic aggregator.
4. Gate the new module, the old monomial module, and downstream catalog-facing
   consumers.
5. Run the full gate, rebuild the wiki graph, and commit.
