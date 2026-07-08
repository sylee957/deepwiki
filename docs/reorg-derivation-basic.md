# Derivation Basic Split

## Target module

`DeepWiki.SymbolicIntegration.Core.Differential.DerivationBasic`

## Declarations to move

- `deriv_mul_eq`

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.deriv_mul_eq --depth 2` shows direct users in
`Core.Differential.NormalSpecial`, `Core.Differential.Gcd.Derivative`, and
`DifferentialAlgebraFacts`, with downstream source aliases and splitting-factor proofs.

## Unify list

- Keep `Core.Differential.Gcd.Derivative` focused on gcd-with-derivative associate identities.
- Put the generic Leibniz product-rule rewrite in an earlier shared derivation API module.
- Keep downstream import paths working through `Core.Differential.Gcd.Derivative`/`NormalSpecial` while exposing the shared
  module from the topic root.

## Steps

1. Add `DerivationBasic.lean` with `deriv_mul_eq`.
2. Import it from `Core.Differential.Gcd.Derivative` and remove the local declaration there.
3. Import it from the topic root before `Core.Differential.Gcd.Derivative`.
4. Gate the new leaf, `Core.Differential.Gcd.Derivative`, `NormalSpecial`, and the full library.
