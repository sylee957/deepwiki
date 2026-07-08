# QFun fold derivative helpers

## Target module

Move the generic `qadd`-fold derivative helpers into
`DeepWiki.SymbolicIntegration.Compute.RationalFunction`, beside the `toQFun`
API for `qadd`, `qzero`, and `toQFun_foldl_qadd`.

## Declarations to move

- `DeepWiki.SymbolicIntegration.Compute.deriv_toQFun_foldl_qadd`
- `DeepWiki.SymbolicIntegration.Compute.foldl_residual_eq`

## Impact

`scripts/wiki rdeps deriv_toQFun_foldl_qadd --depth 2` reports direct users in:

- `DeepWiki/SymbolicIntegration/Compute/HermiteInnerCorrectness.lean`
- `DeepWiki/SymbolicIntegration/Compute/HermiteQRegularity.lean`
- `DeepWiki/SymbolicIntegration/Compute/HermiteMultifactorResidual.lean`

`scripts/wiki rdeps foldl_residual_eq --depth 2` reports no current dependents.

## Unify list

- Keep `qadd`/`qzero` fold denotation lemmas together.
- Keep derivative-of-fold lemmas close to `toQFun_foldl_qadd`, not inside the
  Hermite inner-loop correctness proof.
- Leave Hermite-specific residual identities in the Hermite modules.

## Steps

1. Add the list-sum import to `Compute.RationalFunction`.
2. Move the two generic fold lemmas after `toQFun_qderiv`.
3. Remove the moved declarations and now-unneeded import from
   `Compute.HermiteInnerCorrectness`.
4. Gate `Compute.RationalFunction`, `Compute.HermiteInnerCorrectness`, direct
   consumers, then the full library.
