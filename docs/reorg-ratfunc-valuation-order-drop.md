# RatFunc valuation order-drop kernel

## Target module

Move the polynomial order-drop kernel from
`DeepWiki.SymbolicIntegration.Computable.RischDE.NormalPoleOrderDrop` to
`DeepWiki.SymbolicIntegration.Computable.RatFuncValuation.PolynomialOrderDrop`.

## Declarations to move

- `pow_sub_one_dvd_deriv_of_pow_dvd`
- `not_pow_dvd_deriv_of_normal`
- `emultiplicity_deriv_eq_sub_one_of_normal`
- `emultiplicity_wronskian_numerator_eq_of_normal`

## Impact

`scripts/wiki rdeps emultiplicity_wronskian_numerator_eq_of_normal --depth 2`
reports direct use by:

- `DeepWiki/SymbolicIntegration/Computable/RatFuncValuation/NormalPole.lean`

Text search shows the old module is imported by:

- `DeepWiki/SymbolicIntegration/Computable/RatFuncValuation/NormalPole.lean`
- `DeepWiki/SymbolicIntegration/Computable/RischDE.lean`
- `DeepWiki/SymbolicIntegration/Computable/RischDE/TowerCorrectG.lean`

## Unify list

- Put valuation-specific polynomial order-drop kernels beside the valuation lift.
- Keep `RischDE.NormalPoleOrderDrop` as a compatibility aggregator.
- Do not change theorem statements or exported declaration names.

## Steps

1. Move the implementation file to
   `Computable/RatFuncValuation/PolynomialOrderDrop.lean`.
2. Replace the old `RischDE.NormalPoleOrderDrop` file with an import-only
   compatibility aggregator.
3. Update `RatFuncValuation.NormalPole` and the `RatFuncValuation` aggregator to
   import the new module directly.
4. Gate the new module, old compatibility module, direct consumers, and the full
   library.
