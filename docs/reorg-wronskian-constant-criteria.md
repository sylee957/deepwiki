# Wronskian constant-criteria reorganization

## Target module

Move the Wronskian linear-dependence-over-constants criteria from
`DeepWiki.SymbolicIntegration.AlgebraicConstants.Wronskian` into
`DeepWiki.SymbolicIntegration.Core.Differential.Wronskian`.

## Declarations to move

- `linearDependentOverConst`
- `linearDependentOverConst_succAbove`
- `dependent_iterDeriv_smul`
- `linearDependentOverConst_of_dependent_iterDeriv`
- `linearDependentOverConst_of_wronskian_eq_zero`
- `wronskian_eq_zero_iff_linearDependentOverConst`
- `wronskian_ne_zero_iff_not_linearDependentOverConst`
- `iterDeriv_algebraMap`
- `wronskian_algebraMap`
- `not_linearDependentOverConst_algebraMap`

## `wiki rdeps` impact

- `linearDependentOverConst`: Wronskian criteria and Chapter 3 source aliases.
- `wronskian_eq_zero_iff_linearDependentOverConst`: Chapter 3 source alias.
- `not_linearDependentOverConst_algebraMap`: Chapter 3 source alias.

## Unify list

- Keep the entire Wronskian and constant-linear-dependence API in the differential core.
- Leave `AlgebraicConstants.Wronskian` as a compatibility aggregator for existing imports.
- Keep `AlgebraicConstants.lean` importing the compatibility module.

## Steps

1. Move the declarations into `Core/Differential/Wronskian.lean`.
2. Replace `AlgebraicConstants/Wronskian.lean` with an import-only compatibility module.
3. Gate the core leaf, compatibility module, algebraic constants aggregator, source catalog consumer,
   full library, and wiki graph.
