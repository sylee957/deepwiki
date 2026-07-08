# RatFunc constant embedding API reorg

## Target module

`DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncFractions`

## Declarations to move

- `LiouvilleExp.algebraMap_eq_algebraMap_C`
- `LiouvilleExp.algebraMap_poly_mem_range_iff`
- `LiouvilleLog.algebraMap_eq_algebraMap_C`
- `LiouvilleLog.algebraMap_poly_mem_range_iff`

Replace the exp/log-local copies with shared declarations:

- `ratFunc_algebraMap_eq_algebraMap_C`
- `ratFunc_algebraMap_poly_mem_range_iff`

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.LiouvilleExp.algebraMap_eq_algebraMap_C --depth 2`
reported direct use in `LiouvilleExpExtension.lean` and
`Computable/LiouvilleExpBridge.lean`, with downstream exp pole-matching and Liouville
results.

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.LiouvilleLog.algebraMap_eq_algebraMap_C --depth 2`
reported direct use in `LiouvilleLogExtension.lean`, with downstream log tower
results.

`LiouvilleExp.algebraMap_poly_mem_range_iff` has no dependents.  The log variant is
used by `LiouvilleLog.mem_range_of_deriv_mem_range` and downstream reductions.

## Unify list

- One `RatFunc` constant embedding equality, independent of exp/log derivations.
- One range characterization for polynomial images that are constants.

## Steps

1. Add the shared API to `Core/Polynomial/RatFuncFractions.lean`.
2. Import that module in the exp/log proof files.
3. Rewrite exp/log and bridge call sites to the shared names.
4. Delete the duplicated local declarations.
5. Gate the touched modules and rebuild the wiki graph.
