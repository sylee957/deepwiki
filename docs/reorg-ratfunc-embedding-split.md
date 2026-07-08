# RatFunc embedding API split

## Target module

`DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncEmbedding`

## Declarations to move

From `Core/Polynomial/RatFuncFractions.lean`:

- `ratFunc_algebraMap_ne_zero`
- `ratFunc_algebraMap_eq_algebraMap_C`
- `ratFunc_algebraMap_poly_mem_range_iff`

Keep in `Core/Polynomial/RatFuncFractions.lean`:

- `ratFunc_mk_add_mk`
- `ratFunc_mk_mul_mk`
- `ratFunc_list_sum_algebraMap_div_const`

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.ratFunc_algebraMap_eq_algebraMap_C --depth 2`
shows direct use in `LiouvilleExpExtension.lean`, `LiouvilleLogExtension.lean`, and
`Computable/LiouvilleExpBridge.lean`, plus the range lemma.

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.ratFunc_mk_add_mk --depth 2`
shows direct use in `RationalFunctionDerivative.lean` and
`Computable/FractionFieldDeriv.lean`.

## Unify list

- Put polynomial-to-`RatFunc` embedding facts in `RatFuncEmbedding`.
- Leave representative fraction arithmetic in `RatFuncFractions`.
- Keep `RatFuncFractions` importing `RatFuncEmbedding` so existing arithmetic proofs can use
  `ratFunc_algebraMap_ne_zero`.
- Narrow Liouville imports to `RatFuncEmbedding`.

## Steps

1. Create `Core/Polynomial/RatFuncEmbedding.lean` with the embedding declarations.
2. Remove those declarations from `RatFuncFractions.lean` and import the new module there.
3. Update direct embedding-only imports in Liouville files to the new module.
4. Add the new module to the `DeepWiki.SymbolicIntegration` root import list.
5. Gate the new module, the old fractions module, the affected Liouville modules, then the full checker.
6. Rebuild the wiki graph and commit.
