# Squarefree Yun Loop Split

## Target module

`DeepWiki.SymbolicIntegration.Core.Polynomial.SquarefreeYunLoop`

## Declarations to move

- `Babs`
- `Dabs`
- `YunInv`
- `Dabs_eq_mul`
- `Babs_eq_mul`
- `gcd_Babs_Dabs`
- `yunStep_preserves`
- `yunStep_emit_assoc`
- `yunLoopAbs`
- `yunLoopAbs_forall₂`
- `yunLoopAbs_squarefree`
- `yunLoopAbs_pairwise_isRelPrime`
- `yunLoopAbs_prod_assoc`
- `prodPow`
- `prodPow_associated`
- `prodPow_append_singleton`
- `prodPow_range_map_eq_finset`
- `prodPow_one_sqfreeFactPart_range_associated`
- `yunLoopAbs_prodPow_assoc`

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.Babs --depth 2` shows direct users in
`SquarefreeFactorization`, `Compute/SquarefreeYun`, and computable Yun-squarefree bridge
files. `scripts/wiki rdeps DeepWiki.SymbolicIntegration.YunInv --depth 2` and
`scripts/wiki rdeps DeepWiki.SymbolicIntegration.yunLoopAbs --depth 2` show the same
abstract-loop users plus downstream reconstruction lemmas.

## Unify list

- Keep `SquarefreeYun` focused on the Yun recurrence polynomial and recurrence-level
  coprimality/gcd extraction.
- Move abstract loop state, emitted-factor API, and powered-product reconstruction into the
  loop module.
- Update direct imports that consume `Babs`, `YunInv`, `yunLoopAbs`, or `prodPow` to import
  `SquarefreeYunLoop`.

## Steps

1. Add `SquarefreeYunLoop.lean` importing `SquarefreeYun`.
2. Remove the loop-state sections from `SquarefreeYun.lean`.
3. Import the new module from the topic root and direct consumers.
4. Gate the new module, direct consumers, and full library.
