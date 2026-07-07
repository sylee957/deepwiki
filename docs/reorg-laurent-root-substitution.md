# Laurent root-substitution split

## Target modules

- `DeepWiki.SymbolicIntegration.LaurentCoefficients.RootInvariant`
- `DeepWiki.SymbolicIntegration.LaurentCoefficients.RootEvaluation`
- `DeepWiki.SymbolicIntegration.LaurentCoefficients.TaylorCoefficient`
- `DeepWiki.SymbolicIntegration.LaurentCoefficients.RootSubstitution` remains an aggregator.

## Declarations to move

`RootInvariant` owns the specialized recursion invariant in `K(x)`:

- `lDenomα`, `diffSubst_lDenom`, `lDenomα_ne_zero`
- `lFracα`, `hFracα`, `lFracα_zero`
- `reduced_numα`, `ratFuncKDeriv_lFracα`
- `iterate_ratFuncKDeriv_hFracα`

`RootEvaluation` owns the engine-output root evaluation bridge:

- `eval_laurentSubst_some`
- `laurentQ_eval_at_root`
- `eval_diffSubst_laurentNum_eq_laurentQ_eval`
- `eval_laurentH`
- `eval_laurentH_eq_diffSubst_laurentNum`

`TaylorCoefficient` owns the evaluated rational-function bridge and regular-root package:

- `eval_lDenomα_ne_zero`
- `eval_lFracα`, `eval_smul_lFracα`
- `eval_ratFuncKDeriv_iterate_hFracα_at_root`
- `IsLaurentRegularRoot`
- `eval_laurentH_eq_taylor_coeff`

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.eval_laurentH_eq_taylor_coeff --depth 3`
reports downstream use in `LaurentCoefficients.Assembly` and the source catalog.

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.iterate_ratFuncKDeriv_hFracα --depth 3`
reports the catalog invariant restatement and the Taylor coefficient evaluation.

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.eval_laurentH_eq_diffSubst_laurentNum --depth 3`
reports the catalog root-evaluation restatement, the Taylor bridge, and assembly.

## Unify list

- Keep the existing `RootSubstitution` import path as an aggregator so downstream files
  need no semantic retargeting.
- Place the genuine rational-function recursion near the fraction invariant it
  specializes.
- Place Taylor evaluation after both root evaluation and the rational invariant.

## Steps

1. Add the three stage modules.
2. Replace `RootSubstitution.lean` with an aggregator importing `TaylorCoefficient`.
3. Gate each new module, then the existing `RootSubstitution` aggregator.
4. Run the full gate, rebuild the wiki graph, and commit.
