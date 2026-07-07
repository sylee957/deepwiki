# Laurent root-substitution bridge reorg

## Target module

`DeepWiki.SymbolicIntegration.LaurentCoefficients` should become an aggregator over thematic Laurent-coefficient modules.

Planned modules:

- `DeepWiki.SymbolicIntegration.LaurentCoefficients.Engine`: current engine definitions and base recursion.
- `DeepWiki.SymbolicIntegration.LaurentCoefficients.RootSubstitution`: root substitution, `diffSubst` bridge, and Taylor-coefficient bridge.
- Later split candidate: engine-form partial-fraction assembly.

## Declarations to move

First mechanical step:

- Move the current contents of `DeepWiki/SymbolicIntegration/LaurentCoefficients.lean` to
  `DeepWiki/SymbolicIntegration/LaurentCoefficients/Engine.lean`.
- Replace `DeepWiki/SymbolicIntegration/LaurentCoefficients.lean` with an aggregator import.

Second thematic step:

- Move root-substitution and Taylor bridge declarations out of `Engine`:
  `eval_laurentSubst_some`, `laurentQ_eval_at_root`, `lDenomα`, `diffSubst_lDenom`,
  `lDenomα_ne_zero`, `lFracα`, `hFracα`, `lFracα_zero`, `reduced_numα`,
  `ratFuncKDeriv_lFracα`, `iterate_ratFuncKDeriv_hFracα`,
  `eval_diffSubst_laurentNum_eq_laurentQ_eval`, `eval_laurentH`,
  `eval_laurentH_eq_diffSubst_laurentNum`, `eval_lDenomα_ne_zero`,
  `eval_lFracα`, `eval_smul_lFracα`, `eval_ratFuncKDeriv_iterate_hFracα_at_root`,
  `IsLaurentRegularRoot`, `eval_laurentH_eq_taylor_coeff`.

## Impact

`wiki rdeps` checks before the split:

- `diffSubst_lDenom`: used by `reduced_numα`, `ratFuncKDeriv_lFracα`.
- `eval_diffSubst_laurentNum_eq_laurentQ_eval`: catalog alias only.
- `eval_laurentH_eq_diffSubst_laurentNum`: used by `eval_laurentH_eq_taylor_coeff`, catalog alias.
- `eval_laurentH_eq_taylor_coeff`: used by `localCoeff_eq_laurentH`, catalog alias.
- `localCoeff_eq_laurentH`: used by `localPrincipalPart_eq_engineSum`, catalog alias.

Existing import sites of `DeepWiki.SymbolicIntegration.LaurentCoefficients` remain valid through the aggregator.

## Unify list

- Keep declaration names and namespaces unchanged.
- Keep book/source aliases in `Sources/` pointed at the same declaration names.
- Keep `diffSubst` core in `Core/Differential/DifferentialPolynomials.lean`; this reorg is only the Laurent-side bridge.

## Steps

1. Pure move: make `LaurentCoefficients.lean` an aggregator and move current contents to `LaurentCoefficients/Engine.lean`; gate and commit.
2. Extract the root-substitution/Taylor bridge into `LaurentCoefficients/RootSubstitution.lean`; update aggregator order; gate and commit.
3. Rebuild `scripts/wiki` and resample the `diffSubst` partition signal.
