# Log Residue Tower Abstract Split

## Target module

Move the abstract polynomial residue/root support out of the computable
soundness bridge into:

- `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LogResidueTower`

Keep the computable transport and field-identity assembly in:

- `DeepWiki.SymbolicIntegration.Computable.LogPartTowerSoundness`

## Declarations to move

- `LogResidueTower.residueLinearFactor_eq`
- `LogResidueTower.roots_residueResultantTowerG_eq_residues`
- `LogResidueTower.residue_gcd_associated_linear_factor`
- `LogResidueTower.residue_gcd_eq_linear_factor`

## `wiki rdeps` impact

- `residueLinearFactor_eq` is used by
  `roots_residueResultantTowerG_eq_residues`.
- `roots_residueResultantTowerG_eq_residues` is used by the computable
  qfun specialization in `Computable.LogPartTowerSoundness`.
- `residue_gcd_eq_linear_factor` is used by
  `Computable.OneShotAssembly`.

## Unify list

- The abstract RT residue-linear-factor facts should live with the
  Rothstein-Trager library support, not under `Computable`.
- `Computable.LogPartTowerSoundness` imports the new abstract module and keeps
  only the computable `logResidueSumG` readings and reduced-case field identity.
- The Rothstein-Trager aggregator imports the new module.

## Steps

1. Add `RothsteinTrager/LogResidueTower.lean` with the abstract namespace.
2. Remove the abstract namespace from `Computable/LogPartTowerSoundness.lean`.
3. Update imports and aggregators.
4. Gate the new abstract module, the computable bridge, `OneShotAssembly`, and
   the full library.
