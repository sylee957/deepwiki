# Fraction-field linear-factor derivative reorg

## Theme

The scattered root-linear-factor theme has most root-evaluation facts in
`Core/Differential/LinearRootEvaluation`, while the `extendDeriv` log-derivative
specializations live in the consumer-named module
`Computable/ResidueLinearFactor`.

## Target Module

Move the `extendDeriv` linear-factor API to:

- `DeepWiki.SymbolicIntegration.Computable.FractionFieldDerivLinearFactor`

This keeps the declarations on the computable side because they depend on
`extendDeriv` from `Computable/FractionFieldDeriv`, avoiding a reverse import
from `Core` into `Computable`.

## Decls To Move

- `ResidueMatchTower.extendDeriv_implicitDeriv_logDeriv_X_sub_C`
- `ResidueMatchTower.extendDeriv_implicitDeriv_C_logDeriv_X_sub_C`

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.ResidueMatchTower.extendDeriv_implicitDeriv_C_logDeriv_X_sub_C --depth 2`
shows direct use by:

- `ResidueMatchTower.primitive_monomial_residue_match`
- `primitive_monomial_residue_match_engine`
- `ResidueMatchTower.primitive_residue_match_list`

Text imports to update:

- `Computable.lean`
- `Computable/ResidueMatchSoundness.lean`
- `Computable/OneShotAssembly.lean`
- `Computable/OneShotAssembly/ResidueMatch.lean`

## Unify List

- Preserve declaration names and namespaces.
- Rename the file/module only; do not change theorem statements or proofs.
- Update module docstring from residue-matching consumer wording to
  fraction-field derivative provider wording.

## Steps

1. Rename `Computable/ResidueLinearFactor.lean` to
   `Computable/FractionFieldDerivLinearFactor.lean`.
2. Update the module docstring and imports that reference the old module.
3. Gate `DeepWiki.SymbolicIntegration.Computable.FractionFieldDerivLinearFactor`.
4. Gate direct consumers and full `scripts/check.sh`.
5. Rebuild `scripts/wiki build`.
