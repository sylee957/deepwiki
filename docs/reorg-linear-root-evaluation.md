# Linear root-evaluation helper reorg

Superseded note: the remaining computable `extendDeriv` linear-factor API was
later renamed from `Computable.ResidueLinearFactor` to
`Computable.FractionFieldDerivLinearFactor`.

## Target module

Create `DeepWiki.SymbolicIntegration.Core.Differential.LinearRootEvaluation` for generic facts about a
linear factor `X - C α` in a differential field.

## Declarations to move

Move from `DeepWiki.SymbolicIntegration.Computable.ResidueLinearFactor`:

- `ResidueMatchTower.eval_mapCoeffs_of_isRoot`
- `ResidueMatchTower.eval_implicitDeriv_of_isRoot`
- `ResidueMatchTower.algebraMap_div_X_sub_C_split`
- `ResidueMatchTower.divByMonic_C_mul_X_sub_C`

Keep in `Computable.ResidueLinearFactor`:

- `ResidueMatchTower.extendDeriv_implicitDeriv_logDeriv_X_sub_C`

## Impact

`wiki rdeps` before the move:

- `eval_mapCoeffs_of_isRoot`: used by `eval_implicitDeriv_of_isRoot` and
  `ResidueMatchTower.residue_mul_eval_sub_eq`.
- `eval_implicitDeriv_of_isRoot`: used by residue-match soundness.
- `algebraMap_div_X_sub_C_split`: used by residue-match soundness, one-shot assembly,
  hyperexp full soundness, and LRT soundness.
- `divByMonic_C_mul_X_sub_C`: used by one-shot assembly and hyperexp full soundness.

The existing import path remains valid because `Computable.ResidueLinearFactor` will import the new Core module.

## Unify list

- Keep declaration names and `ResidueMatchTower` namespace unchanged.
- Do not move `extendDeriv_implicitDeriv_logDeriv_X_sub_C` into Core, because it depends on
  the fraction-field extension API currently under `Computable`.
- Do not touch executable or `native_decide` paths.

## Steps

1. Add the Core module and move the four generic lemmas there.
2. Replace their old definitions with an import of the Core module.
3. Gate `DeepWiki.SymbolicIntegration.Computable.ResidueLinearFactor`, then the full gate.
4. Rebuild `scripts/wiki` and commit.
