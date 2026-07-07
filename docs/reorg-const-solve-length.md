# Constant-solve length helper reorg

## Target module

`DeepWiki.SymbolicIntegration.Computable.LinearSolveCorrect`

## Declaration to move

- `CPolyG.cConstSolveUniqueQ_length`
  - From `DeepWiki.SymbolicIntegration.Computable.CoupledDE.Assembly`
  - To `DeepWiki.SymbolicIntegration.Computable.LinearSolveCorrect`

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.CPolyG.cConstSolveUniqueQ_length --depth 3`:

- `CPolyG.coupledClearedCheck_of_cCoupledDESystem`
- `cCoupledDESystem_sound`
- `DeepWiki.Si.alg_8_1_coupledDESystem_sound`
- `CPolyG.reconstruct`
- `CPolyG.reconstruct_base`

Because `CoupledDE.Assembly` already imports `LinearSolveCorrect`, downstream references should remain
unchanged after the move.

## Unify list

- Keep the theorem name and statement unchanged.
- No executable/native-decision paths change.

## Steps

1. Move `cConstSolveUniqueQ_length` into `LinearSolveCorrect` near `cConstSolveUniqueQ_sound`.
2. Remove the theorem from `CoupledDE.Assembly`.
3. Gate `Computable.LinearSolveCorrect`, then `Computable.CoupledDE.Assembly`, then full `scripts/check.sh`.
4. Rebuild `scripts/wiki build` and commit.
