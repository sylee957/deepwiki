# Reorg: normal-pole order drop

Target module: `DeepWiki.SymbolicIntegration.Computable.RischDE.NormalPoleOrderDrop`

Decls to move:
- `pow_sub_one_dvd_deriv_of_pow_dvd`
  `Computable/RischDE/TowerCorrectG.lean` -> `Computable/RischDE/NormalPoleOrderDrop.lean`
- `not_pow_dvd_deriv_of_normal`
  `Computable/RischDE/TowerCorrectG.lean` -> `Computable/RischDE/NormalPoleOrderDrop.lean`
- `emultiplicity_deriv_eq_sub_one_of_normal`
  `Computable/RischDE/TowerCorrectG.lean` -> `Computable/RischDE/NormalPoleOrderDrop.lean`
- `emultiplicity_wronskian_numerator_eq_of_normal`
  `Computable/RischDE/TowerCorrectG.lean` -> `Computable/RischDE/NormalPoleOrderDrop.lean`

Impact:
- `emultiplicity_wronskian_numerator_eq_of_normal` is used by `RatFuncValuation` through
  `ratFuncOrd_extendDeriv_eq_sub_one_of_normal`, then by the normal-denominator RDE bounds.
- `emultiplicity_deriv_eq_sub_one_of_normal` currently has no downstream callers.
- `TowerCorrectG` should import the new module only for its examples/axiom audit if needed.
- `RatFuncValuation` should import the new module directly instead of the broad `TowerCorrectG`.

Unify:
- No duplicate theorem to retire in this pass. The improvement is module ownership: the polynomial
  normal-pole valuation kernel becomes a standalone RischDE support module instead of living among
  carrier-generic cleared-identity helpers.

Steps:
1. Create `NormalPoleOrderDrop.lean` with the moved section and restatement examples.
2. Trim `TowerCorrectG.lean` to cleared-identity helpers and import the new module.
3. Point `RatFuncValuation.lean` at the narrow module.
4. Import the new module from the `RischDE` aggregator.
5. Gate focused modules, rebuild wiki, full gate, commit.
