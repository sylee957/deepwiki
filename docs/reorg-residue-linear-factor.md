# Reorg: residue linear-factor support

Target module: `DeepWiki.SymbolicIntegration.Computable.ResidueLinearFactor`

Decls to move:
- `ResidueMatchTower.extendDeriv_implicitDeriv_logDeriv_X_sub_C`
  `Computable/ResidueMatchSoundness.lean` -> `Computable/ResidueLinearFactor.lean`
- `ResidueMatchTower.eval_mapCoeffs_of_isRoot`
  `Computable/ResidueMatchSoundness.lean` -> `Computable/ResidueLinearFactor.lean`
- `ResidueMatchTower.eval_implicitDeriv_of_isRoot`
  `Computable/ResidueMatchSoundness.lean` -> `Computable/ResidueLinearFactor.lean`
- `ResidueMatchTower.algebraMap_div_X_sub_C_split`
  `Computable/ResidueMatchSoundness.lean` -> `Computable/ResidueLinearFactor.lean`
- `ResidueMatchTower.divByMonic_C_mul_X_sub_C`
  `Computable/OneShotAssembly.lean` -> `Computable/ResidueLinearFactor.lean`

Impact:
- `extendDeriv_implicitDeriv_logDeriv_X_sub_C` is used by the primitive/general residue-match proofs
  and by `monomial_residue_sum_eq_cancel_add`.
- `eval_mapCoeffs_of_isRoot` feeds `eval_implicitDeriv_of_isRoot`, which feeds
  `residue_mul_eval_sub_eq`.
- `algebraMap_div_X_sub_C_split` feeds the general monomial residue-match decomposition.
- `divByMonic_C_mul_X_sub_C` feeds `hyperexp_cancel_sum_eq`.
- `ResidueMatchSoundness` and `OneShotAssembly` should import the new module; downstream users keep
  their existing imports.

Unify:
- No duplicate theorem to retire. The improvement is module ownership: reusable linear-factor and root
  evaluation facts become a predictable support module instead of being embedded in higher-level
  soundness/assembly files.

Steps:
1. Create `ResidueLinearFactor.lean` with the moved support lemmas.
2. Import it from `ResidueMatchSoundness.lean` and remove the moved local lemmas.
3. Import it from `OneShotAssembly.lean` and remove the hyperexp quotient helper there.
4. Import the new module from `Computable.lean`.
5. Gate the new module, `ResidueMatchSoundness`, `OneShotAssembly`, immediate hyperexp consumer, then
   rebuild wiki and run full `scripts/check.sh`.
