# Fraction-field derivation reorg

## Target module

Move the source-neutral fraction-field derivation API out of
`DeepWiki.SymbolicIntegration.Computable.FractionFieldDeriv` into
`DeepWiki.SymbolicIntegration.Core.Differential.FractionFieldDeriv`.

Move the linear-factor `extendDeriv` lemmas from
`DeepWiki.SymbolicIntegration.Computable.FractionFieldDerivLinearFactor` into
`DeepWiki.SymbolicIntegration.Core.Differential.FractionFieldDerivLinearFactor`.

The computable/tower-specific definitions stay under `Computable`.

## Declarations to move

- `extendDerivFun`
- `extendDerivFun_mk`
- `extendDerivFun_algebraMap`
- `extendDerivFun_add`
- `extendDerivFun_mul`
- `extendDerivFun_zero`
- `extendDerivAddHom`
- `extendDerivFun_zsmul`
- `extendDerivFun_smul`
- `extendDerivQ`
- `extendDeriv`
- `extendDeriv_apply`
- `extendDeriv_algebraMap`
- `extendDeriv_mk`
- `extendDeriv_logDeriv`
- `extendDeriv_logDeriv_mk`
- `fractionFieldDifferential`
- `ResidueMatchTower.extendDeriv_implicitDeriv_logDeriv_X_sub_C`
- `ResidueMatchTower.extendDeriv_implicitDeriv_C_logDeriv_X_sub_C`

Leave in `Computable.FractionFieldDeriv`:

- `towerFractionFieldDeriv`
- `towerFractionFieldDeriv_algebraMap`
- `towerFractionFieldDeriv_mk`
- `towerFractionFieldDeriv_logDeriv`
- `towerFractionFieldDifferential`

## `wiki rdeps` impact

`extendDeriv` has 39 direct dependents, including residue-match soundness,
normal-pole valuation lemmas, tower derivation bridges, and computable engine
field-identity proofs. The move keeps the declaration names unchanged and leaves
`Computable.FractionFieldDeriv` as an import-compatible wrapper for existing
consumers.

`ResidueMatchTower.extendDeriv_implicitDeriv_logDeriv_X_sub_C` has three direct
dependents: its constant-numerator specialization, `monomial_residue_match_of_cancel`,
and `monomial_residue_sum_eq_cancel_add`. The old computable linear-factor module
will re-export the new core module.

## Unify list

- Generic quotient-rule derivation and `Differential (RatFunc K)` construction:
  `Core.Differential.FractionFieldDeriv`.
- Linear-factor logarithmic derivative lemmas: `Core.Differential.FractionFieldDerivLinearFactor`.
- Tower/engine specialization over `CPolyG` and `QFunNZG`: `Computable.FractionFieldDeriv`.

## Steps

1. Add `Core/Differential/FractionFieldDeriv.lean` with the generic `extendDeriv`
   API and its restatement examples.
2. Trim `Computable/FractionFieldDeriv.lean` to import the core module and retain
   only the tower specialization.
3. Add `Core/Differential/FractionFieldDerivLinearFactor.lean` with the generic
   linear-factor log-derivative lemmas.
4. Trim `Computable/FractionFieldDerivLinearFactor.lean` to a compatibility
   re-export.
5. Import the new core modules from `Core/Differential.lean`.
6. Gate `Core.Differential.FractionFieldDeriv`,
   `Computable.FractionFieldDeriv`, and the full library.
