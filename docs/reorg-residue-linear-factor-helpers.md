# Residue linear-factor helper reorg

Superseded note: the computable linear-factor helper module was later renamed
from `Computable.ResidueLinearFactor` to
`Computable.FractionFieldDerivLinearFactor`.

## Target module

`DeepWiki.SymbolicIntegration.Computable.ResidueLinearFactor`

## Declarations to move

- `ResidueMatchTower.extendDeriv_implicitDeriv_C_logDeriv_X_sub_C`

Keep the existing namespace and declaration name.

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.ResidueMatchTower.extendDeriv_implicitDeriv_C_logDeriv_X_sub_C --depth 2`
reports direct use by `primitive_monomial_residue_match`, with downstream primitive
engine and one-shot residue-match results.

The more general helper `extendDeriv_implicitDeriv_logDeriv_X_sub_C` already lives in
`Computable/ResidueLinearFactor.lean`, so the constant-specialized helper should live
there too.  Moving the pair all the way into `Core/Differential` would pull the
`extendDeriv` dependency from `Computable/FractionFieldDeriv` into core, so this pass
keeps the current boundary.

## Unify list

- General linear-factor log-derivative helper.
- Constant-monomial specialization used by primitive residue matching.

## Steps

1. Add `extendDeriv_implicitDeriv_C_logDeriv_X_sub_C` to
   `Computable/ResidueLinearFactor.lean`.
2. Delete the duplicate definition from `Computable/ResidueMatchSoundness.lean`.
3. Gate both modules and the full checker.
4. Rebuild the wiki graph and commit the helper relocation.
