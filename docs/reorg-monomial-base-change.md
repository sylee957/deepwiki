# Monomial base-change reorganization

## Target module

`DeepWiki.SymbolicIntegration.MonomialConstants.BaseChange`

## Declarations to move

- `mapCoeffs_map`
- `implicitDeriv_map`
- `isSpecial_map_of_isSpecial`

## `wiki rdeps` impact

- `implicitDeriv_map` is used by `MonomialConstants.BaseChange`, `SpecialFirstKind`,
  LRT soundness/discharge modules, and source-catalog corollaries.
- `mapCoeffs_map` is the local helper for `implicitDeriv_map`.
- `isSpecial_map_of_isSpecial` feeds `isSpecialFirstKind_map` and catalog aliases.

## Unify list

- Put generic monomial-derivation base-change facts in `MonomialConstants.BaseChange`.
- Keep first-kind residue/log-derivative material in `SpecialFirstKind`.
- Let `MonomialConstants.Basic` import monomial extension facts directly, instead of
  importing first-kind theory only to obtain shared setup.

## Steps

1. Change `MonomialConstants.Basic` to import `MonomialExtensions`.
2. Move the three base-change lemmas from `SpecialFirstKind` to `MonomialConstants.BaseChange`.
3. Import `MonomialConstants.BaseChange` from `SpecialFirstKind`.
4. Gate `BaseChange`, `SpecialFirstKind`, the `MonomialConstants` aggregator, and
   representative downstream LRT/catalog consumers.
5. Run the full gate, rebuild the wiki graph, and commit.
