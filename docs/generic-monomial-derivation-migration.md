# Generic monomial-derivation migration

## Goal

Retire the misleading `DensePoly.cmapDeriv` and `DensePoly.cmonomialDeriv` names.  Both
definitions are already generic over a polynomial representation `P`; their correct home is
`CPolyEngine`, alongside `mapCoeffs`, `deriv`, and the denotation laws.

This is a namespace/API migration, not an algorithm rewrite: dense list reduction remains selected by
the `CPolyEngine DensePoly` instance, while sparse and future representations use the same generic
formulas.

## Current inventory

- Definitions currently live in `Engine/MonomialDeriv.lean` under `namespace DensePoly`, despite
  quantifying over arbitrary `[CPoly P] [CPolyEngine P]`.
- The matching denotation theorems already live in `namespace CPolyEngine`.
- There are 53 source/catalog consumer modules.  The high-fanout consumers include tower Hermite,
  normal-part soundness, LRT soundness, and the source catalogs, so retaining an old alias would hide
  incomplete migration rather than reduce risk.

## Phases

1. Move the generic definitions and their generic denotation statements to `CPolyEngine` as
   `mapDeriv` and `monomialDeriv`.  Keep only genuinely dense reduction lemmas under `DensePoly`.
2. Migrate executable/algorithm modules first, then soundness/assembly modules, using focused gates
   after each coherent batch.
3. Migrate `Sources/` catalog terms and update docstrings to name `CPolyEngine.monomialDeriv`.
4. Confirm `rg` finds no old names, rebuild the wiki graph, inspect rdeps, and run a clean-tree full
   `scripts/check.sh` before deleting this plan in the landing commit.

## Acceptance checks

- No declaration named `DensePoly.cmapDeriv` or `DensePoly.cmonomialDeriv` remains.
- Generic consumers, notably `CFrac.towerDerivCFracWith`, mention only `CPolyEngine` operations.
- Dense and sparse tower validations still compile through their selected engine instances.
- No compatibility alias or deprecated forwarding declaration is retained.
