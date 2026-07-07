# Canonical split-squarefree-factor reorg

## Target module

`DeepWiki.SymbolicIntegration.CanonicalRepresentation.SplitSquarefreeFactor`

## Declarations to move

- `squarefreeSpecialPart`
- `squarefreeNormalPart`
- `splitSquarefreeFactor`
- `squarefreeSpecialPart_prod_X_sub_C_associated`
- `splitSquarefreeFactor_prod_X_sub_C`

## Impact from `wiki rdeps`

- `splitSquarefreeFactor_prod_X_sub_C` has no current reverse dependencies.
- The moved definitions are a self-contained squarefree denominator split API used by the
  theorem in the same block.

## Unify list

- Keep generic split-factor definitions and recursive correctness in
  `CanonicalRepresentation.SplitFactor` / `SplitFactorCorrect`.
- Put the one-squarefree-factor `gcd(p,Dp)` split and its fully-split correctness theorem in
  the new `SplitSquarefreeFactor` leaf.
- Leave the RatFunc canonical representation and root characterization in the parent for later
  partition passes.

## Steps

1. Add `CanonicalRepresentation/SplitSquarefreeFactor.lean` with the moved declarations.
2. Import it from `CanonicalRepresentation.lean`.
3. Remove the moved squarefree-factor sections from the parent.
4. Gate the new module, parent module, full gate, then rebuild the wiki graph.
