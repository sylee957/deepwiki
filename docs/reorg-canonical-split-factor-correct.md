# Canonical split-factor correctness reorg

## Target module

`DeepWiki.SymbolicIntegration.CanonicalRepresentation.SplitFactorCorrect`

## Declarations to move

- `splitFactorStep_prod_X_sub_C_pow_associated`
- `splitFactorStep_prod_X_sub_C_associated`
- `isSplitFactorStep_prod_X_sub_C`
- `splitFactorStep_associated_prod_special`
- `isNormalSqfree_of_forall_prime_normal`
- `isNormalSqfree_of_splitFactorStep_natDegree_zero`
- `isSpecial_splitFactorStep`
- `splitFactorStep_dvd`
- `splitFactorAux_isSplittingFactorizationGen`
- `splitFactor_isSplittingFactorizationGen`

## Impact from `wiki rdeps`

- `splitFactorStep_associated_prod_special` is used by the Bronstein chapter catalog, the
  local split-factor correctness lemmas, and `Computable/SplitFactorWfCorrect.lean`.
- `splitFactorAux_isSplittingFactorizationGen` is used by
  `splitFactor_isSplittingFactorizationGen` and the Bronstein chapter catalog alias.
- `isSplitFactorStep_prod_X_sub_C` has no current reverse dependencies.

## Unify list

- Keep definitions in `CanonicalRepresentation.SplitFactor`.
- Keep normal/squarefree predicates in `CanonicalRepresentation.NormalSqfree`.
- Move only proof-layer correctness for `splitFactorStep`, `splitFactorAux`, and `splitFactor`
  into the new `SplitFactorCorrect` leaf.
- Leave squarefree-factor splitting, the final canonical representation, and root
  characterization in the parent for later partition passes.

## Steps

1. Add `CanonicalRepresentation/SplitFactorCorrect.lean` with the moved declarations.
2. Import the new module from `CanonicalRepresentation.lean`.
3. Remove the moved sections from `CanonicalRepresentation.lean`.
4. Gate the new module, parent module, direct downstream computable/catalog users, full gate,
   then rebuild the wiki graph.
