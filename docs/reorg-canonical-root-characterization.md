# Canonical root-characterization reorg

## Target module

`DeepWiki.SymbolicIntegration.CanonicalRepresentation.RootCharacterization`

## Declarations to move

- `deriv_eq_zero_of_isSpecial_of_isRoot`
- `deriv_ne_zero_of_isNormal_of_isRoot`
- `deriv_eq_zero_iff_isRoot_special`
- `deriv_ne_zero_iff_isRoot_normal`

## Impact from `wiki rdeps`

- `deriv_eq_zero_iff_isRoot_special` is used by the Bronstein chapter catalog alias and by
  `deriv_ne_zero_iff_isRoot_normal`.
- The other moved declarations are the local support ladder for the two root-characterization
  theorems.

## Unify list

- Keep normal/special/splitting predicates in the earlier canonical-representation leaves.
- Put the coefficient-lifting root characterization in a dedicated leaf.
- Leave the parent as the RatFunc canonical-representation construction and correctness API.

## Steps

1. Add `CanonicalRepresentation/RootCharacterization.lean` with the moved declarations.
2. Import it from `CanonicalRepresentation.lean`.
3. Remove the moved root-characterization section from the parent.
4. Gate the new module, parent module, relevant source catalog target, full gate, then rebuild
   the wiki graph.
