# Special-normal coprimality reorg

## Target module

Move root-level `DeepWiki.SymbolicIntegration.SpecialNormalCoprime` to
`DeepWiki.SymbolicIntegration.CanonicalRepresentation.SpecialNormalCoprime`.

The file proves the coprimality fact used to discharge canonical reconstruction
split hypotheses, and already imports the canonical-representation layer.

## Declarations to move

- `isSpecial_of_prime_dvd_isSpecial`
- `isCoprime_of_isSpecial_isNormalSqfree`

## `wiki rdeps` impact

`isCoprime_of_isSpecial_isNormalSqfree` is used by:

- `canonicalReconstruction_of_charZero`
- `crNormNum_degree_lt_crNormDen`

`isSpecial_of_prime_dvd_isSpecial` is only used by
`isCoprime_of_isSpecial_isNormalSqfree`.

## Unify list

- Keep generic normal/special definitions under `Core.Differential.NormalSpecial`.
- Keep canonical-representation-specific split discharge lemmas under
  `CanonicalRepresentation`.
- Delete the root-level module path; update internal imports directly.

## Steps

1. Move `SpecialNormalCoprime.lean` into `CanonicalRepresentation/`.
2. Replace its broad `CanonicalRepresentation` import with the specific
   `CanonicalRepresentation.NormalSqfree` import to avoid an aggregator cycle.
3. Add the new module to `CanonicalRepresentation.lean`.
4. Update `Computable/CanonicalReconstructionCharZero.lean` to import the new path.
5. Gate the moved module, its consumer, and the full library; rebuild the wiki graph
   and commit.
