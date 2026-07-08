# IsSimilar fraction-field bridge

## Target module

Move the generic fraction-field bridge for `IsSimilar` into
`DeepWiki.SymbolicIntegration.PseudoDivision`, where `IsSimilar` and its basic
API are defined.

## Declarations to move

- `DeepWiki.SymbolicIntegration.IsSimilar.exists_fractionRing`

## Impact

`scripts/wiki show DeepWiki.SymbolicIntegration.IsSimilar.exists_fractionRing`
currently places the theorem in
`DeepWiki.SymbolicIntegration.SubresultantPRS.Remainder`.

Text search reports direct use only by:

- `DeepWiki.SymbolicIntegration.subresultant_prs_eq_fractionRing`
- the Chapter 1 source-catalog docstring describing that theorem.

## Unify list

- Keep `IsSimilar` satellites with the `IsSimilar` definition.
- Keep subresultant endpoint and PRS-specific fraction-ring statements in
  `SubresultantPRS.Remainder`.
- Do not change theorem statements or exported names.

## Steps

1. Add the fraction-ring import to `PseudoDivision`.
2. Move `IsSimilar.exists_fractionRing` after the core `IsSimilar` API.
3. Remove the duplicate from `SubresultantPRS.Remainder`.
4. Gate `PseudoDivision`, `SubresultantPRS.Remainder`, Chapter 1 catalog, then
   the full library.
