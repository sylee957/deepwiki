# Lazard base obstruction reorganization

## Target module

Create `DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.LazardBaseObstruction` for the concrete
`xy + 1` obstruction to automatic Lazard base divisibility, and keep
`LazardDescent` focused on the base-condition and sorted-basis descent API.

## Declarations to move

- `leadingYCoeff_xyAddOne_not_dvd_one`
- `lazardView_xyAddOne`
- `leadingYCoeff_xyAddOne`
- `not_isUnit_leadingYCoeff_xyAddOne`
- `not_C_leadingYCoeff_dvd_lazardView_xyAddOne`

## Impact

`scripts/wiki rdeps` shows the obstruction declarations are catalog-facing:

- `not_C_leadingYCoeff_dvd_lazardView_xyAddOne` is used by `Sources.Doi_10_1007_b138171.Chapter2`.
- `leadingYCoeff_xyAddOne` is used internally by the obstruction leaf and by the same source catalog.

The descent declarations continue to live behind the old `LazardDescent` import path, which also imports
the obstruction leaf for compatibility.

## Unify list

- Keep theorem names, statements, and proofs unchanged.
- Put the counterexample/obstruction ladder in `LazardBaseObstruction`.
- Keep `HasLazardBaseDvd`, `HasLazardBaseDegreeZero`, and the diagonal descent theorems in `LazardDescent`.

## Steps

1. Add `LazardBaseObstruction.lean` with the five obstruction declarations.
2. Import it from `LazardDescent.lean` and remove the duplicated declarations there.
3. Gate the new leaf, `LazardDescent`, Lazard factorization, the source catalog, and the full repository.
4. Rebuild the wiki graph and commit.
