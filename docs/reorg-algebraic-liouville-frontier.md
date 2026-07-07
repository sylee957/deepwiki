# Reorganize algebraic Liouville frontier bridge

## Target module

`DeepWiki.SymbolicIntegration.Computable.Algebraic.LiouvilleFrontier`

## Declarations To Move

- `LiouvilleStructure.hasWeakLiouvilleForm_iff_isAlgebraicElementary`
- `LiouvilleStructure.algebraicLiouvilleFrontier_proved`
- `LiouvilleStructure.isAlgebraicElementary_finiteDimensional_discharge`

## Why

`Computable/LiouvilleStructure` should own the weak-Liouville form and descent/progapagation lemmas over
Mathlib's `IsLiouville`. The three moved declarations are the algebraic-completeness bridge from that
weak form into `AlgebraicCompleteness.IsAlgebraicElementary` and
`AlgebraicCompleteness.AlgebraicLiouvilleFrontier`, so readers looking for the algebraic frontier should
find them under `Computable/Algebraic`.

## Impact

- Direct consumers:
  - `Sources/Doi_10_1007_978_3_030_98767_1/Rosenlicht.lean`
- Support imports:
  - `Computable/Algebraic.lean` should import the new module.
- Names and namespaces stay unchanged.

## Unify List

- Keep the weak-Liouville core in `LiouvilleStructure`.
- Keep algebraic-completeness predicates in `Algebraic/AlgebraicCompleteness`.
- Put only the bridge between those two layers in `Algebraic/LiouvilleFrontier`.

## Steps

1. Add `Computable/Algebraic/LiouvilleFrontier.lean` importing `Computable.LiouvilleStructure`.
2. Move the three bridge declarations and their axiom audit to the new module.
3. Remove the bridge declarations/restatement/audit lines from `LiouvilleStructure`.
4. Update the algebraic aggregator and Rosenlicht catalog imports.
5. Gate the new module, old module, catalog, rebuild the wiki graph, run full `scripts/check.sh`, and commit.
