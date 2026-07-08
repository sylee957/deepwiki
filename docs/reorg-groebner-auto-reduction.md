# Groebner auto-reduction reorg

## Target module

Create `DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.AutoReduction`.

`ReducedBasis` should keep the reduced-basis construction pipeline and final existence theorem,
while `AutoReduction` owns the normal-form facts used to replace each basis element by its
remainder modulo the other elements.

## Decls to move

- `coeff_remainder_degree_eq`
- `degree_remainder_eq`
- `isUnit_leadingCoeff_erase`
- `autoReduceElt`
- `autoReduceElt_spec`
- `autoReduceElt_reduced`
- `sub_autoReduceElt_mem_span`
- `autoReduce`
- `mem_autoReduce`
- `isReducedGroebnerBasis_autoReduce`

## `wiki rdeps` impact

- `coeff_remainder_degree_eq` is used by `degree_remainder_eq`.
- `degree_remainder_eq` is used by `autoReduceElt_spec`.
- `autoReduceElt` and satellites are used by `autoReduce`, `mem_autoReduce`,
  `isReducedGroebnerBasis_autoReduce`, and then by `exists_isReducedGroebnerBasis`.
- `isReducedGroebnerBasis_autoReduce` is used by:
  - `exists_isReducedGroebnerBasis`
  - the source catalog alias for Chapter 2
  - `lazard_Pk_eq_Rk_Sk_unconditional` through the reduced-basis existence theorem.

## Unify list

- Keep division/remainder primitives in `BuchbergerAlgorithm`.
- Put auto-reduction remainder behavior in `AutoReduction`.
- Keep monicization/minimal-degree representative construction in `ReducedBasis`.
- Keep `exists_isReducedGroebnerBasis` in `ReducedBasis`, importing `AutoReduction`.

## Steps

1. Add `Groebner/AutoReduction.lean` with the moved declarations.
2. Import `AutoReduction` from `ReducedBasis`.
3. Remove the moved declarations from `ReducedBasis`.
4. Gate `AutoReduction`, `ReducedBasis`, downstream `DividedBasis`, the source chapter, and
   the full project.
