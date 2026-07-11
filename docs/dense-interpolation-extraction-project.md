# Extract dense interpolation from `GenericBezout`

## Goal

Move the concrete `DensePoly` Lagrange implementation out of
`ComputableAlgebra/GenericBezout.lean` into a dense-named module. Keep the public declarations
and their qualified names unchanged; `GenericBezout` should retain only the representation-selected
`CPoly.interpolate` API, its generic denotation satellites, and the abstract resultant material.

## Boundary

The extraction unit is the `namespace DensePoly` block defining `cinterpolate` plus its
denotation/evaluation/degree theorems. Its local Lagrange-term helpers stay private. The public
surface remains:

- `DensePoly.cinterpolate`
- `DensePoly.toPolyG_cinterpolateG`
- `DensePoly.eval_toPolyG_cinterpolateG`
- `DensePoly.degree_toPolyG_cinterpolateG_lt`

`CPoly.interpolate`, `toPoly_interpolate`, `eval_toPoly_interpolate`, and
`degree_toPoly_interpolate_lt` remain in `GenericBezout.lean` and import the dense module.

## Execution

1. Add `PolyInterpolateDense.lean` with the moved `DensePoly` block and its needed polynomial imports.
2. Replace the block in `GenericBezout.lean` with an import of the new module; do not rename any
   declarations or alter theorem statements.
3. Import the new module in `ComputableAlgebra.lean` immediately before `GenericBezout`.
4. Gate the new module, `GenericBezout`, and a downstream interpolation user such as
   `Engine.SubresultantTowerSpec`, then run the full gate on a clean worktree.
