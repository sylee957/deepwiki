# Make `CFieldDomain` representation-explicit

## Goal

Remove the `DensePoly` default from `CFieldDomain`. A domain proof is a fact about a coefficient
type *and a polynomial representation*, so its representation must be explicit at every use site.
This makes the fraction-domain prerequisite symmetric with `CFrac F P`, `CPolyGcd P`, and
`CPolyEuclidean P`.

## Inventory

Generic fraction algorithms already bind `[CFieldDomain α P]`. The remaining omitted-parameter
uses are dense tower entry points: `DenseFrac β`, `DensePoly β`, or their Risch/tower correctness
layers. They should become `[CFieldDomain β DensePoly]` (and analogously for `α`/concrete aliases).
No generic algorithm should acquire a dense parameter during the migration.

## Phases

1. Remove the default `P := DensePoly` from `CFieldDomain` in `ComputableAlgebra/Fraction.lean`.
2. Mechanically make the dense tower/Risch callers explicit, including `variable`, `omit`,
   `instance`, `example`, and local-binder occurrences.
3. Keep existing generic `P` call sites unchanged; their explicit representation is the target API.
4. Re-run focused tower/Risch gates, then the full gate. Audit that no one-argument
   `CFieldDomain` binder remains in elaborated code.

## Visibility

`CFieldDomain` and its `nz_one`/`nz_mul` laws remain public interface contracts. This migration
does not add a compatibility alias: an omitted representation would hide a material algorithm
choice, so callers must state it.
