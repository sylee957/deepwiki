# Dynamic derivatives for mixed transcendental towers

## Verified obstruction

The current executable carrier `DenseFracTower` is not a representation of a general differential
tower.  In `CarrierRec.lean`, `instCDiffFieldSpecCFracRec` constructs the derivative of every
represented fraction step with

```
fractionFieldDifferential (Differential.implicitDeriv (CPoly.toPoly CPoly.one))
```

so the built-in `CDiffField` at every `DenseFracTower (n + 1)` is the unit-monomial derivative
`t' = 1`.  A stage input can separately carry `Dt = t`, `Dt = t² + 1`, or another monomial
derivative, and the local polynomial algorithms use that argument correctly.  But when a successor
recurses into a coefficient in the preceding field, the field's built-in derivative is again the
unit derivative, not the derivative selected for the preceding extension.

Consequently, no realization can simultaneously satisfy the current `CDiffFieldSpec` transport for
`DenseFracTower` and the recursive realization law for a nonprimitive predecessor.  This is why a
full primitive/exponential/tangent tower theorem cannot truthfully be completed by adding lemmas
around the existing carrier.

## What remains valid

- The new `TowerRealization`/recursive-log construction is a valid semantic pattern for a tower
  **once its coefficient derivatives are supplied dynamically**.
- The local ordinary and LRT adapters are valid for the current, static represented derivative.
- The new coefficient-stage API correctly carries a requested lower `Dt`; this prevents the former
  accidental hard-coding of `Dt = 1`, but it cannot by itself change the carrier's derivative.

## Required replacement

Introduce a representation-independent `DifferentialTowerPresentation` indexed by depth.  It must
carry, at every level:

1. the computable field and polynomial representation;
2. an **explicit** coefficient derivation and its denotational square, rather than relying on the
   globally inferred `CDiffField` instance;
3. the monomial derivative for the next rational-function extension;
4. the induced differential field at the successor and the embedding/derivation commuting square;
5. dense and sparse adapters that implement the same presentation without becoming the orchestration
   layer.

The common Risch-stage specification must take this presentation (or an equivalent explicit
derivation dictionary).  `RischStageInput.Dt` then specifies the extension currently integrated,
while coefficient recursion uses the presentation's preceding derivative.  This makes the
`TowerRealization` construction inhabitable for primitive, exponential, and tangent sequences.

## Migration order

1. Factor the Prop-free computable derivation operations out of `CDiffField` into an explicit
   per-level dictionary, with a `Lawful` companion carrying the denotation law.
2. Parameterize polynomial, Hermite/normal, and special-mononomial stages by that dictionary;
   retain the current dense APIs as primitive-tower compatibility adapters only.
3. Define `DifferentialTowerPresentation` and derive its semantic recursive realization from the
   supplied derivative sequence.
4. Rebuild the ordinary/LRT realization adapters and `TowerCoefficientStage.IsRealized` over the
   presentation.
5. Prove the recursive tangent finish theorem using the lifted lower derivative identity, then
   instantiate primitive, exponential, and tangent stages and derive finite-tower induction.
6. Audit and retire the static `DenseFracTower` orchestration paths once callers use the new
   presentation; preserve only deliberately primitive compatibility imports.

This is a design correction, not a proof gap: continuing with the static carrier would make a
mixed-tower soundness claim false in its intended semantics.
