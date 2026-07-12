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

## Landed foundation

`MonomialDeriv.lean` now provides `CFieldDerivation` and its explicitly parameterized
`LawfulCFieldDerivation` law. `CPolyEngine.mapDerivWith` and
`CPolyEngine.monomialDerivWith` use this dictionary directly, while the legacy implicit operations
remain compatibility wrappers. `Tower/Deriv.lean` similarly provides
`CFrac.towerDerivCFracWithDerivation` and its function-field square.

`Tower/DifferentialPresentation.lean` records a finite derivative sequence, the monomial derivative
at every successor, the computable quotient-rule equation, and the successor semantic square with
the lower `Differential` supplied explicitly. It deliberately does not install a global
`Differential` instance: doing so would let `CRingSpec.R` silently recover the legacy primitive
derivative. This is the common dynamic input that the Risch/Hermite/special stages must consume.

`Tower/PolyPartDynamic.lean` now exports the checked nonlinear and primitive kernels as
`CDifferentialPolynomialReduction`: accepted outputs have an explicit reconstruction and normal-form
certificate, and completeness remains an independent domain-relative capability. The polynomial
branch can therefore enter `RemainderIntegrationStage` without recovering a global derivative.

`Hermite/DifferentialNormal.lean` supplies the corresponding explicit normal-reduction contract.
Its certificate includes the function-field reconstruction equation, constant logarithmic
coefficients, nonzero log arguments, and relative completeness. Existing normal reducers are
certified compatibility adapters through the legacy context, so dense and sparse code remains an
implementation choice rather than a second orchestration language.

`MonomialDifferentialStage.lean` gives the special/polynomial branch the same treatment. It has an
explicit function-field log sum and a certified adapter for existing primitive, hyperexponential,
and tangent special solvers. `Tower/RecursiveElementaryDynamic.lean` already provides the analogous
explicit coefficient-recursion stage.

## Migration order

1. Parameterize normal postprocessing and the canonical/one-level assembly handoffs by the landed
   explicit dictionary, then compose the polynomial, special, normal, and coefficient stages through
   one dynamic output-remainder invariant.
2. Rebuild the ordinary/LRT realization adapters and `TowerCoefficientStage.IsRealized` over the
   presentation.
3. Prove the recursive tangent finish theorem using the lifted lower derivative identity, then
   instantiate primitive, exponential, and tangent stages and derive finite-tower induction.
4. Audit and retire the static `DenseFracTower` orchestration paths once callers use the new
   presentation; preserve only deliberately primitive compatibility imports.

This is a design correction, not a proof gap: continuing with the static carrier would make a
mixed-tower soundness claim false in its intended semantics.
