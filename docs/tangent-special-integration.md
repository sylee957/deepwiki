# Recursive hypertangent special integration

## Goal

Implement the concrete `CTangentSpecialIntegrator` required by
`Engine/CoupledDE/TangentCapability.lean`.  It must realize the hypertangent branch of Bronstein,
*Symbolic Integration I*, Section 5.10 without putting coupled-solver details into the generic
Figure-5.1 assembler.

## Mathematical spine

For a hypertangent `t` with `Dt = eta * (t^2 + 1)`, Section 5.10 separates the special
denominator `h = t^2 + 1` from the polynomial part.

1. For a reduced input with pole order `m > 0` at `h`, write the cleared numerator modulo `h` as
   `a * t + b`.
2. Solve the coupled system
   `D c - 2*m*eta*d = a` and `D d + 2*m*eta*c = b` in the coefficient field.
3. Form `q0 = (c*t + d) / h^m`, replace the input by `input - D(q0)`, and recurse.  The valuation at
   `h` strictly increases, so this terminates after the original pole order.
4. Polynomial-reduce the residue.  Its degree-`< 2` remainder has coefficient `r_t`; emit
   `(r_t / (2*eta)) * log(h)` only when this residue is constant.  The remaining constant term is
   the coefficient-field obligation.

The existing `cCoupledDECancelTan` is a degree-bounded realization of the coupled solve, proved
sound by `TangentReconstruct.lean`.  Its present concrete coefficient representation is
`DensePoly Q` (polynomials in `x`), while the stage interface is over `DenseFrac Q`; a correct
realizer must make this denominator-clearing/reconstruction boundary explicit rather than silently
cast coefficients.

## Phases

1. **Coefficient boundary.** Define a private, checked adapter from the current `DensePoly Q`
   coupled solver to the coefficient representation used by a tangent special input.  State its
   output as a field identity, including every nonzero common denominator certificate.  Do not
   change `CTangentCoupledSolver` merely to hide this mismatch.
2. **One-pole reducer.** In a new `CoupledDE/HypertangentSpecial.lean`, implement one checked
   pole-cancellation step.  It extracts `m`, divides the cleared numerator by `t^2 + 1`, invokes
   the adapter, constructs `(c*t+d)/(t^2+1)^m`, and verifies the resulting partial
   `IntegralResult` with `CPoly.checkIdentity`.
3. **Well-founded recursion.** Recurse on the special valuation/pole order, with the decrease
   theorem localized beside the executable recursion.  The public operation returns an
   `IntegralResult`, preserving every log term accumulated by recursive calls.
4. **Polynomial tail.** Compose the existing polynomial reducer with the Section-5.10 degree-one
   remainder rule.  Add the `log(t^2+1)` term only with a checked constant-residue certificate;
   otherwise decline rather than assert elementary integrability.
5. **Capability realization.** Export the selected operation and a
   `LawfulCTangentSpecialIntegrator tangentCoupledSolver ...` instance.  Its proof should compose
   checked one-pole identities and the recursive invariant; `checkedTangentMonomialCase` remains
   the independent outer certificate boundary.
6. **Relative completeness.** State the finite checked-acceptance domain first.  Upgrade it only
   after proving the coupled-system and constant-descent completeness assumptions required by
   Bronstein's theorem.
7. **Integration and retirement.** Instantiate `tangentRischLevel` and its sparse transport with
   the realizer, add focused examples, use `scripts/wiki rdeps` on any previous tangent bridge,
   then retire only genuinely superseded bridge code.

## Verification sequence

For each phase: check the new/touched module, `TangentCapability`, the dense and sparse tangent
Risch-level consumers, then the bare `scripts/check.sh` gate.  Before deleting an old bridge or
driver, run `scripts/wiki build`, `scripts/wiki rdeps`, and a source-level `rg` check because the
current graph index can retain stale edges after a refactor.
