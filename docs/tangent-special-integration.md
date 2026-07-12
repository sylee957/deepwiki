# Recursive hypertangent special integration

## Status

`Engine/CoupledDE/TangentSpecial.lean` now provides `recursiveTangentSpecialIntegrator`: a selected,
certificate-checked `CTangentSpecialIntegrator` with a named finite acceptance domain. Its private raw
candidate generator recognizes a bounded power of `t²+1`, recursively lowers that pole through the coupled
solver, polynomial-reduces the remainder, and emits the checked `log(t²+1)` term. The focused executable
validation accepts a pole-order-three input.

This is a sound checked realization, not yet a proof of Bronstein's semantic completeness theorem.

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

1. **Coefficient boundary (bounded rational solver).** The recursive algorithm consumes the
   representation-neutral `CTangentCoefficientSolver α` interface. Its `DenseFrac ℚ` realization,
   `tangentRationalCoefficientSolver` clears all input and derivative denominators, solves the finite
   rational linear system at the supplied degree bound, and certificate-checks the result. The older
   `tangentPolynomialCoefficientSolver` remains a narrower specialized realizer. Semantic completeness
   still needs a bound proving that every solvable rational system is searched.
2. **One-pole reducer (checked).** `TangentSpecial.lean` divides by `t^2 + 1`, invokes the coefficient solver
   operation, constructs the candidate correction, and releases the final result only through
   `CPoly.checkIdentity`.
3. **Structural recursion (implemented).** The executable recursion follows the recognized pole
   order and accumulates the rational part. A semantic valuation-decrease theorem remains open.
4. **Polynomial tail (checked).** The selected operation uses nonlinear polynomial reduction, recursively
   integrates its constant coefficient to a rational part plus lower-field logarithms, lifts both into the
   current level, and emits `log(t^2+1)` only after a computable constant-residue guard; otherwise it declines.
5. **Capability realization (implemented).** The raw candidate is private;
   `recursiveTangentSpecialIntegrator` is the selected checked operation and has both `Lawful…` and
   finite-domain `Complete…` instances. The operation and its dense/sparse Risch-level compositions are generic
   over the coefficient differential field; `DenseFrac ℚ` is only the concrete rational-solver realization.
6. **Semantic relative completeness.** Upgrade the checked domain only
   after proving the coupled-system and constant-descent completeness assumptions required by
   Bronstein's theorem.
7. **Level integration (implemented).** The selected operation executes Bronstein's pole-order-three
   example, the `log(t^2+1)` polynomial case, and a lower-field `1/x` tail whose `log x` result is lifted into
   the outer result. `recursiveTangentRischLevel` and
   `sparseRecursiveTangentRischLevel` inject a per-level coupled solver and checked special stage,
   while retaining polynomial and normal stages as explicit dependencies. The semantic completeness
   upgrade remains. `TangentDepth.lean` packages these choices uniformly over `DenseFracTower n`; every
   successor coefficient operation now runs the preceding selected Risch level and certificate-checks the
   lifted rational-plus-log result. The checker is complete for semantic coefficient-result certificates, and
   the dense-fraction bridge now derives such a certificate from a lower `IsIntegralResultP` identity with
   constant coefficients and nonzero arguments. A lower `LawfulGenuineCRischLevel` plus
   `CompleteCRischLevel` now implies eventual success of the coefficient adapter. The outer Risch fuel is split
   into polynomial and monomial budgets, and the monomial budget reaches the lower Risch call through the
   tangent coefficient adapter; tower capabilities no longer freeze a per-level coefficient fuel. Dense and
   sparse assembled levels now carry that genuine-result contract through every successor. Full semantic
   completeness still requires the coupled solver and its degree-bound hypotheses. The special-stage budget
   now splits into independent denominator-recognition, encoded coupled-solver, polynomial-reduction, and
   lower-coefficient budgets. `TangentSpecialConfig` has been retired: the executable receives its selected
   `CPolynomialReduction` operation explicitly, and sparse tower capabilities separately expose the outer
   sparse and tangent-internal dense polynomial stages with their contracts. `TangentReducedCompleteDomain`
   records semantic solvability along every selected pole-lowering state, and its composition theorem derives
   one finite encoded budget solely from `CompleteCTangentCoefficientSolver`, without a solver-monotonicity
   assumption. The outer candidate-completeness theorem now continues that witness through
   `CompleteCPolynomialReduction` and `CompleteCRecursiveElementaryIntegrator`, producing one finite budget
   for the entire raw special stage. Promoting this to the public checked integrator still requires deriving
   its final certificate from the stage soundness laws.

## Verification sequence

For each phase: check the new/touched module, `TangentCapability`, the dense and sparse tangent
Risch-level consumers, then the bare `scripts/check.sh` gate.  Before deleting an old bridge or
driver, run `scripts/wiki build`, `scripts/wiki rdeps`, and a source-level `rg` check because the
current graph index can retain stale edges after a refactor.
