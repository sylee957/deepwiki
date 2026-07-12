# Algebraic coefficient-log transport

## Objective

Allow an upper hyperexponential or tangent stage to consume a lower primitive
LRT antiderivative without erasing its algebraic-residue logarithms. This is
the missing construction required for arbitrary orders of primitive,
hyperexponential, and tangent extensions, rather than merely a selected tower
of independently certified stages.

## Current boundary

`CRecursiveElementaryIntegrator` returns `CoefficientIntegralResult`: one
coefficient-field rational value plus ordinary constant-coefficient logarithms.
`Tower/RecursiveElementary` lifts a lower `IntegralResult` into that format.
An `LrtResult`, however, represents a family
`Σ_{R(c)=0} c log S(c,t)` over an algebraic constant extension; it cannot be
encoded as `List (α × α)` without choosing roots or extending `α`. The current
primitive recursion therefore correctly requests only a log-free rational
lower antiderivative.

`Tower/AlgebraicCoefficient.lean` now supplies the complete semantic boundary:
`AlgebraicCoefficientLog` has separate ordinary and root-free LRT
constructors, `AlgebraicCoefficientIntegralResult` stores their common list,
and `IsAlgebraicCoefficientIntegralResult` interprets it over every
same-universe algebraically closed differential extension. The ordinary and
LRT embeddings preserve the derivative identity as well as their respective
genuine-log certificates. The next step is to make this result language the
output of coefficient recursion rather than only an embedding target.

The tangent reconstruction audit adds one necessary distinction for phase 4:
`AlgebraicCoefficientLog` describes a **lower** unit-monomial antiderivative,
whose derivative is in the coefficient field. It is not a replacement for an
upper `IntegralResult.logs` entry, whose argument is differentiated by the
current monomial `Dt`. The next full-result carrier must therefore retain two
separate layers: local `(coefficient, polynomial-argument)` logs for the
current extension, and inherited algebraic coefficient logs. It combines their
denotations only at the reconstruction theorem.

## Phases

1. **Done.** Define an algebraic coefficient-log language, with ordinary log terms and
   root-free LRT residue-log families as distinct constructors. Give it a
   semantic interpretation over an algebraically closed differential extension
   and genuine-log validity predicates.
2. **Done.** Define an algebraic coefficient-integral result: a rational coefficient
   part plus that language. Prove embeddings from `CoefficientIntegralResult`
   and `LrtResult`, preserving derivative identities and genuine logs.
3. **Done.** Generalize the recursive coefficient interface and its checked adapter to
   this result language. The representation-independent `IntegrationStage`
   contract now lives in `Tower/Stage`, and the ordinary recursive adapter
   embeds through `CRecursiveElementaryIntegrator.asAlgebraicCoefficientStage`.
   `DenseLrtStage.asAlgebraicCoefficientStage` supplies the primitive adapter
   from its genuine stage theorem while retaining the root-free residue guard.
4. **In progress.** `Tower/TranscendentalResult.lean` defines the two-layer
   full-result carrier and its semantic invariant. Generalize tangent and
   hyperexponential special/reconstruction assemblies to append inherited
   algebraic coefficient logs without forcing them into `IntegralResult.logs`,
   then prove their local soundness and relative completeness by composition.
5. Replace the selected-only claim in `TranscendentalTowerScheme` with a true
   heterogeneous successor constructor, whose lower adapter is supplied by the
   preceding stage. Then prove finite-tower soundness and relative completeness
   by induction.
6. Audit and retire the old selected-only mixed wrapper only once all public
   callers use the heterogeneous constructor. Dense and sparse remain
   conversion adapters; neither gains an independent assembler.

## Gates

Gate each phase serially: the coefficient-language module, its ordinary and
LRT embeddings, tangent/hyperexponential assemblies, `Tower/Transcendental`,
then the full `scripts/check.sh` gate. Before deleting a wrapper, run
`scripts/wiki rdeps` and confirm current-source callers with `rg` when the
graph is stale.
