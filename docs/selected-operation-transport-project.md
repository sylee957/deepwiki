# Selected-operation transport project

## Purpose

Finish the algorithm-interface migration at the remaining dense well-founded frontier without
pretending that two lawful selected implementations compute definitionally equal output.

`CPolyGcd DensePoly α` has a generic low-priority selection and the tower-specific high-priority
`CFracGcdCoreWf` selection. Likewise, dense squarefree factorization has a generic Yun selection and
the tower-specific fraction-free selection. Both selections are lawful, but `cHermiteReduceTower`,
`cIntegrateReducedLrt`, and the recursive LRT frontier contain their selected outputs. Replacing the
well-founded instances in their hypotheses therefore changes the terms being certified; a law about
denotations does not make those terms definitionally equal.

## Evidence and boundary

- `Engine/Tower/WellFounded.lean` installs `instCPolyGcdDenseWf` and
  `instCPolySquarefreeDenseWf`, with the latter feeding the exact
  `DensePoly.cHermiteReduceTower` output.
- `ComputableAlgebra/PolyReprGcd.lean` and `PolyEuclideanDense.lean` also provide lawful generic
  dense selections. Their laws establish mathematical correctness, not equality with the
  fraction-free runtime output.
- `cHermiteReduceTowerG_lawfulHermiteReduction`, the LRT residue correction stack, and
  `PrimitiveFrontierLrt.hreducedLrt` certify that exact well-founded output. They are intentional
  `CFracGcdCoreWf` consumers, whereas composition-only clients should continue to depend only on
  `CPolyGcd`, `CPolySquarefree`, `CPolyResultant`, and `CPolySubresultant`.

## Work plan

1. **Pin inventory.** For every remaining `CFracGcdCoreWf` reference, record whether it selects a
   runtime algorithm, proves a fact about a particular selected output, or is an obsolete umbrella
   constraint. Remove only the third category. Use `scripts/wiki rdeps` before changing each public
   theorem or class.
2. **Result contracts, not instance equality.** Where a theorem needs an algorithm's output, state the
   smallest semantic result contract for that output (factorization, exact division, reconstruction,
   or residue relation). Reuse `LawfulCPoly*` laws when they already provide it; add a result-level
   interface only when the needed relation is genuinely absent. Do not add a global axiom that two
   selected instances are equal.
3. **Parameterize executable composition.** Move Hermite and LRT composition bodies to take the selected
   gcd, squarefree, resultant, and subresultant capabilities explicitly, so their outputs are built from
   the same operations their contracts describe. Keep fraction-free code as the dense selected
   implementation rather than wrapping it behind a fake generic definition.
4. **Prove generic soundness.** Reprove Hermite residual and LRT result contracts from the selected
   capabilities. The well-founded correctness development then supplies the dense instance of those
   contracts; it no longer needs to be smuggled through consumer signatures as `CFracGcdCoreWf`.
5. **Migrate frontiers in dependency order.** Start with local Hermite realization lemmas, then reduced
   LRT soundness, then `PrimitiveFrontierLrt` and `LawfulRischLevelLrt`. Change an
   implementation-specific theorem only after its composition consumers use the new contract.
6. **Audit the remainder.** The only surviving `CFracGcdCoreWf` references should be the recursive
   fraction-free gcd/Yun implementation and proofs specifically about that implementation. Re-run the
   direct-concrete-call search and classify every result in the project document.

## Current checkpoint

- The primitive fraction-free PRS recursion and its termination lemma are private behind the
  `CFracGcdCoreWf` instance.
- `cHermiteReduceTower_squarefree_of_decomposition` derives the Hermite leftover-denominator contract
  from any lawful selected squarefree decomposition. The well-founded realization now supplies its Yun
  proof to that generic bridge instead of re-proving the denominator property inside the concrete theorem.
- `cHermiteReduceTower_lawful_of_contracts` assembles the selected Hermite output from its field identity,
  lawful squarefree decomposition, and properness contracts. The well-founded theorem is now a provider
  of those three facts rather than the place where the result interface is assembled.
- `LawfulCPolySquarefree` is the companion law for a selected `CPolySquarefree` operation. The
  fraction-free dense Yun implementation supplies that law from its existing gcd-correctness frontier,
  and the Hermite realization consumes the law rather than naming the Yun implementation directly.
- The LRT assembler now consumes the reduced result's field identity and a separate nonzero rational-denominator
  contract. `PrimitiveFrontierLrt` exports both facts, so recursive LRT composition no longer reaches into the
  well-founded Hermite denominator proof.
- `LawfulCPolySplitFactor` now supplies the denotation law for a selected differential split. The dense
  well-founded splitter is its provider, while canonical normalization derives nonzero/proper normal parts from
  that law without selecting the Wf instance. `LrtReducedProperFrontier` packages soundness and denominator
  nonzeroness for a selected proper reduced input; it supplies `PrimitiveFrontierLrt`, so primitive LRT consumers
  depend on selected operations and result contracts rather than `CFracGcdCoreWf`.
- `cHermiteReduceTowerG_leftover_proper_of_degree_le_one` now quantifies over `CPolySquarefree` and the
  selected `CPoly.squarefreeYun` output. Its Wf/LRT consumer resolves that selection at the concrete
  boundary instead of forcing the properness theorem itself to depend on `CFracGcdCoreWf`.
- `CPolyEuclidean.toPoly_div_congr` now states exact-division congruence for every lawful polynomial
  representation. Hermite's former public dense/Wf-named theorem is retired; only a private notation
  adapter remains for the legacy dense `toPoly` reader at its single file-local call site.
- The private reduced-stage composition lemmas in `IntegratorCases/ReducedSound.lean` now quantify over
  selected squarefree, gcd, and resultant capabilities. `CFracGcdCoreWf` remains only on the public
  Stage-2 theorems that realize those abstract Hermite and residue contracts for the dense Wf output.
- `IsPureNormalBranch` and `IsPolynomialBranch` now depend on the selected gcd and differential
  split-factor capabilities used by `canonicalRepresentationFast`, rather than on the dense
  `CFracGcdCoreWf` implementation that happens to supply those capabilities in Wf drivers. The
  pure-normal and polynomial driver-shape theorems likewise quantify over the selected gcd, split,
  squarefree, and resultant operations used by `cIntegrateGFullWf`.
- `cLogArgTower` now canonicalizes every selected gcd with `CPoly.cmonic`. Its linear-factor theorem
  and the reduced residue-log/field-identity composition layer consequently require only the selected
  squarefree, gcd, and resultant capabilities; the full Wf driver theorems remain concrete because they
  certify that particular runtime output.
- The primitive, polynomial, and hyperexponential one-shot theorems for `cIntegrateGFullWf` are likewise
  selected-operation compositions. Their former `CFracGcdCoreWf` bounds were obsolete umbrellas and have
  been replaced by the gcd, split-factor, squarefree, and resultant capabilities appearing in the driver.
- The Round-2 integral-basis pipeline now threads `[CLinearSolve ℚ]` from `pTraceRadical` and
  `ipOCoords` through `round2Step`, the pass/iteration loop, and `integralBasis`. Fixed `ℚ` coefficients
  no longer cause Lean to hardcode the global nullspace implementation into these executable drivers.
- The general algebraic-function rational and logarithmic solvers, `afIntegrateAlgebraicWf`, and the
  full `cIntegrateGeneralCurveDecide` soundness/completeness API now thread `[CLinearSolve ℚ]`. The
  concrete curve witnesses remain explicit specialization boundaries using the default rational RREF
  instance, while reusable drivers and contracts accept any selected linear-solver implementation.
- The Risch–Norman `cParallelIntegrate` driver and its representation-generic tower wrapper now select
  `CLinearSolve.solveAny` through `[CLinearSolve ℚ]`; Chapter 10 examples remain concrete default-RREF
  regression checks rather than fixing that implementation in the reusable API.
- The coupled-DE base solver, tangent-cancellation recursion, and their soundness/reconstruction chain
  now share a selected `[CLinearSolve ℚ]`; the soundness proofs request `[LawfulCLinearSolve ℚ]` only at
  the row-equation boundary. Chapter 8 executable examples remain default-RREF specializations.
- The dense weak normalizer now selects its resultant operation through
  `[CPolyResultant DensePoly]`. That same capability is threaded through the reusable Risch-DE solver,
  soundness/completeness predicates, decision-procedure API, and next-tower completeness frontier;
  Chapter 6 executable checks remain concrete default-dense specializations.
- Matrix inversion is now the public derived operation `CLinearSolve.matrixInverse`, implemented by
  solving against the standard basis through the selected `solveUnique`. The concrete engine-local
  `matInv` Gauss–Jordan implementation is retired, and Round-2, integral-basis, general-divisor, and
  general-curve decision APIs explicitly thread `[CLinearSolve (DenseFrac ℚ)]`. The fraction-free
  agreement and degree-swell benchmarks still pass at the default represented-fraction solver.
- `canonicalReconstruction_of_charZero` and the shared primitive special-part proof now consume
  `CPolySplitFactor` together with `LawfulCPolySplitFactor`; neither theorem fixes the dense Wf splitter or
  requests gcd correctness that the reconstruction does not use.
- The recursive LRT coefficient integrators depend on the lower-level `LawfulRischLevelLrt` and its selected
  gcd, split, squarefree, resultant, and subresultant operations. The tower instance additionally requests an
  abstract `CRischField`, selected tower-level operations, and the lawful split contract. Its soundness theorem
  no longer exposes `CFracGcdCoreWf` or the implementation-specific PRS `Fact`; those remain only in the
  explicit bridge that constructs `PrimitiveFrontierLrt` from concrete genuine-data proofs.
- The primitive `LawfulRischLevelLrt` base instance now has the same selected-operation boundary: `CRischField`,
  gcd, lawful split, squarefree, resultant, subresultant, and `PrimitiveFrontierLrt`. Its former
  `CFracGcdCoreWf` and PRS-correctness section variables were unused composition umbrellas.

## Verification

For each slice, run the touched module, its immediate consumer, and then `scripts/check.sh` serially.
Build the wiki graph after a green full gate. Validate each new generic executable path on a sparse
carrier where the algorithm is representation-independent; validate dense fraction-free paths by their
semantic result contract, not by an unprovable equality with a different selected algorithm.

## Visibility rule

Keep selected capability operations and result contracts public. Mark only file-local adapters from the
well-founded implementation to a result contract `private`; use `protected` only for carrier readers whose
dot notation is part of the intended API.
