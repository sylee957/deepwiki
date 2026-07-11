# Representation-independent computable fractions and algorithm dependencies

## Goal

Turn `CFrac` from the current dense-polynomial carrier into the fraction-representation interface,
parallel to `CPoly`. Rename the current specialization to `DenseFrac`, add `SparseFrac`, and make
SymbolicIntegration depend on abstract, lawful polynomial and linear-algebra algorithms instead of
calling dense gcd, resultant, subresultant, and solve implementations directly.

The intended stack is:

```text
CPoly P + CPolyEngine P + LawfulCPolyEngine P
                    |
              CFrac F P
               /       \
       DenseFrac       SparseFrac
```

`CFrac F P` associates a fraction carrier `F` with the polynomial representation `P` stored in its
numerator and denominator. `DenseFrac` uses `DensePoly`; `SparseFrac` uses `CPoly.SparsePoly`.
Fraction arithmetic is generic over the interface and selects the underlying polynomial engine through
`CPolyEngine P`, so the dense specialization retains the established computation while the sparse one
runs the same fraction algorithm.

## Phases

1. **Carrier/interface split — DONE.** Introduce `CFrac F P` with genuinely distinct `DenseFrac` and
   `SparseFrac` proof-carrying structures in symmetric representation modules. Their constructors are private
   and pair storage is protected; construction and generic inspection pass through `CFrac`, while symmetric protected
   `DenseFrac.num`/`den` and `SparseFrac.num`/`den` satellites preserve readable dot notation without exposing
   concrete fields. Migrate type occurrences from the old `CFrac α` carrier to `DenseFrac α`; keep `CFrac.*`
   as the generic API namespace, not a compatibility type alias.
2. **Raw fraction boundary — DONE.** Retire the duplicate legacy pair arithmetic. Valid field operations now
   use `DenseFrac`/`CFrac`; the unused `RawFrac` module was removed once reverse-dependency checks showed
   that no algorithm boundary still consumed unchecked numerator/denominator pairs.
3. **Generic field engine — DONE.** Generalize denominator-domain evidence, constructors, add/mul/neg/inv,
   zero and equality tests, and the `CField` instance over `[CFrac F P] [CPolyEngine P]`. Preserve the Prop-free runtime
   path; correctness assumptions remain in companion lawful classes. `CFrac.ofFraction` requires explicit
   nonzero evidence, while `CFrac.ofFraction?` exposes the executable checked `Option` boundary. The public
   operations are the symmetric `CFrac.add`/`mul`/`neg`/`inv`/`sub`/`deriv`/`isZero`/`eq` family; the legacy
   `q*NZ` names were retired because denominator validity is already enforced by the carrier.
4. **Generic denotation — DONE.** State the bridge into `RatFunc` through `CPoly.toPoly`, prove the fraction
   homomorphism laws with `LawfulCPolyEngine`, and expose `CFieldSpec (F α)`. Validate both
   `DenseFrac` and `SparseFrac` through their representation-independent denotation laws.
5. **Tower rewiring — IN PROGRESS.** Generalize fraction derivation and tower constructors over a fraction
   representation where their bodies only use the interface. `towerDerivCFracWith` and the iterated
   `CDiffField` instance now work for any `CFrac F P`, with a generic `RatFunc` commuting square and a
   `SparseFrac` computation witness. The lawful `CFieldSpec` instance is now generic over every `CFrac F P`,
   rather than duplicated for dense and sparse carriers; recursive `CharZero`, `Algebra ℚ`, and
   `CDiffFieldSpec` tower instances are representation-independent as well. The parallel tower coefficient
   guard now works over any inner `CFrac F Q`, selecting gcd and division through `CPolyGcd Q` and
   `CPolyEuclidean Q`; dense and sparse inner fractions both execute through the same wrapper. Keep dense
   specialization only where an actual downstream polynomial algorithm is still dense.
6. **Abstract algorithm capabilities — IN PROGRESS.** Introduce Prop-free/lawful pairs for polynomial
    gcd/division, resultant/subresultant, and linear solve. `CLinearSolve`/`LawfulCLinearSolve` now expose
    unique and arbitrary consistent-system solves plus homogeneous-kernel selection, with length and row-equation
    laws for each returned vector. Parametric Risch constraints, represented-fraction logarithmic-dependence
    constraints, and the parallel Risch–Norman system now expose those lawful row equations; coupled-DE
    and parallel-integration consumers request the capability rather than `cConstSolveUniqueQ` or
    `cConstSolveAnyQ` directly. In the second slice,
   `CPolyGcd`/`LawfulCPolyGcd` selects gcd for raw-fraction reduction, with the selection indexed by
   both polynomial representation and coefficient field, while
   `CPolyEuclidean`/`LawfulCPolyEuclidean` selects division and extended Bézout: dense polynomials use the
   well-founded engine, sparse polynomials use the generic `CPoly` engine, and the rational-function
    exact-division bridge consumes only the capability. Concrete dense and generic implementations become
    instances. Gcd-derived fraction normalization and polynomial lcm are now representation-independent
    `CPoly` algorithms selecting both gcd and exact division through those capabilities; normalized Bezout
    cofactors, extended-Euclidean splitting, and the reduced Diophantine solver likewise select `gcdExt`,
    quotient, and remainder through `CPolyEuclidean`. The former dense-only `qnormPair`, `cLcmQ`,
    `cbezoutOneWf`, `cextendedEuclideanSplitWf`, and `cdiophantine` helpers are retired. The third slice adds
    `CPolyResultant`/`LawfulCPolyResultant`: dense polynomials select the
   well-founded PRS resultant, sparse polynomials select the generic Sylvester determinant, and tower,
   radical, general-curve, and discriminant consumers request the capability. The dense implementation and
   its lawful instance now live in `ComputableAlgebra/PolyResultantDense.lean`. The tower residue-resultant
   bridge now proves correctness from `LawfulCPolyResultant`. The fourth slice generalizes the
   Sylvester-submatrix algorithm itself over `CPoly` and introduces `CPolySubresultant`/
   `LawfulCPolySubresultant`; dense and sparse LRT paths share the implementation, with correctness proved
   once through `CPoly.toPoly`. The fraction-free Bareiss determinant, adjugate, and Cramer solve are also
   representation-independent over `CPoly P`, selecting exact division through `CPolyEuclidean P`; dense
   consumers and a sparse execution witness share that core. Its rational-function denominator clearing,
   determinant, adjugate, inverse, and solve wrappers are likewise generic over `CFrac F P`; `DenseFrac`
   consumers and a `SparseFrac` determinant witness use the same definitions. Hermite row reduction and its
   polynomial-matrix operations are representation-independent as well: `PolyMatrix P α` carries the
   representation explicitly, Euclidean sweeps select `CPolyEuclidean.div`, and dense algebraic-function
   consumers plus a sparse triangularization witness share the implementation. The bivariate
   subresultant PRS and tower primitive-part consumers now select gcd, extended gcd, quotient, and
   remainder through `CPolyGcd` and `CPolyEuclidean`; dense correctness proofs cross the selection boundary
   with the instance equality lemmas. The tower split-factor, Yun squarefree, Hermite reduction, and SPDE
   paths now select all quotient and extended-gcd operations through `CPolyEuclidean`; their correctness
   stacks use the lawful Euclidean identity, remainder-degree, exact-division, and divisibility bridges
   rather than unfolding the dense implementation. Hermite residual recovery is representation-independent
   over `CPoly P`: its raw-pair denotation, split and radical certificates, and decidable honesty bundle use
   `CPolyEngine P` and `CPolyEuclidean P`, so dense source witnesses are only specialization boundaries.
   Fraction gcd cancellation now lives in `ComputableAlgebra/FracReduce.lean` and is generic over
   `CFrac F P`, `CPolyGcd P`, and `CPolyEuclidean P`; the dense-only `Engine/QFunReduce.lean` module is
   retired, and the public operation is now the symmetric `CFrac.reduce` API with dense and sparse
   computations plus a shared denotation theorem.
   Monic-denominator normalization is the generic `CFrac.reduceMonic` operation in the same module;
   algebraic integral-basis and divisor consumers no longer depend on the dense-only `qReduceNZ` helper.
   The parametric Risch-DE constraint builder, kernel solve, and limited-integration wrapper now live in
   the `CPoly` namespace: gcd/lcm and quotient/remainder select `CPolyGcd` and `CPolyEuclidean`, while
   homogeneous solving selects `CLinearSolve.nullspaceBasis`. Dense consumers and a sparse execution
   witness share the same definitions. The logarithmic structure decision is generic over `CFrac F P` as
   well: denominator clearing selects the gcd and Euclidean capabilities, relation detection selects the
   linear solver, and dense and sparse fractions execute the same `CFrac.logIsNewMonomial` and
   `CFrac.logRelationCoeffs` definitions. Polynomial quotient arithmetic now lives in
   `ComputableAlgebra/PolyQuotient.lean`: `reduceMod`, `mulMod`, power-basis construction,
   multiplication matrices, and trace matrices are generic over `CPoly P`, select engine and Euclidean
   capabilities, carry lawful denotation satellites, and execute on sparse polynomials. The algebraic
   function-field and integral-basis stacks consume that API; only the `DenseFrac` Bareiss discriminant
   wrapper remains a deliberate dense specialization. The radical Case 1, Case 2, Case 3, generalized
   Case 3, and exponential cofactor/residual kernels are generic `CPoly` algorithms, with sparse execution
   witnesses; the surrounding `RadElem` iteration stays domain-specific while selecting quotient,
   remainder, and extended-gcd operations through `CPolyEuclidean`. Cantor/Mumford arithmetic,
   integral-basis and divisor utilities, Picard support extraction, and general-curve coprimality contracts
   likewise select Euclidean operations rather than naming the dense well-founded implementations. The
   tower Risch-DE normalizer, valuation, denominator stages, Hermite/LRT contracts, and function-algebra
   soundness hypotheses now select `CPolyEuclidean.div`/`gcdExt`; only the dense Euclidean implementation
   and its implementation-level correctness proofs name `cdivWf`/`cgcdWf` directly. That specialization now
   lives in `ComputableAlgebra/PolyEuclideanDense.lean`, so Engine modules import the selected capability
   rather than owning the implementation. Algebraic Round-2,
   full integral-basis, and general-curve rational/log solves select `CLinearSolve.nullspaceBasis`; the
   duplicate algebraic `kernelBasis` implementation has been retired. `CPolySubresultant` now lives in
   ComputableAlgebra, and the root-free LRT construction and its correctness stack consume the selected
   scalar and parametric subresultant operations rather than exposing the concrete helper name. Lagrange
   interpolation now has a representation-selected `CPoly.interpolate` output with denotation, evaluation,
   and degree laws; residue-resultant and parametric-subresultant construction independently select their
   inner elimination and outer interpolation representations, with all-sparse execution witnesses. The
   radical and general-curve algebraic residue-resultant wrappers likewise expose `*With` kernels selecting
   their interpolation representation while retaining dense entry points for the existing soundness stack.
   The general-curve kernel independently selects the base-variable polynomial, curve-variable polynomial,
   fraction carrier, and residue-variable polynomial representations; an all-sparse double-resultant witness
   exercises both selected resultant capabilities and selected Euclidean quotient recovery. Algebraic-function
   trace discriminants now run as `CFrac.discriminant` with independently selected base and curve polynomial
   representations, while `CPoly.discResultant` selects the derivative and resultant capabilities; the dense-only
   entry points were retired and a sparse curve cross-check covers both paths. Base single-`w`
   limited integration now runs as `CFrac.limitedIntegrateSingleBase`, selecting fraction access/construction,
   polynomial gcd/division and antiderivation, and nullspace solving through their interfaces; dense and sparse
   fraction witnesses execute the same definition, while the num/den callback remains an explicit dense boundary.
   The base properness and parametric logarithmic-derivative recognizers also moved from `DensePoly` to `CFrac`;
   coefficient extraction now uses `CPoly.coeff`, and a sparse-fraction witness shares the recognizer body.
   Point evaluation now belongs to the symmetric fraction API as `CFrac.eval`, selecting polynomial evaluation
   for the stored representation; the dense-only `qEvalAtRoot` helper was retired and Round-2 trace reduction
   consumes the generic operation, with sparse evaluation evidence colocated in `Fraction.lean`.
   Logarithmic-relation verification now runs as `CFrac.logRelationCheck`; the dense-only
   `structRelationCheck` was retired, rational coefficients enter through `CFrac.ofScalar`, and the sparse
   logarithmic-dependence witness verifies the recovered relation through the same generic fraction arithmetic.
   Function-algebra component recombination now runs as `CPoly.afIntegrateFunctionAlgebra`, selecting modular
   multiplication, Euclidean remainder, addition, and zero through the polynomial interfaces; its existing dense
   quotient soundness theorem crosses the specialization boundary explicitly, and a sparse witness executes the kernel.
   Finite root scanning with multiplicity now runs as `CPoly.rootsWithMult`, using representation bounds, selected
   evaluation, linear-factor construction, and Euclidean division rather than dense list length and literals; the
   Picard point-extraction path specializes it to dense storage while a sparse double-root witness shares the kernel.
   Yun squarefree decomposition now has a representation-independent `CPoly.squarefreeYun` kernel selecting
   derivative, normalization, quotient, subtraction, and extended gcd through polynomial capabilities. The
   simple-radical square/squarefree split, integral-basis checks, discriminant, and genus consequently live in
   `CPoly`. Selection is coefficient-aware: sparse polynomials and ordinary dense coefficients use the generic
   kernel, while dense tower coefficients with `CFracGcdCoreWf` select the established fraction-free Yun engine.
   Tower Hermite reduction consumes `CPoly.squarefreeYun`, and its correctness stack crosses the selected dense
   implementation through an explicit equality bridge.
   Differential normal/special splitting now runs as `CPoly.splitFactor`, composing the selected gcd and
   Euclidean capabilities with the generic monomial derivative. Denominator and reduced canonical-normality
   gates moved into the symmetric `CFrac.denomNormalGate` / `CFrac.canonNormalizedGate` API; the Risch-DE
   instance, sound solver, and completeness stack specialize that API to dense towers, while sparse fractions
   execute both gates through the same kernel. Weak normalization, its semantic normality predicate, reduction
   bridge, Boolean specification, and `RatFunc` denotation satellites now quantify over arbitrary `CFrac F P`;
   only the re-pin corollary and legacy `towerFractionFieldDeriv` spelling remain dense specializations.
   The established dense well-founded split loop itself now takes `CPolyGcd DensePoly α`, and its correctness
   is proved from `LawfulCPolyGcd` through a private dense-denotation adapter; the former
   `CgcdBCorrect cgcdFFCoreWf` callback has been removed. Weak normalization, normal-denominator reduction,
   special-polynomial construction, and their completeness bridges request the selected gcd/split
   capabilities rather than using `CFracGcdCoreWf` as an implementation-selection proxy.
   The well-founded SPDE and headline Risch-DE runtimes now select `CPolyGcd` and `CPolySplitFactor`
   directly, and the structural/raw-soundness stack carries those capabilities instead of the concrete
   fraction-free gcd core. The one-level integration assembly likewise selects squarefree decomposition,
   gcd, splitting, and resultant capabilities independently; `CFracGcdCoreWf` remains only where the dense
   tower implementation or its implementation-specific correctness frontier is genuinely required.
   In particular, the recursive LRT frontier certifies the exact well-founded Hermite/LRT output; substituting
   an independently selected (though lawful) implementation there requires an explicit transport theorem,
   not an instance-only migration.
   The entire `Engine/RischDE/` completeness stack now follows that boundary: normal-denominator and
   degree-bound residuals, inner exhaustiveness, wrapper completeness, and the decision-procedure frontier
   expose selected gcd/split capabilities and contain no `CFracGcdCoreWf` reference. Root-free LRT integration
   likewise requests squarefree, resultant, and subresultant capabilities directly, with its executable
   validation routed through the project computation tactic.
   The reduced-integrator composition is now capability-specific as well: Hermite reduction requests
   `CPolySquarefree`, residue construction requests `CPolyResultant`, rational log arguments request
   `CPolyGcd`, and `cIntegrateCase` composes those with `CPolySplitFactor`. The root-free LRT log path selects
   `CPolySquarefree`, `CPolyResultant`, and `CPolySubresultant` directly, without a fraction-gcd proxy; its
   `CPoly.lrtLogArg` kernel is representation-independent and has both dense and sparse execution witnesses.
   The shared Rothstein–Trager numerator and residue interpolation now live at `CPoly.amcDd` and
   `CPoly.residueResultantTower`; dense names are specialization boundaries, while sparse inner and outer
   polynomial representations execute the same kernels. The primitive and guarded-primitive hooks no longer
   carry a gcd-selection proxy; the primitive LRT decision API explicitly selects squarefree, resultant, and
   subresultant operations, while its raw correction-proof setup remains concrete. Canonical reconstruction
   and the shared primitive special-part soundness now
   likewise request the selected gcd together with its lawful interface. Outside its concrete correction-proof
   boundary, the hyperexponential hook's normal/full drivers, full-soundness API, and `hyperexpCase` hook now
   request selected gcd, split, squarefree, and resultant capabilities. The
   tower Risch-DE completeness predicate/frontier now request selected gcd and differential-split
   capabilities directly. The fuel-free top integrator likewise declares its actual composition inputs:
   gcd, differential split, squarefree decomposition, and resultant, rather than using the recursive dense
   fraction-gcd implementation as an umbrella constraint. The
   generic reconstruction field-identity helper is private after a direct-dependent
   audit showed that only `canonicalReconstruction` consumes it.
   The rational RREF implementation, its `CLinearSolve ℚ` instance, and the corresponding lawful proof
   now live in `ComputableAlgebra/LinearAlgebraRat*.lean`; SymbolicIntegration imports the selected
   linear-solver capability instead of owning the concrete executable solver or its correctness stack.
   SymbolicIntegration consumers request the weakest capability they need. The redundant
   `CTowerGcdWitnessWf` class has been retired: its only law followed from `LawfulCPolyGcd`, whose public
   `compute_one_isUnit` satellite now supplies the tower split-factor proof without mentioning
   `cgcdFFCoreWf`.
7. **Consumer migration — IN PROGRESS.** Rewire closed components in dependency order: rational reduction and tower
   gcd; residue/resultant and squarefree layers; linear systems and coupled DE; algebraic-function
   Bareiss/Hermite consumers. Remove parallel implementations when two bodies express the same algorithm;
   retain representation-selected optimized instances when their implementations intentionally differ.
8. **Completion audit.** Classify every remaining `DenseFrac`, `DensePoly.c*`, concrete subresultant,
   and concrete solver dependency as either an explicit specialization boundary or an unfinished
   migration. Run the full warning-/sorry-free gate and rebuild the dependency graph before completion.

## Checkpoint discipline

Land the phases in small gate-green commits. Each new representation-independent executable path gets a
`SparseFrac` or `SparsePoly` consumer or correctness witness. Computable declarations do not contain
ad hoc `native_decide` proof scripts or executable showcase examples. Concrete evidence goals use the local
`cdecide` tactic, which permits only definitional reduction and kernel `decide`. Executable showcases that
intentionally permit compiled decision use the separate `ccompute` tactic.
Constructor APIs still require explicit evidence or expose an `Option`-returning checked boundary;
concrete fraction literals use the intent-specific `cfrac_nonzero` tactic rather than a default proof.
A generic
wrapper around a concrete dense algorithm does
not count as migration: the algorithm itself must be supplied through an abstract capability or remain
explicitly dense at the call site.

Access modifiers follow dependency evidence rather than visibility minimization: delete dead APIs; use
`private` only for file-local implementation or proof helpers; use `protected` only when dot notation is
the intended reading; and keep interface operations, lawful bridges, and predictable satellite lemmas
public so downstream algorithms can depend on them explicitly and searches remain effective.
