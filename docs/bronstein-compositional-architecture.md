# Bronstein compositional integration architecture

## Objective

Refactor the transcendental engine around Bronstein Figure 5.1: shared Hermite,
polynomial, and residue reductions feed a monomial-case solver, which reduces
remaining obligations recursively to the coefficient field. The generic assembler
depends only on executable stage interfaces and `Lawful…` contracts.

## Current verified pieces

- Leaf operation/law splits exist for fractions, gcd, Euclidean division, resultants, interpolation,
  squarefree decomposition, and subresultants, with dense and sparse lawful realizers. The squarefree and
  subresultant specifications and lawful contracts live in `ComputableAlgebra`; the engine consumes them as leaves.
- `CMonomialCase.integrateSpecial` returns a full `IntegralResult`, so special stages can contribute both
  rational and logarithmic terms. `combineIntegralResults_isIntegralResultP` is the single
  representation-neutral recombination square; the obsolete pair-only theorem, former dense-only wrapper,
  and unchecked executable example have been retired. The root-free LRT path deliberately retains the separate
  rational-only `CLrtMonomialCase` interface.
- `CMonomialCase P` is now the representation-parameterized, Prop-free operation interface used by
  dense and recursive realizers; `LawfulCMonomialCase` separates its soundness, denominator preservation,
  and normal-postprocessing laws, while `CompleteCMonomialCase` records relative completeness separately.
- `CRecursiveMonomialCase P` makes the lower coefficient-field reduction an explicit input to a
  tower monomial stage.  Its `Lawful…` and `Complete…` contracts lift any lawful/complete
  `CRecursiveCoefficientIntegrator` into the existing `CMonomialCase` contract, so the generic
  Figure-5.1 assembler remains representation- and solver-neutral.
- `CRecursiveCoefficientIntegrator` also carries the optional single-`w` limited-integration
  operation used by Bronstein's degree-raising primitive polynomial reduction.  The LRT primitive
  tower case is now a lawful `CRecursiveMonomialCase` realization, and the prior executable case is
  exactly its specialization with `towerCoefficientIntegratorLrt`.
- `CLimitedIntegrateSingleLrt` / `LawfulCLimitedIntegrateSingleLrt` /
  `CompleteCLimitedIntegrateSingleLrt` isolate the coefficient-field
  single-generator operation from the LRT level itself.  The conservative `none` capability is lawful;
  the named base realizer `limitedIntegrateSingleLrtBase` runs the generic candidate routine only after an
  identity check, and its law proves the full decomposition and constant-coefficient condition. Its
  completeness theorem deliberately names the exact checked-acceptance domain rather than claiming that
  the current finite candidate search covers every denotational solution.
- `CCanonicalRepresentation`/`LawfulCCanonicalRepresentation` have dense and sparse-facing
  realizations. The sparse realization transports the dense backend through denotation-preserving
  polynomial conversion.
- `CCanonicalRepresentation` and `LawfulCCanonicalRepresentation` expose canonical decomposition and its
  reconstruction/nonzero/properness laws; `canonicalRepresentationFast` is the dense realizer.
- `LawfulHermiteReduction` and `LawfulResidueLogPart` are representation-neutral stage-result
  contracts; the selected dense realizations cross `toPoly_list_eq` explicitly.
- `CHermiteReduction`/`LawfulCHermiteReduction` pair a representation-neutral Hermite operation with
  semantic nonzero, reconstruction, squarefree, and low-derivation-degree properness laws. The existing
  dense reducer now realizes this contract: normal-squarefreeness discharges its repeated-Yun-factor
  coprimality frontier, and the checked dense Risch-level adapter obtains the law as an instance rather
  than accepting it as an assumption.
- `CResidueLogPart` makes residue-log extraction option-valued. `LawfulCResidueLogPart` certifies every
  successful reconstruction, while `CompleteCResidueLogPart` separately states completeness relative to
  a lawful residue source and a genuine logarithmic witness.
- The dense realization `checkedResidueLogPart` runs the existing Rothstein-Trager computation but exposes
  its logs only after nonzero-denominator and full identity checks; it has a lawful soundness instance
  without claiming completeness for a bounded source.
- Sparse-facing Hermite and checked residue-log realizations transport the dense backends explicitly.
  Residue coefficients stay in `α`; only resultant inputs and logarithm arguments cross the polynomial
  representation boundary.
- `reduceNormal` composes Hermite and residue-log operations; `reduceNormal_sound` and
  `reduceNormal_complete` prove the normal branch by contract composition only.
- `CNormalReduction` abstracts the normal branch. `LawfulCNormalReduction` carries its denotational
  soundness law, while `CompleteCNormalReduction` states relative completeness on a selected domain.
  `hermiteResidueNormalReduction` realizes the interface, with separate soundness and completeness domains.
- `hyperexpCheckedNormalReduction` realizes the same soundness interface for dense residual-feedback
  hyperexponential normal integration. It validates the candidate-driven output by checking its denominator,
  logarithm arguments, and full identity; its relative-completeness contract is explicitly limited to
  raw outputs accepted by those checks.
- `hyperexpRischLevel` composes that normal stage with the checked Laurent special stage and an arbitrary
  polynomial reducer. Its soundness and relative-completeness theorems follow from the selected stage
  contracts; completeness is limited to the explicit checked special and normal acceptance domains.
- `assembleOneLevel` is the executable representation-neutral Figure-5.1 spine: canonical split,
  polynomial and special integration, an injected normal reducer, monomial-specific normal postprocessing,
  and recombination.
  `assembleOneLevel_sound` derives its full one-level identity solely from lawful capability instances.
- The obsolete concrete `OneShotAssembly.lean` driver has been retired after its one-shot entry points became
  dead. Its reusable residue identity now lives in `Engine/ResidueMatchBridge.lean` as a leaf theorem used by
  the checked hyperexponential soundness development.
- The dense fuel-free top entry `UnifiedFuelFree.cIntegrateGFullWf` has also been retired: its only callers
  were legacy validation examples, including an explicitly unchecked result, rather than the compositional
  Risch-level pipeline.
- The guarded primitive monomial operation has a `LawfulCMonomialCase` instance. Its intentionally narrow
  guard does not claim `CompleteCMonomialCase`; the former standalone dense driver and redundant wrapper
  theorem have been retired.
- The checked hyperexponential monomial operation validates its Laurent special result before exposing it,
  uses exact normal-result passthrough, and supplies lawful plus acceptance-domain complete monomial
  capabilities. Its former standalone dense driver and redundant wrapper theorem have been retired.
- `denseMonomialCaseAsSparse` transports any lawful dense monomial specialization to a lawful sparse one.
  `sparseRischLevel` composes that hook with sparse canonical, Hermite, residue-log, and generic polynomial
  reduction stages into a sound sparse Figure-5.1 level.
- `CRischLevel` packages a one-level executable solver, while `LawfulCRischLevel` states soundness and
  `CompleteCRischLevel` separately states relative completeness over an explicit semantic domain.
  `oneLevelRisch` packages the generic assembler and
  `oneLevelRischWithRecursiveCoefficient` installs an explicit lower coefficient stage;
  `oneLevelRischSoundDomain` and `oneLevelRischCompleteDomain` lift the selected normal reducer's
  domain through canonical decomposition and add explicit stage-decomposition witnesses for completeness.
- `LawfulGenuineCNormalReduction`, `LawfulGenuineCMonomialCase`, and
  `LawfulGenuineCRischLevel` separately track the Liouville side conditions that the formal derivative
  identity alone cannot express: constant log coefficients and nonzero log arguments.  The generic assembler
  composes these contracts; checked normal and tangent-special realizers enforce them executable-side, and
  dense/sparse recursive tangent levels now expose the resulting genuine-output contract to their successor
  coefficient adapters.
- `convertRischLevel` is a representation boundary rather than a second assembler: its lawful, genuine,
  and complete instances transport the source level's denotation square, Liouville side conditions, and
  eventual success to the pulled-back target domain, including converted logarithmic terms.
- `CPolynomialReduction`/`LawfulCPolynomialReduction` now separate the Prop-free, fuel-bounded
  polynomial-reduction operation from its reconstruction, normal-form, and relative-completeness
  obligations. `towerPolynomialReduction` exposes the existing nonlinear and primitive kernels only
  after executable reconstruction and requested-degree-normal-form checks; its lawful contract now carries
  both facts. Its degree-bound and eventual-fuel realization proof remains an explicit next step: first
  state the nonlinear (`2 ≤ deg Dt`) and primitive (constant nonzero `Dt`) reduction domains, then prove
  that one recursive step cancels the leading term and strictly decreases the selected degree measure,
  and finally iterate that decrease to derive an input-degree fuel bound. Only that theorem may install
  `CompleteCPolynomialReduction` beyond the exact executable-acceptance domain.
- `CResidueSource P α` is the Prop-free residue-candidate capability and
  `LawfulCResidueSource P α` states constant-root completeness. The bounded-rational source is
  representation-neutral but intentionally has no lawful instance because a finite sweep is incomplete.
  `CConstantEnumerator` / `LawfulCConstantEnumerator` now supply a separate finite-constant-field
  realization: filtering the enumerated constants by the representation's lawful polynomial evaluation
  yields a lawful residue source for every polynomial representation.
- `CRischLevelLrt` is the Prop-free recursive algebraic-residue operation, while
  `LawfulCRischLevelLrt` packages its special and reduced soundness contracts. The LRT coefficient
  integrator transports the separate limited-integration contract through `DenseFrac`, so every accepted
  limited result proves both `c = D(b) + r·η` and `D(r) = 0`. The primitive base and
  `DenseFrac` tower-step instances provide the recursive induction path.

## Leaf inventory

| Capability | Executable interface | Lawful contract | Realization location |
|---|---|---|---|
| Fractions | `CFrac` | `LawfulCFrac` | `ComputableAlgebra/Fraction.lean` and representation modules |
| Polynomial engine | `CPolyEngine` | `LawfulCPolyEngine` | `ComputableAlgebra/PolyEngine*.lean` |
| GCD | `CPolyGcd` | `LawfulCPolyGcd` | `ComputableAlgebra/PolyReprGcd.lean` |
| Euclidean division | `CPolyEuclidean` | `LawfulCPolyEuclidean` | `ComputableAlgebra/PolyEuclidean.lean` |
| Squarefree Yun | `CPolySquarefree` | `LawfulCPolySquarefree` | `ComputableAlgebra/PolySquarefree*.lean` |
| Resultant | `CPolyResultant` | `LawfulCPolyResultant` | `ComputableAlgebra/PolyResultant.lean` |
| Subresultant | `CPolySubresultant` | `LawfulCPolySubresultant` | `ComputableAlgebra/PolySubresultant*.lean` |
| Interpolation | `CPolyInterpolate` | `LawfulCPolyInterpolate` | `ComputableAlgebra/PolyInterpolate.lean` |
| Linear solve | `CLinearSolve` | `LawfulCLinearSolve` | `ComputableAlgebra/LinearAlgebra.lean` |
| Residue candidates | `CResidueSource` | `LawfulCResidueSource` | `Engine/ResidueSource.lean` |

Therefore the first architectural refactor is **not** another leaf abstraction. It is to make the
existing leaf contracts the only dependencies of the canonical, Hermite, polynomial, residue, and
monomial stage contracts.

## Remaining work

1. Enlarge the explicit `ResidueLogPartDomain` beyond checked/known residue families by proving an actually
   complete residue-source theorem. Dense and sparse checked residue stages now realize
   `CompleteCResidueLogPart` on their exact executable-acceptance domains, and the composite
   Hermite-residue normal domain can consume those contracts. Bounded candidate sweeps remain intentionally
   incomplete and must not acquire a universal-domain instance.
2. Generalize the concrete `recursiveTangentSpecialIntegrator` beyond its current `ℚ(x)` polynomial-data
   coupled solver. The executable now implements Bronstein's reduced hypertangent recursion: it recognizes a
   power of `t²+1`, calls the coupled solver at each pole order, subtracts the reconstructed derivative, recurses,
   performs the final nonlinear polynomial reduction, descends the constant coefficient through
   `CRecursiveElementaryIntegrator`, lifts the lower field's rational and logarithmic antiderivative terms,
   and emits the possible constant multiple of `log(t²+1)`. The log-free
   `CRecursiveCoefficientIntegrator` remains the operation needed by limited integration and embeds into the
   elementary interface on an explicit rational-antiderivative domain. Its unchecked
   candidate generator is private; the selected operation is certificate-checked, has a
   `LawfulCTangentSpecialIntegrator` instance, and is relatively complete on its explicit acceptance domain.
   `CTangentCoefficientSolver` now states the representation-neutral coefficient-field system
   `Dc - λd = a`, `Dd + λc = b`, with separate lawful and domain-relative-completeness contracts; its checked
   adapter is sound and complete on its explicit executable-acceptance domain. The recursive tangent stage now
   depends only on this interface. Its contracts, recursive kernel, and dense/sparse Risch-level compositions
   are generic over the coefficient differential field `α`, so each tower level can inject its coupled solver
   and lower coefficient integrator. The concrete `tangentRationalCoefficientSolver` clears rational-function
   denominators, solves the resulting finite linear system, and certificate-checks the reconstructed pair.
   This is executable relative completeness at a selected degree bound; semantic completeness still needs a
   degree-bound theorem for general coefficient-field fractions. The former one-shot `CTangentSpecialBridge`
   could not express the recursion and has
   been retired. Soundness no longer depends on the
   low-degree Hermite theorem: `tangentNormalReduction`
   certificate-checks every raw normal result, and `tangentRischLevel` composes it with the coupled solver and
   special integrator through the generic assembler. `sparseTangentRischLevel` transports the same composition through the
   sparse representation boundary. Both canonical compositions certificate-check every reassembled special
   fraction and are sound without solver or bridge laws; the former unchecked duplicate APIs have been retired.
   Their explicit checked-acceptance domains now compose the polynomial, normal, and tangent contracts into
   dense and sparse `CompleteCRischLevel` instances. This is executable relative completeness only. The generic
   monomial special stage now returns a full `IntegralResult`, so it can represent the constant multiple of
   `log(t²+1)` produced by hypertangent polynomial reduction; the LRT primitive path retains its separate
   rational-only `CLrtMonomialCase`. Full semantic tangent completeness still needs a semantic completeness
   theorem for the generalized coupled solver and coefficient recursion, beyond checked acceptance. The
   depth-indexed `DenseTangentTowerCapabilities` family now selects generic tangent levels inductively and
   derives their contracts uniformly. Every successor step constructs its elementary coefficient operation
   from the preceding selected Risch level, lifts its rational and logarithmic result through `DenseFrac`, and
   certificate-checks the lifted derivative identity, constant coefficients, and nonzero arguments. The
   checker now reflects its denotational contract in both directions. The dense-fraction denotation bridge
   proves that a lower `IsIntegralResultP` identity with constant coefficients and nonzero arguments becomes a
   genuine lifted coefficient result, so the adapter is complete on a domain stated entirely in the lower
   Risch vocabulary. The representation-neutral `LawfulGenuineCRischLevel` packages exactly the stronger
   lower-level soundness needed here, and together with `CompleteCRischLevel` proves that the checked
   coefficient adapter succeeds at some finite lower fuel. The generic assembler now decodes its outer fuel
   into independent polynomial and
   monomial-stage budgets using `Nat.unpair`; the tangent monomial stage forwards its budget into
   `CRecursiveElementaryIntegrator`, and dense/sparse successor capabilities derive that budgeted adapter from
   the preceding level without storing a fixed coefficient fuel. Checked normal and tangent-special stages now
   establish the genuine-success contract for selected dense and sparse tangent levels, so the adapter's
   eventual-success theorem applies compositionally at every successor. The remaining gap is semantic
   completeness of the coupled solver and its degree bound, not propagation of Liouville side conditions.
   The recursive tangent stage no longer has `TangentSpecialConfig`: its monomial budget carries independent
   denominator-recognition, encoded coupled-solver, polynomial-reduction, and lower-coefficient budgets, so
   existential bounds from the stage completeness contracts can be threaded without assuming monotonicity.
   Its polynomial continuation is now a selected `CPolynomialReduction` operation rather than a direct call to
   the dense tower kernel; sparse tower capabilities expose the distinct outer sparse and tangent-internal
   dense reductions explicitly.
3. Connect one-level relative completeness to the recursive tower path. This needs a separate
   relative-completeness contract for Bronstein's limited integration
   `a = D(b) + c·η`: `LawfulCLimitedCoefficientIntegrator` and
   `CompleteCLimitedCoefficientIntegrator` now tie returned pairs to that identity and take explicit
   admissibility domains, so ordinary recursive antiderivative completeness alone cannot justify the
   degree-raising branch. The LRT tower lifts the leaf completeness contract through `DenseFrac` on
   `towerLimitedCoefficientDomain`, which explicitly requires a coefficient-field solution with a descended
   constant. `CompleteCRecursiveMonomialCase` likewise names both recursive coefficient domains; its
   lifting theorem requires callers to select them explicitly rather than silently assuming `True`.
   `Tower/LrtDepth.lean` now packages the dictionary-dependent carrier `DenseFracTower n`; the recursive
   `lawfulDenseLrtTower` builder selects a `CRischLevelLrt` and its `LawfulCRischLevelLrt` contract by induction
   from a per-level leaf/frontier capability family, and its theorems give soundness and the explicit-domain
   success equivalence uniformly at every depth.
   `PrimitivePolynomialDomain` now states closure of every generated degree-raising residual under the selected
   limited domain; `cIntegratePrimPolyDegRaise_complete` and the recursive primitive monomial instance compose
   that closure into executable success. Full semantic completeness still requires proving that every genuinely
   integrable primitive polynomial satisfies this closure predicate; that mathematical constant-descent theorem
   remains open.
   Ordinary coefficient recursion is kept distinct from broad elementary integration:
   `CompleteCRischLevelRationalLrt` requires relative completeness of the lower level's log-free integrator,
   and `towerRecursiveCoefficientDomain` lifts exactly that capability through `DenseFrac`. Together with the
   limited-domain lift, `completeTowerPrimitiveCaseLrt` derives the concrete tower monomial completeness contract.
   `completePrimitiveMonomialCase_on_tower` instantiates that composition at `DenseFrac ℚ`, using the checked
   base limited-integration domain and the selected lower-level log-free acceptance domain. This is an executable
   grounding, not yet the open semantic constant-descent theorem above.
4. Continue deleting dead dense/Wf drivers after reverse-dependency checks; retain no internal shim.

## Visibility policy

- `private`: recursion kernels, simulation bridges, proof-local algebra.
- Public: selected executable operation, its `Lawful…` class, and one realization theorem.
- `protected`: only when qualified access is the useful public spelling; namespace qualification alone
  is preferred for ordinary helpers.

## Gates

For each phase: touched module, direct assembler/realizer consumer, bare `scripts/check.sh`, then a
`scripts/wiki rdeps` deadness check before retirement.
