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
- `Assemble.lean` now proves `combineSN_isIntegralResultP` once for every lawful polynomial
  representation. Its former dense-only wrapper and unchecked executable example have been retired.
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
  logarithm arguments, and full identity; it intentionally has no completeness instance.
- `hyperexpRischLevel` composes that normal stage with the checked Laurent special stage and an arbitrary
  lawful polynomial reducer, yielding a dense sound hyperexponential one-level realization.
- `assembleOneLevel` is the executable representation-neutral Figure-5.1 spine: canonical split,
  polynomial and special integration, an injected normal reducer, monomial-specific normal postprocessing,
  and recombination.
  `assembleOneLevel_sound` derives its full one-level identity solely from lawful capability instances.
- The guarded primitive monomial operation has a `LawfulCMonomialCase` instance. Its intentionally narrow
  guard does not claim `CompleteCMonomialCase`; the former standalone dense driver and redundant wrapper
  theorem have been retired.
- The checked hyperexponential monomial operation validates its Laurent special result before exposing it,
  uses exact normal-result passthrough, and supplies a lawful monomial capability. Its former standalone
  dense driver and redundant wrapper theorem have been retired.
- `denseMonomialCaseAsSparse` transports any lawful dense monomial specialization to a lawful sparse one.
  `sparseRischLevel` composes that hook with sparse canonical, Hermite, residue-log, and generic polynomial
  reduction stages into a sound sparse Figure-5.1 level.
- `CRischLevel` packages a one-level executable solver, while `LawfulCRischLevel` states soundness and
  `CompleteCRischLevel` separately states relative completeness over an explicit semantic domain.
  `oneLevelRisch` packages the generic assembler and
  `oneLevelRischWithRecursiveCoefficient` installs an explicit lower coefficient stage;
  `oneLevelRischSoundDomain` and `oneLevelRischCompleteDomain` lift the selected normal reducer's
  domain through canonical decomposition and add explicit stage-decomposition witnesses for completeness.
- `convertRischLevel` is a representation boundary rather than a second assembler: its lawful instance
  transports a source level's denotation square to the pulled-back target domain, including converted
  logarithmic terms.
- `CPolynomialReduction`/`LawfulCPolynomialReduction` now separate the Prop-free, fuel-bounded
  polynomial-reduction operation from its reconstruction, normal-form, and relative-completeness
  obligations. `towerPolynomialReduction` exposes the existing nonlinear and primitive kernels only
  after an executable reconstruction check; `polynomialReductionCheck_sound` is the generic
  denotation bridge. Its degree-bound and eventual-fuel realization proof remains an explicit next step.
- `CResidueSource P α` is the Prop-free residue-candidate capability and
  `LawfulCResidueSource P α` states constant-root completeness. The bounded-rational source is
  representation-neutral but intentionally has no lawful instance because a finite sweep is incomplete.
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
   complete residue-source theorem. `CompleteCResidueLogPart` and the composite Hermite-residue normal domain
   are now domain-parameterized; bounded candidate sweeps remain intentionally incomplete and must not acquire
   a universal-domain instance.
2. Implement the concrete recursive `CTangentSpecialIntegrator` and a relative-completeness contract for tangent
   normal reduction. Bronstein's reduced hypertangent algorithm repeatedly strips a power of `t²+1`, calls the
   coupled solver, subtracts the reconstructed derivative, and recurses; the former one-shot
   `CTangentSpecialBridge` could not express this loop and has been retired. Soundness no longer depends on the
   low-degree Hermite theorem: `tangentNormalReduction`
   certificate-checks every raw normal result, and `tangentRischLevel` composes it with the coupled solver and
   special integrator through the generic assembler. `sparseTangentRischLevel` transports the same composition through the
   sparse representation boundary. Both canonical compositions certificate-check every reassembled special
   fraction and are sound without solver or bridge laws; the former unchecked duplicate APIs have been retired.
   Their explicit checked-acceptance domains now compose the polynomial, normal, and tangent contracts into
   dense and sparse `CompleteCRischLevel` instances. This is executable relative completeness only. Full semantic
   tangent completeness still needs the concrete recursive integrator and a special-stage result shape that can
   represent the constant multiple of `log(t²+1)` produced by hypertangent polynomial reduction; the LRT primitive
   path should retain its separate rational-only special interface.
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
