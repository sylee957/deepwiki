# Bronstein compositional integration architecture

## Objective

Refactor the transcendental engine around Bronstein Figure 5.1: shared Hermite,
polynomial, and residue reductions feed a monomial-case solver, which reduces
remaining obligations recursively to the coefficient field. The generic assembler
depends only on executable stage interfaces and `Lawful…` contracts.

## Current verified pieces

- Leaf operation/law splits exist for fractions, gcd, Euclidean division, squarefree
  decomposition, resultants, and subresultants.
- `Assemble.lean` now proves `combineSN_isIntegralResultP` once for every lawful polynomial
  representation; the former `DensePoly` theorem is a specialization through `toPoly_list_eq`.
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
- `CPolynomialReduction`/`LawfulCPolynomialReduction` now separate the Prop-free, fuel-bounded
  polynomial-reduction operation from its reconstruction, normal-form, and relative-completeness
  obligations. `towerPolynomialReduction` exposes the existing nonlinear and primitive kernels only
  after an executable reconstruction check; `polynomialReductionCheck_sound` is the generic
  denotation bridge. Its degree-bound and eventual-fuel realization proof remains an explicit next step.
- `CResidueSource P α` is the Prop-free residue-candidate capability and
  `LawfulCResidueSource P α` states constant-root completeness. The bounded-rational source is
  representation-neutral but intentionally has no lawful instance because a finite sweep is incomplete.
- `CRischLevelLrt` is the Prop-free recursive algebraic-residue operation, while
  `LawfulCRischLevelLrt` packages its special and reduced soundness contracts. The primitive base and
  `DenseFrac` tower-step instances provide the recursive induction path.

## Leaf inventory

| Capability | Executable interface | Lawful contract | Realization location |
|---|---|---|---|
| Fractions | `CFrac` | `LawfulCFrac` | `ComputableAlgebra/Fraction.lean` and representation modules |
| Polynomial engine | `CPolyEngine` | `LawfulCPolyEngine` | `ComputableAlgebra/PolyEngine*.lean` |
| GCD | `CPolyGcd` | `LawfulCPolyGcd` | `ComputableAlgebra/PolyReprGcd.lean` |
| Euclidean division | `CPolyEuclidean` | `LawfulCPolyEuclidean` | `ComputableAlgebra/PolyEuclidean.lean` |
| Squarefree Yun | `CPolySquarefree` | `LawfulCPolySquarefree` | `ComputableAlgebra/PolySquarefree.lean`, semantic law in `Engine/SquarefreeDecomposition.lean` |
| Resultant | `CPolyResultant` | `LawfulCPolyResultant` | `ComputableAlgebra/PolyResultant.lean` |
| Subresultant | `CPolySubresultant` | `LawfulCPolySubresultant` | `Engine/SubresultantSpec.lean` |
| Interpolation | `CPolyInterpolate` | `LawfulCPolyInterpolate` | `ComputableAlgebra/PolyInterpolate.lean` |
| Linear solve | `CLinearSolve` | `LawfulCLinearSolve` | `ComputableAlgebra/LinearAlgebra.lean` |
| Residue candidates | `CResidueSource` | `LawfulCResidueSource` | `Engine/ResidueSource.lean` |

Therefore the first architectural refactor is **not** another leaf abstraction. It is to make the
existing leaf contracts the only dependencies of the canonical, Hermite, polynomial, residue, and
monomial stage contracts.

## Remaining work

1. Realize `CompleteCResidueLogPart` for an actually complete residue source. Bounded candidate sweeps
   remain intentionally incomplete and must not acquire a false lawful instance.
2. Implement the concrete `CTangentSpecialBridge` and a relative-completeness contract for tangent normal
   reduction. Soundness no longer depends on the low-degree Hermite theorem: `tangentNormalReduction`
   certificate-checks every raw normal result, and `tangentRischLevel` composes it with the coupled solver and
   bridge through the generic assembler. `sparseTangentRischLevel` transports the same composition through the
   sparse representation boundary. Relative completeness remains after the concrete bridge is available.
3. Connect one-level relative completeness to the recursive tower path. This needs a separate
   relative-completeness contract for Bronstein's limited integration
   `a = D(b) + c·η`: `LawfulCLimitedCoefficientIntegrator` and
   `CompleteCLimitedCoefficientIntegrator` now tie returned pairs to that identity and record the boundary
   explicitly, so ordinary
   recursive antiderivative completeness alone cannot justify the degree-raising branch. The LRT
   tower has not yet realized the limited-completeness contract; completeness remains relative to
   explicit stage-decomposition witnesses until that mathematical decomposition theorem is formalized.
4. Continue deleting dead dense/Wf drivers after reverse-dependency checks; retain no internal shim.

## Visibility policy

- `private`: recursion kernels, simulation bridges, proof-local algebra.
- Public: selected executable operation, its `Lawful…` class, and one realization theorem.
- `protected`: only when qualified access is the useful public spelling; namespace qualification alone
  is preferred for ordinary helpers.

## Gates

For each phase: touched module, direct assembler/realizer consumer, bare `scripts/check.sh`, then a
`scripts/wiki rdeps` deadness check before retirement.
