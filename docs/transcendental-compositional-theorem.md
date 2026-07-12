# Compositional transcendental-extension theorem

## Objective

Prove an executable, representation-independent Risch-level theorem for finite
transcendental towers. Each level must compose canonical decomposition,
polynomial reduction, normal/Hermite reduction, monomial-special integration,
recursive coefficient integration, and logarithmic reconstruction. The final
theorem is sound and relatively complete from the contracts of those stages;
dense and sparse code are adapters, not separate algorithms.

## Existing foundation

`Assemble.lean` already provides the common executable spine:

- `CMonomialCase`, `LawfulCMonomialCase`, and
  `LawfulGenuineCMonomialCase` state the special-stage derivative square and
  the Liouville side conditions.
- `CompleteCMonomialCase` gives a stage-relative completeness interface.
- `OneLevelAssemblyWitness`, `oneLevelRischCompleteDomain`, and
  `completeCRischLevel` compose polynomial, normal, and monomial stages.
- `convertRischLevel` and `denseMonomialCaseAsSparse` transport lawful,
  genuine, and complete contracts across representations.

`Tower/Compositional` now exposes `IntegrationStage`: an output-polymorphic,
fuel-indexed contract carrying a semantic domain, accepted-output correctness,
and relative completeness. `DenseRischStage.asIntegrationStage` exports the
ordinary-log dense stages, while `DenseLrtStage.asIntegrationStage` exports the
guarded algebraic-residue primitive stage without coercing its log type.
`SparseLrtStage` is the corresponding certified sparse-input adapter: it runs
the dense root-free backend and deliberately retains the dense LRT result.

The specializations share one output-polymorphic stage theorem while retaining their mathematically distinct
semantic domains:

| Case | Current path | Gap to close |
| --- | --- | --- |
| Primitive | Root-free LRT `CLrtMonomialCase`, `Tower/LrtDepth`, and recursive limited integration | `DenseLrtStage` now packages the recursive finite LRT tower with formal soundness and relative completeness. Full-domain completeness assumes special decomposition and a genuine primitive monomial; the Wf gcd derives either a nonzero residue resultant or the no-poles empty-log branch. |
| Exponential | `Hyperexp/CaseChecked`, `Hyperexp/NormalSemantic`, `Hyperexp/RischLevel`, and `Hyperexp/TowerStage` | Laurent special and residual-feedback normal stages now form a certified dense tower stage; retain only the dense-to-sparse adapter as the tower-facing sparse path. |
| Tangent | `CoupledDE/TangentSpecial` and `TangentDepth` | The reduced semantic domain now composes coupled solving, polynomial reduction, coefficient recursion, and checked output as a certified dense tower stage; the independent sparse depth orchestrator is retired in favor of the common adapter. |

## Migration rules

1. Retain `CMonomialCase` as the single full-result special interface. Do not
   introduce another generic operation layer unless a missing invariant cannot
   be stated through its existing soundness, genuine-output, or completeness
   contracts.
2. Keep `CLrtMonomialCase` separate: it returns rational data because LRT logs
   are algebraic-residue objects, not `IntegralResult.logs`. Bridge at the
   assembly/remainder theorem, not by coercing LRT logs into an invalid shape.
3. State semantic domains by the actual mathematical stage witnesses. Checked
   acceptance domains remain useful executable fallbacks but must not be the
   only claimed completeness result when a semantic proof exists.
4. Dense and sparse realizations must be connected by existing conversion
   theorems. Do not duplicate reduction or completeness proofs by
   representation.
5. Retire a previous path only after `scripts/wiki rdeps` and a serial gate
   prove it has no remaining consumers. Do not add compatibility shims for a
   dead internal API.

## Phases

### Phase 1 — consolidate the existing common remainder specification

`OneLevelAssemblyWitness` already records the canonical split and the
polynomial, special, and normal stage witnesses needed by
`completeCRischLevel`. Do not introduce a parallel
`OneLevelRemainderInvariant`. Instead, add the missing conversion and
recombination lemmas around this existing witness, and state the LRT bridge in
terms of the same three-stage shape.

Gate: `scripts/check.sh DeepWiki.SymbolicIntegration.Engine.PolynomialAssembly`
and immediate assembler consumers.

### Phase 2 — tangent becomes the reference semantic specialization

Move only the reusable parts of the tangent certified-completion result into
the common invariant: output certificate, genuine logarithms, and the special
remainder identity. Keep `TangentReducedCompleteDomain`, the coupled system,
and `Dt = η(t²+1)` local. The resulting tangent theorem must instantiate the
common invariant and its dense/sparse depth adapters must consume that theorem.

Gate: tangent special, dense depth, sparse depth, then their aggregators.

### Phase 3 — hyperexponential semantic domain

`hyperexpLaurentSpecialDomain` states hyperexponential shape, certified
special denominator, and coefficient-RDE solvability. The residual-normal
domain records its pre-correction residual identity and solvable scalar RDE.
Field-RDE completeness proves both checked stages and the fully semantic
`completeCRischLevelHyperexpSemantic` theorem. The acceptance-only
hyperexponential completeness domains were retired after a caller audit.

Gate: `Hyperexp/CaseChecked`, `Hyperexp/NormalCapability`, and
`Hyperexp/RischLevel`.

### Phase 4 — primitive/LRT bridge

`lrtRationalSpecialResult` now turns a `CLrtMonomialCase` rational special
certificate into the common `IsMonomialSpecialResult` with no ordinary logs;
algebraic-residue logs remain in the LRT result layer. Its completeness bridge
produces the common semantic special witness. Next, connect the complete LRT
assembly to the tower package without merging its algebraic log type into
`IntegralResult`.

`DenseLrtStage` now performs that tower packaging: it has a selected LRT
operation, explicit primitive decomposition domain, formal algebraic-residue
soundness, and relative completeness at every finite dense fraction-tower
depth. Its `integrateGenuine` wrapper checks `allResiduesConstantLrt`, so every
successful guarded run proves `IsGenuineIntegralResultLrt`. The inverse
assembler theorem
`isElementaryIntegrableGenuineLrt_normal_of_full_of_special` subtracts the
rational special antiderivative from a full genuine LRT witness (including a
degenerate raw rational denominator), preserving its algebraic logs. Therefore
`DenseLrtStage.normalResidueGuard_of_genuine` derives the canonical normal
Liouville guard from full-input genuine integrability, and the common
`asIntegrationStage` now uses `genuineFullDomain`: special decomposition plus
the input-independent `GenuinePrimitiveMonomialLrt` condition. From it, the Wf
gcd derivation establishes normal-residue support—either normal-resultant
nonvanishing or a constant Hermite residual denominator, whose symbolic log
list is empty—without a caller-supplied residue guard or resultant condition.
`SparseLrtStage` converts only its input at the representation boundary; its
algebraic-residue output stays dense rather than being incorrectly coerced into
ordinary sparse logarithms.

The former standalone `cIntegrateReducedLrtGuarded` acceptance-only reducer has
been retired after a reverse-dependency audit. `cResidueConstantGuard` and
`AllResiduesConstantLrt` remain the shared primitive-stage leaves.

`DenseLrtLevelCapabilities` makes every selected implementation refinement
explicit: lawful gcd/split-factor/squarefree operations, Liouville descent,
and the root-free residue criterion. Canonical-normal denominator
nonvanishing now follows directly from the selected lawful split
factorization. The established fraction-free Yun implementation supplies the
criterion through `primitiveLrtResidueCriterionWf`.
`denseLrtLevelCapabilitiesWf` materializes that Wf gcd and criterion together
with selected Risch, splitting, squarefree, and Liouville frontiers. The Wf gcd
theorem also derives the normal-residue-support disjunction from the genuine
monomial condition and canonical properness; this must not be silently
identified with a default split-factor instance.

The rational base is now grounded: `instLrtLiouvilleFrontierQ` proves its
Liouville descent because `CDiffField.cderiv` is definitionally zero on `ℚ`, so
every root-free residue polynomial passes the guard. The recursive Wf gcd
boundary is now concrete: degree-fuelled pseudo-division replaces the unsound
fixed fuel cutoff; `PrimPRSRegular/Termination` proves a finite regular run,
and `WellFounded` lifts it through denominator clearing and monic
normalization. `LawfulCPolyGcd` is tied to its selected `CFieldSpec`, so the
base-and-successor instances synthesize for every `DenseFracTower` level. This
closes the primitive normal-residue-support boundary.

Gate: `LrtMonomialCase`, `RischTowerLrt`, `RischSolverTowerLrt`, and primitive
grounding modules.

### Phase 5 — finite-tower theorem

`Tower/Compositional` now provides `DenseRischStage`, its certified
`SparseRischStage` adapter, and `DenseRischTowerScheme`. Its
`asIntegrationTowerScheme` adapter routes every concrete dense level through
the generic induction, which exposes soundness, genuine logarithms, and
relative completeness at every selected depth. `hyperexpDenseRischStage` and
`denseTangentCompositionalStage` are the first concrete dense stage
constructors, and their sparse forms are obtained only with
`DenseRischStage.toSparse`.

The output-polymorphic `IntegrationStage` is the common boundary for those
ordinary-log stages and the guarded LRT primitive stage, so algebraic-residue
logs remain valid first-class evidence rather than an invalid coercion. Dense
ordinary stages supply sparse adapters by result conversion; the LRT primitive
stage supplies a sparse-input/dense-result adapter because its root-free
residue construction is dense.

`IntegrationTowerScheme` supplies the generic finite-depth induction: its
recursive `stage` selection proves accepted-output correctness and eventual
success at every depth directly from the base and successor contracts.

`Tower/Transcendental` now supplies the common-output
`LayeredTranscendentalTowerScheme`. It selects primitive LRT,
hyperexponential, or tangent at every depth but always returns
`TowerIntegralResult`: ordinary local logs, root-free local LRT families, and
inherited logs retain the depth at which they were created. Its `stage_sound`
and `stage_complete` are the end-to-end finite-tower theorems in that common
semantic language. `primitiveLayeredTranscendentalStage`,
`hyperexpLayeredTranscendentalStage`, and `tangentLayeredTranscendentalStage`
are the three certified constructor entry points.
The primitive entry point can use `denseLrtLevelCapabilitiesWf`, which supplies
the Wf gcd residue criterion; its full-domain theorem derives canonical normal
support and the Liouville guard internally.

The layered tower interface now passes the full certified lower level to each
successor constructor, and its soundness/completeness theorems compose those
contracts by finite recursion. The existing concrete constructors still do
**not** consume heterogeneous lower logarithms to construct arbitrary
alternations from the preceding result alone:
ordinary hyperexponential/tangent recursion lifts lower `IntegralResult` logs
through `CRecursiveElementaryIntegrator`, whereas the primitive LRT recursion
intentionally consumes only a log-free rational lower antiderivative. A fully
heterogeneous construction requires an algebraic-coefficient log language and
a transport theorem through the requisite algebraic constant extension. Until
that interface exists, do not describe the selector as proving recursive
interoperation for every arbitrary primitive/hyperexponential/tangent order.
The dependency-ordered implementation plan is
`docs/algebraic-coefficient-transport.md`.
`Tower/AlgebraicCoefficient.lean` now gives the shared algebraically closed
semantics, an ordinary recursive-coefficient stage adapter, and the common
stage contract; `Tower/AlgebraicCoefficientLrt.lean` adapts genuine primitive
LRT stages while preserving root-free residue-log evidence. What remains is
to make tangent and hyperexponential reconstruction consume this common
coefficient-stage output instead of the ordinary-only `CoefficientIntegralResult`.

Gate: tower aggregators and a full serial `scripts/check.sh`.

### Phase 6 — retirement

Audit acceptance-only and one-shot orchestration paths. Retire only paths
subsumed by the semantic theorem and demonstrably unused. Update
`docs/bronstein-compositional-architecture.md` in the same commit as each
retirement.

## First implementation milestone

Phase 1 should be implemented before changing primitive or hyperexponential
algorithms. Its completion criterion is a conversion/recombination API around
`OneLevelAssemblyWitness` and a theorem that exposes its stage witnesses from
`oneLevelRischCompleteDomain`. This creates one stable target for all three
monomial cases.
