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

An earlier `AlgebraicCoefficientLog` bridge duplicated this purpose with a
separate coefficient-result carrier. It was retired after caller audit:
`TowerLog` is the sole heterogeneous-log syntax. A local ordinary or LRT node
records the monomial derivative that created it, and `TowerLog.inherited`
retains a lower node without reinterpreting it as an upper
`IntegralResult.logs` entry.

## Phases

1. **In progress.** `Tower/LogTower.lean` is the single full-result carrier:
   `TowerIntegralResult` and `IsTowerIntegralResult` are now the output and
   semantic invariant of primitive, hyperexponential, and tangent selected
   stages. The obsolete one-level `TranscendentalResult` carrier has been
   retired after source and reverse-dependency audit. Generalize tangent and
   hyperexponential special/reconstruction assemblies to append inherited
   algebraic coefficient logs without forcing them into `IntegralResult.logs`,
   then prove their local soundness and relative completeness by composition.
   `TowerLog` supplies the required depth-indexed syntax:
   `TowerLog.inherited` preserves a lower ordinary or LRT log at its own field
   level, while each local node retains the monomial derivative of the
   extension that created it. The ordinary/LRT embeddings preserve genuine-log
   evidence. `TowerLog.EvaluationMaps` now packages the algebra and
   differential-algebra structures at every depth together with compatibility
   for the canonical `Kₙ → Kₙ₊₁` rational-function inclusion. `TowerLog.denote`
   therefore evaluates every local or inherited log with the exact structure
   needed by its source-level soundness contract. `IsTowerIntegralResult` is
   the common recursive semantic invariant, and both the ordinary and
   root-free LRT result embeddings transport their existing certificates into
   it. `TowerIntegralResult.appendInherited` now combines a successor-local
   result with the preceding result's depth-preserving log syntax. Its
   genuine-log theorem composes both certificates, while
   `TowerLog.denote_inherited`, `towerLog_denoteSum_inheritAll`, and
   `TowerIntegralResult.denoteSum_appendInherited` prove that inherited logs
   are evaluated at exactly their original field depth.
   `IsTowerIntegralResultWithLowerLogs` is the relative successor certificate,
   and `isTowerIntegralResult_appendInherited` transports it to the ordinary
   tower invariant. The remaining work is to make tangent and
   hyperexponential reconstruction produce that relative certificate.
   `TowerIntegralResult.add` and its rational, log, differentiated-denotation,
   and genuine-log laws now provide the common reconstruction operation for
   composing polynomial, normal, special, and inherited pieces.
   `denseFracTower_K_succ` and `denseFracTowerKStep` expose the required
   `Kₙ₊₁ = RatFunc Kₙ` field equality and canonical inclusion across the
   packaged carrier boundary.
2. Make the concrete tangent and hyperexponential successor constructors consume
   the complete lower `LayeredTranscendentalLevel` that
   `LayeredTranscendentalTowerScheme` now supplies. Their lower adapter must
   transport heterogeneous coefficient logs, then finite-tower soundness and
   relative completeness follow by the existing induction. The lower level now
   exposes `runCoefficient`: it turns a represented fraction into the
   certified unit-monomial Risch input and carries forward the selected
   domain, soundness, and relative-completeness hypotheses. Concrete
   reconstructions must discharge those hypotheses from their coefficient
   integrability witnesses; they must not treat this wrapper as unconditional
   recursive success. `TowerCoefficientStage` now exports precisely this
   lower-field contract independently of the selector, and
   `LayeredTranscendentalLevel.asTowerCoefficientStage` is the certified
   adapter from a selected lower level. `towerTangentSpecialCandidate` now
   executes tangent special reconstruction against that stage: it uses the
   lower rational part in the polynomial tail and appends lower logs only as
   `TowerLog.inherited` nodes. Its local genuine-log theorem composes the
   tangent coefficient check with the lower stage's `LogsGenuine` result.
   Semantic soundness and relative-completeness proofs are next; the
   ordinary-only candidate remains the legacy path until those proofs and
   caller migration land.
3. The old native-result `TranscendentalTowerScheme` has been retired after a
   source and reverse-dependency audit; audit the remaining selected-stage
   constructors once the heterogeneous successor constructor is in place. Dense and sparse remain
   conversion adapters; neither gains an independent assembler.

## Gates

Gate each phase serially: the recursive log carrier, tangent/hyperexponential
assemblies, `Tower/Transcendental`, then the full `scripts/check.sh` gate.
Before deleting a wrapper, run
`scripts/wiki rdeps` and confirm current-source callers with `rg` when the
graph is stale.
