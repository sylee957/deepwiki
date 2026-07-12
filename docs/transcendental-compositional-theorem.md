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

The current specializations do not yet share one semantic completeness story:

| Case | Current path | Gap to close |
| --- | --- | --- |
| Primitive | Root-free LRT `CLrtMonomialCase` and recursive limited integration | Keep its algebraic-residue log representation separate, but expose a bridge from its rational special result to the common one-level remainder invariant. |
| Exponential | `Hyperexp/CaseChecked` and `Hyperexp/RischLevel` | Completeness is only the Laurent candidate acceptance domain; factor its semantic special domain and residual-feedback normal domain. |
| Tangent | `CoupledDE/TangentSpecial` and depth adapters | The reduced semantic domain now composes coupled solving, polynomial reduction, coefficient recursion, and checked output; extract the reusable monomial-special pattern without erasing tangent-specific recurrence hypotheses. |

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

Replace `hyperexpCheckedSpecialDomain` and the residual-feedback normal
acceptance domain as the primary completeness statement with semantic stage
domains. Preserve the checked domains as explicit fallback realizations. Feed
the resulting special/normal witnesses into the Phase-1 invariant.

Gate: `Hyperexp/CaseChecked`, `Hyperexp/NormalCapability`, and
`Hyperexp/RischLevel`.

### Phase 4 — primitive/LRT bridge

Define the bridge theorem from `CLrtMonomialCase`'s rational special identity
plus LRT residue logs to `OneLevelRemainderInvariant`. Do not merge LRT's
algebraic log type into the ordinary `IntegralResult` type. Lift recursive
limited-coefficient completeness through the bridge.

Gate: `LrtMonomialCase`, `RischTowerLrt`, `RischSolverTowerLrt`, and primitive
grounding modules.

### Phase 5 — finite-tower theorem

Introduce a tower-indexed stage package with: carrier representation adapter,
canonical/normal/polynomial capabilities, monomial classification, and the
lower-level coefficient adapter. Prove by induction that each selected level
is lawful, genuine, and relatively complete on its compositional domain.
State separate dense and sparse selector theorems as instantiations of this
package.

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
