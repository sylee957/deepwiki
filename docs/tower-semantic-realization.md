# Recursive semantic realization for transcendental towers

## Problem corrected

`TowerLog.EvaluationMaps` evaluates every represented tower level in one algebraically closed field `E` and
therefore returns every logarithmic derivative in `RatFunc E`.  That is sufficient for one monomial stage, but
not for recursive coefficient integration: a lower result's differentiated logarithms must become coefficients
of the next extension before that extension's own logarithms are introduced.  There is no canonical map from
`RatFunc E` back into the same `E`, so a single final field cannot justify the successor composition theorem.

The old evaluator remains a valid one-level transport API.  It must not be used to state cross-level
soundness of `appendInherited`, `TowerCoefficientStage`, or the recursive tangent candidate.

## Target realization

For a fixed finite monomial tower, choose fields recursively:

```
F₀     algebraically closed differential extension of K₀
Fₙ₊₁  algebraically closed differential extension of RatFunc(Fₙ)
```

At each depth `n`, the realization contains:

- `Kₙ → Fₙ`, commuting with the represented coefficient derivation;
- the actual monomial derivative `Dtₙ` and the induced differential structure on `RatFunc(Fₙ)`;
- a differential embedding `RatFunc(Fₙ) → Fₙ₊₁`;
- a commuting square identifying `Kₙ₊₁ = RatFunc(Kₙ)` with the composite
  `Kₙ₊₁ → RatFunc(Fₙ) → Fₙ₊₁`.

`DeepWiki.SymbolicIntegration.TowerRealization` in
`DeepWiki/SymbolicIntegration/Engine/Tower/Realization.lean` now records these requirements.  In particular,
`stepDifferential_eq` prevents a proof from silently replacing a primitive, exponential, or tangent monomial
derivation with the unrelated formal `d/dX` derivation.

## Composition invariant

The replacement invariant is indexed by a realization rather than a universal single field.

1. A local level-`n` result differentiates in `RatFunc(Fₙ)` to the embedded input fraction.
2. A lower coefficient result has the same derivative equality in `RatFunc(Fₙ)`.
3. The differential lift maps that equality into `Fₙ₊₁`, hence into `RatFunc(Fₙ₊₁)` as a coefficient identity.
4. The successor-local rational and log identity is proved in `RatFunc(Fₙ₊₁)`.
5. Addition combines the two identities; inherited logs are interpreted through the lift, never re-evaluated in
   an unrelated one-level target.

This is the sound induction step needed by the tangent coefficient recursion.  The same invariant is shared by
primitive and exponential stages; only `Dtₙ` and their stage-local reduction contracts differ.

## Migration order

1. Define realization-indexed local rational and log derivative denotations, including a lifted inherited-log
   contribution.
2. Restate the one-level ordinary and LRT soundness adapters against that local invariant.
3. Prove the coefficient-lift lemma from `TowerRealization.stepDifferentialAlgebra` and `coherent`.
4. Prove `finishTowerTangentCandidate` sound; then expose it through the selected tangent stage.
5. Give primitive and hyperexponential selected stages the same realization-indexed contract and use
   `IntegrationTowerScheme` / `LayeredTranscendentalTowerScheme` for finite-tower soundness and relative
   completeness.
6. Audit callers, retire `EvaluationMaps`-based cross-level claims and the legacy one-shot tangent
   orchestration, while keeping one-level compatibility imports only where still used.

No retirement is justified before step 5: the legacy path still supplies the only verified selected tangent
stage, and the current `EvaluationMaps` theorems remain useful for isolated one-level LRT evaluation.
