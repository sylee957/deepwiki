# Tower orchestration rework — retire the broken LRT-depth legacy layer

**Goal.** The presentation path (`DifferentialTowerPresentation` + `DifferentialTranscendentalLevel`
+ `DifferentialCoefficientBridge` + `DifferentialCoefficientTowerScheme`, keystone
`Tower/DifferentialLegacyCapabilities.lean`) is the sound new spine and **builds clean**. The gate is
red for exactly one reason: `Tower/LrtDepth.lean` does not compile (a `CPolySquarefree` data-field
instance diamond — root-caused, not a timeout; see `feedbacks/gate-lrtdepth-squarefree-diamond.md`).
Because the LRT grounding was already decided to drop to the frontier boundary, this layer is
**deleted, not repaired**. Retirement is coverage-safe: **no `Sources/` catalog references any
LRT-depth name.**

## Dependency audit (verified 2026-07-12)

Names living **only** in `Tower/LrtDepth.lean`: `DenseLrtStage`, `DenseLrtLevelCapabilities`,
`lawfulDenseLrtTower` (+ `denseLrtLevelCapabilitiesWf`). Their **only** consumer is
`Tower/Transcendental.lean` (via the `DenseLrtStage.as*` and `LayeredTranscendentalStage.primitive`
constructions).

`Tower/Transcendental.lean` is a **leaf**: its `LayeredTranscendental*` exports have **zero external
consumers** (only `Engine/Tower.lean` imports the module, as an aggregator). It is the "second
orchestration language" the design doc warns against. → **delete wholesale.**

`Engine/RischTowerLrtGrounding.lean` **survives.** Every name its body uses
(`CRischLevelLrt`, `IsIntegralResultLrt`, `PrimitiveFrontierLrt`, `LrtResult`,
`rischLevelLrt_succeeds_iff_integrable`, `towerPrimitiveCaseLrt`, `completeTowerPrimitiveCaseLrt`,
`CompleteCLrtMonomialCase`) is defined in `RischTowerLrt` / `LrtSoundness` / `LrtCompleteness` /
`RischSolverTowerLrt` / `LrtMonomialCase` — **not** in `LrtDepth`. Its `import LrtDepth` at line 1 is
a transitive-convenience import (LrtDepth re-exported `RischSolverTowerLrt`). → **swap the import to
`RischSolverTowerLrt` (+ whatever else is needed); keep the file.**

`Engine/CoupledDE/TangentDepth.lean` **survives.** Its `import LrtDepth` at line 4 is **unused** — no
LrtDepth name appears in its body. → **drop the import line; keep the file.** (Once `Transcendental`
is gone, `denseTangentTower` etc. have no consumers, but they are genuine content and don't block the
gate; retention is deliberate — a later semantic-consolidation pass can revisit.)

## Phases (each its own gate-green commit)

- **P1 — drop the dead `TangentDepth` import.** Remove line 4 `import ...Tower.LrtDepth` from
  `CoupledDE/TangentDepth.lean`. Gate `DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentDepth`.
  *(Independent, safe, shrinks the LrtDepth reverse-dep set before deletion.)*

- **P2 — re-anchor `RischTowerLrtGrounding`'s import.** Replace its `import ...Tower.LrtDepth` with
  `import ...Engine.RischSolverTowerLrt` (add more only if the gate demands). Gate the module and its
  two consumers (`Engine/PrimitiveCase`, `Engine.lean`).

- **P3 — delete `Tower/Transcendental.lean`.** Remove the file and its import in `Engine/Tower.lean`.
  Confirm nothing else references `LayeredTranscendental*`. Gate `DeepWiki.SymbolicIntegration.Engine.Tower`.

- **P4 — delete `Tower/LrtDepth.lean`.** Remove the file and its import in `Engine/Tower.lean`. By now
  it has no remaining importers. Full `scripts/check.sh` → GATE: PASS (the previously-only-failing
  module is gone).

- **P5 — contract restatement.** In `Tower/DifferentialLegacyCapabilities.lean` (or a sibling),
  confirm/keep the `example`s pinning `stage_sound`/`stage_complete` for primitive (done, genuine),
  exponential (`t'=t`), tangent (`t'=t²+1`), each through the ONE presentation path. Document the
  exp/tangent solver frontier (differential-explicit monomial-special + normal reducers at the
  selected `Dt`) as the single named external frontier if not yet inhabited.

- **P6 — final audit.** `scripts/wiki build`; `scripts/wiki rdeps` on the retired names returns empty.
  Update the SI memory + this doc. Rebuild default gate once more.

## Status — COMPLETE (2026-07-12)

All phases landed; `scripts/check.sh` → **GATE: PASS** on all default targets (4953 jobs,
warning-/sorry-free). Commits on branch `retire-lrt-depth-orchestration`:

- `68f2b0aa` foundation — presentation keystone + this plan.
- `44a60893` **P1** — TangentDepth off LrtDepth (direct CarrierRec/WellFounded/
  CanonicalReconstructionCharZero imports + explicit `[CFracGcdCoreWf (DenseFracTower n)]`
  binders; the tower canonical-rep instance cannot auto-recurse on `n`).
- `3d2e6e4a` **P2** — RischTowerLrtGrounding re-anchored to RischSolverTowerLrt (survives; its
  body used no LrtDepth name).
- `fc20a509` **P3+P4** — deleted `Tower/LrtDepth.lean` (660 L, the sole gate-failing module) and
  `Tower/Transcendental.lean` (455 L, its only consumer, a leaf); both imports dropped from the
  Tower aggregator. Merged because the aggregator can't be green with either dangling.
- **P5** — contract pins already present in `DifferentialLegacyCapabilities.lean`: `example`s
  pinning `stage_sound`/`stage_complete` for primitive (genuine composition) and exp/tangent
  (through `exponentialOneStepScheme`/`tangentOneStepScheme`), with `rfl` witnesses that the
  monomial derivatives are `t`/`t²+1`, never `1`. Exp/tangent take the local capability bundles
  as hypotheses — the documented differential-explicit-solver frontier.
- **P6** — `scripts/wiki build` rebuilt; `rdeps DenseLrtStage` → "no declaration matching"; no
  orphan catalogs; no LRT-depth name anywhere in `DeepWiki/`+`Sources/`.

Net: −1115 L of broken/dead orchestration; the sound presentation path is the sole
transcendental-tower spine. LRT grounding remains a documented external frontier (unchanged).

## Invariants

- Rebuild the wiki graph and re-audit callers before each deletion; gate serially.
- No `Sources/` catalog edits (coverage unchanged — retirement touches only engine internals).
- Keep `RischTowerLrtGrounding` and `TangentDepth` — they are genuine content, not shims.
- Completeness stays RELATIVE to the supplied frontier. LRT grounding = documented external frontier;
  do not reassemble `PrimitiveFrontierLrt` / `residueCriterion` concretely.
