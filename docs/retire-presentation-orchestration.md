# Retire the superseded presentation-path orchestration

**Goal.** Retire the "less general / superseded" computational solver layer: the
**presentation-path transcendental-tower orchestration** (`docs/dynamic-tower-derivation.md`), which was
built as a candidate orchestration replacement but is superseded by the **LRT / `CRischLevel`
(RischLevel) track** that the actual sound-and-complete solvers use (`hyperexpRischLevel`,
`tangentRischLevel`, `CRischLevelLrt.integrate`, the P1–P17 sound+complete capstones).

## Why it's retirable (verified 2026-07-13 via the wiki graph)

The presentation-path files form a **self-contained island**: of the Engine-level `Differential*`
orchestration files, **all have 0 external consumers** (no decl outside the island uses them) EXCEPT
`DifferentialAlgebraicClosure` (6 external consumers — the genuinely-live algebraic-closure infra the
LRT soundness uses, **KEEP**). **No `Sources/` catalog references any of them** → coverage-safe. They
are imported only by the `Engine.lean` / `Tower.lean` aggregators and each other.

The sound-and-complete transcendental Risch results (per-level + tower-depth, primitive/hyperexp/tangent)
all route through the LRT/RischLevel track, NOT this presentation path. The presentation path's own
`stage_sound`/`stage_complete` `example`s are self-referential — nothing consumes their output.

## Retire (13 files, ~2802 lines, coverage-safe)

`Engine/Tower/DifferentialPresentation.lean`, `Engine/Tower/DifferentialTranscendental.lean`,
`Engine/Tower/DifferentialLegacyCapabilities.lean`, `Engine/Tower/DifferentialCoefficientBridge.lean`,
`Engine/Tower/RecursiveMonomialDifferential.lean`, `Engine/DifferentialCanonical.lean`,
`Engine/DifferentialAssembly.lean`, `Engine/DifferentialReconstruction.lean`,
`Engine/DifferentialOneLevel.lean`, `Engine/MonomialDifferentialStage.lean`,
`Engine/MonomialDifferentialPostprocess.lean`, `Engine/Hermite/DifferentialNormal.lean`,
`Engine/Hermite/DifferentialStage.lean`.

**KEEP:** `Engine/DifferentialAlgebraicClosure.lean` (live, 6 consumers); the abstract diff-algebra
foundations (`Core/Differential/*`, `DifferentialFields`, `DifferentialAlgebra/*`,
`RaoDifferentialPolynomials`) — these are the Mathlib-style differential-algebra layer, not
orchestration.

## Phases (gate-green per phase)

- **P1** — remove the island's import lines from `Engine.lean` and `Tower.lean`; delete the 13 files;
  `git rm`. Since the island has no external consumer, this lands in one gate-green push. Verify the
  KEEP file (`DifferentialAlgebraicClosure`) and all downstream still build.
- **P2** — `scripts/wiki build`; confirm the retired decls have no callers; audit no orphaned imports;
  update `docs/dynamic-tower-derivation.md` (mark the path retired) and this doc.

## Status — COMPLETE (2026-07-13)

- **P1 done** (`e9de68a9`): 13 files / ~2802 lines deleted; imports removed from `Engine.lean`/`Tower.lean`;
  full gate PASS (4941 jobs, was 4954).
- **P2 done**: `scripts/wiki build` rebuilt (20530 → 20198 decls); `rdeps primitiveOneStepStage` /
  `DifferentialTranscendentalLevel` → "no declaration matching"; no orphaned imports; sweep found no
  other superseded-solver islands (`LogTower`/`Compositional`/`TangentCapability`/`Algebraic/*` are all
  live with external consumers; the sparse-representation layer — `convertRischLevel`,
  `sparseHyperexpRischLevel`, `instCCanonicalRepresentationSparse` — is the deliberate
  representation-independence keepsake and stays). `docs/dynamic-tower-derivation.md` marked retired.

The sound-and-complete transcendental Risch results are unaffected (they never used the presentation
path). Net: −2802 lines of superseded orchestration; the LRT/RischLevel track is the sole live
transcendental solver path.

## Invariants

- Rebuild the wiki graph and re-audit before deletion; gate with `scripts/check.sh` (must be GATE:
  PASS, warning-/sorry-free).
- No `Sources/` catalog edits (coverage unchanged).
- KEEP `DifferentialAlgebraicClosure` and the abstract diff-algebra foundations.
