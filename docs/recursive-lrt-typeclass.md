# Toward a recursive typeclass Risch solver with no dangling frontiers

**North star.** One recursive, typeclass-resolved Risch solver where every frontier class field is
**discharged into a proven instance** — so a ground solver resolves parameter-free, with a-priori
soundness *and* completeness, no assumed hypotheses left.

## Where we are (2026-07-05)

- **Recursion: built.** `LawfulRischLevel α` (class, `RischTower.lean`) + `instLawfulRischLevelPrimitive`
  (base) + `instLawfulRischLevelTower` (step, `[LawfulRischLevel β] → LawfulRischLevel (QFunNZG β)`). A solver
  resolves at every tower depth (validated at depth 2). The coefficient recursion is sound
  (`towerCoeffIntegrate_sound`, denotational; the rational path is load-bearing here — a coefficient integral
  is *limited* integration, log-free by nature).
- **Decision procedure: built.** `primitiveLrtDecides` — `IsElementaryIntegrableGenuineLrtG ↔ guard`, the
  soundness+completeness characterization for the algebraic-residue (LRT) case. The residue bridge it was
  reduced to is now **proven** (`allResiduesConstantLrtG_of_guard`, `ResidueConstantBridge.lean`).
- **Differential (AlgebraicClosure K): built** — un-blocks instantiating the LRT `∀E` soundness concretely.

## What dangles — the frontier classes (none materialized)

| Frontier | File | Field | Discharge status |
|---|---|---|---|
| `PrimitiveFrontier` | `RischTowerPrimitive` | `hreduced : IsIntegralResultG` (rational reduced) | normal-part soundness PROVEN for δ≤1 (`cHermiteReduceTowerGWf_numer_degree_lt…`); needs materialization at the concrete carrier |
| ~~`LiouvilleFrontier`~~ | ~~`LiouvilleCompleteness`~~ | ~~`descendGenuine` (rational completeness)~~ | **RETIRED (701dbf95)** — redundant with `LrtLiouvilleFrontier`; sole consumer migrated to the LRT certificate |
| `PrimitiveFrontierLrt` | `RischTowerPrimitiveLrt` | `hreducedLrt : IsIntegralResultLrtG` (algebraic reduced) | **closed to `LrtReducedGenuineData`** (`hreducedLrt_of_genuineAll`); remaining = the genuine Bronstein conditions per input |
| `LrtLiouvilleFrontier` | `LrtCompleteness` | `descendGenuineLrt` (algebraic completeness) | keystone done; remaining = computable→abstract residue bridge |

`LawfulRischLevel` produces `IntegralResultG` (rational residues); the LRT track uses `LrtResultG`
(algebraic). So they are **not the same solver** — merging is a re-basing, not a deletion.

## ★ Key finding (2026-07-05): the rational reduced frontier is NOT universally dischargeable

`PrimitiveFrontier.hreduced` concludes `IsIntegralResultG` (rational, K-level residues). But
`cIntegrateReducedGWf_primitive_of_splitData` (`PrimitiveReducedGrounded.lean`) shows that soundness needs
the **rational-residue split data**: `hden : ⟦Dstar⟧ = Lagrange.nodal s id` (the reduced denominator splits
into *distinct linear* factors over `K`), plus the residue formula/distinctness. For an input whose residues
are algebraic (don't split over `K`), `IsIntegralResultG` is **false** — the rational reduced integrator gives
wrong/incomplete logs. So `PrimitiveFrontier` can never be materialized as a ground instance; it is a genuine
frontier, not an unproven-but-true statement.

**Consequence for the north star.** "No dangling frontiers" is impossible on the rational `IntegralResultG`
recursion. The path is therefore **step 2′ = re-base `LawfulRischLevel` (and the tower step) on `LrtResultG`**,
where the reduced frontier `PrimitiveFrontierLrt` *is* dischargeable — it is already closed to
`LrtReducedGenuineData` (`hreducedLrt_of_genuineAll`), and those residue-data conditions ARE providable over
the splitting field / algebraic closure (now that `Differential (AlgebraicClosure K)` is built). The genuine
Bronstein side conditions (`hilt` non-degeneracy etc.) are the honest irreducible frontier — the real
boundary of the algorithm's correctness, not bookkeeping.

Revised plan: (1) general connection `IsElementaryIntegrableGenuineG → …Lrt` [universally true, buildable];
(2′) re-base the recursion on `LrtResultG`; (3) discharge `PrimitiveFrontierLrt` from the genuine data over the
closure; (4) discharge `descendGenuineLrt`; (5) ground instance. The re-base (2′) is the load-bearing refactor.

## ★★ The re-base, phased (2026-07-05) — user directive "rebase it and retire redundant one"

**Head start (mapped):** the *one-level* LRT assembly is already complete — `cIntegrateCaseLrt` +
`cIntegrateCaseLrt_sound` (full special+reduced → `LrtResultG`, `LrtAssembly.lean`), `combineSNLrt`, and
`PrimitiveFrontierLrt` (dischargeable to `LrtReducedGenuineData`). The special-part hook `MonomialCase` and the
generic coefficient recursion `cLimitedIntegratePolyRatG` are *shared* (result-type-agnostic). What is missing
is only the **recursive LRT tower class** + its LRT coefficient integrator. So the re-base reuses most of the
stack.

Phases (each its own gate-green commit):

- **Phase 1 — `LawfulRischLevelLrt` class + base instance.** `RischTowerLrt.lean`: the recursive LRT class
  (`case` + `specialSound` [K-level, shared] + `reducedSoundLrt` [LRT]), `integrate` via `cIntegrateCaseLrt`,
  `soundFormalLrt` via `cIntegrateCaseLrt_sound`, and `instLawfulRischLevelLrtPrimitive` from
  `[PrimitiveFrontierLrt α]` (reusing `primitiveGuardedCase_specialSound`). No coefficient recursion at the base.
  **← current.**
- **Phase 2 — the LRT tower step.** `towerCoeffIntegrateLrt` (log-free coefficient integrator recursing into
  `LawfulRischLevelLrt β`) + its K-level soundness (∀E ⇒ K by injectivity of `ratFuncBaseChange` on log-free
  results), fed to the shared `cLimitedIntegratePolyRatG`; then `instLawfulRischLevelLrtTower`. Validate depth-2.
- **Phase 3 — retire the redundant rational recursion.** Once the LRT tower resolves at every depth, delete the
  rational `LawfulRischLevel` reduced-log path + `PrimitiveFrontier` (the undischargeable frontier). Keep the
  generic coefficient recursion (`cLimitedIntegratePolyRatG`) — it is result-type-agnostic and reused.
- **Phase 4 — ground instance + completeness.** Discharge `PrimitiveFrontierLrt` from the genuine data
  (`hreducedLrt_of_genuineAll`); the completeness frontier `LrtLiouvilleFrontier` stays the honest boundary.

## Plan (dependency-ordered)

1. **Consolidate the completeness frontiers.** DONE (partial): the rational `LiouvilleFrontier` is RETIRED — its one consumer (the ∫1/log x demo) migrated to the stronger `LrtLiouvilleFrontier` certificate; `LiouvilleCompleteness.lean` deleted. The general connection (below) that would DERIVE it is still open. Prove `IsElementaryIntegrableGenuineG → IsElementaryIntegrableGenuineLrtG`
   (a rational genuine result is an algebraic one — each rational log `(c,v)` is the root of `X−c`). Then
   `LrtLiouvilleFrontier ⇒ LiouvilleFrontier` (both descend to the same `cResidueConstantGuardG`), retiring
   the separately-assumed rational completeness frontier. **Smallest, cleanest first win.**
2. **Discharge the reduced soundness at the concrete carrier.** Materialize `PrimitiveFrontier (QFunNZG ℚ)`
   (and the tower carriers) from the proven δ≤1 normal-part soundness — turning the assumed `hreduced` into a
   theorem for the concrete levels. Then `instLawfulRischLevelTower` resolves with a real base.
3. **Discharge the completeness bridge** (`descendGenuine`/`descendGenuineLrt`) — the computable→abstract
   residue criterion, using the proven keystones. The residue bridge just built is the sufficiency half; this
   is the necessary half.
4. **Materialize the ground instance.** With 1–3, `instance : LawfulRischLevel (QFunNZG ℚ)` resolves with no
   hypotheses → the recursive solver is fully proven, soundness + completeness, no dangling frontier.

**Decision to make for step 2/4:** keep `LawfulRischLevel` on `IntegralResultG` (rational — load-bearing for
the coefficient recursion) and treat the LRT decision as the *completeness* layer over it, OR re-base the whole
recursion on `LrtResultG` (fully general, big refactor). Step 1 is orthogonal and worth doing first either way.

## Non-goals / kept

- `cIntegrateGFullWf` (the live, `native_decide`-validated compute engine) stays — it is the executable path,
  complementary to this a-priori-proof architecture.
