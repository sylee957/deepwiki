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

## What dangles — the four frontier classes (none materialized)

| Frontier | File | Field | Discharge status |
|---|---|---|---|
| `PrimitiveFrontier` | `RischTowerPrimitive` | `hreduced : IsIntegralResultG` (rational reduced) | normal-part soundness PROVEN for δ≤1 (`cHermiteReduceTowerGWf_numer_degree_lt…`); needs materialization at the concrete carrier |
| `LiouvilleFrontier` | `LiouvilleCompleteness` | `descendGenuine` (rational completeness) | keystone (`isLiouville_logExtension_uncond`) done; remaining = computable→abstract bridge |
| `PrimitiveFrontierLrt` | `RischTowerPrimitiveLrt` | `hreducedLrt : IsIntegralResultLrtG` (algebraic reduced) | **closed to `LrtReducedGenuineData`** (`hreducedLrt_of_genuineAll`); remaining = the genuine Bronstein conditions per input |
| `LrtLiouvilleFrontier` | `LrtCompleteness` | `descendGenuineLrt` (algebraic completeness) | keystone done; remaining = computable→abstract residue bridge |

`LawfulRischLevel` produces `IntegralResultG` (rational residues); the LRT track uses `LrtResultG`
(algebraic). So they are **not the same solver** — merging is a re-basing, not a deletion.

## Plan (dependency-ordered)

1. **Consolidate the completeness frontiers.** Prove `IsElementaryIntegrableGenuineG → IsElementaryIntegrableGenuineLrtG`
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
