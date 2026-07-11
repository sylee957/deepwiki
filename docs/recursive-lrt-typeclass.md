# Toward a recursive typeclass Risch solver with no dangling frontiers

**North star.** One recursive, typeclass-resolved Risch solver where every frontier class field is
**discharged into a proven instance** — so a ground solver resolves parameter-free, with a-priori
soundness *and* completeness, no assumed hypotheses left.

## Where we are (2026-07-05)

- **Recursion: built.** `LawfulRischLevel α` (class, `RischTower.lean`) + `instLawfulRischLevelPrimitive`
  (base) + `instLawfulRischLevelTower` (step, `[LawfulRischLevel β] → LawfulRischLevel (CFracG β)`). A solver
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
| `PrimitiveFrontier` | `RischTowerPrimitive` | `hreduced : IsIntegralResultG` (rational reduced) | normal-part soundness PROVEN for δ≤1 (`cHermiteReduceTowerG_numer_degree_lt…`); needs materialization at the concrete carrier |
| ~~`LiouvilleFrontier`~~ | ~~`LiouvilleCompleteness`~~ | ~~`descendGenuine` (rational completeness)~~ | **RETIRED (701dbf95)** — redundant with `LrtLiouvilleFrontier`; sole consumer migrated to the LRT certificate |
| `PrimitiveFrontierLrt` | `RischTowerPrimitiveLrt` | `hreducedLrt : IsIntegralResultLrtG` (algebraic reduced) | **closed to `LrtReducedGenuineData`** (`hreducedLrt_of_genuineAll`); remaining = the genuine Bronstein conditions per input |
| `LrtLiouvilleFrontier` | `LrtCompleteness` | `descendGenuineLrt` (algebraic completeness) | keystone done; remaining = computable→abstract residue bridge |

`LawfulRischLevel` produces `IntegralResultG` (rational residues); the LRT track uses `LrtResultG`
(algebraic). So they are **not the same solver** — merging is a re-basing, not a deletion.

## ★ Key finding (2026-07-05): the rational reduced frontier is NOT universally dischargeable

`PrimitiveFrontier.hreduced` concludes `IsIntegralResultG` (rational, K-level residues). But the rational
reduced soundness needs the **rational-residue split data** — `hden : ⟦Dstar⟧ = Lagrange.nodal s id` (the
reduced denominator splits into *distinct linear* factors over `K`), plus the residue formula/distinctness (the
now-retired `cIntegrateReducedG_primitive_of_splitData` made this explicit). For an input whose residues
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

- **Phase 1 — paired LRT operation and contract.** `RischTowerLrt.lean` now defines the Prop-free
  `CRischLevelLrt` (`case` + `limitedIntegrateSingle`) and `LawfulCRischLevelLrt` (K-level special and LRT
  reduced soundness). Its `integrate` and `soundFormalLrt` compose the supplied operation and contract via
  `cIntegrateCaseLrt_sound`; `instCRischLevelLrtPrimitive` and its lawful companion realize the primitive base.
- **Phase 2 — the LRT tower step.** `towerCoeffIntegrateLrt` is a log-free coefficient integrator recursing
  into a lower `CRischLevelLrt β`, with its lawful contract providing K-level soundness (∀E ⇒ K by injectivity
  of `ratFuncBaseChange` on log-free results); `instCRischLevelLrtTower` and its lawful companion realize the step.
- **Phase 3 — retire the redundant rational recursion.** Once the LRT tower resolves at every depth, delete the
  rational `LawfulRischLevel` reduced-log path + `PrimitiveFrontier` (the undischargeable frontier). Keep the
  generic coefficient recursion (`cLimitedIntegratePolyRatG`) — it is result-type-agnostic and reused.
- **Phase 4 — grounding + the honest end state.** DONE. `RischTowerLrtGrounding.lean`:
  `lrtSolver_sound_on_tower` — on the concrete carrier `CFracG ℚ` (the real ℚ(x)-tower), the assembled
  `CRischLevelLrt.integrate` is sound (`IsIntegralResultLrtG`) depending on **only** the two honest
  frontiers (`PrimitiveFrontierLrt` at the levels used + the tower-level gcd `Fact`; `Fact (GcdFFCorrect ℚ)` is
  a resolved instance). Plus an `example` deriving the whole solver from `LrtReducedGenuineData` via
  `hreducedLrt_of_genuineAll`.

### ★★★ Outcome (2026-07-05): the re-base is COMPLETE

**Correction to an earlier overstatement:** a hypothesis-free ground instance is *not* "mathematically
impossible" — that was too strong. The remaining frontiers are **unproven soundness/criterion theorems for
believed-correct algorithms, plus genuine scope conditions** — eliminable *in principle* via large proofs:

- `PrimitiveFrontierLrt` closes to `LrtReducedGenuineData`, now the **5 genuine Bronstein conditions
  `{hcopgcd, hDt0 (scope), hAD, hm, hE}`** (down from 8 across three sessions). Removed as *derived, not assumed*:
  - **`hilt`** (`hE.3`, "residual not a single pure log") **was a genuine algorithm gap** — `cIntegrateReducedLrtG`
    returned *wrong* answers on pure logs (`∫1/t → log(t+1)`) because `cLrtLogArgG` omitted the `i = deg Dstar`
    branch. **RESOLVED (`a1a61216`)** + **DROPPED (`b4f98d37`):** the branch emits `Dstar`, proven sound
    (`evalLrtArg_const_embed_eq` + `entry_log_eq_fiber_prod` case-split on `idx+1 = cdegG Dstar`, the `i=n` fiber
    being *all* poles).
  - **`hB`** (`implicitDeriv` nonvanishing at the poles) — derived from `hE` normality via
    `isCoprime_prod_X_sub_C_implicitDeriv_iff`; the `hE` bundle shrank three→one (just `hnorm`).
  - **`hR0`** (residue resultant ≠ 0) **DROPPED (`884f0b44`, 2026-07-05)** — Bronstein Thm 5.6.1/§4.4 derives it
    from `hE` normality: over `E = AlgebraicClosure K`, `rtResultantGen_ne_zero` + the `_map` bridge +
    `algebraMap` injectivity give `R ≠ 0`. See the ★ universe note in the recipe below.
  The 5 survivors are genuine (Bronstein's own hypotheses): `hcopgcd`/`hE` = normality, `hDt0` = primitive-case
  scope, `hm` = the exact degree-drop (only an *upper* bound is provable generically), `hAD` = Hermite
  properness (dischargeable-in-principle but only via a concrete-carrier `CFracG ℚ` lemma with several
  engine-regularity side conditions, so it stays for now).

  **★ Drop recipe (all deps confirmed to exist, 2026-07-05):** a ~150-line multi-lemma dev in `LrtSoundness.lean`:
  1. **`evalLrtArg_const_embed_eq`** (BUILT + gate-tested, then reverted with the rest): `evalLrtArg (Dstar.map
     (·::[])) c = Dstar_E` when `Dstar_E` monic (via `raw_eq_map` with `P = (toPolyG Dstar).map C`; `raw = Dstar_E`;
     monic ⟹ normalization trivial). This is the `i = n` log-argument.
  2. **Extend `mem_cLrtLogArgG`** with a 4th conjunct `idx+1 = cdegG Dstar → p.2 = Dstar.map (·::[])` (the `i=n`
     branch value; the existing 3rd conjunct is the `≠` subresultant case). Fix the 3 consumers' `obtain` arity
     (`nodup_roots`, `cover`, `entry_log` — add one `_`).
  3. **Restructure `entry_log_eq_fiber_prod` to DROP `hi`**: establish `idx+1 ≤ cdegG Dstar` (`hindex` +
     `Polynomial.rootMultiplicity_le_natDegree` + `natDegree_rtResultantGen_le` + `cdegG_eq_natDegree`), then
     `by_cases idx+1 = cdegG Dstar`: `= n` uses `hp2n` + `evalLrtArg_const_embed_eq` + **fiber = allpoles** (from
     `natDegree_gcd_eq_count_residue_gen` + `rootMultiplicity_rtResultantGen_eq_natDegree_gcd` ⟹ `#fiber = idx+1 =
     n = #allpoles` ⟹ `Finset.eq_of_subset_of_card_le`; fiber-product = nodal = `Dstar_E`); `< n` is the existing
     subresultant path (`hi` derived via `lt_of_le_of_ne`).
  4. **Thread up:** `logMatch_of_setup` stops passing `hilt c` to `entry_log`; `_of_setup`/`LrtReducedGenuineData`/
     `_of_genuine` drop the `hilt` field from the `hE` bundle.
  5. **Drop `hR0` — DONE (`884f0b44`).** `residueResultant_ne_zero_of_hnormAlgClosure` (new
     `LrtResidueResultantDischarge.lean`): instantiate at `E = AlgebraicClosure (CFieldSpec.K α)`, derive `hB`
     from `hnorm`, then `toPolyG_cResidueResultantTowerG_map` + `rtResultantGen_ne_zero` + `map` injectivity
     ⟹ `R ≠ 0`. `_of_genuine` moved here (it now derives `hR0`) and supplies `hRpp` via `primPart_ne_zero`.
     **★ Universe trap (this was the exact snag that stalled the prior attempt):** instantiating the *inline
     structure field* `hE : ∀ (E : Type u) …` at `AlgebraicClosure K` fails with "failed to synthesize
     `CFieldSpec α`", because `CFieldSpec.K : Type*` is an **existential universe independent of `α`**, and a
     rigid structure-field universe `u` won't unify with it (nor will an explicit `.{u}` param). Fix: make the
     `∀E` normality a **universe-polymorphic `def LrtPoleNormalityData`** (mirroring `IsIntegralResultLrtG`),
     store *that* in the field, and instantiate the def — its E-universe auto-generalizes and unifies. Changing
     `hE` to the def alters the structure's universe arity, so downstream `.{u, _}` / `.{u, _, u}` annotations on
     `LrtReducedGenuineData` are dropped (inference suffices).
- `GcdFFCorrect` at tower levels — fraction-free-gcd = genuine-gcd PRS-regularity; classical subresultant
  theory, portable (pieces in `YunTowerCorrect`/`SplitFactorHelpers`). Medium.
- `LrtLiouvilleFrontier` (completeness descent) — abstract Liouville keystone proven in-project
  (`isLiouville_logExtension_uncond`); the remaining computable→abstract residue bridge is a large
  witness-threaded residue-algebra development (the converse of the forward soundness dev). Large.

So "no dangling frontier" is achieved *structurally* (the recursion resolves at every depth; every hypothesis is
a **named** condition; the undischargeable-in-principle rational `PrimitiveFrontier` is deleted), but the three
frontiers are **genuine remaining mathematics**, each a multi-session discharge — not proven-impossible.

**Completeness now derivable from the contract** (`b3fe0b3e`): `CRischLevelLrt.reducedDecides` — the lawful
contract that gives `soundFormalLrt` also *decides* genuine integrability of the reduced part (`←` from
`reducedSoundLrt`, `→` from `[LrtLiouvilleFrontier α]`), with the frontier kept separate.

The one deferred *mechanical* item is the general connection `IsElementaryIntegrableGenuineG → …Lrt` (the
`evalLrtArg` monic-normalization makes it ~150 intricate lines) — not needed for the re-base, since the rational
recursion is retired.

## Plan (dependency-ordered)

1. **Consolidate the completeness frontiers.** DONE (partial): the rational `LiouvilleFrontier` is RETIRED — its one consumer (the ∫1/log x demo) migrated to the stronger `LrtLiouvilleFrontier` certificate; `LiouvilleCompleteness.lean` deleted. The general connection (below) that would DERIVE it is still open. Prove `IsElementaryIntegrableGenuineG → IsElementaryIntegrableGenuineLrtG`
   (a rational genuine result is an algebraic one — each rational log `(c,v)` is the root of `X−c`). Then
   `LrtLiouvilleFrontier ⇒ LiouvilleFrontier` (both descend to the same `cResidueConstantGuardG`), retiring
   the separately-assumed rational completeness frontier. **Smallest, cleanest first win.**
2. **Discharge the reduced soundness at the concrete carrier.** Materialize `PrimitiveFrontier (CFracG ℚ)`
   (and the tower carriers) from the proven δ≤1 normal-part soundness — turning the assumed `hreduced` into a
   theorem for the concrete levels. Then `instLawfulRischLevelTower` resolves with a real base.
3. **Discharge the completeness bridge** (`descendGenuine`/`descendGenuineLrt`) — the computable→abstract
   residue criterion, using the proven keystones. The residue bridge just built is the sufficiency half; this
   is the necessary half.
4. **Materialize the ground instance.** With 1–3, `instance : LawfulRischLevel (CFracG ℚ)` resolves with no
   hypotheses → the recursive solver is fully proven, soundness + completeness, no dangling frontier.

**Decision to make for step 2/4:** keep `LawfulRischLevel` on `IntegralResultG` (rational — load-bearing for
the coefficient recursion) and treat the LRT decision as the *completeness* layer over it, OR re-base the whole
recursion on `LrtResultG` (fully general, big refactor). Step 1 is orthogonal and worth doing first either way.

## Non-goals / kept

- `cIntegrateGFullWf` (the live, `native_decide`-validated compute engine) stays — it is the executable path,
  complementary to this a-priori-proof architecture.
