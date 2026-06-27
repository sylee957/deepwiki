import DeepWiki.SymbolicIntegration.ComputableOneShotAssembly
import DeepWiki.SymbolicIntegration.ComputableOneShotSoundness
import DeepWiki.SymbolicIntegration.ComputableHyperexpFullSoundness
import DeepWiki.SymbolicIntegration.ComputableIntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.ComputableUnifiedMixedSoundness
import DeepWiki.SymbolicIntegration.ComputableUnifiedMixedWfSoundness
import DeepWiki.SymbolicIntegration.ComputableRischDESolveSound
import DeepWiki.SymbolicIntegration.ComputableRischDESolveSoundWf
import DeepWiki.SymbolicIntegration.ComputableRischDEDecisionProcedure
import DeepWiki.SymbolicIntegration.ComputableRischDECompleteness
import DeepWiki.SymbolicIntegration.ComputableAlgebraicWfSoundness
import DeepWiki.SymbolicIntegration.ComputableFunctionAlgebraIntegrate
import DeepWiki.SymbolicIntegration.ComputableAlgebraicDecide
import DeepWiki.SymbolicIntegration.ComputableGeneralCurveDecide
import DeepWiki.SymbolicIntegration.ComputableElementaryIntegrate

/-!
# Integration-functions catalog — coverage + soundness/completeness index

A VERIFIED index of every integration entry point in the symbolic-integration engine. Each function below
is documented with (a) what it integrates (coverage) and (b) the name of the soundness/completeness theorem
that certifies it — and then REFERENCED by an anonymous `example` that names the theorem, so this catalog
fails to compile if a referenced guarantee is renamed or removed. The catalog is documentation + verification
only; it states no new mathematics.

## Second purpose — the Mixed-layer coupling map

Below the index, the `## Mixed-layer coupling` section records, per engine the `cIntegrateMixed*` layer
dispatches to, whether that engine has a STANDALONE soundness theorem (one NOT phrased through
`cIntegrateMixedWf`) — the precondition checklist for removing the Mixed layer.

## Transcendental integrators (Bronstein ch. 5 and 6, over a tower base `CPolyG α`)

* `cIntegrateGFull` / `cIntegrateGFullWf` — the full transcendental driver (canonical split, then RDE-oracle
  poly part, then Rothstein-Trager log part) over a tower base; fuel'd and fuel-free.
  Soundness (checker-free, gated on engine-success bridges): `cIntegrateGFull_primitive_oneShot` (primitive /
  logarithmic monomial) and `cIntegrateGFull_hyperexp_oneShot` (hyperexponential, conditional on `∑c = 0`).
  Completeness: via the RDE solver and `cIntegrateGChecked` below — no direct decision procedure on the driver.
* `cIntegratePolyG` / `cIntegratePolyGWf` — the polynomial-part integrator (Bronstein §5.4 / §6).
  Soundness: PARTIAL — `field_identity_cIntegratePolyG_const` covers the constant case only.
* `cIntegrateReducedG` / `cIntegrateReducedGWf` — the reduced / simple-part capstone (Hermite rational part +
  Rothstein-Trager log part). Soundness: CONDITIONAL field-identity lemmas
  `field_identity_of_cIntegrateReducedG_primitive` / `_hyperexp` / `_of_residueMatch` / `_of_checkIdentityG`.
* `cIntegrateHyperexpNormalG` — the hyperexponential normal-part integrator (§5.9 residual feedback).
  Soundness (unconditional, no `∑c = 0`): `cIntegrateHyperexpNormalG_sound`.
* `cIntegrateHyperexpFullG` — the full hyperexponential driver (Laurent special part + normal part).
  Soundness: `cIntegrateHyperexpFullG_sound`.
* `cIntegrateHyperexpG` / `cIntegrateHyperexpLaurentG` / `cIntegrateHyperexpNormalReducedG` — hyperexponential
  sub-drivers. Soundness: NO direct theorem — their correctness flows through `cIntegrateHyperexpNormalG_sound`
  / `cIntegrateHyperexpFullG_sound`. (Documented gap, flagged for the coordinator.)
* `cIntegrateElementaryG` — the unified elementary integrator over a tower base `α = QFunNZG β`.
  Soundness: NO standalone theorem — only `native_decide` round-trip example validations
  (`algDerivG` against the integrand). (Documented gap, flagged for the coordinator.)
* `cIntegrateGChecked` — the self-validating tower integrator (runs `cIntegrateGFull`, then guards by
  `checkIdentityG`). Soundness (UNCONDITIONAL, all regimes): `cIntegrateGChecked_correct` (carrier-generic)
  and `cIntegrateGChecked_correct_qfunNZG` (at `α = QFunNZG ℚ`).

## The Risch differential-equation solver (Bronstein §6, the RDE oracle)

* `crischDESolveSound` — the corrected recursive RDE solver `D(Y) + F·Y = G`; checks §6.1 solvability itself.
  Soundness (unconditional, no `IsCanonNormalized` hypothesis): `crischDESolveSound_field`.
  Completeness: `crischDESolveSound_isDecisionProcedure` — `some ⟺ FieldRDESolvable`, modulo exactly three
  named §6 residuals; the soundness arrow is `crischDESolveSound_decides_of_residual`.
* `crischDESolveSoundWf` — the FUEL-FREE sound RDE solver. Soundness: `crischDESolveSoundWf_field`.

## Algebraic integrators (Bronstein vol. II / Trager, over `RadExt` or a general plane curve)

* `cIntegrateAlgebraic` / `cIntegrateAlgebraicWf` — the simple-radical integrator over `y² = ρ` (multi-case
  rational dispatch + principal-case log solve); fuel'd and fuel-free.
  Soundness (UNCONDITIONAL modulo the engine round-trip): `cIntegrateAlgebraicWf_sound`.
* `afIntegrateAlgebraic` / `afIntegrateAlgebraicWf` — the general-curve integrator over `K(x)[y]/(f)`.
  Soundness: `afIntegrateAlgebraicWf_sound` (rational round-trip) and the cross-multiplied
  `afIntegrateAlgebraicWf_isGeneralAlgebraicIntegral`.
* `afIntegrateFunctionAlgebra` — the function-algebra (zero-divisor / reducible-curve) integrator.
  Soundness: `afIntegrateFunctionAlgebra_sound`.
* `cIntegrateAlgebraicDecide` — the self-determining `Option` simple-radical integrator (Trager elementarity).
  Soundness: `cIntegrateAlgebraicDecide_sound`. Completeness: `cIntegrateAlgebraicDecide_complete`
  (`none → ¬ elementary`). Decision procedure: `cIntegrateAlgebraicDecide_decides`
  (`some ⟺ elementary`), modulo the named Trager frontier (Liouville-for-algebraic + good-reduction torsion).
* `cIntegrateGeneralCurveDecide` — the self-determining `Option` integrator over an ARBITRARY plane curve.
  Soundness: `cIntegrateGeneralCurveDecide_sound`. Completeness: `cIntegrateGeneralCurveDecide_complete`.
  Decision procedure: `cIntegrateGeneralCurveDecide_decides`, modulo the general `Pic⁰`-torsion frontier.

## Unified integrator — the layer slated for removal

* `cIntegrateMixed` / `cIntegrateMixedWf` — ONE entry over an `IntegrandSpec` tag: a `transcendental` spec
  routes to `cIntegrateGFull(Wf)`, an `algebraic` spec to `cIntegrateAlgebraic(Wf)`. Fuel'd and fuel-free.
  Soundness: `cIntegrateMixedWf_sound` (capstone, both arms — COUPLED: takes per-arm hypotheses discharged by
  the standalone engine theorems); arms `cIntegrateMixedWf_transcendental_oneShot` /
  `cIntegrateMixedWf_algebraic_oneShot`.
* `cIntegrateMixedChecked` — the self-validating unified integrator (guards `cIntegrateMixed` by `checkMixed`).
  Soundness (UNCONDITIONAL): `cIntegrateMixedChecked_sound`; the validator core is `checkMixed_sound`.

## Legacy integrators (level-1 `QFunNZ`, superseded by the `*G` tower forms)

* `cIntegrate` — the legacy assembled top-level integrator (level-1). Soundness: NO standalone theorem
  (use the `*G` tower forms `cIntegrateGFull` / `cIntegrateGChecked`).
* `cIntegrateReduced` — the legacy reduced-case capstone (level-1). Soundness: NO standalone theorem.
* `cIntegrateG` / `cIntegrateGWf` — the tower integrator without the self-check guard. Soundness: NO direct
  theorem (its correctness is the guarded `cIntegrateGChecked_correct` and the one-shots).
-/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## Verified references — transcendental engines

Each `#check @<name>` below names a soundness/completeness theorem, so the catalog FAILS to compile if the
theorem is renamed or removed. Grouped by engine. (`#check` emits info only — no `warning:`/`error:`.) -/

-- `cIntegrateGFull` / `cIntegrateGFullWf`: the checker-free transcendental one-shots.
#check @cIntegrateGFull_primitive_oneShot
#check @cIntegrateGFull_hyperexp_oneShot

-- `cIntegratePolyG`: PARTIAL soundness — the constant case only.
#check @field_identity_cIntegratePolyG_const

-- `cIntegrateReducedG`: the conditional reduced-case field identities.
#check @field_identity_of_cIntegrateReducedG_primitive
#check @field_identity_of_cIntegrateReducedG_hyperexp

-- `cIntegrateHyperexpNormalG`: unconditional normal-part soundness.
#check @cIntegrateHyperexpNormalG_sound

-- `cIntegrateHyperexpFullG`: the full hyperexponential driver soundness.
#check @cIntegrateHyperexpFullG_sound

-- `cIntegrateGChecked`: the self-validating tower integrator's unconditional correctness
-- (carrier-generic, and at `α = QFunNZG ℚ`).
#check @cIntegrateGChecked_correct
#check @cIntegrateGChecked_correct_qfunNZG

/-! ## Verified references — the Risch differential-equation solver -/

-- `crischDESolveSound`: unconditional soundness, the decision procedure, and the completeness arrow.
#check @crischDESolveSound_field
#check @crischDESolveSound_isDecisionProcedure
#check @crischDESolveSound_decides_of_residual

-- `crischDESolveSoundWf`: the fuel-free sound RDE solver.
#check @crischDESolveSoundWf_field

/-! ## Verified references — algebraic engines -/

-- `cIntegrateAlgebraic` / `cIntegrateAlgebraicWf`: unconditional radical soundness.
#check @cIntegrateAlgebraicWf_sound

-- `afIntegrateAlgebraic` / `afIntegrateAlgebraicWf`: the general-curve soundness.
#check @afIntegrateAlgebraicWf_sound

-- `afIntegrateFunctionAlgebra`: the function-algebra (zero-divisor) soundness.
#check @afIntegrateFunctionAlgebra_sound

-- `cIntegrateAlgebraicDecide`: soundness / completeness / decision procedure (Trager elementarity).
#check @cIntegrateAlgebraicDecide_sound
#check @cIntegrateAlgebraicDecide_complete
#check @cIntegrateAlgebraicDecide_decides

-- `cIntegrateGeneralCurveDecide`: soundness / completeness / decision procedure over an arbitrary curve.
#check @cIntegrateGeneralCurveDecide_sound
#check @cIntegrateGeneralCurveDecide_complete
#check @cIntegrateGeneralCurveDecide_decides

/-! ## Verified references — the unified Mixed layer (slated for removal) -/

-- `cIntegrateMixedWf`: the both-arms capstone and the two per-arm one-shots.
#check @cIntegrateMixedWf_sound
#check @CPolyG.cIntegrateMixedWf_transcendental_oneShot
#check @cIntegrateMixedWf_algebraic_oneShot

-- `cIntegrateMixed` / `cIntegrateMixedChecked`: the self-validating unified soundness and the validator core.
#check @cIntegrateMixedChecked_sound
#check @checkMixed_sound

/-! ## Mixed-layer coupling

The precondition checklist for REMOVING the `cIntegrateMixed*` layer: for each engine that layer dispatches
to, does the engine have a STANDALONE soundness theorem (one NOT phrased through `cIntegrateMixedWf` /
`cIntegrateMixedChecked`)? If every dispatched engine is standalone-sound, removing the Mixed layer orphans
no guarantee.

### What the Mixed layer actually dispatches to (verified by the reduction lemmas below)

`cIntegrateMixed` / `cIntegrateMixedWf` is a single `match` on the `IntegrandSpec` top-extension tag — two
arms, one engine each, no recursion:

* `.transcendental Dt a d cands` → `cIntegrateGFull(Wf) Dt a d cands` (the canonical-split + RDE-oracle poly
  part + Rothstein-Trager log part driver).
* `.algebraic ρ R B residual c D degBound` → `cIntegrateAlgebraic(Wf) ρ R B residual c D degBound` (the
  simple-radical multi-case rational dispatch + principal-case log solve).

The dispatch targets are pinned by `cIntegrateMixedWf_transcendental_eq` (= `.transcendental
(cIntegrateGFullWf …)`) and `cIntegrateMixedWf_algebraic_eq` (= `.algebraic (cIntegrateAlgebraicWf …)`),
referenced below. So the Mixed layer dispatches to exactly TWO engines.

### Per-dispatched-engine coupling verdict

* **Transcendental arm — `cIntegrateGFull(Wf)` — ✅ STANDALONE.** Its soundness theorems
  `cIntegrateGFull_primitive_oneShot` / `cIntegrateGFull_hyperexp_oneShot` are stated and proved about the
  driver directly (over `RatFunc (CFieldSpec.K α)`), with NO mention of `cIntegrateMixed*`. Indeed the Mixed
  arm `cIntegrateMixedWf_transcendental_oneShot` is proved BY reducing to `cIntegrateGFull_primitive_oneShot`
  (the dependency runs Mixed → engine, not the reverse). The guarded `cIntegrateGChecked_correct` is also
  standalone.
* **Algebraic arm — `cIntegrateAlgebraic(Wf)` — ✅ STANDALONE.** Its soundness `cIntegrateAlgebraicWf_sound`
  is stated and proved about the engine directly (`toPolyG (algDeriv ρ (cIntegrateAlgebraicWf …)) = toPolyG
  integrand`, via `toPolyG_algDeriv_eq_of_roundtrip`), with NO mention of `cIntegrateMixed*`. The Mixed arm
  `cIntegrateMixedWf_algebraic_oneShot` reuses the abstract `isAlgebraicIntegral_of_parts` (also standalone).

### Engines that are NOT dispatched-to by the Mixed layer (but the prompt lists as algebraic engines)

The self-determining Trager decision integrators `cIntegrateAlgebraicDecide` and
`cIntegrateGeneralCurveDecide` are SEPARATE top-level entry points; the Mixed layer does not route to them
(its algebraic arm calls `cIntegrateAlgebraic(Wf)`, not the `*Decide` integrators). Their soundness /
completeness (`cIntegrateAlgebraicDecide_{sound,complete,decides}`,
`cIntegrateGeneralCurveDecide_{sound,complete,decides}`) is standalone and independent of the Mixed layer.

### ⚠️ Standalone-soundness GAPS (NOT engines the Mixed layer dispatches to — flagged for the coordinator)

These do NOT block Mixed removal (the Mixed layer never calls them), but the catalog records them as
soundness gaps in the engine at large:

* `cIntegrateElementaryG` — NO standalone soundness theorem; only `native_decide` round-trip example
  validations (`algDerivG` against the integrand).
* `cIntegrateHyperexpG` / `cIntegrateHyperexpLaurentG` / `cIntegrateHyperexpNormalReducedG` — NO direct
  soundness theorem (correctness flows through `cIntegrateHyperexpNormalG_sound` / `cIntegrateHyperexpFullG_sound`).
* Legacy `cIntegrate` / `cIntegrateG` / `cIntegrateReduced` — NO standalone soundness theorem (superseded by
  the `*G` tower forms `cIntegrateGFull` / `cIntegrateGChecked`).

### ★ VERDICT

Both engines the Mixed layer dispatches to — `cIntegrateGFull(Wf)` (transcendental) and
`cIntegrateAlgebraic(Wf)` (algebraic) — are STANDALONE-sound. The Mixed-layer soundness
(`cIntegrateMixedWf_sound`, `cIntegrateMixedChecked_sound`) is a thin per-arm dispatch that REUSES these
standalone engine theorems; it contributes no unique guarantee. Therefore the `cIntegrateMixed*` layer can be
removed without orphaning any soundness — nothing must be decoupled first. -/

-- ★ The dispatch targets, VERIFIED: the Mixed layer routes the transcendental arm to `cIntegrateGFullWf` and
-- the algebraic arm to `cIntegrateAlgebraicWf` (so the coupling audit above is about exactly these two engines).
#check @CPolyG.cIntegrateMixedWf_transcendental_eq
#check @cIntegrateMixedWf_algebraic_eq

-- ★ Standalone transcendental soundness (about `cIntegrateGFull(Wf)` directly — NOT via Mixed):
#check @cIntegrateGFull_primitive_oneShot
#check @cIntegrateGChecked_correct
-- ★ Standalone algebraic soundness (about `cIntegrateAlgebraicWf` directly — NOT via Mixed):
#check @cIntegrateAlgebraicWf_sound

end DeepWiki.SymbolicIntegration
