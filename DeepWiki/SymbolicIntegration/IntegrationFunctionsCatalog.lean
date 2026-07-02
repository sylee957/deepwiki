import DeepWiki.SymbolicIntegration.ComputableOneShotAssembly
import DeepWiki.SymbolicIntegration.ComputableOneShotSoundness
import DeepWiki.SymbolicIntegration.ComputableHyperexpFullSoundness
import DeepWiki.SymbolicIntegration.ComputableIntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.ComputableUnifiedFuelFree
import DeepWiki.SymbolicIntegration.ComputableRischDESolveSoundWf
import DeepWiki.SymbolicIntegration.ComputableRischDEDecisionProcedure
import DeepWiki.SymbolicIntegration.ComputableRischDECompleteness
import DeepWiki.SymbolicIntegration.ComputableTowerRischDECompleteness
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

## Transcendental integrators (Bronstein ch. 5 and 6, over a tower base `CPolyG α`)

* `cIntegrateGFull` / `cIntegrateGFullWf` — the full transcendental driver (canonical split, then RDE-oracle
  poly part, then Rothstein-Trager log part) over a tower base; fuel'd and fuel-free.
  Soundness (checker-free, gated on engine-success bridges): `cIntegrateGFullWf_primitive_oneShot`
  (fuel-free primitive / logarithmic monomial), `cIntegrateGFullWf_hyperexp_oneShot` (fuel-free
  hyperexponential, conditional on `∑c = 0`), and `cIntegrateGFullWf_poly_oneShot` (fuel-free polynomial branch
  `fp ≠ 0`, gated on the poly-RDE soundness `D(qp) = fp`). Level-1 specializations:
  `cIntegrateGFullWf_primitive_oneShot_qfunNZG` and `cIntegrateGFullWf_hyperexp_oneShot_qfunNZG`.
  ★ `cIntegrateGFullWf_primitive_oneShot_inputProper_qfunNZG` — the fuel-free primitive normal-part capstone
  at `α = QFunNZG ℚ`, `deg Dt ≤ 1`, with the abstract degree obstruction `hA` discharged from Wf Hermite
  leftover properness plus simple-part properness; leaves only the genuine Bronstein side conditions.
  ★ `cIntegrateGFullWf_poly_oneShot_simpleProper_qfunNZG` — the fuel-free primitive-base polynomial capstone
  at `α = QFunNZG ℚ`, with `hpoly` and `hA` discharged from constant-base and simple-properness hypotheses.
  The carrier-agnostic `checkIdentityG` ⟹ field-identity bridge (`field_identity_of_checkIdentityG`,
  `ComputableIntegrateTowerCorrectG`) gates a result on the engine's own self-check; the fuel-free top-entry
  bridge is `field_identity_of_cIntegrateGFullWf_of_checkIdentityG`.
  Completeness: via the RDE solver — no direct decision procedure on the driver.
* `cIntegratePolyG` / `cIntegratePolyGWf` — the polynomial-part integrator (Bronstein §5.4 / §6).
  Soundness: PARTIAL — `field_identity_cIntegratePolyG_const` covers the constant case only.
* `cIntegrateReducedGWf` — the fuel-free reduced / simple-part capstone (Hermite rational part +
  Rothstein-Trager log part). Soundness: CONDITIONAL fuel-free field-identity lemmas
  `field_identity_of_cIntegrateReducedGWf_primitive` / `_hyperexp` /
  `_of_checkIdentityG` / `_hyperexp_overshoot`.
* `cIntegrateHyperexpNormalGWf` — the fuel-free hyperexponential normal-part integrator (§5.9 residual
  feedback). Soundness (unconditional, no `∑c = 0`): `cIntegrateHyperexpNormalGWf_sound`, with
  `cIntegrateHyperexpNormalGWf_sound_qfunNZG` as the level-1 `ℚ(x)(t)` specialization.
* `cIntegrateHyperexpFullGWf` — the fuel-free full hyperexponential driver (Laurent special part + normal
  part). Soundness: `cIntegrateHyperexpFullGWf_sound`.
* `cIntegrateHyperexpG` / `cIntegrateHyperexpLaurentG` — hyperexponential
  sub-drivers. Soundness: NO direct theorem — their correctness flows through the normal/full hyperexp
  soundness theorems. (Documented gap, flagged for the coordinator.)
* `cIntegrateElementaryG` — the unified elementary integrator over a tower base `α = QFunNZG β`.
  Soundness: NO standalone theorem — only `native_decide` round-trip example validations
  (`algDerivG` against the integrand). (Documented gap, flagged for the coordinator.)

## The Risch differential-equation solver (Bronstein §6, the RDE oracle)

* `crischDESolveSoundWf` — the cataloged FUEL-FREE RDE solver for `D(Y) + F·Y = G`; checks §6.1 solvability
  itself and routes the inner §6 solve through `cRischDEGWf`. Soundness: `crischDESolveSoundWf_field`, under
  the direct Wf soundness certificate `RischDESoundnessWf`. Completeness/decision procedure:
  `crischDESolveSoundWf_isDecisionProcedure`, modulo the Wf-native `RischDEDecisionProcedureFrontierWf` and
  `RischDESoundnessWf`. The Wf field frontier can be assembled directly from the Wf inner residual-tip
  frontier by `decisionProcedureFrontierWf_of_innerFrontier`.
  The older fueled `crischDESolveSound` remains documented for comparison; the public decision theorem uses
  the Wf solver and direct Wf soundness certificate.

## Algebraic integrators (Bronstein vol. II / Trager, over `RadExt` or a general plane curve)

* `cIntegrateAlgebraic` / `cIntegrateAlgebraicWf` — the simple-radical integrator over `y² = ρ` (multi-case
  rational dispatch + principal-case log solve); fuel'd and fuel-free.
  Soundness (UNCONDITIONAL modulo the engine round-trip): `cIntegrateAlgebraicWf_sound`.
* `afIntegrateAlgebraicWf` — the fuel-free general-curve integrator over `K(x)[y]/(f)`.
  Soundness: `afIntegrateAlgebraicWf_sound` (rational round-trip) and the cross-multiplied
  `afIntegrateAlgebraicWf_isGeneralAlgebraicIntegralWf`.
* `afIntegrateFunctionAlgebra` — the function-algebra (zero-divisor / reducible-curve) integrator.
  Soundness: `afIntegrateFunctionAlgebra_sound`.
* `cIntegrateAlgebraicDecide` — the self-determining `Option` simple-radical integrator (Trager elementarity).
  Soundness: `cIntegrateAlgebraicDecide_sound`. Completeness: `cIntegrateAlgebraicDecide_complete`
  (`none → ¬ elementary`). Decision procedure: `cIntegrateAlgebraicDecide_decides`
  (`some ⟺ elementary`), modulo the named Trager frontier (Liouville-for-algebraic + good-reduction torsion).
* `cIntegrateGeneralCurveDecide` — the self-determining `Option` integrator over an ARBITRARY plane curve.
  Soundness: `cIntegrateGeneralCurveDecide_sound`. Completeness: `cIntegrateGeneralCurveDecide_complete`.
  Decision procedure: `cIntegrateGeneralCurveDecide_decides`, modulo the general `Pic⁰`-torsion frontier.

## Legacy integrators (level-1 ℚ(x) = `QFunNZG ℚ`, superseded by the `*G` tower forms)

* `cIntegrate` / `cIntegrateReduced` — **REMOVED** (superseded by `cIntegrateGFull` / `cIntegrateReducedG`;
  the call graph confirmed only their own examples depended on them). Their reusable `cevalG` Horner-eval
  helper survives in `ComputableIntegrate`.
* `cIntegrateG` / `cIntegrateGWf` — **REMOVED** (the pre-RDE reduced-case tower drivers, subsumed by
  `cIntegrateGFull` / `cIntegrateGFullWf`; the call graph confirmed only their `…Wf_eq` bridge and
  `native_decide` validations depended on them). The reduced-case capstones `cIntegrateReducedG` /
  `cIntegrateReducedGWf` survive.
-/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## Verified references — transcendental engines

Each `#check @<name>` below names a soundness/completeness theorem, so the catalog FAILS to compile if the
theorem is renamed or removed. Grouped by engine. (`#check` emits info only — no `warning:`/`error:`.) -/

-- `cIntegrateGFull` / `cIntegrateGFullWf`: the checker-free transcendental one-shots (primitive, hyperexp, poly).
#check @cIntegrateGFullWf_primitive_oneShot
#check @cIntegrateGFullWf_hyperexp_oneShot
#check @cIntegrateGFullWf_poly_oneShot
#check @cIntegrateGFullWf_primitive_oneShot_qfunNZG
#check @cIntegrateGFullWf_hyperexp_oneShot_qfunNZG
#check @field_identity_of_cIntegrateGFullWf_of_checkIdentityG
-- ★ the primitive normal-part capstone: hA discharged for deg Dt ≤ 1 at ℚ(x)(t).
#check @cIntegrateGFullWf_primitive_oneShot_inputProper_qfunNZG
-- ★ the primitive-base polynomial capstone: hpoly and hA discharged at ℚ(x)(t).
#check @cIntegrateGFullWf_poly_oneShot_simpleProper_qfunNZG

-- `cIntegratePolyG`: PARTIAL soundness — the constant case only.
#check @field_identity_cIntegratePolyG_const

-- `cIntegrateReducedGWf`: the conditional fuel-free reduced-case field identities.
#check @field_identity_of_cIntegrateReducedGWf_primitive
#check @field_identity_of_cIntegrateReducedGWf_hyperexp
#check @field_identity_of_cIntegrateReducedGWf_of_checkIdentityG
#check @field_identity_of_cIntegrateReducedGWf_hyperexp_overshoot

-- `cIntegrateHyperexpNormalGWf`: unconditional fuel-free normal-part soundness.
#check @cIntegrateHyperexpNormalGWf_sound
#check @cIntegrateHyperexpNormalGWf_sound_qfunNZG

-- `cIntegrateHyperexpFullGWf`: the fuel-free full hyperexponential driver soundness.
#check @cIntegrateHyperexpFullGWf_sound

-- `field_identity_of_checkIdentityG`: the carrier-agnostic `checkIdentityG` ⟹ field-identity bridge
-- (`ComputableIntegrateTowerCorrectG`), consumed by the a-priori one-shots above.
#check @field_identity_of_checkIdentityG

/-! ## Verified references — the Risch differential-equation solver -/

-- `crischDESolveSoundWf`: the fuel-free sound RDE solver and its Wf-native decision wrapper.
#check @crischDESolveSoundWf_field
#check @RischDEDecisionProcedureFrontierWf
#check @decisionProcedureFrontierWf_of_innerFrontier
#check @crischDESolveSoundWf_isDecisionProcedure

-- ★ The TOWER-INDUCTION for RDE completeness (`ComputableTowerRischDECompleteness`): the old class-oracle
-- step `crischFieldComplete_step` is still available for `CRischField.crischDESolve`, and the public Wf step
-- `crischFieldCompleteWf_step` targets `crischDESolveSoundWf` directly, modulo the Wf per-level frontier
-- `RischDEStepFrontierWf` and direct Wf soundness certificates. The Wf per-level frontier now exposes the
-- Wf inner residual-tip frontier and uses `decisionProcedureFrontierWf_of_innerFrontier` to assemble the
-- field-level decision frontier. Remaining non-RDE completeness frontiers are separate: the tower-case
-- `NondegenerateLog` (multi-level ℚ-linear-dependence structure theorem; the rational base is done,
-- `nondegenerateLog_ratFunc_iff_logDeriv_ne_zero`), the exponential Liouville instance (off-limits), and the
-- tangent §5.10 reduction (a separate engine).
#check @crischFieldComplete_Q
#check @crischFieldComplete_step
#check @RischDEStepFrontierWf
#check @crischFieldCompleteWf_step

/-! ## Verified references — algebraic engines -/

-- `cIntegrateAlgebraic` / `cIntegrateAlgebraicWf`: unconditional radical soundness.
#check @cIntegrateAlgebraicWf_sound

-- `afIntegrateAlgebraicWf`: the general-curve soundness.
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

end DeepWiki.SymbolicIntegration
