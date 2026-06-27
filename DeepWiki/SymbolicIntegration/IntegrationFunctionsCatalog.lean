import DeepWiki.SymbolicIntegration.ComputableOneShotAssembly
import DeepWiki.SymbolicIntegration.ComputableOneShotSoundness
import DeepWiki.SymbolicIntegration.ComputableHyperexpFullSoundness
import DeepWiki.SymbolicIntegration.ComputableIntegrateTowerCorrectG
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

end DeepWiki.SymbolicIntegration
