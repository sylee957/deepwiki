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
  logarithmic monomial), `cIntegrateGFull_hyperexp_oneShot` (hyperexponential, conditional on `∑c = 0`), and
  `cIntegrateGFull_poly_oneShot` (polynomial branch `fp ≠ 0`, gated on the poly-RDE soundness `D(qp) = fp`).
  ★ `cIntegrateGFull_primitive_oneShot_inputProper_qfunNZG` — the primitive normal-part capstone at
  `α = QFunNZG ℚ`, `deg Dt ≤ 1`, with the abstract degree obstruction `hA` **discharged** (proven
  Hermite-leftover-properness + unconditional input-properness); leaves only the genuine Bronstein side
  conditions (`hrecon`/`hden`/`hnorm`).
  The carrier-agnostic `checkIdentityG` ⟹ field-identity bridge (`field_identity_of_checkIdentityG`,
  `ComputableIntegrateTowerCorrectG`) gates a result on the engine's own self-check.
  Completeness: via the RDE solver — no direct decision procedure on the driver.
* `cIntegratePolyG` / `cIntegratePolyGWf` — the polynomial-part integrator (Bronstein §5.4 / §6).
  Soundness: PARTIAL — `field_identity_cIntegratePolyG_const` covers the constant case only.
* `cIntegrateReducedG` / `cIntegrateReducedGWf` — the reduced / simple-part capstone (Hermite rational part +
  Rothstein-Trager log part). Soundness: CONDITIONAL field-identity lemmas
  `field_identity_of_cIntegrateReducedG_primitive` / `_hyperexp` / `_of_residueMatch` / `_of_checkIdentityG`.
* `cIntegrateHyperexpNormalG` — the hyperexponential normal-part integrator (§5.9 residual feedback).
  Soundness (unconditional, no `∑c = 0`): `cIntegrateHyperexpNormalG_sound`.
* `cIntegrateHyperexpFullG` — the full hyperexponential driver (Laurent special part + normal part).
  Soundness: `cIntegrateHyperexpFullG_sound`.
* `cIntegrateHyperexpG` / `cIntegrateHyperexpLaurentG` — hyperexponential
  sub-drivers. Soundness: NO direct theorem — their correctness flows through `cIntegrateHyperexpNormalG_sound`
  / `cIntegrateHyperexpFullG_sound`. (Documented gap, flagged for the coordinator.)
* `cIntegrateElementaryG` — the unified elementary integrator over a tower base `α = QFunNZG β`.
  Soundness: NO standalone theorem — only `native_decide` round-trip example validations
  (`algDerivG` against the integrand). (Documented gap, flagged for the coordinator.)

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
#check @cIntegrateGFull_primitive_oneShot
#check @cIntegrateGFull_hyperexp_oneShot
#check @cIntegrateGFull_poly_oneShot
-- ★ the primitive normal-part capstone: hA discharged for deg Dt ≤ 1 at ℚ(x)(t).
#check @cIntegrateGFull_primitive_oneShot_inputProper_qfunNZG

-- `cIntegratePolyG`: PARTIAL soundness — the constant case only.
#check @field_identity_cIntegratePolyG_const

-- `cIntegrateReducedG`: the conditional reduced-case field identities.
#check @field_identity_of_cIntegrateReducedG_primitive
#check @field_identity_of_cIntegrateReducedG_hyperexp

-- `cIntegrateHyperexpNormalG`: unconditional normal-part soundness.
#check @cIntegrateHyperexpNormalG_sound

-- `cIntegrateHyperexpFullG`: the full hyperexponential driver soundness.
#check @cIntegrateHyperexpFullG_sound

-- `field_identity_of_checkIdentityG`: the carrier-agnostic `checkIdentityG` ⟹ field-identity bridge
-- (`ComputableIntegrateTowerCorrectG`), consumed by the a-priori one-shots above.
#check @field_identity_of_checkIdentityG

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
