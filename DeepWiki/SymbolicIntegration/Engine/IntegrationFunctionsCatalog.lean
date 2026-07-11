import DeepWiki.SymbolicIntegration.Engine.OneShotAssembly
import DeepWiki.SymbolicIntegration.Engine.OneShotSoundness
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.FullSoundness
import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.UnifiedFuelFree
import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveSoundWf
import DeepWiki.SymbolicIntegration.Engine.RischDE.DecisionProcedure
import DeepWiki.SymbolicIntegration.Engine.RischDE.Completeness
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDECompleteness
import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicWfSoundness
import DeepWiki.SymbolicIntegration.Engine.FunctionAlgebraIntegrate
import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicDecide
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralCurveDecide
import DeepWiki.SymbolicIntegration.Engine.ElementaryIntegrate

/-!
# Integration-functions catalog — soundness/completeness index

A verified index of the engine's integration entry points: the `#check`s below name each
soundness/completeness/decision theorem, so the catalog fails to compile if a guarantee is renamed
or removed. Documentation only — no new mathematics. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-! ## Verified references — transcendental engines -/

-- `cIntegrateGFull` / `cIntegrateGFullWf`: the checker-free transcendental one-shots (primitive, hyperexp, poly).
#check @cIntegrateGFullWf_primitive_oneShot
#check @cIntegrateGFullWf_hyperexp_oneShot
#check @cIntegrateGFullWf_poly_oneShot
#check @cIntegrateGFullWf_primitive_oneShot_qfunNZG
#check @cIntegrateGFullWf_hyperexp_oneShot_qfunNZG
#check @field_identity_of_cIntegrateGFullWf_of_checkIdentityG
-- The primitive normal-part capstone: `hA` discharged for `deg Dt ≤ 1` at `ℚ(x)(t)`.
#check @cIntegrateGFullWf_primitive_oneShot_inputProper_qfunNZG
-- The primitive-base polynomial capstone: `hpoly` and `hA` discharged at `ℚ(x)(t)`.
#check @cIntegrateGFullWf_poly_oneShot_simpleProper_qfunNZG

-- `CPoly.antiderivative`: PARTIAL soundness — the constant case only.
#check @field_identity_antiderivative_const

-- `cIntegrateReduced`: the conditional fuel-free reduced-case field identities.
#check @field_identity_of_cIntegrateReducedG_primitive
#check @field_identity_of_cIntegrateReducedG_hyperexp
#check @field_identity_of_cIntegrateReducedG_of_checkIdentityG
#check @field_identity_of_cIntegrateReducedG_hyperexp_overshoot

-- `cIntegrateHyperexpNormal`: unconditional fuel-free normal-part soundness.
#check @cIntegrateHyperexpNormalG_sound
#check @cIntegrateHyperexpNormalG_sound_qfunNZG

-- `cIntegrateHyperexpFull`: the fuel-free full hyperexponential driver soundness.
#check @cIntegrateHyperexpFullG_sound

-- `field_identity_of_checkIdentityG`: the carrier-agnostic `checkIdentity` ⟹ field-identity bridge
-- (`ComputableIntegrateTowerCorrectG`), consumed by the a-priori one-shots above.
#check @field_identity_of_checkIdentityG

/-! ## Verified references — the Risch differential-equation solver -/

-- `crischDESolveSoundWf`: the fuel-free sound RDE solver and its Wf-native decision wrapper.
#check @crischDESolveSoundWf_field
#check @RischDEDecisionProcedureFrontierWf
#check @decisionProcedureFrontierWf_of_innerFrontier
#check @crischDESolveSoundWf_isDecisionProcedure

-- The Wf-first tower induction for RDE completeness: the public Wf
-- predicate `CRischFieldCompleteWf` and step `crischFieldCompleteWf_step` target `crischDESolveSoundWf`
-- directly, modulo the Wf per-level frontier
-- `RischDEStepFrontierWf` and direct Wf soundness certificates. The Wf per-level frontier now exposes the
-- Wf inner residual-tip frontier and uses `decisionProcedureFrontierWf_of_innerFrontier` to assemble the
-- field-level decision frontier through selected gcd and differential-split capabilities. The residual
-- recursion layer that calls `CRischField.crischDESolve`
-- one level down is represented by the base IH `CRischFieldComplete β`.
#check @crischFieldComplete_Q
#check @CRischFieldCompleteWf
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
