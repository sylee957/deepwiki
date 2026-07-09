import DeepWiki.SymbolicIntegration.Engine.OneShotSoundness
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.NormalPartSoundness.Telescope
import DeepWiki.SymbolicIntegration.Engine.NormalPartSoundness.Properness

/-! # Abstract soundness for the tower integrator's normal part

Hermite-telescoping soundness for `cHermiteReduceTowerG`: the assembled rational part `g` satisfies
`D(g) + h = a/d`, together with the leftover-properness degree analysis (unconditional for
`deg Dt ≤ 1`, margin-gated for `deg Dt ≥ 2`). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-! ### The normal-part assembly through the `checkIdentityG` certificate -/

/-- The fuel-free reduced-case field identity from the `checkIdentityG` certificate: for
`res = cIntegrateReducedG Dt a d cands`, if `checkIdentityG Dt res a d = true`, then
`D(g) + logResidueSumG Dt res.logs = amG a/amG d`. -/
theorem field_identity_of_cIntegrateReducedG_of_checkIdentityG [CFracGcdCoreWf α] (Dt : CPolyG α)
    (a d : CPolyG α) (cands : List α)
    (hgden : toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.2 ≠ 0)
    (haden : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ (CPolyG.cIntegrateReducedG Dt a d cands).logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt (CPolyG.cIntegrateReducedG Dt a d cands) a d = true) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedG Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedG Dt a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  field_identity_of_checkIdentityG Dt (CPolyG.cIntegrateReducedG Dt a d cands) a d
    hgden haden hlogs hcheck

/-! ### Axiom audit — rests only on the standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms amG_toPolyG_fracAddG
#print axioms amG_toPolyG_foldl_fracAddG
#print axioms towerFractionFieldDerivG_amG_fracAccG
#print axioms sum_towerFractionFieldDerivG_telescope
#print axioms degree_lt_of_exact_div
#print axioms cHermiteReduceTowerG_leftover_proper_of_residual
#print axioms degree_fracAdd_lt_of_proper
#print axioms degree_fracAdd_lt_of_margin
#print axioms toPolyG_fracAddG_margin
#print axioms foldl_guarded_fracAddG_margin
#print axioms toPolyG_residualFraction_proper_of_margin
#print axioms degree_resNum_lt
#print axioms degree_implicitDeriv_frac_lt_of_margin
#print axioms toPolyG_fracAddG_proper
#print axioms foldl_fracAddG_proper
#print axioms foldl_guarded_fracAddG_proper
#print axioms toPolyG_gprimeNum_proper_of_margin
#print axioms toPolyG_gprimeNum_proper_of_degree_le_one
#print axioms toPolyG_resNum_proper
#print axioms toPolyG_residualFraction_proper_of_degree_le_one
#print axioms degree_lt_pow_succ_of_degree_lt
#print axioms toPolyG_inner_summand_proper
#print axioms cHermiteReduceTowerInner_g_proper
#print axioms toPolyG_seedPair_proper
#print axioms cHermiteReduceTowerInner_gloc_proper
#print axioms cHermiteReduceTowerG_g_proper
#print axioms cHermiteReduceTowerG_residual_proper_of_degree_le_one
#print axioms cHermiteReduceTowerG_telescope
#print axioms cHermiteReduceTowerG_telescope_seed
#print axioms field_identity_of_cIntegrateReducedG_of_checkIdentityG
end DeepWiki.SymbolicIntegration
