import DeepWiki.SymbolicIntegration.Engine.PolynomialBranchSoundness
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.NormalPartSoundness.Telescope
import DeepWiki.SymbolicIntegration.Engine.NormalPartSoundness.Properness

/-! # Abstract soundness for the tower integrator's normal part

Hermite-telescoping soundness for `cHermiteReduceTower`: the assembled rational part `g` satisfies
`D(g) + h = a/d`, together with the leftover-properness degree analysis (unconditional for
`deg Dt ≤ 1`, margin-gated for `deg Dt ≥ 2`). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-! ### The normal-part assembly through the `checkIdentity` certificate -/

/-- The fuel-free reduced-case field identity from the `checkIdentity` certificate: for
`res = cIntegrateReduced Dt a d cands`, if `checkIdentity Dt res a d = true`, then
`D(g) + logResidueSum Dt res.logs = am a/am d`. -/
theorem field_identity_of_cIntegrateReducedG_of_checkIdentityG [CPolyGcd DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] (Dt : DensePoly α)
    (a d : DensePoly α) (cands : List α)
    (hgden : toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2 ≠ 0)
    (haden : toPoly d ≠ 0)
    (hlogs : ∀ cv ∈ (DensePoly.cIntegrateReduced Dt a d cands).logs, toPoly cv.2 ≠ 0)
    (hcheck : CPoly.checkIdentity Dt (DensePoly.cIntegrateReduced Dt a d cands) a d = true) :
    towerFractionFieldDeriv Dt
        (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
          / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
        + logResidueSum Dt (DensePoly.cIntegrateReduced Dt a d cands).logs
      = am α (toPoly a) / am α (toPoly d) :=
  field_identity_of_checkIdentityG Dt (DensePoly.cIntegrateReduced Dt a d cands) a d
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
