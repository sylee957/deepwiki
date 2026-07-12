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

end DeepWiki.SymbolicIntegration
