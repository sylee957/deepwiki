import DeepWiki.SymbolicIntegration.ComputableIntegrateTowerCorrectG

/-! # Semantic specifications for certified integration results

This file starts the spec-first layer for the computable tower integrator: executable drivers may still
return `IntegralResultG`, but downstream correctness should consume semantic `Prop` specifications rather
than unfold computation or rerun Boolean checks.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **Semantic tower integral-result specification.** `IsIntegralResultG Dt anum aden res` says the
rational part and logarithmic terms stored in `res` differentiate to the integrand `anum / aden` in the
tower fraction field. This is the Prop-level contract that certified algorithms should expose. -/
def IsIntegralResultG (Dt anum aden : CPolyG α) (res : IntegralResultG α) : Prop :=
  towerFractionFieldDerivG Dt
      (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
    + logResidueSumG Dt res.logs
      = amG α (toPolyG anum) / amG α (toPolyG aden)

/-- A passed `checkIdentityG` certificate yields the semantic tower integral-result specification. -/
theorem isIntegralResultG_of_checkIdentityG (Dt : CPolyG α) (res : IntegralResultG α)
    (anum aden : CPolyG α)
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt res anum aden = true) :
    IsIntegralResultG Dt anum aden res :=
  field_identity_of_checkIdentityG Dt res anum aden hgden haden hlogs hcheck

end CPolyG

end DeepWiki.SymbolicIntegration
