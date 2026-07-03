import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG

/-! # Semantic specifications for certified integration results

The `Prop`-level contract `IsIntegralResultG` that certified tower integrators expose, so downstream
correctness consumes a specification rather than unfolding computation. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- `IsIntegralResultG Dt anum aden res`: the rational part and log terms in `res` differentiate to the
integrand `anum / aden` in the tower fraction field. -/
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
