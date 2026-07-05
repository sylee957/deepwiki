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
integrand `anum / aden` in the tower fraction field. This is a **formal** log-derivative identity — it treats
each residue `cᵢ` as a constant (`logResidueSumG = Σ cᵢ·Δvᵢ/vᵢ`), so it certifies a *genuine* antiderivative
`⟦g⟧ + Σ cᵢ·log vᵢ` only when the residues are actually constants (`AllResiduesConstantG`). -/
def IsIntegralResultG (Dt anum aden : CPolyG α) (res : IntegralResultG α) : Prop :=
  towerFractionFieldDerivG Dt
      (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
    + logResidueSumG Dt res.logs
      = amG α (toPolyG anum) / amG α (toPolyG aden)

/-- Every residue coefficient `cᵢ` in `res.logs` is a **constant** (`D cᵢ = 0`, computably
`cisZeroG [cderiv cᵢ]`). This is what upgrades the formal `IsIntegralResultG` identity to a genuine
antiderivative: `D(⟦g⟧ + Σ cᵢ·log vᵢ) = D(g) + Σ (D(cᵢ)·log vᵢ + cᵢ·Δvᵢ/vᵢ)`, and the spurious `D(cᵢ)·log vᵢ`
vanishes exactly when each `D cᵢ = 0`. Established by the primitive integrability guard. -/
def AllResiduesConstantG (res : IntegralResultG α) : Prop :=
  res.logs.all (fun cv => cisZeroG [CDiffField.cderiv cv.1]) = true

/-- **The genuine integral-result certificate**: the formal identity `IsIntegralResultG` **and** all residues
constant (`AllResiduesConstantG`). The conjunction is what genuinely certifies `⟦g⟧ + Σ cᵢ·log vᵢ` is an
antiderivative of `anum/aden`; `IsIntegralResultG` alone is the formal (constant-treated) identity. -/
def IsGenuineIntegralResultG (Dt anum aden : CPolyG α) (res : IntegralResultG α) : Prop :=
  IsIntegralResultG Dt anum aden res ∧ AllResiduesConstantG res

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
