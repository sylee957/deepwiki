import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG

/-! # Semantic specifications for certified integration results

The `Prop`-level contract `IsIntegralResult` that certified tower integrators expose, so downstream
correctness consumes a specification rather than unfolding computation. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPoly CFrac

namespace CPoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- `IsIntegralResult Dt anum aden res`: the rational part and log terms in `res` differentiate to the
integrand `anum / aden` in the tower fraction field. This is a **formal** log-derivative identity — it treats
each residue `cᵢ` as a constant (`logResidueSum = Σ cᵢ·Δvᵢ/vᵢ`), so it certifies a *genuine* antiderivative
`⟦g⟧ + Σ cᵢ·log vᵢ` only when the residues are actually constants (`AllResiduesConstant`). -/
def IsIntegralResult (Dt anum aden : CPoly α) (res : IntegralResult α) : Prop :=
  towerFractionFieldDeriv Dt
      (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
    + logResidueSum Dt res.logs
      = am α (toPoly anum) / am α (toPoly aden)

/-- Every residue coefficient `cᵢ` in `res.logs` is a **constant** (`D cᵢ = 0`, computably
`cisZero [cderiv cᵢ]`). This is what upgrades the formal `IsIntegralResult` identity to a genuine
antiderivative: `D(⟦g⟧ + Σ cᵢ·log vᵢ) = D(g) + Σ (D(cᵢ)·log vᵢ + cᵢ·Δvᵢ/vᵢ)`, and the spurious `D(cᵢ)·log vᵢ`
vanishes exactly when each `D cᵢ = 0`. Established by the primitive integrability guard. -/
def AllResiduesConstant (res : IntegralResult α) : Prop :=
  res.logs.all (fun cv => cisZero [CDiffField.cderiv cv.1]) = true

/-- **The genuine integral-result certificate**: the formal identity `IsIntegralResult` **and** all residues
constant (`AllResiduesConstant`). The conjunction is what genuinely certifies `⟦g⟧ + Σ cᵢ·log vᵢ` is an
antiderivative of `anum/aden`; `IsIntegralResult` alone is the formal (constant-treated) identity. -/
def IsGenuineIntegralResult (Dt anum aden : CPoly α) (res : IntegralResult α) : Prop :=
  IsIntegralResult Dt anum aden res ∧ AllResiduesConstant res

/-- A passed `checkIdentity` certificate yields the semantic tower integral-result specification. -/
theorem isIntegralResultG_of_checkIdentityG (Dt : CPoly α) (res : IntegralResult α)
    (anum aden : CPoly α)
    (hgden : toPoly res.rational.2 ≠ 0) (haden : toPoly aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPoly cv.2 ≠ 0)
    (hcheck : CPoly.checkIdentity Dt res anum aden = true) :
    IsIntegralResult Dt anum aden res :=
  field_identity_of_checkIdentityG Dt res anum aden hgden haden hlogs hcheck

end CPoly

end DeepWiki.SymbolicIntegration
