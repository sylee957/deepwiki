import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.CheckIdentityCorrect

/-! # Semantic specifications for certified integration results

The `Prop`-level contract `IsIntegralResult` that certified tower integrators expose, so downstream
correctness consumes a specification rather than unfolding computation. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

open DensePoly CFrac

/-! ### Representation-independent integral-result specifications -/

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- `IsIntegralResultP` is the formal tower integral identity for any lawful polynomial representation. -/
def IsIntegralResultP (Dt anum aden : P α) (res : IntegralResult α P) : Prop :=
  towerFractionFieldDerivP Dt
      (am α (CPoly.toPoly res.rational.1) / am α (CPoly.toPoly res.rational.2))
    + logResidueSumP Dt res.logs
      = am α (CPoly.toPoly anum) / am α (CPoly.toPoly aden)

/-- A passed representation-independent checker certificate yields `IsIntegralResultP`. -/
theorem isIntegralResultP_of_checkIdentity (Dt : P α) (res : IntegralResult α P)
    (anum aden : P α)
    (hgden : CPoly.toPoly res.rational.2 ≠ 0) (haden : CPoly.toPoly aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0)
    (hcheck : CPoly.checkIdentity Dt res anum aden = true) :
    IsIntegralResultP Dt anum aden res :=
  field_identity_of_checkIdentityP Dt res anum aden hgden haden hlogs hcheck

namespace DensePoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- The dense tower fraction-field element represented by `num/den`. -/
noncomputable abbrev fieldFrac (num den : DensePoly α) : RatFunc (CFieldSpec.K α) :=
  am α (toPoly num) / am α (toPoly den)

/-- `IsIntegralResult Dt anum aden res`: the rational part and log terms in `res` differentiate to the
integrand `anum / aden` in the tower fraction field. This is a **formal** log-derivative identity — it treats
each residue `cᵢ` as a constant (`logResidueSum = Σ cᵢ·Δvᵢ/vᵢ`), so it certifies a *genuine* antiderivative
`⟦g⟧ + Σ cᵢ·log vᵢ` only when the residues are actually constants (`AllResiduesConstant`). -/
def IsIntegralResult (Dt anum aden : DensePoly α) (res : IntegralResult α) : Prop :=
  towerFractionFieldDeriv Dt
      (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
    + logResidueSum Dt res.logs
      = am α (toPoly anum) / am α (toPoly aden)

/-- Every residue coefficient `cᵢ` in `res.logs` is a **constant** (`D cᵢ = 0`, computably
`cisZero [cderiv cᵢ]`). This is what upgrades the formal `IsIntegralResult` identity to a genuine
antiderivative: `D(⟦g⟧ + Σ cᵢ·log vᵢ) = D(g) + Σ (D(cᵢ)·log vᵢ + cᵢ·Δvᵢ/vᵢ)`, and the spurious `D(cᵢ)·log vᵢ`
vanishes exactly when each `D cᵢ = 0`. Established by the primitive integrability guard. -/
def AllResiduesConstant {P : Type u → Type u} {α : Type u} [CField α] [CDiffField α]
    (res : IntegralResult α P) : Prop :=
  res.logs.all (fun cv => cisZero [CDiffField.cderiv cv.1]) = true

example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let res : IntegralResult ℚ CPoly.SparsePoly :=
      ⟨(ofList [0], ofList [1]), [((1 : ℚ), ofList [1, 1])]⟩
    AllResiduesConstant res := by
  rfl

/-- **The genuine integral-result certificate**: the formal identity `IsIntegralResult` **and** all residues
constant (`AllResiduesConstant`). The conjunction is what genuinely certifies `⟦g⟧ + Σ cᵢ·log vᵢ` is an
antiderivative of `anum/aden`; `IsIntegralResult` alone is the formal (constant-treated) identity. -/
def IsGenuineIntegralResult (Dt anum aden : DensePoly α) (res : IntegralResult α) : Prop :=
  IsIntegralResult Dt anum aden res ∧ AllResiduesConstant res

/-- A passed `checkIdentity` certificate yields the semantic tower integral-result specification. -/
theorem isIntegralResultG_of_checkIdentityG (Dt : DensePoly α) (res : IntegralResult α)
    (anum aden : DensePoly α)
    (hgden : toPoly res.rational.2 ≠ 0) (haden : toPoly aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPoly cv.2 ≠ 0)
    (hcheck : CPoly.checkIdentity Dt res anum aden = true) :
    IsIntegralResult Dt anum aden res :=
  field_identity_of_checkIdentityG Dt res anum aden hgden haden hlogs hcheck

end DensePoly

end DeepWiki.SymbolicIntegration
