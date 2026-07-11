import DeepWiki.SymbolicIntegration.Engine.CheckIdentityCorrect
import DeepWiki.SymbolicIntegration.Engine.ResidueSource

/-! # Residue logarithm part interface

The Rothstein–Trager residue-logarithm stage of the Risch reduced case. A list of `logs = [(cᵢ, vᵢ)]` is a
*lawful* residue-log part of `hNum/Dstar` when its logarithmic derivative sum reconstructs the
proper squarefree-denominator leftover fraction in the field form consumed by the reduced integrator. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CFrac

universe u v

variable {P : Type u → Type u} [CPoly P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- `logs` is a residue-log part of `hNum/Dstar`: `Σᵢ cᵢ · D(log vᵢ) = ⟦hNum/Dstar⟧`. -/
structure LawfulResidueLogPart (Dt hNum Dstar : P α) (logs : List (α × P α)) : Prop where
  /-- `Σᵢ cᵢ · (D(am vᵢ) / am vᵢ) = ⟦hNum/Dstar⟧`. -/
  residue_match : (logs.map (fun cv => am α (Polynomial.C (CFieldSpec.toK cv.1))
        * (towerFractionFieldDerivP Dt (am α (CPoly.toPoly cv.2)) /
          am α (CPoly.toPoly cv.2)))).sum
      = am α (CPoly.toPoly hNum) / am α (CPoly.toPoly Dstar)

/-- Prop-free residue-logarithm operation driven by a selected residue source. -/
class CResidueLogPart (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] [CResidueSource P α] where
  /-- Produce logarithmic terms for a proper squarefree-denominator remainder, or reject it. -/
  compute : P α → P α → P α → Option (List (α × P α))

/-- Soundness and relative-completeness laws for a selected residue-logarithm operation. -/
class LawfulCResidueLogPart [CPolyEngine P] [CResidueSource P α]
    [CResidueLogPart P α] : Prop where
  /-- Every successful residue-logarithm result reconstructs the input remainder. -/
  sound : ∀ (Dt hNum Dstar : P α) (logs : List (α × P α)),
    CResidueLogPart.compute Dt hNum Dstar = some logs →
      LawfulResidueLogPart Dt hNum Dstar logs
  /-- A complete residue source finds every genuinely integrable proper squarefree remainder. -/
  complete : LawfulCResidueSource P α → ∀ (Dt hNum Dstar : P α),
    CPoly.toPoly Dstar ≠ 0 → Squarefree (CPoly.toPoly Dstar) →
    (CPoly.toPoly hNum).degree < (CPoly.toPoly Dstar).degree →
    (∃ logs : List (α × P α), LawfulResidueLogPart Dt hNum Dstar logs ∧
      (∀ cv ∈ logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      (∀ cv ∈ logs, CPoly.toPoly cv.2 ≠ 0)) →
    ∃ logs, CResidueLogPart.compute Dt hNum Dstar = some logs

end DeepWiki.SymbolicIntegration
