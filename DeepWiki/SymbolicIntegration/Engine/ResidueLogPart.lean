import DeepWiki.SymbolicIntegration.Engine.CheckIdentityCorrect

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

end DeepWiki.SymbolicIntegration
