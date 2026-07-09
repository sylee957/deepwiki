import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG

/-! # Residue logarithm part interface

The Rothstein–Trager residue-logarithm stage of the Risch reduced case. A list of `logs = [(cᵢ, vᵢ)]` is a
*lawful* residue-log part of `hNum/Dstar` when its logarithmic derivative sum reconstructs the
proper squarefree-denominator leftover fraction in the field form consumed by the reduced integrator. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZ

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- `logs` is a residue-log part of `hNum/Dstar`: `Σᵢ cᵢ · D(log vᵢ) = ⟦hNum/Dstar⟧`. -/
structure LawfulResidueLogPart (Dt hNum Dstar : CPoly α) (logs : List (α × CPoly α)) : Prop where
  /-- `Σᵢ cᵢ · (D(am vᵢ) / am vᵢ) = ⟦hNum/Dstar⟧`. -/
  residue_match : (logs.map (fun cv => am α (Polynomial.C (CFieldSpec.toK cv.1))
        * (towerFractionFieldDeriv Dt (am α (toPoly cv.2)) / am α (toPoly cv.2)))).sum
      = am α (toPoly hNum) / am α (toPoly Dstar)

end DeepWiki.SymbolicIntegration
