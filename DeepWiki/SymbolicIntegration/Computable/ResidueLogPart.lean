import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG

/-! # Residue logarithm part interface

The Rothstein–Trager residue-logarithm stage of the Risch reduced case. A list of `logs = [(cᵢ, vᵢ)]` is a
*lawful* residue-log part of `hNum/Dstar` when its logarithmic derivative sum reconstructs the
proper squarefree-denominator leftover fraction in the field form consumed by the reduced integrator. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- `logs` is a residue-log part of `hNum/Dstar`: `Σᵢ cᵢ · D(log vᵢ) = ⟦hNum/Dstar⟧`. -/
structure LawfulResidueLogPart (Dt hNum Dstar : CPolyG α) (logs : List (α × CPolyG α)) : Prop where
  /-- `Σᵢ cᵢ · (D(amG vᵢ) / amG vᵢ) = ⟦hNum/Dstar⟧`. -/
  residue_match : (logs.map (fun cv => amG α (Polynomial.C (CFieldSpec.toK cv.1))
        * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
      = amG α (toPolyG hNum) / amG α (toPolyG Dstar)

end DeepWiki.SymbolicIntegration
