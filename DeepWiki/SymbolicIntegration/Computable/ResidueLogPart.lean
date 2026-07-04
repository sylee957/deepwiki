import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG

/-! # Interface: `LawfulResidueLogPart` (Stage-1 abstract)

The Rothstein–Trager residue-logarithm stage of the Risch reduced case. A list of `logs = [(cᵢ, vᵢ)]` is a
*lawful* residue-log part of `hNum/Dstar` when `Σᵢ cᵢ·D(log vᵢ) = ⟦hNum/Dstar⟧` — i.e. the logarithmic
derivative sum reconstructs the (proper, squarefree-denominator) leftover fraction. No concrete algorithm.

The law is stated in the `towerFractionFieldDerivG`/`amG` form the assembler consumes
(`field_identity_of_reducedG_of_residueMatch`). See `docs/risch-two-stage-discipline.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **Interface law: `logs` is a residue-log part of `hNum/Dstar`.** `Σᵢ cᵢ · D(log vᵢ) = ⟦hNum/Dstar⟧`
(the Rothstein–Trager residue match), in the `towerFractionFieldDerivG` form the assembler recombines. -/
structure LawfulResidueLogPart (Dt hNum Dstar : CPolyG α) (logs : List (α × CPolyG α)) : Prop where
  /-- `Σᵢ cᵢ · (D(amG vᵢ) / amG vᵢ) = ⟦hNum/Dstar⟧`. -/
  residue_match : (logs.map (fun cv => amG α (Polynomial.C (CFieldSpec.toK cv.1))
        * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
      = amG α (toPolyG hNum) / amG α (toPolyG Dstar)

end DeepWiki.SymbolicIntegration
