import DeepWiki.SymbolicIntegration.Computable.LrtSoundness
import DeepWiki.SymbolicIntegration.Computable.DifferentialAlgebraicClosure

/-! # Instantiating the LRT `∀E` soundness at the algebraic closure

`IsIntegralResultLrtG` is stated over every algebraically closed differential extension `E` of
`K = CFieldSpec.K α`, allowing the log part to carry algebraic residues without choosing a closure.
This file instantiates that polymorphic statement at the canonical `E = AlgebraicClosure K`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CharZero (CFieldSpec.K α)]

/-- **The LRT soundness, concretely over the algebraic closure.** Instantiates the `∀ E [IsAlgClosed E] …`
identity of `IsIntegralResultLrtG` at `E = AlgebraicClosure (CFieldSpec.K α)`. -/
theorem isIntegralResultLrtG_algebraicClosure (Dt anum aden : CPolyG α) (res : LrtResultG α)
    (h : IsIntegralResultLrtG Dt anum aden res) :
    (towerDerivExt Dt (amGExt (toPolyG res.rational.1) / amGExt (toPolyG res.rational.2))
        + logResidueSumLrtG Dt res.logs : RatFunc (AlgebraicClosure (CFieldSpec.K α)))
      = amGExt (toPolyG anum) / amGExt (toPolyG aden) :=
  h (AlgebraicClosure (CFieldSpec.K α))

end DeepWiki.SymbolicIntegration
