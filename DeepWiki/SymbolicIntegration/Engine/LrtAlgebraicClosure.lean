import DeepWiki.SymbolicIntegration.Engine.LrtSoundness
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.AlgebraicClosure

/-! # Instantiating the LRT `∀E` soundness at the algebraic closure

`IsIntegralResultLrt` is stated over every algebraically closed differential extension `E` of
`K = CFieldSpec.K α`, allowing the log part to carry algebraic residues without choosing a closure.
This file instantiates that polymorphic statement at the canonical `E = AlgebraicClosure K`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac Polynomial

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CharZero (CFieldSpec.K α)]

/-- **The LRT soundness, concretely over the algebraic closure.** Instantiates the `∀ E [IsAlgClosed E] …`
identity of `IsIntegralResultLrt` at `E = AlgebraicClosure (CFieldSpec.K α)`. -/
theorem isIntegralResultLrtG_algebraicClosure (Dt anum aden : DensePoly α) (res : LrtResult α)
    (h : IsIntegralResultLrt Dt anum aden res) :
    (towerDerivExt Dt (amGExt (toPoly res.rational.1) / amGExt (toPoly res.rational.2))
        + logResidueSumLrt Dt res.logs : RatFunc (AlgebraicClosure (CFieldSpec.K α)))
      = amGExt (toPoly anum) / amGExt (toPoly aden) :=
  h (AlgebraicClosure (CFieldSpec.K α))

end DeepWiki.SymbolicIntegration
