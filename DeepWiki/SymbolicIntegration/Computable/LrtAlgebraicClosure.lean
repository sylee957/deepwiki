import DeepWiki.SymbolicIntegration.Computable.LrtSoundness
import DeepWiki.SymbolicIntegration.Computable.DifferentialAlgebraicClosure

/-! # Instantiating the LRT `∀E` soundness at the algebraic closure

`IsIntegralResultLrtG` is stated over *every* algebraically-closed differential extension `E` of
`K = CFieldSpec.K α` — the "descent vehicle" that lets the log part carry algebraic residues without pinning
a closure. With `Differential (AlgebraicClosure K)` now built
(`DifferentialAlgebraicClosure.lean`), that `∀E` can finally be **instantiated** at the canonical
`E = AlgebraicClosure K`, yielding a single concrete identity — no longer only "for all E". -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CharZero (CFieldSpec.K α)]

/-- **The LRT soundness, concretely over the algebraic closure.** Instantiates the `∀ E [IsAlgClosed E] …`
identity of `IsIntegralResultLrtG` at `E = AlgebraicClosure (CFieldSpec.K α)` — every required instance now
resolves (`Differential` / `DifferentialAlgebra` from `DifferentialAlgebraicClosure.lean`, `IsAlgClosed` and
`Algebra` canonically). The `∀E` formulation is no longer a barrier to a concrete statement. -/
theorem isIntegralResultLrtG_algebraicClosure (Dt anum aden : CPolyG α) (res : LrtResultG α)
    (h : IsIntegralResultLrtG Dt anum aden res) :
    (towerDerivExt Dt (amGExt (toPolyG res.rational.1) / amGExt (toPolyG res.rational.2))
        + logResidueSumLrtG Dt res.logs : RatFunc (AlgebraicClosure (CFieldSpec.K α)))
      = amGExt (toPolyG anum) / amGExt (toPolyG aden) :=
  h (AlgebraicClosure (CFieldSpec.K α))

end DeepWiki.SymbolicIntegration
