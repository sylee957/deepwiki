import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG

/-! # Interface: `LawfulHermiteReduction`

The Hermite-reduction stage of the Risch reduced case, stated purely against the denotation. A Hermite
output `(gnum, gden, hNum, Dstar)` for input `a/d` with monomial derivation `Dt` is *lawful* when it clears
the cleared Hermite identity `D⟦gnum/gden⟧ + ⟦hNum/Dstar⟧ = ⟦a/d⟧`, the leftover denominator `Dstar` is
squarefree, and the leftover fraction `hNum/Dstar` is proper. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Interface law for a Hermite reduction output `(gnum, gden, hNum, Dstar)` of `a/d`. -/
structure LawfulHermiteReduction (Dt a d gnum gden hNum Dstar : CPolyG α) : Prop where
  /-- The cleared Hermite identity `D⟦gnum/gden⟧ + ⟦hNum/Dstar⟧ = ⟦a/d⟧`. -/
  field_identity : towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
      + amG α (toPolyG hNum) / amG α (toPolyG Dstar) = amG α (toPolyG a) / amG α (toPolyG d)
  /-- The leftover denominator is squarefree. -/
  squarefree : Squarefree (toPolyG Dstar)
  /-- The leftover fraction is proper. -/
  proper : (toPolyG hNum).degree < (toPolyG Dstar).degree

end DeepWiki.SymbolicIntegration
