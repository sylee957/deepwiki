import DeepWiki.SymbolicIntegration.Engine.CheckIdentityCorrect

/-! # Interface: `LawfulHermiteReduction`

The Hermite-reduction stage of the Risch reduced case, stated purely against the denotation. A Hermite
output `(gnum, gden, hNum, Dstar)` for input `a/d` with monomial derivation `Dt` is *lawful* when it clears
the cleared Hermite identity `D⟦gnum/gden⟧ + ⟦hNum/Dstar⟧ = ⟦a/d⟧`, the leftover denominator `Dstar` is
squarefree, and the leftover fraction `hNum/Dstar` is proper. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CFrac

universe u v

variable {P : Type u → Type u} [CPoly P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Interface law for a Hermite reduction output `(gnum, gden, hNum, Dstar)` of `a/d`. -/
structure LawfulHermiteReduction (Dt a d gnum gden hNum Dstar : P α) : Prop where
  /-- The cleared Hermite identity `D⟦gnum/gden⟧ + ⟦hNum/Dstar⟧ = ⟦a/d⟧`. -/
  field_identity : towerFractionFieldDerivP Dt
      (am α (CPoly.toPoly gnum) / am α (CPoly.toPoly gden))
      + am α (CPoly.toPoly hNum) / am α (CPoly.toPoly Dstar)
        = am α (CPoly.toPoly a) / am α (CPoly.toPoly d)
  /-- The leftover denominator is squarefree. -/
  squarefree : Squarefree (CPoly.toPoly Dstar)
  /-- The leftover fraction is proper. -/
  proper : (CPoly.toPoly hNum).degree < (CPoly.toPoly Dstar).degree

end DeepWiki.SymbolicIntegration
