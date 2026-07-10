import DeepWiki.ComputableAlgebra.PolyReprResultant
import DeepWiki.ComputableAlgebra.PolyReprSparse

/-! # Representation-selected polynomial resultants

`CPolyResultant` selects an executable resultant algorithm for a polynomial representation, while
`LawfulCPolyResultant` records its denotation as the Sylvester resultant. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Executable resultant selected by a computable polynomial representation. -/
class CPolyResultant (P : Type u → Type u) [CPoly P] where
  /-- Compute the resultant of two represented polynomials. -/
  compute : {α : Type u} → [CField α] → P α → P α → α

/-- Denotation law for a representation-selected executable resultant. -/
class LawfulCPolyResultant (P : Type u → Type u) [CPoly P] [CPolyResultant P] : Prop where
  /-- The selected computation denotes the Sylvester resultant at the represented degrees. -/
  compute_spec : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q : P α),
    CFieldSpec.toK (CPolyResultant.compute p q) =
      Polynomial.resultant (CPoly.toPoly p) (CPoly.toPoly q) (CPoly.cdeg p) (CPoly.cdeg q)

variable {P : Type u → Type u} [CPoly P] [CPolyResultant P] [LawfulCPolyResultant.{u,v} P]

namespace LawfulCPolyResultant

/-- Universe-explicit projection of the selected resultant's denotation law. -/
theorem compute_spec' {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q : P α) :
    CFieldSpec.toK (CPolyResultant.compute p q) =
      Polynomial.resultant (CPoly.toPoly p) (CPoly.toPoly q) (CPoly.cdeg p) (CPoly.cdeg q) := by
  exact @LawfulCPolyResultant.compute_spec P inferInstance inferInstance inferInstance α inferInstance
    (inferInstance : CFieldSpec.{u,v} α) p q

end LawfulCPolyResultant

/-- Sparse polynomials use the representation-generic Sylvester determinant. -/
instance instCPolyResultantSparse : CPolyResultant CPoly.SparsePoly where
  compute := CPoly.cResultant

/-- The sparse Sylvester implementation satisfies the abstract resultant law. -/
instance instLawfulCPolyResultantSparse : LawfulCPolyResultant CPoly.SparsePoly where
  compute_spec := by
    intro α _ _ p q
    change CFieldSpec.toK (CPoly.cResultant p q) =
      Polynomial.resultant (CPoly.toPoly p) (CPoly.toPoly q) (CPoly.cdeg p) (CPoly.cdeg q)
    simpa only [toR_eq_toK] using CPoly.toR_cResultant p q

example :
    CPolyResultant.compute
      (CPoly.SparsePoly.ofList [(0, -1), (2, 1)] : CPoly.SparsePoly ℚ)
      (CPoly.SparsePoly.ofList [(0, -1), (1, 1)]) = 0 := by
  native_decide

end DeepWiki.SymbolicIntegration
