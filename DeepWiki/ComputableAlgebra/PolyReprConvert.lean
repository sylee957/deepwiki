import DeepWiki.ComputableAlgebra.PolyEngine

/-! # Denotation-preserving polynomial representation conversion

Conversion enumerates coefficients through one `CPolyEngine` and rebuilds them through another. -/

namespace DeepWiki.SymbolicIntegration

universe u v

namespace CPolyEngine

/-- Convert a polynomial between computable representations through its low-to-high coefficient list. -/
def convert {P Q : Type u → Type u} [CPoly P] [CPolyEngine P] [CPoly Q] [CPolyEngine Q]
    {α : Type u} [CCommRing α] (p : P α) : Q α :=
  CPolyEngine.ofCoeffList (P := Q) (CPolyEngine.coeffList p)

/-- Representation conversion preserves the denoted polynomial. -/
theorem toPoly_convert {P Q : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] [CPoly Q] [CPolyEngine Q] [LawfulCPolyEngine.{u,v} Q]
    {α : Type u} [CCommRing α] [CRingSpec.{u,v} α] (p : P α) :
    CPoly.toPoly (convert (Q := Q) p) = CPoly.toPoly p := by
  rw [convert, LawfulCPolyEngine.toPoly_ofCoeffList,
    CPoly.toPoly_ofList_eq_dense, ← CPoly.toPoly_ofList_eq_dense (P := P),
    LawfulCPolyEngine.toPoly_coeffList]

end CPolyEngine

end DeepWiki.SymbolicIntegration
