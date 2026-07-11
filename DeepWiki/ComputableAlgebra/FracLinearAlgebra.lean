import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.LinearAlgebra

/-! # Representation-independent fraction linear algebra

Every proof-carrying `CFrac` carrier selects the generic computable-field Gauss implementation.
-/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Represented fractions select generic Gauss-Jordan linear solving through their `CFrac` field instance. -/
instance instCLinearSolveCFrac {F : (α : Type u) → [CField α] → Type u}
    {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CFrac F P] [LawfulCFrac F P]
    {α : Type u} [CField α] [CFieldDomain α P] : CLinearSolve (F α) :=
  CLinearSolve.gauss

end DeepWiki.SymbolicIntegration
