import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.FracReprSparse
import DeepWiki.ComputableAlgebra.LinearAlgebra

/-! # Sparse-fraction linear algebra

Sparse represented fractions select the generic computable-field Gauss implementation. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Sparse represented fractions select generic Gauss–Jordan linear solving. -/
instance instCLinearSolveSparseFrac {α : Type u} [CField α]
    [CFieldDomain α CPoly.SparsePoly] : CLinearSolve (SparseFrac α) :=
  CLinearSolve.gauss

end DeepWiki.SymbolicIntegration
