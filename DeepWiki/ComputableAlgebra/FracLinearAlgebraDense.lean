import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.FracReprDense
import DeepWiki.ComputableAlgebra.LinearAlgebra

/-! # Dense-fraction linear algebra

Dense represented fractions select the generic computable-field Gauss implementation. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Dense represented fractions select generic Gauss–Jordan linear solving. -/
instance instCLinearSolveDenseFrac {α : Type u} [CField α] [CFieldDomain α DensePoly] :
    CLinearSolve (DenseFrac α) :=
  CLinearSolve.gauss

end DeepWiki.SymbolicIntegration
