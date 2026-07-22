import DeepWiki.SymbolicIntegration.DifferentialAlgebra.PolynomialDerivative

/-! # Formal polynomial derivative compatibility

Compatibility names for the formal derivative now owned by `SymbolicIntegration.DifferentialAlgebra`.
-/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R]

open scoped Differential FormalDiff

/-- Compatibility alias for the `FormalDiff` derivative computation rule. -/
theorem polynomial_differential_apply (q : Polynomial R) :
    q′ = Polynomial.derivative q :=
  DeepWiki.SymbolicIntegration.polynomial_differential_apply q

end DeepWiki.CAlgebra
