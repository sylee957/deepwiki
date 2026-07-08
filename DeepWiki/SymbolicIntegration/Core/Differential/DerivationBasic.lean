import DeepWiki.SymbolicIntegration.DifferentialFields

/-! # Basic derivation algebra

Small generic rewrites for differential rings.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

/-- Leibniz product rule: `(p·b)′ = p·b′ + b·p′`. -/
theorem deriv_mul_eq {R : Type*} [CommRing R] [Differential R] (p b : R) :
    (p * b)′ = p * b′ + b * p′ := by
  simp only [Derivation.leibniz, smul_eq_mul]

end DeepWiki.SymbolicIntegration
