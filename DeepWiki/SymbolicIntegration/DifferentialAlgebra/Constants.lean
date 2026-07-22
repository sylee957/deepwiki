import DeepWiki.SymbolicIntegration.DifferentialAlgebra.Basic

/-! # Constants in differential extensions

Basic API for constants in differential extensions. -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

section Extension

/-- Constants of the base field remain constants in a differential extension. -/
theorem deriv_algebraMap_eq_zero {F E : Type*} [Field F] [Field E] [Differential F]
    [Differential E] [Algebra F E] [DifferentialAlgebra F E] {c : F} (hc : c′ = 0) :
    (algebraMap F E c)′ = 0 := by
  rw [deriv_algebraMap, hc, map_zero]

end Extension

end DeepWiki.SymbolicIntegration
