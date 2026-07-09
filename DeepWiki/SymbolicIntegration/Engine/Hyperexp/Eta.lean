import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Hyperexponential coefficient reader

The generic reader `cExpEta Dt = Dt/t` of the coefficient `η` of a hyperexponential
monomial `Dt = η·t`. -/

namespace DeepWiki.SymbolicIntegration


namespace DensePoly

variable {α : Type*} [CField α]

/-- Hyperexponential coefficient `cExpEta Dt = Dt/t = η ∈ α` for a monomial `Dt = η·t`. -/
def cExpEta (Dt : DensePoly α) : α :=
  clead (cdivWf Dt (cshift 1 [CCommRing.one]))

end DensePoly

end DeepWiki.SymbolicIntegration
