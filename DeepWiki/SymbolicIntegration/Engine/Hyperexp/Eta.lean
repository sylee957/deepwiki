import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Hyperexponential coefficient reader

The generic reader `cExpEta Dt = Dt/t` of the coefficient `η` of a hyperexponential
monomial `Dt = η·t`. -/

namespace DeepWiki.SymbolicIntegration


namespace CPoly

variable {α : Type*} [CField α]

/-- Hyperexponential coefficient `cExpEta Dt = Dt/t = η ∈ α` for a monomial `Dt = η·t`. -/
def cExpEta (Dt : CPoly α) : α :=
  clead (cdivWf Dt (cshift 1 [CField.one]))

end CPoly

end DeepWiki.SymbolicIntegration
