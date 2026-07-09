import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Hyperexponential coefficient reader

The generic reader `cExpEtaG Dt = Dt/t` of the coefficient `η` of a hyperexponential
monomial `Dt = η·t`. -/

namespace DeepWiki.SymbolicIntegration


namespace CPoly

variable {α : Type*} [CField α]

/-- Hyperexponential coefficient `cExpEtaG Dt = Dt/t = η ∈ α` for a monomial `Dt = η·t`. -/
def cExpEtaG (Dt : CPoly α) : α :=
  cleadG (cdivWf Dt (cshiftG 1 [CField.one]))

end CPoly

end DeepWiki.SymbolicIntegration
