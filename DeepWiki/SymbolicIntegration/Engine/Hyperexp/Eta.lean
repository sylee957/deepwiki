import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Hyperexponential coefficient reader

The generic reader `cExpEtaG Dt = Dt/t` of the coefficient `η` of a hyperexponential
monomial `Dt = η·t`. -/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α]

/-- Hyperexponential coefficient `cExpEtaG Dt = Dt/t = η ∈ α` for a monomial `Dt = η·t`. -/
def cExpEtaG (Dt : CPolyG α) : α :=
  cleadG (cdivWf Dt (cshiftG 1 [CField.one]))

end CPolyG

end DeepWiki.SymbolicIntegration
