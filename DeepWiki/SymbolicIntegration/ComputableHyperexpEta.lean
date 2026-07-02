import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd

/-! # Hyperexponential coefficient reader

The generic reader `cExpEtaG Dt = Dt/t` of the coefficient `η` of a hyperexponential
monomial `Dt = η·t`. -/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α]

/-- Hyperexponential coefficient `cExpEtaG Dt = η ∈ α`: for a hyperexponential monomial
`Dt = η·t` (`δ = 1`), divide `Dt` by `t` (`cshiftG 1 [1]`, exact quotient via `cdivWf`) and read
the resulting degree-0 `t`-polynomial's coefficient. -/
def cExpEtaG (Dt : CPolyG α) : α :=
  cleadG (cdivWf Dt (cshiftG 1 [CField.one]))

end CPolyG

end DeepWiki.SymbolicIntegration
