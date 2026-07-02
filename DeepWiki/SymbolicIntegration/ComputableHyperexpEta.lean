import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd

/-! # Hyperexponential coefficient reader

The generic reader `cExpEtaG Dt = Dt/t`, factored out of the Risch-DE engine so Wf
hyperexponential drivers can use it without importing the fueled RDE oracle.
-/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Generic hyperexponential coefficient `η = Dt/t ∈ α`** `cExpEtaG Dt`: for a hyperexponential
monomial `Dt = η·t` (`δ = 1`), divide `Dt` by `t` (`cshiftG 1 [1]`) and read the resulting degree-0
`t`-polynomial's coefficient `η ∈ α`. The exact quotient is computed by `cdivWf`. Generic mirror of
`cExpEta`. -/
def cExpEtaG (Dt : CPolyG α) : α :=
  cleadG (cdivWf Dt (cshiftG 1 [CField.one]))

end CPolyG

end DeepWiki.SymbolicIntegration
