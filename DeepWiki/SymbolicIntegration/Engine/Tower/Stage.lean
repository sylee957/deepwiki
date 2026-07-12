import Mathlib.Data.Nat.Basic

/-! # Representation-independent integration stages

The common executable stage contract and its finite recursive composition. Concrete polynomial,
coefficient, and monomial layers instantiate this neutral interface without depending on one another. -/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- A finite-search integration stage with semantic domain, soundness, and relative completeness. -/
structure IntegrationStage (Input : Type u) (Output : Type v) (Integrable : Input → Prop)
    (Correct : Input → Output → Prop) where
  /-- Run the stage at a finite search budget. -/
  run : ℕ → Input → Option Output
  /-- Semantic input and output-remainder invariant of the stage. -/
  domain : Input → Prop
  /-- Every accepted result satisfies the stage's semantic output contract. -/
  sound : ∀ fuel input output, domain input → run fuel input = some output → Correct input output
  /-- Every integrable input in the invariant domain succeeds at some finite budget. -/
  complete : ∀ input, domain input → Integrable input → ∃ fuel output, run fuel input = some output

/-- A finite integration tower selects a base stage and builds every successor from its predecessor. -/
structure IntegrationTowerScheme (Input : ℕ → Type u) where
  /-- Output representation selected at each tower depth. -/
  Output : ℕ → Type v
  /-- Semantic integrability predicate selected at each depth. -/
  Integrable : ∀ n, Input n → Prop
  /-- Semantic correctness predicate selected at each depth. -/
  Correct : ∀ n, Input n → Output n → Prop
  /-- Certified stage at the base depth. -/
  base : IntegrationStage (Input 0) (Output 0) (Integrable 0) (Correct 0)
  /-- Certified successor-stage constructor. -/
  step : ∀ n, IntegrationStage (Input n) (Output n) (Integrable n) (Correct n) →
    IntegrationStage (Input (n + 1)) (Output (n + 1)) (Integrable (n + 1)) (Correct (n + 1))

/-- The stage selected by a finite integration tower at depth `n`. -/
def IntegrationTowerScheme.stage (T : IntegrationTowerScheme Input) : (n : ℕ) →
    IntegrationStage (Input n) (T.Output n) (T.Integrable n) (T.Correct n)
  | 0 => T.base
  | n + 1 => T.step n (T.stage n)

/-- Every accepted result of the recursively selected stage is semantically correct. -/
theorem IntegrationTowerScheme.stage_sound (T : IntegrationTowerScheme Input) (n fuel : ℕ)
    (input : Input n) (output : T.Output n) (hdomain : (T.stage n).domain input)
    (hrun : (T.stage n).run fuel input = some output) : T.Correct n input output :=
  (T.stage n).sound fuel input output hdomain hrun

/-- Every integrable in-domain input eventually succeeds at the selected finite tower stage. -/
theorem IntegrationTowerScheme.stage_complete (T : IntegrationTowerScheme Input) (n : ℕ)
    (input : Input n) (hdomain : (T.stage n).domain input)
    (hintegrable : T.Integrable n input) :
    ∃ fuel output, (T.stage n).run fuel input = some output :=
  (T.stage n).complete input hdomain hintegrable

end DeepWiki.SymbolicIntegration
