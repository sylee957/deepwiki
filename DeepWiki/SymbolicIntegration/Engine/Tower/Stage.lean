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

/-- The output of one integration stage together with the semantic remainder it leaves for later stages. -/
structure RemainderResult (Output : Type u) (Remainder : Type v) where
  /-- The extracted antiderivative contribution. -/
  output : Output
  /-- The remainder invariant passed to the next compositional stage. -/
  remainder : Remainder

/-- A finite-search integration stage whose certified output explicitly carries a semantic remainder.

The executable algorithm remains representation-neutral. Polynomial reduction, Hermite reduction,
monomial special integration, coefficient recursion, and logarithmic reconstruction can therefore
use the same contract while choosing their own output and remainder types. -/
structure RemainderIntegrationStage (Input : Type u) (Output : Type v) (Remainder : Type w)
    (Integrable : Input → Prop) (Correct : Input → Output → Remainder → Prop) where
  /-- The underlying finite-search stage. -/
  stage : IntegrationStage Input (RemainderResult Output Remainder) Integrable
    (fun input result => Correct input result.output result.remainder)

namespace RemainderIntegrationStage

/-- Every accepted remainder-stage result satisfies its selected output-remainder invariant. -/
theorem sound (S : RemainderIntegrationStage Input Output Remainder Integrable Correct)
    (fuel : ℕ) (input : Input) (result : RemainderResult Output Remainder)
    (hdomain : S.stage.domain input) (hrun : S.stage.run fuel input = some result) :
    Correct input result.output result.remainder :=
  S.stage.sound fuel input result hdomain hrun

/-- Every integrable in-domain input eventually produces a certified output-remainder pair. -/
theorem complete (S : RemainderIntegrationStage Input Output Remainder Integrable Correct)
    (input : Input) (hdomain : S.stage.domain input) (hintegrable : Integrable input) :
    ∃ fuel result, S.stage.run fuel input = some result :=
  S.stage.complete input hdomain hintegrable

end RemainderIntegrationStage

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
