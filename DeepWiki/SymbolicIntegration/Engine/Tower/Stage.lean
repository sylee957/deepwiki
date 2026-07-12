import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pairing

/-! # Representation-independent integration stages

The common executable stage contract and its finite recursive composition. Concrete polynomial,
coefficient, and monomial layers instantiate this neutral interface without depending on one another. -/

namespace DeepWiki.SymbolicIntegration

universe u v w

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

namespace IntegrationStage

/-- Sequentially compose finite-search stages, pairing their independent fuel budgets.

The second stage consumes the first stage's certified output. Its domain and integrability are
required for every output satisfying the first stage's invariant, which is exactly what makes
soundness and relative completeness compose without a monotonic-fuel assumption. -/
noncomputable def compose
    {Input : Type u} {Middle : Type v} {Output : Type w}
    {IntegrableS : Input → Prop} {CorrectS : Input → Middle → Prop}
    {IntegrableT : Middle → Prop} {CorrectT : Middle → Output → Prop}
    (S : IntegrationStage Input Middle IntegrableS CorrectS)
    (next : IntegrationStage Middle Output IntegrableT CorrectT) :
    IntegrationStage Input Output
      (fun input => IntegrableS input ∧
        ∀ middle, CorrectS input middle → IntegrableT middle)
      (fun input output => ∃ middle, CorrectS input middle ∧ CorrectT middle output) :=
  { run := fun fuel input =>
      let fuels := Nat.unpair fuel
      (S.run fuels.1 input).bind fun middle => next.run fuels.2 middle
    domain := fun input => S.domain input ∧
      ∀ middle, CorrectS input middle → next.domain middle
    sound := by
      intro fuel input output hdomain hrun
      let fuels := Nat.unpair fuel
      change (S.run fuels.1 input).bind (fun middle => next.run fuels.2 middle) = some output at hrun
      cases hfirst : S.run fuels.1 input with
      | none => simp [hfirst] at hrun
      | some middle =>
        simp only [hfirst, Option.bind_some] at hrun
        have hmiddle := S.sound fuels.1 input middle hdomain.1 hfirst
        exact ⟨middle, hmiddle,
          next.sound fuels.2 middle output (hdomain.2 middle hmiddle) hrun⟩
    complete := by
      intro input hdomain hintegrable
      obtain ⟨fuelS, middle, hrunS⟩ := S.complete input hdomain.1 hintegrable.1
      have hmiddle := S.sound fuelS input middle hdomain.1 hrunS
      obtain ⟨fuelT, output, hrunT⟩ :=
        next.complete middle (hdomain.2 middle hmiddle) (hintegrable.2 middle hmiddle)
      refine ⟨Nat.pair fuelS fuelT, output, ?_⟩
      change (S.run (Nat.unpair (Nat.pair fuelS fuelT)).1 input).bind
        (fun middle => next.run (Nat.unpair (Nat.pair fuelS fuelT)).2 middle) = some output
      rw [Nat.unpair_pair, hrunS]
      exact hrunT }

end IntegrationStage

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

/-- Restrict a certified stage to an additional semantic input guard. -/
noncomputable def restrictInput
    (S : RemainderIntegrationStage Input Output Remainder Integrable Correct)
    (guard : Input → Prop) :
    RemainderIntegrationStage Input Output Remainder
      (fun input => guard input ∧ Integrable input) Correct :=
  { stage :=
      { run := S.stage.run
        domain := fun input => guard input ∧ S.stage.domain input
        sound := by
          intro fuel input result hdomain hrun
          exact S.sound fuel input result hdomain.2 hrun
        complete := by
          intro input hdomain hintegrable
          exact S.complete input hdomain.2 hintegrable.2 } }

/-- Reindex a certified stage along a deterministic input adapter. -/
noncomputable def precompose
    {Source : Type u} {Input : Type v} {Output : Type w} {Remainder : Type _}
    {Integrable : Input → Prop} {Correct : Input → Output → Remainder → Prop}
    (S : RemainderIntegrationStage Input Output Remainder Integrable Correct)
    (adapt : Source → Input) :
    RemainderIntegrationStage Source Output Remainder
      (fun source => Integrable (adapt source))
      (fun source output remainder => Correct (adapt source) output remainder) :=
  { stage :=
      { run := fun fuel source => S.stage.run fuel (adapt source)
        domain := fun source => S.stage.domain (adapt source)
        sound := by
          intro fuel source result hdomain hrun
          exact S.sound fuel (adapt source) result hdomain hrun
        complete := by
          intro source hdomain hintegrable
          exact S.complete (adapt source) hdomain hintegrable } }

/-- Repackage a stage's extracted contribution while preserving its certified remainder. -/
noncomputable def mapOutput
    {Input : Type u} {Output : Type v} {MappedOutput : Type w} {Remainder : Type _}
    {Integrable : Input → Prop} {Correct : Input → Output → Remainder → Prop}
    {MappedCorrect : Input → MappedOutput → Remainder → Prop}
    (S : RemainderIntegrationStage Input Output Remainder Integrable Correct)
    (map : Output → MappedOutput)
    (mapCorrect : ∀ input output remainder, Correct input output remainder →
      MappedCorrect input (map output) remainder) :
    RemainderIntegrationStage Input MappedOutput Remainder Integrable MappedCorrect :=
  { stage :=
      { run := fun fuel input =>
          (S.stage.run fuel input).map fun result => ⟨map result.output, result.remainder⟩
        domain := S.stage.domain
        sound := by
          intro fuel input result hdomain hrun
          obtain ⟨output, houtput, rfl⟩ := Option.map_eq_some_iff.mp hrun
          exact mapCorrect input output.output output.remainder
            (S.sound fuel input output hdomain houtput)
        complete := by
          intro input hdomain hintegrable
          obtain ⟨fuel, output, hrun⟩ := S.complete input hdomain hintegrable
          exact ⟨fuel, ⟨map output.output, output.remainder⟩, by simp [hrun]⟩ } }

/-- Run two independent certified stages on the same input, pairing contributions and remainders.

This is the compositional form needed for branches such as polynomial-special reduction and normal
reduction: neither branch is encoded as an unchecked callback of the other. -/
noncomputable def product
    {Input : Type u} {Output : Type v} {NextOutput : Type w}
    {Remainder : Type _} {NextRemainder : Type _}
    {Integrable : Input → Prop} {NextIntegrable : Input → Prop}
    {Correct : Input → Output → Remainder → Prop}
    {NextCorrect : Input → NextOutput → NextRemainder → Prop}
    (S : RemainderIntegrationStage Input Output Remainder Integrable Correct)
    (T : RemainderIntegrationStage Input NextOutput NextRemainder NextIntegrable NextCorrect) :
    RemainderIntegrationStage Input (Output × NextOutput) (Remainder × NextRemainder)
      (fun input => Integrable input ∧ NextIntegrable input)
      (fun input output remainder =>
        Correct input output.1 remainder.1 ∧ NextCorrect input output.2 remainder.2) :=
  { stage :=
      { run := fun fuel input =>
          let fuels := Nat.unpair fuel
          match S.stage.run fuels.1 input with
          | none => none
          | some left =>
            match T.stage.run fuels.2 input with
            | none => none
            | some right => some ⟨(left.output, right.output), (left.remainder, right.remainder)⟩
        domain := fun input => S.stage.domain input ∧ T.stage.domain input
        sound := by
          intro fuel input result hdomain hrun
          cases hleft : S.stage.run (Nat.unpair fuel).1 input with
          | none => simp [hleft] at hrun
          | some left =>
            cases hright : T.stage.run (Nat.unpair fuel).2 input with
            | none => simp [hleft, hright] at hrun
            | some right =>
              simp only [hleft, hright, Option.some.injEq] at hrun
              subst result
              exact ⟨S.sound _ _ _ hdomain.1 hleft, T.sound _ _ _ hdomain.2 hright⟩
        complete := by
          intro input hdomain hintegrable
          obtain ⟨fuelLeft, left, hleft⟩ := S.complete input hdomain.1 hintegrable.1
          obtain ⟨fuelRight, right, hright⟩ := T.complete input hdomain.2 hintegrable.2
          refine ⟨Nat.pair fuelLeft fuelRight,
            ⟨(left.output, right.output), (left.remainder, right.remainder)⟩, ?_⟩
          simp [Nat.unpair_pair, hleft, hright] } }

/-- Sequentially compose two certified remainder stages with an explicit handoff invariant. -/
noncomputable def compose
    (S : RemainderIntegrationStage Input Output Remainder Integrable Correct)
    (T : RemainderIntegrationStage Remainder NextOutput NextRemainder NextIntegrable NextCorrect)
    (Domain : Input → Prop) (ComposedIntegrable : Input → Prop)
    (firstDomain : ∀ input, Domain input → S.stage.domain input)
    (nextDomain : ∀ input output remainder, Domain input → Correct input output remainder →
      T.stage.domain remainder)
    (splitIntegrable : ∀ input, ComposedIntegrable input → Integrable input ∧
      ∀ output remainder, Correct input output remainder → NextIntegrable remainder)
    (composeCorrect : ∀ input output remainder nextOutput nextRemainder,
      Correct input output remainder → NextCorrect remainder nextOutput nextRemainder →
      ComposedCorrect input (output, nextOutput) nextRemainder) :
    RemainderIntegrationStage Input (Output × NextOutput) NextRemainder ComposedIntegrable
      ComposedCorrect :=
  { stage :=
      { run := fun fuel input =>
          let fuels := Nat.unpair fuel
          match S.stage.run fuels.1 input with
          | none => none
          | some first =>
            match T.stage.run fuels.2 first.remainder with
            | none => none
            | some next => some ⟨(first.output, next.output), next.remainder⟩
        domain := Domain
        sound := by
          intro fuel input result hdomain hrun
          simp only at hrun
          cases hfirst : S.stage.run (Nat.unpair fuel).1 input with
          | none => simp [hfirst] at hrun
          | some first =>
            cases hnext : T.stage.run (Nat.unpair fuel).2 first.remainder with
            | none => simp [hfirst, hnext] at hrun
            | some next =>
              simp only [hfirst, hnext, Option.some.injEq] at hrun
              subst result
              exact composeCorrect input first.output first.remainder next.output next.remainder
                (S.sound _ _ _ (firstDomain input hdomain) hfirst)
                (T.sound _ _ _ (nextDomain input first.output first.remainder hdomain
                  (S.sound _ _ _ (firstDomain input hdomain) hfirst)) hnext)
        complete := by
          intro input hdomain hintegrable
          obtain ⟨hfirstInt, hnextInt⟩ := splitIntegrable input hintegrable
          obtain ⟨fuel₁, first, hfirst⟩ := S.complete input (firstDomain input hdomain) hfirstInt
          have hfirstCorrect := S.sound fuel₁ input first (firstDomain input hdomain) hfirst
          obtain ⟨fuel₂, next, hnext⟩ := T.complete first.remainder
            (nextDomain input first.output first.remainder hdomain hfirstCorrect)
            (hnextInt first.output first.remainder hfirstCorrect)
          refine ⟨Nat.pair fuel₁ fuel₂, ⟨(first.output, next.output), next.remainder⟩, ?_⟩
          simp [Nat.unpair_pair, hfirst, hnext] } }

end RemainderIntegrationStage

/-- A finite tower of remainder-carrying integration stages. -/
structure RemainderIntegrationTowerScheme (Input : ℕ → Type u) where
  /-- Extracted output representation at each tower depth. -/
  Output : ℕ → Type v
  /-- Semantic remainder representation at each tower depth. -/
  Remainder : ℕ → Type w
  /-- Integrability predicate selected at each depth. -/
  Integrable : ∀ n, Input n → Prop
  /-- Output-remainder invariant selected at each depth. -/
  Correct : ∀ n, Input n → Output n → Remainder n → Prop
  /-- Certified base stage. -/
  base : RemainderIntegrationStage (Input 0) (Output 0) (Remainder 0)
    (Integrable 0) (Correct 0)
  /-- Certified successor constructor receiving the immediately preceding stage. -/
  step : ∀ n,
    RemainderIntegrationStage (Input n) (Output n) (Remainder n)
      (Integrable n) (Correct n) →
    RemainderIntegrationStage (Input (n + 1)) (Output (n + 1)) (Remainder (n + 1))
      (Integrable (n + 1)) (Correct (n + 1))

namespace RemainderIntegrationTowerScheme

/-- The remainder-carrying stage selected recursively at a finite tower depth. -/
def stage (T : RemainderIntegrationTowerScheme Input) : (n : ℕ) →
    RemainderIntegrationStage (Input n) (T.Output n) (T.Remainder n)
      (T.Integrable n) (T.Correct n)
  | 0 => T.base
  | n + 1 => T.step n (T.stage n)

/-- Every accepted result of a selected finite tower stage satisfies its output-remainder invariant. -/
theorem stage_sound (T : RemainderIntegrationTowerScheme Input) (n fuel : ℕ)
    (input : Input n) (result : RemainderResult (T.Output n) (T.Remainder n))
    (hdomain : (T.stage n).stage.domain input)
    (hrun : (T.stage n).stage.run fuel input = some result) :
    T.Correct n input result.output result.remainder :=
  (T.stage n).sound fuel input result hdomain hrun

/-- Every integrable in-domain input eventually produces a certified result at its selected depth. -/
theorem stage_complete (T : RemainderIntegrationTowerScheme Input) (n : ℕ)
    (input : Input n) (hdomain : (T.stage n).stage.domain input)
    (hintegrable : T.Integrable n input) :
    ∃ fuel result, (T.stage n).stage.run fuel input = some result :=
  (T.stage n).complete input hdomain hintegrable

end RemainderIntegrationTowerScheme

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
