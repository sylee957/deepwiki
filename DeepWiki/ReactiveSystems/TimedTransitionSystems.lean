import DeepWiki.ReactiveSystems.Bisimulation
import Mathlib.Data.NNReal.Basic

/-! # Timed labelled transition systems (Part II)
The operational model of real-time systems: an LTS whose labels are ordinary
actions *or* time delays `d : ℝ≥0` (`Lab = Act ∪ ℝ≥0`). Modelling
a timed LTS as an `LTS` over the combined label type `Act ⊕ ℝ≥0` lets the whole
untimed theory (bisimulation, its equivalence/largest/gfp characterisations,
HML) apply directly; timed bisimilarity is just bisimilarity over these labels,
which matches both action and delay transitions. The book's structural axioms on
delay transitions — time determinism, zero delay, time additivity — are recorded
as predicates. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The labels of a timed LTS (`Lab = Act ∪ ℝ≥0`): an ordinary action or a time
delay. -/
abbrev TimedLabel (Act : Type*) := Act ⊕ ℝ≥0

/-- A timed labelled transition system: an LTS whose labels are
actions or time delays. -/
abbrev TLTS (Proc Act : Type*) := LTS Proc (TimedLabel Act)

namespace TLTS

variable {Proc Act : Type*}

/-- An action transition `p —a→ q`. -/
def act (T : TLTS Proc Act) (p : Proc) (a : Act) (q : Proc) : Prop := T.step p (.inl a) q

/-- A time-delay transition `p ⤳d q` (`d : ℝ≥0`). -/
def delay (T : TLTS Proc Act) (p : Proc) (d : ℝ≥0) (q : Proc) : Prop := T.step p (.inr d) q

/-- Time determinism: a delay transition leads to a unique state. -/
def TimeDeterministic (T : TLTS Proc Act) : Prop :=
  ∀ ⦃p d q q'⦄, T.delay p d q → T.delay p d q' → q = q'

/-- Zero delay: every state reaches itself with a zero delay. -/
def ZeroDelay (T : TLTS Proc Act) : Prop := ∀ p, T.delay p 0 p

/-- Time additivity / continuity: a delay of `d₁ + d₂` is exactly a delay
`d₁` followed by a delay `d₂`. -/
def TimeAdditive (T : TLTS Proc Act) : Prop :=
  ∀ ⦃p p' : Proc⦄ ⦃d₁ d₂ : ℝ≥0⦄,
    T.delay p (d₁ + d₂) p' ↔ ∃ p'', T.delay p d₁ p'' ∧ T.delay p'' d₂ p'

/-- The **maximal-progress assumption**: an action entirely under a
process's own control (the silent action `τ`) is *urgent* — a state able to
perform `τ` cannot let any positive amount of time elapse. -/
def MaximalProgress (T : TLTS Proc Act) (tau : Act) : Prop :=
  ∀ ⦃p⦄, (∃ r, T.act p tau r) → ∀ ⦃d⦄, 0 < d → ¬ ∃ q, T.delay p d q

/-- Timed (strong) bisimilarity: bisimilarity over the combined
action/delay labels. -/
abbrev TimedBisimilar (T : TLTS Proc Act) : Proc → Proc → Prop := LTS.Bisimilar T

/-- Timed bisimilarity is an equivalence relation. -/
theorem timedBisimilar_equivalence (T : TLTS Proc Act) :
    Equivalence (TimedBisimilar T) := LTS.equivalence_bisimilar

/-- Timed bisimilarity matches both action transitions and time-delay
transitions on each side — the timed bisimulation transfer property. -/
theorem timedBisimilar_iff (T : TLTS Proc Act) (p q : Proc) :
    TimedBisimilar T p q ↔
      (∀ a p', T.act p a p' → ∃ q', T.act q a q' ∧ TimedBisimilar T p' q') ∧
      (∀ a q', T.act q a q' → ∃ p', T.act p a p' ∧ TimedBisimilar T p' q') ∧
      (∀ d p', T.delay p d p' → ∃ q', T.delay q d q' ∧ TimedBisimilar T p' q') ∧
      (∀ d q', T.delay q d q' → ∃ p', T.delay p d p' ∧ TimedBisimilar T p' q') := by
  rw [TimedBisimilar, LTS.bisimilar_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a p' h => h1 (.inl a) p' h, fun a q' h => h2 (.inl a) q' h,
           fun d p' h => h1 (.inr d) p' h, fun d q' h => h2 (.inr d) q' h⟩
  · rintro ⟨ha1, ha2, hd1, hd2⟩
    refine ⟨fun l p' h => ?_, fun l q' h => ?_⟩
    · cases l with
      | inl a => exact ha1 a p' h
      | inr d => exact hd1 d p' h
    · cases l with
      | inl a => exact ha2 a q' h
      | inr d => exact hd2 d q' h

end TLTS

end DeepWiki.ReactiveSystems
