import DeepWiki.ReactiveSystems.TimedTransitionSystems
import DeepWiki.ReactiveSystems.Simulation

/-! # Timed simulation
The one-sided companion of timed bisimilarity: a *timed simulation* matches each
action *and* each time-delay transition of the simulated state (the forward half of
a timed bisimulation), and `s₁` is *timed simulated by* `s₂` when some timed
simulation relates them — exactly simulation over the combined action/delay labels
`Act ⊕ ℝ≥0`. Like the simulation preorder it is reflexive and transitive, and timed
bisimilarity refines it. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Proc Act : Type*}

/-- **Timed simulation preorder** `s₁ ⊑ s₂`: similarity over the combined
action/delay labels — the forward half of timed bisimilarity. -/
abbrev TimedSimulated (T : TLTS Proc Act) : Proc → Proc → Prop := LTS.Simulated T

/-- Timed simulation matches each action transition and each time-delay transition
of the simulated state — the timed-simulation transfer property. -/
theorem timedSimulated_iff (T : TLTS Proc Act) (p q : Proc) :
    TimedSimulated T p q ↔
      ∃ R : Proc → Proc → Prop, (∀ ⦃s₁ s₂⦄, R s₁ s₂ →
        (∀ a s₁', T.act s₁ a s₁' → ∃ s₂', T.act s₂ a s₂' ∧ R s₁' s₂') ∧
        (∀ d s₁', T.delay s₁ d s₁' → ∃ s₂', T.delay s₂ d s₂' ∧ R s₁' s₂')) ∧ R p q := by
  constructor
  · rintro ⟨R, hR, hpq⟩
    exact ⟨R, fun _ _ h => ⟨fun a s₁' hs => hR h (.inl a) s₁' hs,
      fun d s₁' hs => hR h (.inr d) s₁' hs⟩, hpq⟩
  · rintro ⟨R, hR, hpq⟩
    refine ⟨R, fun s₁ s₂ h l s₁' hs => ?_, hpq⟩
    match l with
    | .inl a => exact (hR h).1 a s₁' hs
    | .inr d => exact (hR h).2 d s₁' hs

/-- Timed simulation is reflexive: `p ⊑ p`. -/
@[refl] theorem timedSimulated_refl (T : TLTS Proc Act) (p : Proc) : TimedSimulated T p p :=
  LTS.simulated_refl T p

/-- Timed simulation is transitive: `p ⊑ q → q ⊑ r → p ⊑ r`. -/
theorem TimedSimulated.trans {T : TLTS Proc Act} {p q r : Proc}
    (h₁ : TimedSimulated T p q) (h₂ : TimedSimulated T q r) : TimedSimulated T p r :=
  LTS.Simulated.trans h₁ h₂

/-- **Timed bisimilarity refines the timed-simulation preorder**: `p ~ q → p ⊑ q`. -/
theorem TimedBisimilar.timedSimulated {T : TLTS Proc Act} {p q : Proc}
    (h : TimedBisimilar T p q) : TimedSimulated T p q :=
  LTS.Bisimilar.simulated h

end TLTS

end DeepWiki.ReactiveSystems
