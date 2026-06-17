import DeepWiki.ReactiveSystems.Bisimulation
import DeepWiki.ReactiveSystems.BisimulationWeak
import DeepWiki.ReactiveSystems.Ccs
import DeepWiki.ReactiveSystems.CcsStructuralLaws
import Mathlib.Data.Set.Insert

/-! # Restriction laws of CCS
Restriction does *not* distribute over parallel composition — `(P ∣ Q) ∖ a` can
synchronise internally where `(P ∖ a) ∣ (Q ∖ a)` cannot. And
restricting away every visible action makes a process observationally equivalent
to `0`, but *not* strongly bisimilar to it (a surviving `τ`-loop). -/

namespace DeepWiki.ReactiveSystems

open LTS

/-! ## Restriction does not distribute over `∣` -/

/-- A two-channel alphabet for the counterexample. -/
inductive RChan | a | b
  deriving DecidableEq

/-- The restricted set `{a, ā}`. -/
def rcRestrict : Set (Act RChan) := {Act.name RChan.a, Act.coname RChan.a}

/-- Restriction does **not** distribute over
parallel composition: there are `P, Q` with `(P ∣ Q) ∖ {a} ≁ (P ∖ {a}) ∣ (Q ∖ {a})`.
Witness `P = a.0`, `Q = ā.0`: the left can synchronise (`τ`) while the right is
deadlocked (both `a` and `ā` are restricted away from the components). -/
theorem not_restrict_distrib_par :
    ¬ ∀ (P Q : CCS RChan Empty),
      (CCS.restrict (CCS.par P Q) rcRestrict) ~[ccsLTS noDefs]
        (CCS.par (CCS.restrict P rcRestrict) (CCS.restrict Q rcRestrict)) := by
  intro h
  have hb := h (CCS.pre (.name .a) .nil) (CCS.pre (.coname .a) .nil)
  rw [bisimilar_iff] at hb
  obtain ⟨q', hq', -⟩ := hb.1 Act.tau
    (CCS.restrict (CCS.par CCS.nil CCS.nil) rcRestrict)
    (by rw [ccsLTS_step]
        exact Step.res (by simp [rcRestrict]) (by simp [rcRestrict])
          (Step.com3 (by rintro ⟨⟩) (Step.act _ _) (Step.act _ _)))
  rw [ccsLTS_step, step_par_iff] at hq'
  simp [step_restrict_iff, step_pre_iff, rcRestrict] at hq'

/-! ## Restricting away every visible action -/

/-- The set of all *observable* actions (every action except `τ`). -/
def observable (Name : Type*) : Set (Act Name) := {α | α ≠ Act.tau}

/-- For every process `P`, restricting away all
observable actions yields a process observationally equivalent to `0`:
`P ∖ (Act ∖ {τ}) ≈ 0`. (Only `τ`-moves survive the restriction, and they relate
the residual back to `0`.) -/
theorem restrict_observable_weaklyBisimilar_nil {Name K : Type*} (defn : K → CCS Name K)
    (P : CCS Name K) :
    (CCS.restrict P (observable Name)) ≈[ccsLTS defn, Act.tau] CCS.nil := by
  refine IsWeakBisimulation.le_weaklyBisimilar
    (R := fun x y => (∃ A, x = CCS.restrict A (observable Name)) ∧ y = CCS.nil)
    ?_ ⟨⟨P, rfl⟩, rfl⟩
  rintro x y ⟨⟨A, rfl⟩, rfl⟩
  refine ⟨fun α x' hx => ?_, fun α y' hy => ?_⟩
  · rw [ccsLTS_step, step_restrict_iff] at hx
    obtain ⟨A', hαL, _, _, rfl⟩ := hx
    have hτ : α = Act.tau := by simpa [observable, not_not] using hαL
    subst hτ
    exact ⟨CCS.nil, weakStep_tau_of_tauStar (tauStar_refl _ _ _), ⟨A', rfl⟩, rfl⟩
  · rw [ccsLTS_step] at hy; exact absurd hy not_step_nil

/-- The same does *not* hold up to strong
bisimilarity: `(τ.0) ∖ (Act ∖ {τ}) ≁ 0`, since the restricted process still
performs a `τ`-step that `0` cannot match. -/
theorem not_restrict_observable_bisimilar_nil {Name : Type*} :
    ¬ (CCS.restrict (CCS.pre Act.tau CCS.nil) (observable Name)) ~[ccsLTS noDefs] CCS.nil := by
  intro h
  rw [bisimilar_iff] at h
  obtain ⟨q', hq', -⟩ := h.1 Act.tau (CCS.restrict CCS.nil (observable Name))
    (by rw [ccsLTS_step]; exact Step.res (by simp [observable]) (by simp [observable]) (Step.act _ _))
  rw [ccsLTS_step] at hq'; exact absurd hq' not_step_nil

end DeepWiki.ReactiveSystems
