import DeepWiki.ReactiveSystems.Bisimulation
import DeepWiki.ReactiveSystems.Ccs

/-! # Structural laws of CCS up to strong bisimilarity
The monoid laws of parallel composition and the constant-unfolding law, each a
strong bisimulation: `K ~ defn K`; `P ∣ Q ~ Q ∣ P`,
`P ∣ 0 ~ P`, `(P ∣ Q) ∣ R ~ P ∣ (Q ∣ R)`; plus a witness that
`+` *does* distribute over `∣` in a degenerate case. -/

namespace DeepWiki.ReactiveSystems

open LTS

variable {Name K : Type*} {defn : K → CCS Name K}

/-! ## A constant is bisimilar to its body -/

/-- If `K ≝ P` then `K ~ P`: a process constant
and its defining body have identical successor sets (the `con` SOS rule). -/
theorem const_bisim_body (K0 : K) : (CCS.const K0) ~[ccsLTS defn] (defn K0) := by
  rw [bisimilar_iff]
  refine ⟨fun α p' h => ?_, fun α q' h => ?_⟩
  · rw [ccsLTS_step, step_const_iff] at h
    exact ⟨p', by rw [ccsLTS_step]; exact h, bisimilar_refl _⟩
  · rw [ccsLTS_step] at h
    exact ⟨q', by rw [ccsLTS_step, step_const_iff]; exact h, bisimilar_refl _⟩

/-! ## Parallel composition is a commutative monoid up to `~` -/

/-- The relation `{(A ∣ B, B ∣ A)}` underlying commutativity. -/
def parCommRel (_defn : K → CCS Name K) : CCS Name K → CCS Name K → Prop :=
  fun x y => ∃ A B, x = CCS.par A B ∧ y = CCS.par B A

theorem isBisimulation_parCommRel : IsBisimulation (ccsLTS defn) (parCommRel defn) := by
  rintro x y ⟨A, B, rfl, rfl⟩
  refine ⟨fun α x' hx => ?_, fun α y' hy => ?_⟩
  · rw [ccsLTS_step, step_par_iff] at hx
    rcases hx with ⟨A', hA, rfl⟩ | ⟨B', hB, rfl⟩ | ⟨ℓ, A', B', rfl, hℓ, hA, hB, rfl⟩
    · exact ⟨CCS.par B A', by rw [ccsLTS_step]; exact Step.com2 hA, _, _, rfl, rfl⟩
    · exact ⟨CCS.par B' A, by rw [ccsLTS_step]; exact Step.com1 hB, _, _, rfl, rfl⟩
    · exact ⟨CCS.par B' A', by rw [ccsLTS_step]; exact Step.com3 hℓ.co hB (by rw [Act.co_co]; exact hA),
        _, _, rfl, rfl⟩
  · rw [ccsLTS_step, step_par_iff] at hy
    rcases hy with ⟨B', hB, rfl⟩ | ⟨A', hA, rfl⟩ | ⟨ℓ, B', A', rfl, hℓ, hB, hA, rfl⟩
    · exact ⟨CCS.par A B', by rw [ccsLTS_step]; exact Step.com2 hB, _, _, rfl, rfl⟩
    · exact ⟨CCS.par A' B, by rw [ccsLTS_step]; exact Step.com1 hA, _, _, rfl, rfl⟩
    · exact ⟨CCS.par A' B', by rw [ccsLTS_step]; exact Step.com3 hℓ.co hA (by rw [Act.co_co]; exact hB),
        _, _, rfl, rfl⟩

/-- Parallel composition is commutative:
`P ∣ Q ~ Q ∣ P`. -/
theorem par_comm (A B : CCS Name K) : (CCS.par A B) ~[ccsLTS defn] (CCS.par B A) :=
  isBisimulation_parCommRel.le_bisimilar ⟨A, B, rfl, rfl⟩

/-- The relation `{(A ∣ 0, A)}` underlying the unit law. -/
def parUnitRel (_defn : K → CCS Name K) : CCS Name K → CCS Name K → Prop :=
  fun x y => ∃ A, x = CCS.par A CCS.nil ∧ y = A

theorem isBisimulation_parUnitRel : IsBisimulation (ccsLTS defn) (parUnitRel defn) := by
  rintro x y ⟨A, rfl, rfl⟩
  refine ⟨fun α x' hx => ?_, fun α y' hy => ?_⟩
  · rw [ccsLTS_step, step_par_iff] at hx
    rcases hx with ⟨A', hA, rfl⟩ | ⟨B', hB, rfl⟩ | ⟨ℓ, A', B', rfl, hℓ, hA, hB, rfl⟩
    · exact ⟨A', by rw [ccsLTS_step]; exact hA, _, rfl, rfl⟩
    · exact absurd hB not_step_nil
    · exact absurd hB not_step_nil
  · exact ⟨CCS.par y' CCS.nil, by rw [ccsLTS_step]; exact Step.com1 hy, _, rfl, rfl⟩

/-- `0` is a unit for parallel
composition: `P ∣ 0 ~ P`. -/
theorem par_unit (A : CCS Name K) : (CCS.par A CCS.nil) ~[ccsLTS defn] A :=
  isBisimulation_parUnitRel.le_bisimilar ⟨A, rfl, rfl⟩

/-- The relation `{((A ∣ B) ∣ C, A ∣ (B ∣ C))}` underlying associativity. -/
def parAssocRel (_defn : K → CCS Name K) : CCS Name K → CCS Name K → Prop :=
  fun x y => ∃ A B C, x = CCS.par (CCS.par A B) C ∧ y = CCS.par A (CCS.par B C)

theorem isBisimulation_parAssocRel : IsBisimulation (ccsLTS defn) (parAssocRel defn) := by
  rintro x y ⟨A, B, C, rfl, rfl⟩
  refine ⟨fun α x' hx => ?_, fun α y' hy => ?_⟩
  · rw [ccsLTS_step, step_par_iff] at hx
    rcases hx with ⟨AB', hAB, rfl⟩ | ⟨C', hC, rfl⟩ | ⟨ℓ, AB', C', rfl, hℓ, hAB, hC, rfl⟩
    · -- (A ∣ B) moves; re-split it
      rw [step_par_iff] at hAB
      rcases hAB with ⟨A', hA, rfl⟩ | ⟨B', hB, rfl⟩ | ⟨m, A', B', rfl, hm, hA, hB, rfl⟩
      · exact ⟨CCS.par A' (CCS.par B C), by rw [ccsLTS_step]; exact Step.com1 hA, _, _, _, rfl, rfl⟩
      · exact ⟨CCS.par A (CCS.par B' C), by rw [ccsLTS_step]; exact Step.com2 (Step.com1 hB),
          _, _, _, rfl, rfl⟩
      · exact ⟨CCS.par A' (CCS.par B' C), by rw [ccsLTS_step]; exact Step.com3 hm hA (Step.com1 hB),
          _, _, _, rfl, rfl⟩
    · exact ⟨CCS.par A (CCS.par B C'), by rw [ccsLTS_step]; exact Step.com2 (Step.com2 hC),
        _, _, _, rfl, rfl⟩
    · -- (A ∣ B) does ℓ, C does ℓ.co; re-split the (A ∣ B) move
      rw [step_par_iff] at hAB
      rcases hAB with ⟨A', hA, rfl⟩ | ⟨B', hB, rfl⟩ | ⟨_, _, _, hτ, _, _, _, _⟩
      · exact ⟨CCS.par A' (CCS.par B C'), by rw [ccsLTS_step]; exact Step.com3 hℓ hA (Step.com2 hC),
          _, _, _, rfl, rfl⟩
      · exact ⟨CCS.par A (CCS.par B' C'), by rw [ccsLTS_step]; exact Step.com2 (Step.com3 hℓ hB hC),
          _, _, _, rfl, rfl⟩
      · -- (A ∣ B) move is itself a τ-sync, so it cannot carry the label ℓ
        exact absurd hτ hℓ
  · rw [ccsLTS_step, step_par_iff] at hy
    rcases hy with ⟨A', hA, rfl⟩ | ⟨BC', hBC, rfl⟩ | ⟨ℓ, A', BC', rfl, hℓ, hA, hBC, rfl⟩
    · exact ⟨CCS.par (CCS.par A' B) C, by rw [ccsLTS_step]; exact Step.com1 (Step.com1 hA),
        _, _, _, rfl, rfl⟩
    · rw [step_par_iff] at hBC
      rcases hBC with ⟨B', hB, rfl⟩ | ⟨C', hC, rfl⟩ | ⟨m, B', C', rfl, hm, hB, hC, rfl⟩
      · exact ⟨CCS.par (CCS.par A B') C, by rw [ccsLTS_step]; exact Step.com1 (Step.com2 hB),
          _, _, _, rfl, rfl⟩
      · exact ⟨CCS.par (CCS.par A B) C', by rw [ccsLTS_step]; exact Step.com2 hC, _, _, _, rfl, rfl⟩
      · exact ⟨CCS.par (CCS.par A B') C', by rw [ccsLTS_step]; exact Step.com3 hm (Step.com2 hB) hC,
          _, _, _, rfl, rfl⟩
    · rw [step_par_iff] at hBC
      rcases hBC with ⟨B', hB, rfl⟩ | ⟨C', hC, rfl⟩ | ⟨_, _, _, hτ, _, _, _, rfl⟩
      · exact ⟨CCS.par (CCS.par A' B') C, by rw [ccsLTS_step]; exact Step.com1 (Step.com3 hℓ hA hB),
          _, _, _, rfl, rfl⟩
      · exact ⟨CCS.par (CCS.par A' B) C', by rw [ccsLTS_step]; exact Step.com3 hℓ (Step.com1 hA) hC,
          _, _, _, rfl, rfl⟩
      · exact absurd hτ hℓ.co

/-- Parallel composition is associative:
`(P ∣ Q) ∣ R ~ P ∣ (Q ∣ R)`. -/
theorem par_assoc (A B C : CCS Name K) :
    (CCS.par (CCS.par A B) C) ~[ccsLTS defn] (CCS.par A (CCS.par B C)) :=
  isBisimulation_parAssocRel.le_bisimilar ⟨A, B, C, rfl, rfl⟩

/-- The empty definition environment (no constants). -/
def noDefs : Empty → CCS Name Empty := fun e => e.elim

/-- `+` need not distribute over `∣` in general,
but it *does* in the degenerate all-`0` case: `(0 + 0) ∣ 0 ~ (0 ∣ 0) + (0 ∣ 0)`
(both are deadlocked). -/
theorem par_choice_distrib_nil :
    (CCS.par (CCS.choice CCS.nil CCS.nil) CCS.nil) ~[ccsLTS (noDefs (Name := Name))]
      (CCS.choice (CCS.par CCS.nil CCS.nil) (CCS.par CCS.nil CCS.nil)) := by
  rw [bisimilar_iff]
  refine ⟨fun α p' h => ?_, fun α q' h => ?_⟩
  · rw [ccsLTS_step] at h; simp [step_par_iff, step_choice_iff] at h
  · rw [ccsLTS_step] at h; simp [step_choice_iff, step_par_iff] at h

end DeepWiki.ReactiveSystems
