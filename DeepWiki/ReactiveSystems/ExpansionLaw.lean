import DeepWiki.ReactiveSystems.HennessyMilner
import DeepWiki.ReactiveSystems.Bisimulation
import DeepWiki.ReactiveSystems.Ccs
import DeepWiki.ReactiveSystems.HennessyMilnerExamples

/-! # The expansion law `a.0 ∣ b.0 ~ a.b.0 + b.a.0` and distinguishing formulae
Over the alphabet `Fin 4` (`a = 0, b = 1, c = 2, d = 3`), no constants:
- `b.a.0 + b.0 ≁ b.(a.0 + b.0)`, separated by `⟨b⟩⟨b⟩tt`;
- `a.(b.c.0 + b.d.0) ≁ a.b.c.0 + a.b.d.0`;
- `a.0 ∣ b.0 ~ a.b.0 + b.a.0` (the expansion law), via an explicit four-pair
  bisimulation;
- `(a.0 ∣ b.0) + c.a.0 ≁ a.0 ∣ (b.0 + c.0)`, separated by `⟨a⟩⟨c⟩tt`. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- The constant-free CCS environment over `Fin 4`. -/
abbrev d511 : Empty → CCS (Fin 4) Empty := Empty.elim

/-! ## Pair 1 — `b.a.0 + b.0 ≁ b.(a.0 + b.0)`, separated by `⟨b⟩⟨b⟩tt` -/

/-- `b.a.0 + b.0`. -/
abbrev q1a : CCS (Fin 4) Empty :=
  .choice (.pre (.name 1) (.pre (.name 0) .nil)) (.pre (.name 1) .nil)
/-- `b.(a.0 + b.0)`. -/
abbrev q1b : CCS (Fin 4) Empty :=
  .pre (.name 1) (.choice (.pre (.name 0) .nil) (.pre (.name 1) .nil))
/-- `⟨b⟩⟨b⟩tt`. -/
abbrev f511_1 : HML (Act (Fin 4)) := .dia (.name 1) (.dia (.name 1) .tt)

/-- `b.(a.0 + b.0) ⊨ ⟨b⟩⟨b⟩tt`: after `b`, the state `a.0 + b.0` can do another `b`. -/
theorem q1b_sat : q1b ⊨[ccsLTS d511] f511_1 :=
  ⟨_, by rw [ccsLTS_step]; exact Step.act _ _,
    ⟨_, by rw [ccsLTS_step]; exact Step.sumr (Step.act _ _), trivial⟩⟩

/-- `b.a.0 + b.0 ⊭ ⟨b⟩⟨b⟩tt`: both `b`-successors (`a.0` and `0`) refuse `b`. -/
theorem q1a_unsat : ¬ (q1a ⊨[ccsLTS d511] f511_1) := by
  rintro ⟨p', hp', hdia⟩
  rw [ccsLTS_step, step_choice_iff] at hp'
  rcases hp' with h | h
  · rw [step_pre_iff] at h; obtain ⟨_, rfl⟩ := h
    obtain ⟨q, hq, _⟩ := hdia
    rw [ccsLTS_step, step_pre_iff] at hq
    exact absurd hq.1 (by decide)
  · rw [step_pre_iff] at h; obtain ⟨_, rfl⟩ := h
    obtain ⟨q, hq, _⟩ := hdia
    rw [ccsLTS_step] at hq
    exact absurd hq not_step_nil

/-! ## Pair 4 — `(a.0 ∣ b.0) + c.a.0 ≁ a.0 ∣ (b.0 + c.0)`, separated by `⟨a⟩⟨c⟩tt` -/

/-- `(a.0 ∣ b.0) + c.a.0`. -/
abbrev q4a : CCS (Fin 4) Empty :=
  .choice (.par (.pre (.name 0) .nil) (.pre (.name 1) .nil)) (.pre (.name 2) (.pre (.name 0) .nil))
/-- `a.0 ∣ (b.0 + c.0)`. -/
abbrev q4b : CCS (Fin 4) Empty :=
  .par (.pre (.name 0) .nil) (.choice (.pre (.name 1) .nil) (.pre (.name 2) .nil))
/-- `⟨a⟩⟨c⟩tt`. -/
abbrev f511_4 : HML (Act (Fin 4)) := .dia (.name 0) (.dia (.name 2) .tt)

/-- `a.0 ∣ (b.0 + c.0) ⊨ ⟨a⟩⟨c⟩tt`: after `a` the right component still offers `c`. -/
theorem q4b_sat : q4b ⊨[ccsLTS d511] f511_4 :=
  ⟨_, by rw [ccsLTS_step]; exact Step.com1 (Step.act _ _),
    ⟨_, by rw [ccsLTS_step]; exact Step.com2 (Step.sumr (Step.act _ _)), trivial⟩⟩

/-- `(a.0 ∣ b.0) + c.a.0 ⊭ ⟨a⟩⟨c⟩tt`: its sole `a`-successor `0 ∣ b.0` cannot do `c`. -/
theorem q4a_unsat : ¬ (q4a ⊨[ccsLTS d511] f511_4) := by
  rintro ⟨p', hp', hdia⟩
  rw [ccsLTS_step, step_choice_iff] at hp'
  rcases hp' with h | h
  · rw [step_par_iff] at h
    rcases h with ⟨A', hA, rfl⟩ | ⟨B', hB, rfl⟩ | ⟨ℓ, A', B', htau, _, _, _, _⟩
    · rw [step_pre_iff] at hA; obtain ⟨_, rfl⟩ := hA
      obtain ⟨q, hq, _⟩ := hdia
      rw [ccsLTS_step, step_par_iff] at hq
      rcases hq with ⟨_, hN, _⟩ | ⟨_, hB, _⟩ | ⟨_, _, _, _, _, hN, _, _⟩
      · exact absurd hN not_step_nil
      · rw [step_pre_iff] at hB; exact absurd hB.1 (by decide)
      · exact absurd hN not_step_nil
    · rw [step_pre_iff] at hB; exact absurd hB.1 (by decide)
    · exact absurd htau (by decide)
  · rw [step_pre_iff] at h; exact absurd h.1 (by decide)

/-! ## Pair 3 — the expansion law `a.0 ∣ b.0 ~ a.b.0 + b.a.0` -/

/-- `a.0 ∣ b.0`. -/
abbrev q3a : CCS (Fin 4) Empty := .par (.pre (.name 0) .nil) (.pre (.name 1) .nil)
/-- `a.b.0 + b.a.0`. -/
abbrev q3b : CCS (Fin 4) Empty :=
  .choice (.pre (.name 0) (.pre (.name 1) .nil)) (.pre (.name 1) (.pre (.name 0) .nil))

/-- The four-pair bisimulation behind the expansion law: pairs the parallel
process and its derivatives `0∣b.0`, `a.0∣0`, `0∣0` with the corresponding
states `b.0`, `a.0`, `0` of the interleaving sum. -/
def expRel : CCS (Fin 4) Empty → CCS (Fin 4) Empty → Prop :=
  fun x y =>
    (x = q3a ∧ y = q3b) ∨
    (x = .par .nil (.pre (.name 1) .nil) ∧ y = .pre (.name 1) .nil) ∨
    (x = .par (.pre (.name 0) .nil) .nil ∧ y = .pre (.name 0) .nil) ∨
    (x = .par .nil .nil ∧ y = .nil)

/-- `expRel` is a bisimulation (the basis of the expansion law `a.0∣b.0 ~ a.b.0+b.a.0`). -/
theorem isBisimulation_expRel : IsBisimulation (ccsLTS d511) expRel := by
  rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · -- (a.0 ∣ b.0, a.b.0 + b.a.0)
    refine ⟨fun α x' hx => ?_, fun α y' hy => ?_⟩
    · rw [ccsLTS_step, step_par_iff] at hx
      rcases hx with ⟨A', hA, rfl⟩ | ⟨B', hB, rfl⟩ | ⟨ℓ, A', B', _, _, hA, hB, rfl⟩
      · rw [step_pre_iff] at hA; obtain ⟨rfl, rfl⟩ := hA
        exact ⟨_, by rw [ccsLTS_step, step_choice_iff]; exact Or.inl (Step.act _ _),
          Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · rw [step_pre_iff] at hB; obtain ⟨rfl, rfl⟩ := hB
        exact ⟨_, by rw [ccsLTS_step, step_choice_iff]; exact Or.inr (Step.act _ _),
          Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · rw [step_pre_iff] at hA; obtain ⟨rfl, rfl⟩ := hA
        rw [step_pre_iff] at hB; exact absurd hB.1 (by decide)
    · rw [ccsLTS_step, step_choice_iff] at hy
      rcases hy with h | h
      · rw [step_pre_iff] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, by rw [ccsLTS_step, step_par_iff]; exact Or.inl ⟨_, Step.act _ _, rfl⟩,
          Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · rw [step_pre_iff] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, by rw [ccsLTS_step, step_par_iff]; exact Or.inr (Or.inl ⟨_, Step.act _ _, rfl⟩),
          Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · -- (0 ∣ b.0, b.0)
    refine ⟨fun α x' hx => ?_, fun α y' hy => ?_⟩
    · rw [ccsLTS_step, step_par_iff] at hx
      rcases hx with ⟨A', hA, rfl⟩ | ⟨B', hB, rfl⟩ | ⟨ℓ, A', B', _, _, hA, _, rfl⟩
      · exact absurd hA not_step_nil
      · rw [step_pre_iff] at hB; obtain ⟨rfl, rfl⟩ := hB
        exact ⟨_, by rw [ccsLTS_step]; exact Step.act _ _, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      · exact absurd hA not_step_nil
    · rw [ccsLTS_step, step_pre_iff] at hy; obtain ⟨rfl, rfl⟩ := hy
      exact ⟨_, by rw [ccsLTS_step, step_par_iff]; exact Or.inr (Or.inl ⟨_, Step.act _ _, rfl⟩),
        Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  · -- (a.0 ∣ 0, a.0)
    refine ⟨fun α x' hx => ?_, fun α y' hy => ?_⟩
    · rw [ccsLTS_step, step_par_iff] at hx
      rcases hx with ⟨A', hA, rfl⟩ | ⟨B', hB, rfl⟩ | ⟨ℓ, A', B', _, _, _, hB, rfl⟩
      · rw [step_pre_iff] at hA; obtain ⟨rfl, rfl⟩ := hA
        exact ⟨_, by rw [ccsLTS_step]; exact Step.act _ _, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      · exact absurd hB not_step_nil
      · exact absurd hB not_step_nil
    · rw [ccsLTS_step, step_pre_iff] at hy; obtain ⟨rfl, rfl⟩ := hy
      exact ⟨_, by rw [ccsLTS_step, step_par_iff]; exact Or.inl ⟨_, Step.act _ _, rfl⟩,
        Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  · -- (0 ∣ 0, 0): both deadlocked
    refine ⟨fun α x' hx => ?_, fun α y' hy => ?_⟩
    · rw [ccsLTS_step, step_par_iff] at hx
      rcases hx with ⟨_, hA, _⟩ | ⟨_, hB, _⟩ | ⟨_, _, _, _, _, hA, _, _⟩
      · exact absurd hA not_step_nil
      · exact absurd hB not_step_nil
      · exact absurd hA not_step_nil
    · rw [ccsLTS_step] at hy; exact absurd hy not_step_nil

/-- Expansion law `a.0 ∣ b.0 ~ a.b.0 + b.a.0`:
parallel composition of two prefixes is bisimilar to their interleaving sum. -/
theorem exp_law : q3a ~[ccsLTS d511] q3b :=
  isBisimulation_expRel.le_bisimilar (Or.inl ⟨rfl, rfl⟩)

/-- For the four CCS pairs: pairs 1, 2 and 4 are
not strongly bisimilar (each separated by an HML formula), while pair 3 is
bisimilar (the expansion law). -/
theorem ccs_pairs_expansionLaw_and_distinguishing :
    (∃ F : HML (Act (Fin 4)), (q1b ⊨[ccsLTS d511] F) ∧ ¬ (q1a ⊨[ccsLTS d511] F)) ∧
    (∃ G : HML (Act (Fin 4)), (p55c ⊨[ccsLTS d55] G) ∧ ¬ (p55d ⊨[ccsLTS d55] G)) ∧
    (q3a ~[ccsLTS d511] q3b) ∧
    (∃ H : HML (Act (Fin 4)), (q4b ⊨[ccsLTS d511] H) ∧ ¬ (q4a ⊨[ccsLTS d511] H)) :=
  ⟨⟨f511_1, q1b_sat, q1a_unsat⟩, hmlDistinguishes_nonBisimilarProcessPairs.2, exp_law, ⟨f511_4, q4b_sat, q4a_unsat⟩⟩

end DeepWiki.ReactiveSystems
