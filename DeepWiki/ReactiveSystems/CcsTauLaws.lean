import DeepWiki.ReactiveSystems.Ccs
import DeepWiki.ReactiveSystems.BisimulationWeak
import Mathlib.Tactic.Set

/-! # Milner's τ-laws
The three τ-laws of observational (weak) equivalence over CCS: a silent step
guarded by an action is unobservable, a process is weakly equivalent to itself
prefixed by an absorbed τ-summand, and the third τ-law on action-guarded choice.
Each is proved by exhibiting an explicit weak bisimulation. -/

namespace DeepWiki.ReactiveSystems

open LTS

variable {Name K : Type*} (defn : K → CCS Name K)

/-- τ-law: `α.τ.P ≈ α.P` — a leading silent step after `α` is unobservable. -/
theorem tau_law_1 {α : Act Name} (P : CCS Name K) :
    CCS.pre α (CCS.pre Act.tau P) ≈[ccsLTS defn, Act.tau] CCS.pre α P := by
  refine IsWeakBisimulation.le_weaklyBisimilar
    (R := fun x y =>
      (x = CCS.pre α (CCS.pre Act.tau P) ∧ y = CCS.pre α P) ∨
      (x = CCS.pre Act.tau P ∧ y = P) ∨ x = y) ?_ (Or.inl ⟨rfl, rfl⟩)
  intro p q hR
  rcases hR with ⟨hp, hq⟩ | ⟨hp, hq⟩ | hpq
  · -- pair 1: (α.τ.P, α.P)
    subst hp; subst hq
    constructor
    · -- LHS α.τ.P --α--> τ.P, matched by α.P --α--> P; target pair (τ.P, P) is pair 2
      intro b p' hstep
      simp only [ccsLTS_step, step_pre_iff] at hstep
      obtain ⟨hb, hp'⟩ := hstep; subst hb; subst hp'
      exact ⟨P, step_weakStep (by simp [ccsLTS_step]), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · -- RHS α.P --α--> P, matched by α.τ.P =[α]⇒ P (α-step then τ-step); target (P, P) diagonal
      intro b q' hstep
      simp only [ccsLTS_step, step_pre_iff] at hstep
      obtain ⟨hb, hq'⟩ := hstep; subst q'; subst α
      refine ⟨P, ?_, Or.inr (Or.inr rfl)⟩
      by_cases hbt : b = Act.tau
      · -- both head action and silent tail are τ: `τ.τ.P --τ--> τ.P --τ--> P`
        subst hbt
        exact weakStep_tau_of_tauStar (tauStar_trans
          (tauStar_single (q := CCS.pre Act.tau P) (by simp [ccsLTS_step]))
          (tauStar_single (q := P) (by simp [ccsLTS_step])))
      · -- observable `b`: `b.τ.P --b--> τ.P --τ--> P`
        exact Or.inr ⟨hbt, CCS.pre b (CCS.pre Act.tau P), CCS.pre Act.tau P,
          tauStar_refl _ _ _, by simp [ccsLTS_step], tauStar_single (by simp [ccsLTS_step])⟩
  · -- pair 2: (τ.P, P)
    subst hp; subst q
    constructor
    · -- LHS τ.P --τ--> P, matched by P =[τ]⇒ P (reflexive); target (P, P) diagonal
      intro b p' hstep
      simp only [ccsLTS_step, step_pre_iff] at hstep
      obtain ⟨hb, hp'⟩ := hstep; subst hb; subst p'
      exact ⟨P, weakStep_tau_of_tauStar (tauStar_refl _ _ _), Or.inr (Or.inr rfl)⟩
    · -- RHS P --b--> q', matched by τ.P --τ--> P --b--> q'; target (q', q') diagonal
      intro b q' hstep
      refine ⟨q', ?_, Or.inr (Or.inr rfl)⟩
      by_cases hbt : b = Act.tau
      · subst hbt
        exact weakStep_tau_of_tauStar
          (tauStar_trans (tauStar_single (by simp [ccsLTS_step]))
            (tauStar_single hstep))
      · exact Or.inr ⟨hbt, P, q', tauStar_single (by simp [ccsLTS_step]), hstep,
          tauStar_refl _ _ _⟩
  · -- diagonal pair
    subst hpq
    exact ⟨fun b p' hstep => ⟨p', step_weakStep hstep, Or.inr (Or.inr rfl)⟩,
           fun b q' hstep => ⟨q', step_weakStep hstep, Or.inr (Or.inr rfl)⟩⟩

theorem tau_law_2 (P : CCS Name K) :
    CCS.choice P (CCS.pre Act.tau P) ≈[ccsLTS defn, Act.tau] CCS.pre Act.tau P := by
  have key : IsWeakBisimulation (ccsLTS defn) Act.tau
      (fun x y =>
        (x = CCS.choice P (CCS.pre Act.tau P) ∧ y = CCS.pre Act.tau P) ∨ x = y) := by
    intro p q hR
    rcases hR with ⟨hp, hq⟩ | hpq
    · subst hp; subst hq
      constructor
      · -- LHS moves: P + τ.P  --α-->  p'
        intro α p' hstep
        rw [ccsLTS_step, step_choice_iff] at hstep
        rcases hstep with hPstep | hRstep
        · -- P --α--> p', matched by τ.P --τ--> P --α--> p'
          by_cases hα : α = Act.tau
          · subst hα
            refine ⟨p', ?_, Or.inr rfl⟩
            exact weakStep_tau_of_tauStar
              (tauStar_trans (tauStar_single (L := ccsLTS defn)
                (by rw [ccsLTS_step, step_pre_iff]; exact ⟨rfl, rfl⟩))
                (tauStar_single hPstep))
          · refine ⟨p', ?_, Or.inr rfl⟩
            exact Or.inr ⟨hα, P, p',
              tauStar_single (L := ccsLTS defn)
                (by rw [ccsLTS_step, step_pre_iff]; exact ⟨rfl, rfl⟩),
              hPstep, tauStar_refl _ _ _⟩
        · -- τ.P --α--> p' (right summand): label tau, p' = P
          rw [step_pre_iff] at hRstep
          obtain ⟨hα, hp'⟩ := hRstep
          subst hα; subst p'
          refine ⟨P, ?_, Or.inr rfl⟩
          exact weakStep_tau_of_tauStar
            (tauStar_single (L := ccsLTS defn)
              (by rw [ccsLTS_step, step_pre_iff]; exact ⟨rfl, rfl⟩))
      · -- RHS moves: τ.P --α--> q'
        intro α q' hstep
        rw [ccsLTS_step, step_pre_iff] at hstep
        obtain ⟨hα, hq'⟩ := hstep
        subst hα; subst q'
        refine ⟨P, ?_, Or.inr rfl⟩
        exact weakStep_tau_of_tauStar
          (tauStar_single (L := ccsLTS defn)
            (by rw [ccsLTS_step, step_choice_iff]
                exact Or.inr (by rw [step_pre_iff]; exact ⟨rfl, rfl⟩)))
    · subst hpq
      constructor
      · intro α p' hstep
        exact ⟨p', step_weakStep hstep, Or.inr rfl⟩
      · intro α q' hstep
        exact ⟨q', step_weakStep hstep, Or.inr rfl⟩
  exact key.le_weaklyBisimilar (Or.inl ⟨rfl, rfl⟩)

/-- The third `τ`-law: `α.(P + τ.Q) ≈ α.(P + τ.Q) + α.Q`. -/
theorem tau_law_3 {α : Act Name} (P Q : CCS Name K) :
    CCS.pre α (CCS.choice P (CCS.pre Act.tau Q)) ≈[ccsLTS defn, Act.tau]
      CCS.choice (CCS.pre α (CCS.choice P (CCS.pre Act.tau Q))) (CCS.pre α Q) := by
  set A : CCS Name K := CCS.pre α (CCS.choice P (CCS.pre Act.tau Q)) with hA
  set B : CCS Name K := CCS.choice P (CCS.pre Act.tau Q) with hB
  refine IsWeakBisimulation.le_weaklyBisimilar
    (R := fun x y => (x = A ∧ y = CCS.choice A (CCS.pre α Q)) ∨ x = y) ?_ (Or.inl ⟨rfl, rfl⟩)
  -- `A —α→ B`, the common move of the prefixed term.
  have hAB : Step defn A α B := Step.act _ _
  -- `B —τ→ Q`, the silent move from the right summand of `B`.
  have hBQ : Step defn B Act.tau Q := Step.sumr (Step.act _ _)
  rintro p q (⟨rfl, rfl⟩ | rfl)
  · -- The off-diagonal pair `(A, A + α.Q)`.
    refine ⟨fun a p' hp => ?_, fun a q' hq => ?_⟩
    · -- A move of `A`: it must be `A —α→ B`.
      rw [ccsLTS_step, hA, step_pre_iff] at hp
      obtain ⟨rfl, rfl⟩ := hp
      -- Match with `(A + α.Q) —α→ B` via the left summand; land on the diagonal `(B, B)`.
      exact ⟨B, step_weakStep (Step.suml hAB), Or.inr rfl⟩
    · -- A move of `A + α.Q`: either the left summand `A —α→ B` or the right `α.Q —α→ Q`.
      rw [ccsLTS_step, step_choice_iff] at hq
      rcases hq with hleft | hright
      · -- Left summand: `A —α→ B`.
        rw [hA, step_pre_iff] at hleft
        obtain ⟨rfl, rfl⟩ := hleft
        -- Match with `A —α→ B`; land on the diagonal `(B, B)`.
        exact ⟨B, step_weakStep hAB, Or.inr rfl⟩
      · -- Right summand: `α.Q —α→ Q`, so `q' = Q` and `a = α`.
        rw [step_pre_iff] at hright
        obtain ⟨rfl, rfl⟩ := hright
        -- Match `A =α⇒ q'` (here `q' = Q`): `A —α→ B —τ→ q'`; diagonal `(q', q')`.
        refine ⟨q', ?_, Or.inr rfl⟩
        by_cases hαtau : a = Act.tau
        · -- `a = τ`: the whole thing is a silent chain `A —τ→ B —τ→ q'`.
          subst hαtau
          exact weakStep_tau_of_tauStar
            (tauStar_trans (tauStar_single hAB) (tauStar_single hBQ))
        · -- `a ≠ τ`: one `a`-step `A —α→ B` then the silent tail `B —τ→ q'`.
          exact Or.inr ⟨hαtau, A, B, tauStar_refl _ _ _, hAB, tauStar_single hBQ⟩
  · -- The diagonal pair `(q, q)`: every move is matched by itself.
    exact ⟨fun a p' hp => ⟨p', step_weakStep hp, Or.inr rfl⟩,
           fun a q' hq => ⟨q', step_weakStep hq, Or.inr rfl⟩⟩

end DeepWiki.ReactiveSystems
