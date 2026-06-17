import DeepWiki.ReactiveSystems.BisimulationWeak
import Mathlib.Tactic.DeriveFintype

/-! # Exercise 3.25 — a weak bisimulation showing `s ≈ t`
The LTS: left component `s ⇄ s₁ ⇄ s₂` (a `τ`-cycle), with `s —a→ s₃`, `s₁ —b→ s₄`,
`s₂ —τ→ s₅` (`s₃,s₄,s₅` dead); right component `t —τ→ t₁` (with `t₁ —τ→ t₁`),
`t —a→ t₂`, `t —b→ t₃` (`t₁,t₂,t₃` dead). The relation
`{(s,t),(s₁,t),(s₂,t),(s₃,t₂),(s₄,t₃),(s₅,t₁)}` is a weak bisimulation: the three
`τ`-cycle states have the same observable behaviour (`a`, `b`, and a silent drift to
the dead `s₅` matching `t`'s drift to the divergent `t₁`). -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- States of the Exercise 3.25 LTS. -/
inductive St325 | s | s1 | s2 | s3 | s4 | s5 | t | t1 | t2 | t3
  deriving DecidableEq, Fintype

/-- Actions of Exercise 3.25. -/
inductive A325 | a | b | tau
  deriving DecidableEq, Fintype

/-- Edges: the `s ⇄ s₁ ⇄ s₂` `τ`-cycle with `a`/`b`/`τ` exits, and `t —τ→ t₁ ↺`,
`t —a→ t₂`, `t —b→ t₃`. -/
def edge325 : St325 → A325 → St325 → Bool
  | .s, .tau, .s1 => true
  | .s1, .tau, .s => true
  | .s1, .tau, .s2 => true
  | .s2, .tau, .s1 => true
  | .s, .a, .s3 => true
  | .s1, .b, .s4 => true
  | .s2, .tau, .s5 => true
  | .t, .tau, .t1 => true
  | .t1, .tau, .t1 => true
  | .t, .a, .t2 => true
  | .t, .b, .t3 => true
  | _, _, _ => false

/-- The Exercise 3.25 LTS (reducible, so step facts are decidable). -/
abbrev lts325 : LTS St325 A325 := ⟨fun p x q => edge325 p x q = true⟩

/-! ## The silent (`τ*`) reachabilities used to build the weak transitions -/

/-- `s ⟶τ* s₁`. -/
theorem ts_s_s1 : tauStar lts325 A325.tau St325.s St325.s1 :=
  tauStar_single (show lts325.step St325.s A325.tau St325.s1 by decide)
/-- `s₁ ⟶τ* s`. -/
theorem ts_s1_s : tauStar lts325 A325.tau St325.s1 St325.s :=
  tauStar_single (show lts325.step St325.s1 A325.tau St325.s by decide)
/-- `s₂ ⟶τ* s₁`. -/
theorem ts_s2_s1 : tauStar lts325 A325.tau St325.s2 St325.s1 :=
  tauStar_single (show lts325.step St325.s2 A325.tau St325.s1 by decide)
/-- `s₂ ⟶τ* s`. -/
theorem ts_s2_s : tauStar lts325 A325.tau St325.s2 St325.s :=
  tauStar_trans ts_s2_s1 ts_s1_s
/-- `s ⟶τ* s₅`. -/
theorem ts_s_s5 : tauStar lts325 A325.tau St325.s St325.s5 :=
  tauStar_trans ts_s_s1 (tauStar_trans (tauStar_single
    (show lts325.step St325.s1 A325.tau St325.s2 by decide))
    (tauStar_single (show lts325.step St325.s2 A325.tau St325.s5 by decide)))
/-- `s₁ ⟶τ* s₅`. -/
theorem ts_s1_s5 : tauStar lts325 A325.tau St325.s1 St325.s5 :=
  tauStar_trans (tauStar_single (show lts325.step St325.s1 A325.tau St325.s2 by decide))
    (tauStar_single (show lts325.step St325.s2 A325.tau St325.s5 by decide))
/-- `s₂ ⟶τ* s₅`. -/
theorem ts_s2_s5 : tauStar lts325 A325.tau St325.s2 St325.s5 :=
  tauStar_single (show lts325.step St325.s2 A325.tau St325.s5 by decide)

/-! ## The weak transitions used to match moves -/

/-- An empty silent transition `x =τ⇒ x`. -/
theorem w_refl (x : St325) : lts325 ⊢ x =[A325.tau]⇒[A325.tau] x :=
  weakStep_tau_of_tauStar (tauStar_refl _ _ _)

/-- `s =[a]⇒ s₃`. -/
theorem w_s_a : lts325 ⊢ St325.s =[A325.a]⇒[A325.tau] St325.s3 :=
  step_weakStep (show lts325.step St325.s A325.a St325.s3 by decide)
/-- `s =[b]⇒ s₄`. -/
theorem w_s_b : lts325 ⊢ St325.s =[A325.b]⇒[A325.tau] St325.s4 :=
  weakStep_visible (by decide) ts_s_s1
    (show lts325.step St325.s1 A325.b St325.s4 by decide) (tauStar_refl _ _ _)
/-- `s₁ =[a]⇒ s₃`. -/
theorem w_s1_a : lts325 ⊢ St325.s1 =[A325.a]⇒[A325.tau] St325.s3 :=
  weakStep_visible (by decide) ts_s1_s
    (show lts325.step St325.s A325.a St325.s3 by decide) (tauStar_refl _ _ _)
/-- `s₁ =[b]⇒ s₄`. -/
theorem w_s1_b : lts325 ⊢ St325.s1 =[A325.b]⇒[A325.tau] St325.s4 :=
  step_weakStep (show lts325.step St325.s1 A325.b St325.s4 by decide)
/-- `s₂ =[a]⇒ s₃`. -/
theorem w_s2_a : lts325 ⊢ St325.s2 =[A325.a]⇒[A325.tau] St325.s3 :=
  weakStep_visible (by decide) ts_s2_s
    (show lts325.step St325.s A325.a St325.s3 by decide) (tauStar_refl _ _ _)
/-- `s₂ =[b]⇒ s₄`. -/
theorem w_s2_b : lts325 ⊢ St325.s2 =[A325.b]⇒[A325.tau] St325.s4 :=
  weakStep_visible (by decide) ts_s2_s1
    (show lts325.step St325.s1 A325.b St325.s4 by decide) (tauStar_refl _ _ _)
/-- `s =[τ]⇒ s₅`. -/
theorem w_s_tau_s5 : lts325 ⊢ St325.s =[A325.tau]⇒[A325.tau] St325.s5 :=
  weakStep_tau_of_tauStar ts_s_s5
/-- `s₁ =[τ]⇒ s₅`. -/
theorem w_s1_tau_s5 : lts325 ⊢ St325.s1 =[A325.tau]⇒[A325.tau] St325.s5 :=
  weakStep_tau_of_tauStar ts_s1_s5
/-- `s₂ =[τ]⇒ s₅`. -/
theorem w_s2_tau_s5 : lts325 ⊢ St325.s2 =[A325.tau]⇒[A325.tau] St325.s5 :=
  weakStep_tau_of_tauStar ts_s2_s5
/-- `t =[a]⇒ t₂`. -/
theorem w_t_a : lts325 ⊢ St325.t =[A325.a]⇒[A325.tau] St325.t2 :=
  step_weakStep (show lts325.step St325.t A325.a St325.t2 by decide)
/-- `t =[b]⇒ t₃`. -/
theorem w_t_b : lts325 ⊢ St325.t =[A325.b]⇒[A325.tau] St325.t3 :=
  step_weakStep (show lts325.step St325.t A325.b St325.t3 by decide)
/-- `t =[τ]⇒ t₁`. -/
theorem w_t_tau_t1 : lts325 ⊢ St325.t =[A325.tau]⇒[A325.tau] St325.t1 :=
  weakStep_tau_of_tauStar (tauStar_single (show lts325.step St325.t A325.tau St325.t1 by decide))

/-- The candidate weak bisimulation: the three `τ`-cycle states all relate to `t`,
the `a`/`b`-deadlocks pair up, and the silent-dead `s₅` relates to the divergent `t₁`. -/
def R325 : St325 → St325 → Prop := fun x y =>
  ((x = St325.s ∨ x = St325.s1 ∨ x = St325.s2) ∧ y = St325.t) ∨
  (x = St325.s3 ∧ y = St325.t2) ∨ (x = St325.s4 ∧ y = St325.t3) ∨
  (x = St325.s5 ∧ y = St325.t1)

/-- `R325` is a weak bisimulation. -/
theorem isWeakBisimulation_R325 : IsWeakBisimulation lts325 A325.tau R325 := by
  intro p q hR
  rcases hR with ⟨hx, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- ({s, s₁, s₂}, t)
    rcases hx with rfl | rfl | rfl
    · -- (s, t)
      refine ⟨fun α p' hstep => ?_, fun α q' hstep => ?_⟩
      · rcases (show ∀ α p', edge325 St325.s α p' = true →
            (α = A325.tau ∧ p' = St325.s1) ∨ (α = A325.a ∧ p' = St325.s3) by decide)
            α p' hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨St325.t, w_refl _, Or.inl ⟨Or.inr (Or.inl rfl), rfl⟩⟩
        · exact ⟨St325.t2, w_t_a, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · rcases (show ∀ α q', edge325 St325.t α q' = true →
            (α = A325.tau ∧ q' = St325.t1) ∨ (α = A325.a ∧ q' = St325.t2) ∨
              (α = A325.b ∧ q' = St325.t3) by decide)
            α q' hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨St325.s5, w_s_tau_s5, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        · exact ⟨St325.s3, w_s_a, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
        · exact ⟨St325.s4, w_s_b, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · -- (s₁, t)
      refine ⟨fun α p' hstep => ?_, fun α q' hstep => ?_⟩
      · rcases (show ∀ α p', edge325 St325.s1 α p' = true →
            (α = A325.tau ∧ p' = St325.s) ∨ (α = A325.tau ∧ p' = St325.s2) ∨
              (α = A325.b ∧ p' = St325.s4) by decide)
            α p' hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨St325.t, w_refl _, Or.inl ⟨Or.inl rfl, rfl⟩⟩
        · exact ⟨St325.t, w_refl _, Or.inl ⟨Or.inr (Or.inr rfl), rfl⟩⟩
        · exact ⟨St325.t3, w_t_b, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · rcases (show ∀ α q', edge325 St325.t α q' = true →
            (α = A325.tau ∧ q' = St325.t1) ∨ (α = A325.a ∧ q' = St325.t2) ∨
              (α = A325.b ∧ q' = St325.t3) by decide)
            α q' hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨St325.s5, w_s1_tau_s5, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        · exact ⟨St325.s3, w_s1_a, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
        · exact ⟨St325.s4, w_s1_b, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · -- (s₂, t)
      refine ⟨fun α p' hstep => ?_, fun α q' hstep => ?_⟩
      · rcases (show ∀ α p', edge325 St325.s2 α p' = true →
            (α = A325.tau ∧ p' = St325.s1) ∨ (α = A325.tau ∧ p' = St325.s5) by decide)
            α p' hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨St325.t, w_refl _, Or.inl ⟨Or.inr (Or.inl rfl), rfl⟩⟩
        · exact ⟨St325.t1, w_t_tau_t1, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      · rcases (show ∀ α q', edge325 St325.t α q' = true →
            (α = A325.tau ∧ q' = St325.t1) ∨ (α = A325.a ∧ q' = St325.t2) ∨
              (α = A325.b ∧ q' = St325.t3) by decide)
            α q' hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨St325.s5, w_s2_tau_s5, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        · exact ⟨St325.s3, w_s2_a, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
        · exact ⟨St325.s4, w_s2_b, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · -- (s₃, t₂): both dead
    exact ⟨fun α p' hstep => absurd hstep ((by decide : ∀ α p', ¬ lts325.step St325.s3 α p') α p'),
      fun α q' hstep => absurd hstep ((by decide : ∀ α q', ¬ lts325.step St325.t2 α q') α q')⟩
  · -- (s₄, t₃): both dead
    exact ⟨fun α p' hstep => absurd hstep ((by decide : ∀ α p', ¬ lts325.step St325.s4 α p') α p'),
      fun α q' hstep => absurd hstep ((by decide : ∀ α q', ¬ lts325.step St325.t3 α q') α q')⟩
  · -- (s₅, t₁): s₅ dead; t₁ only τ-loops, matched by the empty silent move
    refine ⟨fun α p' hstep =>
      absurd hstep ((by decide : ∀ α p', ¬ lts325.step St325.s5 α p') α p'), fun α q' hstep => ?_⟩
    rcases (show ∀ α q', edge325 St325.t1 α q' = true → α = A325.tau ∧ q' = St325.t1 by decide)
      α q' hstep with ⟨rfl, rfl⟩
    exact ⟨St325.s5, w_refl _, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

/-- **Exercise 3.25** (§3.4, p.60). `s ≈ t`: the relation `R325` is a weak
bisimulation containing `(s, t)`. -/
theorem ex_3_25 : St325.s ≈[lts325, A325.tau] St325.t :=
  isWeakBisimulation_R325.le_weaklyBisimilar (Or.inl ⟨Or.inl rfl, rfl⟩)

end DeepWiki.ReactiveSystems
