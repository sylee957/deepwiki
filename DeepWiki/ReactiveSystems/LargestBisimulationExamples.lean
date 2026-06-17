import DeepWiki.ReactiveSystems.Bisimulation
import Mathlib.Tactic.DeriveFintype

/-! # Largest-bisimulation and non-bisimilarity examples on finite LTSs
The Example 3.7 LTS: `s —a→ s₁/s₂`, `s₁ —b→ s₃`; `t —a→ t₁`, `t₁ —b→ t₁/t₂`. The
attacker wins from `(s, t)`: after `s —a→ s₁ —b→ s₃` the state `s₃` is dead, but
`t₁` can keep doing `b`, so `s` and `t` are not bisimilar. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- States of the Example 3.7 LTS. -/
inductive E37S | s | s1 | s2 | s3 | t | t1 | t2
  deriving DecidableEq, Fintype

/-- Actions of Example 3.7. -/
inductive E37A | a | b
  deriving DecidableEq, Fintype

/-- Edges: `s —a→ s₁/s₂`, `s₁ —b→ s₃`, `t —a→ t₁`, `t₁ —b→ t₁/t₂`. -/
def edge412 : E37S → E37A → E37S → Bool
  | .s, .a, .s1 => true
  | .s, .a, .s2 => true
  | .s1, .b, .s3 => true
  | .t, .a, .t1 => true
  | .t1, .b, .t1 => true
  | .t1, .b, .t2 => true
  | _, _, _ => false

/-- The Example 3.7 LTS (reducible, so step facts are decidable). -/
abbrev e37 : LTS E37S E37A := ⟨fun p x q => edge412 p x q = true⟩

/-- **Exercise 4.12** (§4.3, p.87). In the Example 3.7 LTS, `s ≁ t`: the attacker
plays `s —a→ s₁` (forcing `t —a→ t₁`), then `t₁ —b→ t₁` (forcing `s₁ —b→ s₃`),
then `t₁ —b→ t₁` again, which `s₃` (dead) cannot match. -/
theorem e37_s_not_bisim_t : ¬ ((E37S.s) ~[e37] (E37S.t)) := by
  intro h
  obtain ⟨q1, hq1, hb1⟩ := ((bisimilar_iff _ _).mp h).1 E37A.a E37S.s1 (by decide)
  obtain rfl : q1 = E37S.t1 := (by decide : ∀ q, e37.step E37S.t E37A.a q → q = E37S.t1) q1 hq1
  obtain ⟨q2, hq2, hb2⟩ := ((bisimilar_iff _ _).mp hb1).2 E37A.b E37S.t1 (by decide)
  obtain rfl : q2 = E37S.s3 := (by decide : ∀ q, e37.step E37S.s1 E37A.b q → q = E37S.s3) q2 hq2
  obtain ⟨q3, hq3, _⟩ := ((bisimilar_iff _ _).mp hb2).2 E37A.b E37S.t1 (by decide)
  exact absurd hq3 ((by decide : ∀ q, ¬ e37.step E37S.s3 E37A.b q) q3)

/-! ## Exercise 4.11 — the largest bisimulation of `P₁..P₅` -/

/-- States `P₁..P₅`: `P₁=a.P₂`, `P₂=a.P₁`, `P₃=a.P₂+a.P₄`, `P₄=a.P₃+a.P₅`, `P₅=0`. -/
inductive P411 | p1 | p2 | p3 | p4 | p5
  deriving DecidableEq, Fintype

/-- The single action `a`. -/
inductive A411 | a
  deriving DecidableEq, Fintype

/-- Edges (single action): `P₁↔P₂`, `P₃→P₂`, `P₃→P₄`, `P₄→P₃`, `P₄→P₅`; `P₅` dead. -/
def edge411 : P411 → A411 → P411 → Bool
  | .p1, .a, .p2 => true
  | .p2, .a, .p1 => true
  | .p3, .a, .p2 => true
  | .p3, .a, .p4 => true
  | .p4, .a, .p3 => true
  | .p4, .a, .p5 => true
  | _, _, _ => false

/-- The `P₁..P₅` LTS. -/
abbrev lts411 : LTS P411 A411 := ⟨fun p x q => edge411 p x q = true⟩

/-- The candidate largest bisimulation `{(P₁,P₂),(P₂,P₁)} ∪ Δ`. -/
def rel411 : P411 → P411 → Bool
  | .p1, .p2 => true
  | .p2, .p1 => true
  | x, y => decide (x = y)

theorem isBisimulation_rel411 : IsBisimulation lts411 (fun p q => rel411 p q = true) := by
  show ∀ p q, rel411 p q = true →
    (∀ x p', edge411 p x p' = true → ∃ q', edge411 q x q' = true ∧ rel411 p' q' = true) ∧
    (∀ x q', edge411 q x q' = true → ∃ p', edge411 p x p' = true ∧ rel411 p' q' = true)
  decide

/-- States with an outgoing `a`-move are never bisimilar to the dead `P₅`. -/
theorem not_bisim_p5 {x x' : P411} (hx : lts411.step x A411.a x') : ¬ (x ~[lts411] P411.p5) :=
  not_bisim_dead_of_step hx (by decide)

/-- **Exercise 4.11** (§4.3, p.86). The largest bisimulation of `P₁..P₅` identifies
exactly `P₁` and `P₂`: `P₁ ~ P₂`, while `P₃, P₄, P₅` are pairwise distinct and
distinct from `P₁`. -/
theorem lts411_only_p1_p2_bisimilar :
    (P411.p1 ~[lts411] P411.p2) ∧ ¬ (P411.p1 ~[lts411] P411.p3) ∧
    ¬ (P411.p1 ~[lts411] P411.p4) ∧ ¬ (P411.p1 ~[lts411] P411.p5) ∧
    ¬ (P411.p3 ~[lts411] P411.p4) ∧ ¬ (P411.p3 ~[lts411] P411.p5) ∧
    ¬ (P411.p4 ~[lts411] P411.p5) := by
  refine ⟨isBisimulation_rel411.le_bisimilar (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- P1 ≁ P3: P3→P4 forces P1→P2, P4→P5 forces P2→P1, giving P1~P5
    intro h
    obtain ⟨p', hp', hb⟩ := ((bisimilar_iff _ _).mp h).2 A411.a P411.p4 (by decide)
    obtain rfl : p' = P411.p2 :=
      (by decide : ∀ q, lts411.step P411.p1 A411.a q → q = P411.p2) p' hp'
    obtain ⟨p'', hp'', hb2⟩ := ((bisimilar_iff _ _).mp hb).2 A411.a P411.p5 (by decide)
    obtain rfl : p'' = P411.p1 :=
      (by decide : ∀ q, lts411.step P411.p2 A411.a q → q = P411.p1) p'' hp''
    exact not_bisim_p5 (by decide : lts411.step P411.p1 A411.a P411.p2) hb2
  · -- P1 ≁ P4: P4→P5 forces P1→P2, giving P2~P5
    intro h
    obtain ⟨p', hp', hb⟩ := ((bisimilar_iff _ _).mp h).2 A411.a P411.p5 (by decide)
    obtain rfl : p' = P411.p2 :=
      (by decide : ∀ q, lts411.step P411.p1 A411.a q → q = P411.p2) p' hp'
    exact not_bisim_p5 (by decide : lts411.step P411.p2 A411.a P411.p1) hb
  · exact not_bisim_p5 (by decide : lts411.step P411.p1 A411.a P411.p2)
  · -- P3 ≁ P4: P4→P5 forces P3→(P2 or P4), giving P2~P5 or P4~P5
    intro h
    obtain ⟨p', hp', hb⟩ := ((bisimilar_iff _ _).mp h).2 A411.a P411.p5 (by decide)
    rcases (by decide : ∀ q, lts411.step P411.p3 A411.a q → q = P411.p2 ∨ q = P411.p4) p' hp' with
      rfl | rfl
    · exact not_bisim_p5 (by decide : lts411.step P411.p2 A411.a P411.p1) hb
    · exact not_bisim_p5 (by decide : lts411.step P411.p4 A411.a P411.p3) hb
  · exact not_bisim_p5 (by decide : lts411.step P411.p3 A411.a P411.p2)
  · exact not_bisim_p5 (by decide : lts411.step P411.p4 A411.a P411.p3)

end DeepWiki.ReactiveSystems
