import DeepWiki.ReactiveSystems.Bisimulation
import Mathlib.Tactic.DeriveFintype

/-! # Example 3.7 — `s ≁ t` (Exercise 4.12)
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
theorem ex_4_12_s_not_bisim_t : ¬ ((E37S.s) ~[e37] (E37S.t)) := by
  intro h
  obtain ⟨q1, hq1, hb1⟩ := ((bisimilar_iff _ _).mp h).1 E37A.a E37S.s1 (by decide)
  obtain rfl : q1 = E37S.t1 := (by decide : ∀ q, e37.step E37S.t E37A.a q → q = E37S.t1) q1 hq1
  obtain ⟨q2, hq2, hb2⟩ := ((bisimilar_iff _ _).mp hb1).2 E37A.b E37S.t1 (by decide)
  obtain rfl : q2 = E37S.s3 := (by decide : ∀ q, e37.step E37S.s1 E37A.b q → q = E37S.s3) q2 hq2
  obtain ⟨q3, hq3, _⟩ := ((bisimilar_iff _ _).mp hb2).2 E37A.b E37S.t1 (by decide)
  exact absurd hq3 ((by decide : ∀ q, ¬ e37.step E37S.s3 E37A.b q) q3)

end DeepWiki.ReactiveSystems
