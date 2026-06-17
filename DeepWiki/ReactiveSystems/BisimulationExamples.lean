import DeepWiki.ReactiveSystems.Bisimulation
import Mathlib.Tactic.DeriveFintype

/-! # Concrete strong-bisimulation examples on finite LTSs
A finite LTS with a decidable step relation makes `IsBisimulation` decidable, so a
witness bisimulation is checked by `decide`. One example exhibits `s ~ t`; another
exhibits strong bisimulations that are not reflexive, symmetric, or transitive. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-! ## A 10-state bisimulation `s ~ t` -/

/-- States of the two LTSs. -/
inductive S35 | s | s1 | s2 | s3 | s4 | t | t1 | t2 | t3 | t4
  deriving DecidableEq, Fintype

/-- Actions of the LTS. -/
inductive A35 | a | b
  deriving DecidableEq, Fintype

/-- The edge relation (as a `Bool`): the two LTSs side by side. -/
def edge35 : S35 → A35 → S35 → Bool
  | .s, .a, .s1 => true
  | .s, .a, .s2 => true
  | .s1, .a, .s3 => true
  | .s1, .b, .s4 => true
  | .s2, .a, .s4 => true
  | .s3, .a, .s => true
  | .s4, .a, .s => true
  | .t, .a, .t3 => true
  | .t, .a, .t1 => true
  | .t3, .a, .t4 => true
  | .t4, .a, .t => true
  | .t1, .a, .t2 => true
  | .t1, .b, .t2 => true
  | .t2, .a, .t => true
  | _, _, _ => false

/-- The LTS with the two state machines side by side. -/
def lts35 : LTS S35 A35 := ⟨fun p x q => edge35 p x q = true⟩

/-- The witnessing relation `{(s,t),(s₁,t₁),(s₂,t₃),(s₃,t₂),(s₄,t₂),(s₄,t₄)}`. -/
def rel35 : S35 → S35 → Bool
  | .s, .t => true
  | .s1, .t1 => true
  | .s2, .t3 => true
  | .s3, .t2 => true
  | .s4, .t2 => true
  | .s4, .t4 => true
  | _, _ => false

/-- The witnessing relation as a `Prop`. -/
def R35 : S35 → S35 → Prop := fun p q => rel35 p q = true

/-- `R35` is a strong bisimulation (checked by `decide`, after unfolding to the
decidable explicit form over the finite state/action types). -/
theorem isBisimulation_R35 : IsBisimulation lts35 R35 := by
  show ∀ p q, rel35 p q = true →
    (∀ x p', edge35 p x p' = true → ∃ q', edge35 q x q' = true ∧ rel35 p' q' = true) ∧
    (∀ x q', edge35 q x q' = true → ∃ p', edge35 p x p' = true ∧ rel35 p' q' = true)
  decide

/-- `s ~ t` in `lts35`, witnessed by the bisimulation `R35`. -/
theorem lts35_s_bisimilar_t : (S35.s) ~[lts35] (S35.t) :=
  isBisimulation_R35.le_bisimilar rfl

/-! ## Bisimulations need not be equivalences -/

/-- The empty (transition-free) LTS: every relation is vacuously a bisimulation. -/
def emptyLTS (Proc Act : Type*) : LTS Proc Act := ⟨fun _ _ _ => False⟩

/-- Over a transition-free LTS, *every* relation is a strong bisimulation. -/
theorem isBisimulation_emptyLTS {Proc Act : Type*} (R : Proc → Proc → Prop) :
    IsBisimulation (emptyLTS Proc Act) R :=
  fun _ _ _ => ⟨fun _ _ h => h.elim, fun _ _ h => h.elim⟩

/-- A strong bisimulation need not be reflexive: the
empty relation is a bisimulation but not reflexive on an inhabited LTS. -/
theorem bisimulation_not_reflexive :
    ∃ R : Bool → Bool → Prop, IsBisimulation (emptyLTS Bool Unit) R ∧ ¬ (∀ x, R x x) :=
  ⟨fun _ _ => False, isBisimulation_emptyLTS _, fun h => h true⟩

/-- A strong bisimulation need not be symmetric:
`{(true, false)}` is a bisimulation but not symmetric. -/
theorem bisimulation_not_symmetric :
    ∃ R : Bool → Bool → Prop, IsBisimulation (emptyLTS Bool Unit) R ∧ ¬ (∀ x y, R x y → R y x) :=
  ⟨fun x y => x = true ∧ y = false, isBisimulation_emptyLTS _,
    fun h => absurd (h true false ⟨rfl, rfl⟩).1 (by decide)⟩

/-- A strong bisimulation need not be transitive:
`{(0,1),(1,2)}` is a bisimulation but not transitive (it omits `(0,2)`). -/
theorem bisimulation_not_transitive :
    ∃ R : Fin 3 → Fin 3 → Prop,
      IsBisimulation (emptyLTS (Fin 3) Unit) R ∧ ¬ (∀ x y z, R x y → R y z → R x z) :=
  ⟨fun x y => (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2), isBisimulation_emptyLTS _, by
    intro h
    rcases h 0 1 2 (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) with ⟨_, h2⟩ | ⟨h2, _⟩ <;>
      exact absurd h2 (by decide)⟩

/-! ## Deciding `s ~ t`, `s ~ u`, `s ~ v` -/

/-- States of the four LTSs. -/
inductive S37
  | s | s1 | s2 | t | t1 | t2 | u | u1 | u2 | u3 | v | v1 | v2 | v3
  deriving DecidableEq, Fintype

/-- Edges of the four LTSs (over actions `a`, `b = A35`). -/
def edge37 : S37 → A35 → S37 → Bool
  | .s, .a, .s1 => true
  | .s1, .b, .s2 => true
  | .s2, .b, .s2 => true
  | .s2, .a, .s => true
  | .t, .a, .t1 => true
  | .t1, .b, .t1 => true
  | .t1, .b, .t2 => true
  | .t2, .a, .t => true
  | .u, .a, .u1 => true
  | .u1, .b, .u3 => true
  | .u3, .a, .u => true
  | .u3, .b, .u2 => true
  | .u2, .b, .u2 => true
  | .u2, .a, .u => true
  | .v, .a, .v1 => true
  | .v1, .b, .v2 => true
  | .v1, .b, .v3 => true
  | .v3, .b, .v3 => true
  | .v3, .b, .v2 => true
  | .v2, .a, .v => true
  | _, _, _ => false

/-- The LTS (reducible, so step facts are decidable). -/
abbrev lts37 : LTS S37 A35 := ⟨fun p x q => edge37 p x q = true⟩

/-- The witness `{(s,u),(s₁,u₁),(s₂,u₃),(s₂,u₂)}` for `s ~ u`. -/
def rel37 : S37 → S37 → Bool
  | .s, .u => true
  | .s1, .u1 => true
  | .s2, .u3 => true
  | .s2, .u2 => true
  | _, _ => false

/-- The witness relation for `s ~ u` is a strong bisimulation. -/
theorem isBisimulation_rel37 : IsBisimulation lts37 (fun p q => rel37 p q = true) := by
  show ∀ p q, rel37 p q = true →
    (∀ x p', edge37 p x p' = true → ∃ q', edge37 q x q' = true ∧ rel37 p' q' = true) ∧
    (∀ x q', edge37 q x q' = true → ∃ p', edge37 p x p' = true ∧ rel37 p' q' = true)
  decide

/-- `s ~ u` (positive case), witnessed by `rel37`. -/
theorem lts37_s_bisimilar_u : (S37.s) ~[lts37] (S37.u) :=
  isBisimulation_rel37.le_bisimilar rfl

/-- `s ≁ t`: the attacker plays `s —a→ s₁ —b→ s₂`
(where `s₂` enables both `a` and `b`); the defender's `t` must reply
`t —a→ t₁ —b→ {t₁, t₂}`, but `t₁` enables only `b` and `t₂` only `a`. -/
theorem lts37_s_not_bisimilar_t : ¬ ((S37.s) ~[lts37] (S37.t)) := by
  intro h
  obtain ⟨q1, hq1, hb1⟩ := ((bisimilar_iff _ _).mp h).1 A35.a S37.s1 (by decide)
  obtain rfl : q1 = S37.t1 := (by decide : ∀ q, lts37.step S37.t A35.a q → q = S37.t1) q1 hq1
  obtain ⟨q2, hq2, hb2⟩ := ((bisimilar_iff _ _).mp hb1).1 A35.b S37.s2 (by decide)
  rcases (by decide : ∀ q, lts37.step S37.t1 A35.b q → q = S37.t1 ∨ q = S37.t2) q2 hq2 with rfl | rfl
  · obtain ⟨q3, hq3, _⟩ := ((bisimilar_iff _ _).mp hb2).1 A35.a S37.s (by decide)
    exact absurd hq3 ((by decide : ∀ q, ¬ lts37.step S37.t1 A35.a q) q3)
  · obtain ⟨q3, hq3, _⟩ := ((bisimilar_iff _ _).mp hb2).1 A35.b S37.s2 (by decide)
    exact absurd hq3 ((by decide : ∀ q, ¬ lts37.step S37.t2 A35.b q) q3)

/-- `s ≁ v`: same shape as `s ≁ t` — after
`s —a→ s₁ —b→ s₂` the defender's `v₁` goes to `v₂` (only `a`) or `v₃` (only `b`),
neither matching `s₂`'s `{a, b}`. -/
theorem lts37_s_not_bisimilar_v : ¬ ((S37.s) ~[lts37] (S37.v)) := by
  intro h
  obtain ⟨q1, hq1, hb1⟩ := ((bisimilar_iff _ _).mp h).1 A35.a S37.s1 (by decide)
  obtain rfl : q1 = S37.v1 := (by decide : ∀ q, lts37.step S37.v A35.a q → q = S37.v1) q1 hq1
  obtain ⟨q2, hq2, hb2⟩ := ((bisimilar_iff _ _).mp hb1).1 A35.b S37.s2 (by decide)
  rcases (by decide : ∀ q, lts37.step S37.v1 A35.b q → q = S37.v2 ∨ q = S37.v3) q2 hq2 with rfl | rfl
  · obtain ⟨q3, hq3, _⟩ := ((bisimilar_iff _ _).mp hb2).1 A35.b S37.s2 (by decide)
    exact absurd hq3 ((by decide : ∀ q, ¬ lts37.step S37.v2 A35.b q) q3)
  · obtain ⟨q3, hq3, _⟩ := ((bisimilar_iff _ _).mp hb2).1 A35.a S37.s (by decide)
    exact absurd hq3 ((by decide : ∀ q, ¬ lts37.step S37.v3 A35.a q) q3)

end DeepWiki.ReactiveSystems
