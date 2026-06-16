import DeepWiki.ReactiveSystems.Bisimulation
import Mathlib.Tactic.DeriveFintype

/-! # Concrete bisimulation examples of Chapter 3 (Exercises 3.5, 3.8)
A finite LTS with a decidable step relation makes `IsBisimulation` decidable, so a
witness bisimulation is checked by `decide`. Exercise 3.5 exhibits `s ~ t`;
Exercise 3.8 exhibits strong bisimulations that are not reflexive / symmetric /
transitive. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-! ## Exercise 3.5 — a 10-state bisimulation `s ~ t` -/

/-- States of the two LTSs of Exercise 3.5. -/
inductive S35 | s | s1 | s2 | s3 | s4 | t | t1 | t2 | t3 | t4
  deriving DecidableEq, Fintype

/-- Actions of Exercise 3.5. -/
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

/-- The LTS of Exercise 3.5. -/
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

/-- **Exercise 3.5** (§3.3, p.42). `s ~ t` in the LTS of Exercise 3.5, witnessed by
the bisimulation `R35`. -/
theorem ex_3_5_bisim : (S35.s) ~[lts35] (S35.t) :=
  isBisimulation_R35.le_bisimilar rfl

/-! ## Exercise 3.8 — bisimulations need not be equivalences -/

/-- The empty (transition-free) LTS: every relation is vacuously a bisimulation. -/
def emptyLTS (Proc Act : Type*) : LTS Proc Act := ⟨fun _ _ _ => False⟩

/-- Over a transition-free LTS, *every* relation is a strong bisimulation. -/
theorem isBisimulation_emptyLTS {Proc Act : Type*} (R : Proc → Proc → Prop) :
    IsBisimulation (emptyLTS Proc Act) R :=
  fun _ _ _ => ⟨fun _ _ h => h.elim, fun _ _ h => h.elim⟩

/-- **Exercise 3.8** (§3.3, p.44). A strong bisimulation need not be reflexive: the
empty relation is a bisimulation but not reflexive on an inhabited LTS. -/
theorem ex_3_8_not_reflexive :
    ∃ R : Bool → Bool → Prop, IsBisimulation (emptyLTS Bool Unit) R ∧ ¬ (∀ x, R x x) :=
  ⟨fun _ _ => False, isBisimulation_emptyLTS _, fun h => h true⟩

/-- **Exercise 3.8** (§3.3, p.44). A strong bisimulation need not be symmetric:
`{(true, false)}` is a bisimulation but not symmetric. -/
theorem ex_3_8_not_symmetric :
    ∃ R : Bool → Bool → Prop, IsBisimulation (emptyLTS Bool Unit) R ∧ ¬ (∀ x y, R x y → R y x) :=
  ⟨fun x y => x = true ∧ y = false, isBisimulation_emptyLTS _,
    fun h => absurd (h true false ⟨rfl, rfl⟩).1 (by decide)⟩

/-- **Exercise 3.8** (§3.3, p.44). A strong bisimulation need not be transitive:
`{(0,1),(1,2)}` is a bisimulation but not transitive (it omits `(0,2)`). -/
theorem ex_3_8_not_transitive :
    ∃ R : Fin 3 → Fin 3 → Prop,
      IsBisimulation (emptyLTS (Fin 3) Unit) R ∧ ¬ (∀ x y z, R x y → R y z → R x z) :=
  ⟨fun x y => (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2), isBisimulation_emptyLTS _, by
    intro h
    rcases h 0 1 2 (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) with ⟨_, h2⟩ | ⟨h2, _⟩ <;>
      exact absurd h2 (by decide)⟩

end DeepWiki.ReactiveSystems
