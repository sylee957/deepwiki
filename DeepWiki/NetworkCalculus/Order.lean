import DeepWiki.NetworkCalculus.Dioids
import Mathlib.Algebra.Order.Kleene

/-! The canonical dioid order `≼ₒ` (`a ⊕ₒ b = b`) with its
partial-order / semilattice / order-bot bridge instances and
isotony lemmas. -/

namespace DeepWiki

namespace Algebra

namespace Bridge

/-- Dioid sum `⊕ₒ` is `+`. -/
theorem oplus_eq_add {T : Type*} [Dioid T] (a b : T) :
    a ⊕ₒ b = a + b := rfl

/-- Dioid product `⊗ₒ` is `*`. -/
theorem otimes_eq_mul {T : Type*} [Dioid T] (a b : T) :
    a ⊗ₒ b = a * b := rfl

/-- Canonical dioid order: `a ≤ b ↔ a ⊕ₒ b = b`. -/
scoped instance instLE {T : Type*} [Dioid T] : LE T where
  le a b := a ⊕ₒ b = b

/-- Notation `a ≼ₒ b` for the canonical dioid order. -/
scoped notation:50 a:51 " ≼ₒ " b:51 => @LE.le _ instLE a b

end Bridge

open scoped Bridge
open Bridge (oplus_eq_add otimes_eq_mul)

namespace Bridge

/-- `≼ₒ` is a `PartialOrder` (refl/trans/antisymm from `⊕ₒ`). -/
scoped instance instPartialOrder
    {T : Type*} [Dioid T] : PartialOrder T where
  toLE := instLE
  le_refl a := Dioid.oplus_idem a
  le_trans a b c (hab : a ≼ₒ b) (hbc : b ≼ₒ c) := by
    show a ⊕ₒ c = c
    rw [← hbc, ← add_assoc, hab]
  le_antisymm a b (hab : a ≼ₒ b) (hba : b ≼ₒ a) := by
    rw [← hab, add_comm, hba]

end Bridge

example {T : Type*} [Dioid T] (a : T) : a ≼ₒ a :=
  le_refl a

example {T : Type*} [Dioid T] {a b c : T}
    (hab : a ≼ₒ b) (hbc : b ≼ₒ c) : a ≼ₒ c :=
  le_trans hab hbc

example {T : Type*} [Dioid T] {a b : T}
    (hab : a ≼ₒ b) (hba : b ≼ₒ a) : a = b :=
  le_antisymm hab hba

namespace Bridge

/-- `⊕ₒ` is the join: `≼ₒ` forms a `SemilatticeSup`. -/
scoped instance instSemilatticeSup
    {T : Type*} [Dioid T] : SemilatticeSup T where
  toPartialOrder := instPartialOrder
  sup a b := a ⊕ₒ b
  le_sup_left a b := by
    show a ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
    rw [← add_assoc, Dioid.oplus_idem]
  le_sup_right a b := by
    show b ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
    rw [add_comm a b, ← add_assoc, Dioid.oplus_idem]
  sup_le a b c hac hbc := by
    show (a ⊕ₒ b) ⊕ₒ c = c
    rw [add_assoc,
        (show b ⊕ₒ c = c from hbc),
        (show a ⊕ₒ c = c from hac)]

/-- `εₒ` (`𝟘`) is the bottom: `≼ₒ` has an `OrderBot`. -/
scoped instance instOrderBot
    {T : Type*} [Dioid T] : OrderBot T where
  bot := εₒ
  bot_le a := zero_add a

/-- A `Dioid` is an `IdemCommSemiring` (`+ = ⊔`). -/
scoped instance instIdemCommSemiring
    {T : Type*} [Dioid T] : IdemCommSemiring T where
  toCommSemiring := instCommSemiring
  toSemilatticeSup := instSemilatticeSup
  toOrderBot := instOrderBot
  add_eq_sup _ _ := rfl

end Bridge

example {T : Type*} [Dioid T] (a b : T) :
    a ≼ₒ a ⊕ₒ b := le_sup_left

example {T : Type*} [Dioid T] (a b : T) :
    b ≼ₒ a ⊕ₒ b := le_sup_right

example {T : Type*} [Dioid T] {a b c : T}
    (hac : a ≼ₒ c) (hbc : b ≼ₒ c) :
    a ⊕ₒ b ≼ₒ c := sup_le hac hbc

example {T : Type*} [Dioid T] (a : T) : εₒ ≼ₒ a := bot_le

/-- Isotony of `⊕ₒ` on the right. -/
theorem add_le_add_right {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (a ⊕ₒ c) ≼ₒ (b ⊕ₒ c) :=
  sup_le_sup_right h c

/-- Isotony of `⊕ₒ` on the left. -/
theorem add_le_add_left {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (c ⊕ₒ a) ≼ₒ (c ⊕ₒ b) :=
  sup_le_sup_left h c

/-- Isotony of `⊗ₒ` on the right. -/
theorem mul_le_mul_right {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (a ⊗ₒ c) ≼ₒ (b ⊗ₒ c) := by
  gcongr

/-- Isotony of `⊗ₒ` on the left. -/
theorem mul_le_mul_left {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (c ⊗ₒ a) ≼ₒ (c ⊗ₒ b) := by
  gcongr

end Algebra

end DeepWiki
