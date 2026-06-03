import VersoManual
import Book.Dioids
import Mathlib.Algebra.Order.Kleene

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The dioid order" =>
A dioid is canonically ordered by its idempotent sum. This chapter
introduces that order, identifies it with `Mathlib`'s `≤`, assembles
the partial order, lattice join, and bottom element — exhibiting the
dioid as one of `Mathlib`'s idempotent commutative semi-rings — and
proves isotony of the two operations.

```lean
namespace VerifiedWiki

namespace Algebra
```

# The canonical order

Every dioid carries a _canonical order_ read off from its sum: $`a` is
below $`b` exactly when adding $`a` to $`b` changes nothing. We take it
as `Mathlib`'s order relation $`\le` directly, so the canonical order
_is_ the partial order `Mathlib` reasons about, written `a ≼ₒ b`.

*Definition:* $`a \preceq b \iff a \oplus b = b`

```lean
namespace Bridge

theorem oplus_eq_add {T : Type*} [Dioid T] (a b : T) :
    a ⊕ₒ b = a + b := rfl

theorem otimes_eq_mul {T : Type*} [Dioid T] (a b : T) :
    a ⊗ₒ b = a * b := rfl

scoped instance instLE {T : Type*} [Dioid T] : LE T where
  le a b := a ⊕ₒ b = b

scoped notation:50 a:51 " ≼ₒ " b:51 => @LE.le _ instLE a b

end Bridge

open scoped Bridge
open Bridge (oplus_eq_add otimes_eq_mul)
```

# The partial order

```lean
namespace Bridge

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
```

The canonical order _is_ `Mathlib`'s $`\le`, so its three order laws
are `Mathlib`'s `le_refl`, `le_trans`, and `le_antisymm` directly — no
separate statements are needed, as the following confirm.

*Theorem:* $`a \preceq a`

```lean
example {T : Type*} [Dioid T] (a : T) : a ≼ₒ a :=
  le_refl a
```

*Theorem:* $`a \preceq b \;\wedge\; b \preceq c \;\Rightarrow\; a \preceq c`

```lean
example {T : Type*} [Dioid T] {a b c : T}
    (hab : a ≼ₒ b) (hbc : b ≼ₒ c) : a ≼ₒ c :=
  le_trans hab hbc
```

*Theorem:* $`a \preceq b \;\wedge\; b \preceq a \;\Rightarrow\; a = b`

```lean
example {T : Type*} [Dioid T] {a b : T}
    (hab : a ≼ₒ b) (hba : b ≼ₒ a) : a = b :=
  le_antisymm hab hba
```

# A dioid is an idempotent commutative semi-ring

Through the partial order, the dioid becomes one of `Mathlib`'s
_idempotent commutative semi-rings_ — the structure whose addition is
the lattice join. The sum is the binary join, $`a \sqcup b = a \oplus
b`, with the least-upper-bound laws following from idempotency; and the
sum neutral $`\varepsilon` is the least element $`\bot`. The final
instance then needs only that addition agrees with the join, which
holds by reflexivity.

```lean
namespace Bridge

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

scoped instance instOrderBot
    {T : Type*} [Dioid T] : OrderBot T where
  bot := εₒ
  bot_le a := zero_add a

scoped instance instIdemCommSemiring
    {T : Type*} [Dioid T] : IdemCommSemiring T where
  toCommSemiring := instCommSemiring
  toSemilatticeSup := instSemilatticeSup
  toOrderBot := instOrderBot
  add_eq_sup _ _ := rfl

end Bridge
```

The join laws are then `Mathlib`'s, recovered as facts about the dioid
sum: each summand is below the sum, and the sum is the least common
upper bound.

*Theorem:* $`a \preceq a \oplus b`

```lean
example {T : Type*} [Dioid T] (a b : T) :
    a ≼ₒ a ⊕ₒ b := le_sup_left
```

*Theorem:* $`b \preceq a \oplus b`

```lean
example {T : Type*} [Dioid T] (a b : T) :
    b ≼ₒ a ⊕ₒ b := le_sup_right
```

*Theorem:* $`a \preceq c \;\wedge\; b \preceq c \;\Rightarrow\; a \oplus b \preceq c`

```lean
example {T : Type*} [Dioid T] {a b c : T}
    (hac : a ≼ₒ c) (hbc : b ≼ₒ c) :
    a ⊕ₒ b ≼ₒ c := sup_le hac hbc
```

The sum neutral $`\varepsilon` is the least element $`\bot`: it lies
below everything, since $`\varepsilon \oplus a = a`.

*Theorem:* $`\varepsilon \preceq a`

```lean
example {T : Type*} [Dioid T] (a : T) : εₒ ≼ₒ a := bot_le
```

# Isotony

*Theorem:* $`a \preceq b \;\Rightarrow\; a \oplus c \preceq b \oplus c`

```lean
theorem add_le_add_right {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (a ⊕ₒ c) ≼ₒ (b ⊕ₒ c) :=
  sup_le_sup_right h c
```

*Theorem:* $`a \preceq b \;\Rightarrow\; c \oplus a \preceq c \oplus b`

```lean
theorem add_le_add_left {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (c ⊕ₒ a) ≼ₒ (c ⊕ₒ b) :=
  sup_le_sup_left h c
```

*Theorem:* $`a \preceq b \;\Rightarrow\; a \otimes c \preceq b \otimes c`

```lean
theorem mul_le_mul_right {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (a ⊗ₒ c) ≼ₒ (b ⊗ₒ c) := by
  gcongr
```

*Theorem:* $`a \preceq b \;\Rightarrow\; c \otimes a \preceq c \otimes b`

```lean
theorem mul_le_mul_left {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (c ⊗ₒ a) ≼ₒ (c ⊗ₒ b) := by
  gcongr
```

```lean
end Algebra
```

```lean
end VerifiedWiki
```
