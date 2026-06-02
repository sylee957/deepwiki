import VersoManual
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Order.Kleene

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Signatures and the additive monoid" =>
The dioid tower begins with the bare _operation signatures_ — a sum
$`\oplus` and a product $`\otimes`, each with a neutral — and the first
algebraic layer over them, the additive monoid. This chapter isolates
that foundation: the signatures, the $`\oplus`-monoid, and the _bridge_
that exhibits it as one of `Mathlib`'s additive monoids.

All declarations live in the `NetworkCalculus` namespace.

```lean
namespace NetworkCalculus
```

# Operation signatures

The tower is built as a chain of _type classes_ over a carrier $`T`.
The operations are recovered by instance resolution, so the glyphs
$`\oplus` and $`\otimes` need no tag — we write them `⊕ₒ` and `⊗ₒ`.

*Definition:* a _sum signature_ on a carrier $`T` is a binary
$`\oplus : T \times T \to T` with a neutral $`\varepsilon`.

```lean
namespace Algebra

class Oplus (T : Type*) where
  oplus : T → T → T
  eps : T

class Otimes (T : Type*) where
  otimes : T → T → T
  one : T

scoped infixl:65 " ⊕ₒ " => Oplus.oplus
scoped infixl:70 " ⊗ₒ " => Otimes.otimes
scoped notation "εₒ" => Oplus.eps
scoped notation "eₒ" => Otimes.one
```

Each signature already carries `Mathlib`'s lawless `Add`/`Zero` and
`Mul`/`One`: $`\oplus, \varepsilon` are the addition and its neutral,
$`\otimes, e` the multiplication and its unit. So $`\oplus = {+}` and
$`\otimes = {*}` definitionally from the start; the monoid bridges
below only add the laws.

```lean
namespace Bridge

scoped instance instAdd {T : Type*} [Oplus T] :
    Add T where add := Oplus.oplus
scoped instance instZero {T : Type*} [Oplus T] :
    Zero T where zero := Oplus.eps
scoped instance instMul {T : Type*} [Otimes T] :
    Mul T where mul := Otimes.otimes
scoped instance instOne {T : Type*} [Otimes T] :
    One T where one := Otimes.one

end Bridge
```

*Definition:* a _product signature_ on $`T` is a binary
$`\otimes : T \times T \to T` with a neutral $`e`.

# The monoid

## The additive monoid

*Definition:* $`(T, \oplus, \varepsilon)` is a _monoid_:
$$`(a \oplus b) \oplus c = a \oplus (b \oplus c), \quad \varepsilon \oplus a = a, \quad a \oplus \varepsilon = a.`

```lean
class AddMonoid (T : Type*) extends Oplus T where
  oplus_assoc : ∀ a b c : T,
    (a ⊕ₒ b) ⊕ₒ c = a ⊕ₒ (b ⊕ₒ c)
  eps_oplus : ∀ a : T, εₒ ⊕ₒ a = a
  oplus_eps : ∀ a : T, a ⊕ₒ εₒ = a
```

```lean
namespace Bridge

scoped instance instAddMonoid
    {T : Type*} [AddMonoid T] : _root_.AddMonoid T where
  toAdd := instAdd
  toZero := instZero
  add_assoc := AddMonoid.oplus_assoc
  zero_add := AddMonoid.eps_oplus
  add_zero := AddMonoid.oplus_eps
  nsmul n a :=
    n.rec Oplus.eps (fun _ acc => Oplus.oplus acc a)

end Bridge
```

## The multiplicative monoid

The product carries the same monoid structure, over the $`\otimes`
signature with neutral $`e`.

*Definition:* $`(T, \otimes, e)` is a _monoid_:
$$`(a \otimes b) \otimes c = a \otimes (b \otimes c), \quad e \otimes a = a, \quad a \otimes e = a.`

```lean
class MulMonoid (T : Type*) extends Otimes T where
  otimes_assoc : ∀ a b c : T,
    (a ⊗ₒ b) ⊗ₒ c = a ⊗ₒ (b ⊗ₒ c)
  one_otimes : ∀ a : T, eₒ ⊗ₒ a = a
  otimes_one : ∀ a : T, a ⊗ₒ eₒ = a
```

```lean
namespace Bridge

scoped instance instMulMonoid
    {T : Type*} [MulMonoid T] : _root_.Monoid T where
  toMul := instMul
  toOne := instOne
  mul_assoc := MulMonoid.otimes_assoc
  one_mul := MulMonoid.one_otimes
  mul_one := MulMonoid.otimes_one
  npow n a :=
    n.rec Otimes.one (fun _ acc => Otimes.otimes acc a)

end Bridge
```

# The commutative monoid

*Definition:* a _commutative_ monoid adds $`a \oplus b = b \oplus a`.

```lean
class AddCommMonoid (T : Type*) extends AddMonoid T where
  oplus_comm : ∀ a b : T, a ⊕ₒ b = b ⊕ₒ a
```

```lean
namespace Bridge

scoped instance instAddCommMonoid
    {T : Type*} [AddCommMonoid T] :
    _root_.AddCommMonoid T where
  toAddMonoid := instAddMonoid
  add_comm := AddCommMonoid.oplus_comm

end Bridge
```

# The semi-ring

*Definition:* a _semi-ring_ is a commutative $`\oplus`-monoid and a $`\otimes`-monoid with
$$`a \otimes (b \oplus c) = (a \otimes b) \oplus (a \otimes c), \quad (a \oplus b) \otimes c = (a \otimes c) \oplus (b \otimes c),`
$$`\varepsilon \otimes a = \varepsilon, \quad a \otimes \varepsilon = \varepsilon.`

```lean
class Semiring (T : Type*) extends
    AddCommMonoid T, MulMonoid T where
  left_distrib : ∀ a b c : T,
    a ⊗ₒ (b ⊕ₒ c) = a ⊗ₒ b ⊕ₒ a ⊗ₒ c
  right_distrib : ∀ a b c : T,
    (a ⊕ₒ b) ⊗ₒ c = a ⊗ₒ c ⊕ₒ b ⊗ₒ c
  eps_otimes : ∀ a : T, εₒ ⊗ₒ a = εₒ
  otimes_eps : ∀ a : T, a ⊗ₒ εₒ = εₒ
```

```lean
namespace Bridge

scoped instance instSemiring
    {T : Type*} [Semiring T] : _root_.Semiring T where
  toAddCommMonoid := instAddCommMonoid
  toMonoid := instMulMonoid
  left_distrib := Semiring.left_distrib
  right_distrib := Semiring.right_distrib
  zero_mul := Semiring.eps_otimes
  mul_zero := Semiring.otimes_eps

end Bridge
```

# The commutative semi-ring

*Definition:* a _commutative semi-ring_ adds $`a \otimes b = b \otimes a`.

```lean
class CommSemiring (T : Type*) extends Semiring T where
  otimes_comm : ∀ a b : T, a ⊗ₒ b = b ⊗ₒ a
```

```lean
namespace Bridge

scoped instance instCommSemiring
    {T : Type*} [CommSemiring T] :
    _root_.CommSemiring T where
  toSemiring := instSemiring
  mul_comm := CommSemiring.otimes_comm

scoped instance instMulCommMonoid
    {T : Type*} [CommSemiring T] :
    _root_.CommMonoid T where
  toMonoid := instMulMonoid
  mul_comm := CommSemiring.otimes_comm

end Bridge
```

# The dioid

*Definition:* a _dioid_ is a commutative semi-ring whose sum is idempotent, $`a \oplus a = a`.

```lean
class Dioid (T : Type*) extends CommSemiring T where
  oplus_idem : ∀ a : T, a ⊕ₒ a = a
```

## The canonical order

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

## The partial order

```lean
namespace Bridge

scoped instance instPartialOrder
    {T : Type*} [Dioid T] : PartialOrder T where
  toLE := instLE
  le_refl a := Dioid.oplus_idem a
  le_trans a b c (hab : a ≼ₒ b) (hbc : b ≼ₒ c) := by
    show a ⊕ₒ c = c
    rw [← hbc, ← AddMonoid.oplus_assoc, hab]
  le_antisymm a b (hab : a ≼ₒ b) (hba : b ≼ₒ a) := by
    rw [← hab, AddCommMonoid.oplus_comm, hba]

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
    rw [← AddMonoid.oplus_assoc, Dioid.oplus_idem]
  le_sup_right a b := by
    show b ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
    rw [AddCommMonoid.oplus_comm a b,
        ← AddMonoid.oplus_assoc, Dioid.oplus_idem]
  sup_le a b c hac hbc := by
    show (a ⊕ₒ b) ⊕ₒ c = c
    rw [AddMonoid.oplus_assoc,
        (show b ⊕ₒ c = c from hbc),
        (show a ⊕ₒ c = c from hac)]

scoped instance instOrderBot
    {T : Type*} [Dioid T] : OrderBot T where
  bot := εₒ
  bot_le a := AddMonoid.eps_oplus a

scoped instance instIdemCommSemiring
    {T : Type*} [Dioid T] : IdemCommSemiring T where
  toCommSemiring := instCommSemiring
  toSemilatticeSup := instSemilatticeSup
  toOrderBot := instOrderBot
  add_eq_sup _ _ := rfl

end Bridge
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
  show a * c ≤ b * c
  gcongr
```

*Theorem:* $`a \preceq b \;\Rightarrow\; c \otimes a \preceq c \otimes b`

```lean
theorem mul_le_mul_left {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (c ⊗ₒ a) ≼ₒ (c ⊗ₒ b) := by
  show c * a ≤ c * b
  gcongr
```

```lean
end Algebra
```

```lean
end NetworkCalculus
```
