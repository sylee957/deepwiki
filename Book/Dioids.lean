import VersoManual
import Mathlib.Algebra.Order.Kleene
import Mathlib.Order.CompleteLattice.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Dioids and complete dioids" =>
This chapter formalizes the algebra of _dioids_, the _canonical order_
they induce, the order properties and isotony, and the _complete dioid_
that adds completeness and lower semi-continuity.

All declarations live in the `NetworkCalculus` namespace.

```lean
namespace NetworkCalculus

open scoped Computability
-- `add_eq_sup : a + b = a ⊔ b`
```

# A dioid, defined from scratch
Rather than _start_ from Mathlib's algebraic hierarchy, we build the
dioid axioms ourselves, bottom-up, following the classical
definitions — a monoid, then a commutative idempotent monoid, then a
semi-ring, then a dioid — and only afterwards _link_ the result to
Mathlib so its order theory and lemmas become available.

In Lean code we write the dioid sum $`\oplus` as `⊕`, the product
$`\otimes` as `⊗`, the additive neutral $`\mathbf{0}` as `ε`, and the
multiplicative neutral $`\mathbf{1}` as `e`. The additive and
multiplicative operators live in separate carrier classes so a single
type can host both.

The notations `⊕ ⊗ ε e` are _scoped_ (under `DioidNotation`), so they
stay confined to this chapter — the names `e`/`ε` remain free elsewhere,
and the symbol `⊕` (which Lean otherwise reads as the disjoint-union
type `Sum`) only takes its dioid meaning where the scope is open. The
sum notation is given high priority so the elaborator prefers it over
`Sum`; where a nested `a ⊕ b` sits in an equation with no surrounding
`⊗` to fix its type, the left-hand side is ascribed `: D` to keep the
elaborator from drifting toward the `Sum` reading.

The whole tower lives in the `Algebra` sub-namespace, so our class names
(`AddMonoid`, `Semiring`, `Dioid`, …) do not shadow Mathlib's identically
named classes elsewhere in the development.

```lean
namespace Algebra

/-- The additive operator `⊕` and its neutral `ε`. -/
class OplusNeutral (D : Type*) where
  /-- The dioid sum. -/
  oplus : D → D → D
  /-- The dioid zero. -/
  eps : D

/-- The multiplicative operator `⊗` and its neutral `e`. -/
class OtimesNeutral (D : Type*) where
  /-- The dioid product. -/
  otimes : D → D → D
  /-- The dioid unit. -/
  one : D

namespace DioidNotation
scoped infixl:65 (priority := high) " ⊕ " =>
  OplusNeutral.oplus
scoped notation "ε" => OplusNeutral.eps
scoped infixl:70 " ⊗ " => OtimesNeutral.otimes
scoped notation "e" => OtimesNeutral.one
end DioidNotation

open scoped DioidNotation
```

A _monoid_ $`(D, \oplus, \varepsilon)`: $`\oplus` is associative with a
two-sided neutral $`\varepsilon`.

```lean
/-- `(D, ⊕)` is a monoid with neutral `ε`. -/
class AddMonoid (D : Type*) extends OplusNeutral D where
  oplus_assoc :
    ∀ a b c : D, ((a ⊕ b) ⊕ c : D) = a ⊕ (b ⊕ c)
  eps_oplus : ∀ a : D, (ε ⊕ a : D) = a
  oplus_eps : ∀ a : D, (a ⊕ ε : D) = a
```

A _commutative_ monoid, then an _idempotent_ one
($`a \oplus a = a`):

```lean
/-- `(D, ⊕)` is a commutative monoid. -/
class AddCommMonoid (D : Type*) extends AddMonoid D where
  oplus_comm : ∀ a b : D, (a ⊕ b : D) = b ⊕ a

/-- `(D, ⊕)` is an idempotent commutative monoid. -/
class AddIdemCommMonoid (D : Type*) extends
    AddCommMonoid D where
  oplus_idem : ∀ a : D, (a ⊕ a : D) = a
```

The multiplicative monoid $`(D, \otimes, e)`:

```lean
/-- `(D, ⊗)` is a monoid with neutral `e`. -/
class MulMonoid (D : Type*) extends OtimesNeutral D where
  otimes_assoc : ∀ a b c : D, (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)
  one_otimes : ∀ a : D, e ⊗ a = a
  otimes_one : ∀ a : D, a ⊗ e = a
```

A _semi-ring_ $`(D, \oplus, \otimes)`: an idempotent commutative additive
monoid and a multiplicative monoid, with $`\otimes` distributing over
$`\oplus` on both sides and $`\varepsilon` absorbing for $`\otimes`. A
_dioid_ adds commutativity of $`\otimes`.

```lean
/-- A semi-ring: distributive, with `ε` absorbing. -/
class Semiring (D : Type*) extends
    AddIdemCommMonoid D, MulMonoid D where
  left_distrib :
    ∀ a b c : D, a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)
  right_distrib :
    ∀ a b c : D, (a ⊕ b) ⊗ c = (a ⊗ c) ⊕ (b ⊗ c)
  eps_otimes : ∀ a : D, ε ⊗ a = ε
  otimes_eps : ∀ a : D, a ⊗ ε = ε

/-- A dioid: a semi-ring with commutative product. -/
class Dioid (D : Type*) extends Semiring D where
  otimes_comm : ∀ a b : D, a ⊗ b = b ⊗ a
```

The combined distributivity over a binary sum on each side gives the
quaternary form $`(a \oplus b) \otimes (c \oplus d) = (a \otimes c) \oplus (b \otimes c) \oplus (a \otimes d) \oplus (b \otimes d)`:

```lean
theorem quaternary_distrib {D : Type*} [Semiring D]
    (a b c d : D) :
    (a ⊕ b) ⊗ (c ⊕ d)
      = (a ⊗ c) ⊕ (b ⊗ c) ⊕ (a ⊗ d) ⊕ (b ⊗ d) := by
  set p := a ⊗ c; set q := b ⊗ c
  set r := a ⊗ d; set s := b ⊗ d
  have hexp : (a ⊕ b) ⊗ (c ⊕ d) = (p ⊕ r) ⊕ (q ⊕ s) := by
    rw [Semiring.right_distrib, Semiring.left_distrib,
      Semiring.left_distrib]
  rw [hexp, AddMonoid.oplus_assoc p q r,
    AddMonoid.oplus_assoc p (q ⊕ r) s,
    AddMonoid.oplus_assoc p r (q ⊕ s)]
  congr 1
  rw [AddCommMonoid.oplus_comm q r,
    AddMonoid.oplus_assoc r q s]
```

# Linking to Mathlib
We now connect our `Dioid` to Mathlib. First, the pure-algebra bridge:
a `Dioid` is a Mathlib `CommSemiring`, mapping
$`\oplus \mapsto {+}`, $`\otimes \mapsto {*}`, $`\varepsilon \mapsto 0`,
$`e \mapsto 1`. The scalar action `n • a` is given in closed form so it
needs no pre-existing `Add`/`Zero` instance during assembly.

```lean
/-- `n • a = a ⊕ ⋯ ⊕ a` (`n` times). -/
def nsmulT {D : Type*} [OplusNeutral D] : ℕ → D → D
  | 0, _ => ε
  | (n + 1), a => nsmulT n a ⊕ a

/-- A `Dioid` is a Mathlib `CommSemiring`. -/
@[reducible] def Dioid.toCommSemiring (D : Type*)
    [Dioid D] : CommSemiring D where
  add := OplusNeutral.oplus
  add_assoc := AddMonoid.oplus_assoc
  zero := OplusNeutral.eps
  zero_add := AddMonoid.eps_oplus
  add_zero := AddMonoid.oplus_eps
  add_comm := AddCommMonoid.oplus_comm
  nsmul := nsmulT
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  mul := OtimesNeutral.otimes
  mul_assoc := MulMonoid.otimes_assoc
  one := OtimesNeutral.one
  one_mul := MulMonoid.one_otimes
  mul_one := MulMonoid.otimes_one
  mul_comm := Dioid.otimes_comm
  left_distrib := Semiring.left_distrib
  right_distrib := Semiring.right_distrib
  zero_mul := Semiring.eps_otimes
  mul_zero := Semiring.otimes_eps
```

A dioid's _canonical order_ is $`a \preceq b :\Leftrightarrow a \oplus b = b`. The carriers of later chapters need a _specific_ order
(transported, reversed), not one re-derived from the algebra, so the
order-bearing class `OrderedDioid` bundles a `Lattice` and an `OrderBot`
together with the algebra, tied by $`a \oplus b = a \sqcup b`. The bridge
then _supplies_ this order to Mathlib's `IdemCommSemiring` — the order
Mathlib sees is exactly the carried one, so no competing order is
introduced.

```lean
/-- A dioid carrying its canonical order as data. -/
class OrderedDioid (D : Type*) extends
    Dioid D, Lattice D, OrderBot D where
  add_eq_sup : ∀ a b : D, (a ⊕ b : D) = a ⊔ b

/-- The Mathlib `IdemCommSemiring` of an `OrderedDioid`,
supplied with the carried order (not a derived one). -/
@[reducible]
noncomputable def OrderedDioid.toIdemCommSemiring
    (D : Type*) [OrderedDioid D] : IdemCommSemiring D :=
  { Dioid.toCommSemiring D,
    (inferInstance : Lattice D),
    (inferInstance : OrderBot D) with
    add_eq_sup := OrderedDioid.add_eq_sup }

end Algebra
```

# The Mathlib interface `IdemDioid`
Downstream, we work through Mathlib's `IdemCommSemiring`, which is
exactly an idempotent commutative semiring whose order is _defined_ by
$`a \le b \iff a + b = b`, with $`a + b = a \sqcup b`. Our `OrderedDioid`
bridges to it, so a dioid is — once linked — precisely an
`IdemCommSemiring`. We name that interface `IdemDioid`; the carriers of
later chapters target it.

```lean
abbrev IdemDioid (α : Type*) := IdemCommSemiring α
```

The notation maps to Lean as $`\oplus = {+}`, $`\otimes = {*}`, $`\mathbf{0} = 0`,
$`\mathbf{1} = 1`, and the canonical order $`\preceq` as $`\le`.

We can build the interface from the algebra alone: given a commutative
semiring whose sum is idempotent, this manufactures the entire
structure with the order _derived_, not supplied, via Mathlib's
`IdemSemiring.ofSemiring`. An instance constructed this way _cannot_
invent an unrelated order: $`\preceq`, $`\sqcup`, $`\bot` are forced to be
$`a \oplus b = b`, $`\oplus`, $`\mathbf{0}`.

```lean
namespace IdemDioid

abbrev ofCommSemiring {α : Type*} [CommSemiring α]
    (add_idem : ∀ a : α, a + a = a) : IdemDioid α :=
  { IdemSemiring.ofSemiring add_idem with
    mul_comm := mul_comm }

end IdemDioid
```

# The canonical order
Idempotency of $`\oplus` induces the _canonical order_ $`a \preceq b \;:\Leftrightarrow\; a \oplus b = b`.
The order is _derived_ from the algebra, not supplied independently. The
order/isotony lemmas below are collected in the `Dioid` namespace (so
later chapters reach them as `Dioid.mul_le_mul_right'`, etc.) and are
stated for the `IdemDioid` interface.

*Theorem:* $`a \preceq b \iff a \oplus b = b`

```lean
namespace Dioid

theorem le_iff_add_eq_right
    {α : Type*} [IdemDioid α] {a b : α} :
    a ≤ b ↔ a + b = b :=
  add_eq_right_iff_le.symm
```

# Order relation and isotony
The canonical relation is a partial order, and both operations are
isotone with respect to it. Each part is restated and proved directly
from the semiring laws.

_Reflexivity_, from idempotency $`a \oplus a = a`:

*Theorem:* $`a \preceq a`

```lean
theorem le_refl' {α : Type*} [IdemDioid α] (a : α) :
    a ≤ a :=
  le_iff_add_eq_right.mpr (add_idem a)
```

_Transitivity_, via
$$`a \oplus c = a \oplus (b \oplus c) = (a \oplus b) \oplus c = b \oplus c = c`

*Theorem:* $`a \preceq b \;\wedge\; b \preceq c \;\Rightarrow\; a \preceq c`

```lean
theorem le_trans' {α : Type*} [IdemDioid α] {a b c : α}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [le_iff_add_eq_right] at hab hbc ⊢
  calc a + c = a + (b + c) := by rw [hbc]
    _ = (a + b) + c := by rw [add_assoc]
    _ = b + c := by rw [hab]
    _ = c := hbc
```

_Antisymmetry_: if $`a \preceq b` and $`b \preceq a` then $`a \oplus b = a = b`.

*Theorem:* $`a \preceq b \;\wedge\; b \preceq a \;\Rightarrow\; a = b`

```lean
theorem le_antisymm' {α : Type*} [IdemDioid α] {a b : α}
    (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [le_iff_add_eq_right] at hab hba
  rw [← hab, add_comm, hba]
```

_Isotony of the sum_ $`\oplus`: if $`a \preceq b` then $`a \oplus c \preceq b \oplus c`, since
$`(a \oplus c) \oplus (b \oplus c) = (a \oplus b) \oplus (c \oplus c) = b \oplus c`.

*Theorem:* $`a \preceq b \;\Rightarrow\; a \oplus c \preceq b \oplus c`

```lean
theorem add_le_add_right'
    {α : Type*} [IdemDioid α] {a b : α}
    (h : a ≤ b) (c : α) : a + c ≤ b + c := by
  rw [le_iff_add_eq_right] at h ⊢
  calc (a + c) + (b + c)
      = (a + b) + (c + c) := by ac_rfl
    _ = b + c := by rw [h, add_idem]
```

The left-handed form follows by commutativity:

*Theorem:* $`a \preceq b \;\Rightarrow\; c \oplus a \preceq c \oplus b`

```lean
theorem add_le_add_left'
    {α : Type*} [IdemDioid α] {a b : α}
    (h : a ≤ b) (c : α) : c + a ≤ c + b := by
  rw [add_comm c, add_comm c]
  exact add_le_add_right' h c
```

_Isotony of the product_ $`\otimes`: if $`a \preceq b` then $`a \otimes c \preceq b \otimes c`, since
$`(a \otimes c) \oplus (b \otimes c) = (a \oplus b) \otimes c = b \otimes c`.

*Theorem:* $`a \preceq b \;\Rightarrow\; a \otimes c \preceq b \otimes c`

```lean
theorem mul_le_mul_right'
    {α : Type*} [IdemDioid α] {a b : α}
    (h : a ≤ b) (c : α) : a * c ≤ b * c := by
  rw [le_iff_add_eq_right] at h ⊢
  rw [← add_mul, h]
```

And the left form, by commutativity:

*Theorem:* $`a \preceq b \;\Rightarrow\; c \otimes a \preceq c \otimes b`

```lean
theorem mul_le_mul_left'
    {α : Type*} [IdemDioid α] {a b : α}
    (h : a ≤ b) (c : α) : c * a ≤ c * b := by
  rw [le_iff_add_eq_right] at h ⊢
  rw [← mul_add, h]
```

```lean
end Dioid
```

# The complete dioid
A _complete dioid_ is a dioid that is moreover a complete lattice for
the canonical order, and whose product $`\otimes` is _lower semi-continuous_:
it distributes over _arbitrary_ sums $`\oplus` on both sides. This is the
identity $`R_a\bigl(\bigoplus x\bigr) = \bigoplus R_a(x)`. The class extends both
the idempotent commutative semiring and a `CompleteLattice`, sharing
the same canonical order. Distributivity is stated over an arbitrary
`Set` to stay in `α`'s universe; the indexed `⨆` forms are derived.

```lean
class CompleteDioid (α : Type*) extends
    IdemCommSemiring α, CompleteLattice α where
  /-- `⊗` distributes over arbitrary `⊕`
  (lower semi-continuity). Stated on the
  left; the right version follows by commutativity
  of `⊗`. -/
  mul_sSup : ∀ (a : α) (s : Set α),
    a * sSup s = ⨆ b ∈ s, a * b
```

The single distributivity field, stated over an arbitrary set on the
left, is `mul_sSup`. Right distributivity is _derived_ from it and
commutativity of $`\otimes`, so it need not be a separate axiom:

*Theorem:* $`\Bigl(\bigsqcup_{b \in s} b\Bigr) \otimes a = \bigsqcup_{b \in s} b \otimes a`

```lean
namespace CompleteDioid

theorem sSup_mul {α : Type*} [CompleteDioid α]
    (a : α) (s : Set α) :
    sSup s * a = ⨆ b ∈ s, b * a := by
  rw [mul_comm, mul_sSup]; simp_rw [mul_comm a]
```

The indexed forms `mul_iSup`/`iSup_mul` follow from `mul_sSup`/
`sSup_mul`:

*Theorem:* $`a \otimes \bigsqcup_i g(i) = \bigsqcup_i a \otimes g(i)` and $`\Bigl(\bigsqcup_i g(i)\Bigr) \otimes a = \bigsqcup_i g(i) \otimes a`

```lean
theorem mul_iSup {α : Type*} [CompleteDioid α]
    {ι : Sort*} (a : α) (g : ι → α) :
    a * ⨆ i, g i = ⨆ i, a * g i := by
  rw [← sSup_range, mul_sSup, iSup_range]

theorem iSup_mul {α : Type*} [CompleteDioid α]
    {ι : Sort*} (g : ι → α) (a : α) :
    (⨆ i, g i) * a = ⨆ i, g i * a := by
  rw [← sSup_range, sSup_mul, iSup_range]
```

The binary special cases distribute $`\otimes` over $`\oplus = \sqcup`:

*Theorem:* $`a \otimes (b \sqcup c) = (a \otimes b) \sqcup (a \otimes c)` and $`(b \sqcup c) \otimes a = (b \otimes a) \sqcup (c \otimes a)`

```lean
theorem mul_sup {α : Type*} [CompleteDioid α]
    (a b c : α) :
    a * (b ⊔ c) = a * b ⊔ a * c := by
  have h1 : (⨆ i : Bool, cond i b c) = b ⊔ c := by
    simp [iSup_bool_eq]
  have h2 :
      (⨆ i : Bool, a * cond i b c)
        = a * b ⊔ a * c := by
    simp [iSup_bool_eq]
  rw [← h1, mul_iSup, h2]

theorem sup_mul {α : Type*} [CompleteDioid α]
    (a b c : α) :
    (b ⊔ c) * a = b * a ⊔ c * a := by
  have h1 : (⨆ i : Bool, cond i b c) = b ⊔ c := by
    simp [iSup_bool_eq]
  have h2 :
      (⨆ i : Bool, cond i b c * a)
        = b * a ⊔ c * a := by
    simp [iSup_bool_eq]
  rw [← h1, iSup_mul, h2]

end CompleteDioid
```

Isotony needs no completeness; it is available here
through the `Dioid` superclass.

```lean
end NetworkCalculus
```
