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

# The dioid
A _dioid_ is a semiring $`(D, \oplus, \otimes, \mathbf{0}, \mathbf{1})` whose sum $`\oplus` is
_idempotent_, $`a \oplus a = a`. We work in the commutative case. Mathlib's
`IdemCommSemiring` is exactly an idempotent commutative semiring whose
order is _defined_ by $`a \le b \iff a + b = b`, with $`a + b = a \sqcup b`. So a
dioid is precisely an `IdemCommSemiring`: the algebra comes first, the
order is derived from it.

```lean
abbrev Dioid (α : Type*) := IdemCommSemiring α
```

The notation maps to Lean as $`\oplus = {+}`, $`\otimes = {*}`, $`\mathbf{0} = 0`,
$`\mathbf{1} = 1`, and the canonical order $`\preceq` as $`\le`.

We can build a dioid from the algebra alone: given a commutative
semiring whose sum is idempotent, this manufactures the entire
structure with the order _derived_, not supplied, via Mathlib's
`IdemSemiring.ofSemiring`. An instance constructed this way _cannot_
invent an unrelated order: $`\preceq`, $`\sqcup`, $`\bot` are forced to be
$`a \oplus b = b`, $`\oplus`, $`\mathbf{0}`.

```lean
namespace Dioid

abbrev ofCommSemiring {α : Type*} [CommSemiring α]
    (add_idem : ∀ a : α, a + a = a) : Dioid α :=
  { IdemSemiring.ofSemiring add_idem with
    mul_comm := mul_comm }
```

# The canonical order
Idempotency of $`\oplus` induces the _canonical order_ $`a \preceq b \;:\Leftrightarrow\; a \oplus b = b`.
The order is _derived_ from the algebra, not supplied independently:

```lean
theorem le_iff_add_eq_right
    {α : Type*} [Dioid α] {a b : α} :
    a ≤ b ↔ a + b = b :=
  add_eq_right_iff_le.symm
```

*Proof.* Definitional: $`a \preceq b :\Leftrightarrow a \oplus b = b`. $`\quad\blacksquare`

# Order relation and isotony
The canonical relation is a partial order, and both operations are
isotone with respect to it. Each part is restated and proved directly
from the semiring laws.

_Reflexivity_, from idempotency $`a \oplus a = a`:

```lean
theorem le_refl' {α : Type*} [Dioid α] (a : α) :
    a ≤ a :=
  le_iff_add_eq_right.mpr (add_idem a)
```

*Proof.* $`a \preceq a \Leftrightarrow a \oplus a = a` (idempotency). $`\quad\blacksquare`

_Transitivity_, via
$$`a \oplus c = a \oplus (b \oplus c) = (a \oplus b) \oplus c = b \oplus c = c`

```lean
theorem le_trans' {α : Type*} [Dioid α] {a b c : α}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [le_iff_add_eq_right] at hab hbc ⊢
  calc a + c = a + (b + c) := by rw [hbc]
    _ = (a + b) + c := by rw [add_assoc]
    _ = b + c := by rw [hab]
    _ = c := hbc
```

*Proof.* From $`a \oplus b = b`, $`b \oplus c = c`:
$$`a \oplus c = a \oplus (b \oplus c) = (a \oplus b) \oplus c = b \oplus c = c. \quad\blacksquare`

_Antisymmetry_: if $`a \preceq b` and $`b \preceq a` then $`a \oplus b = a = b`.

```lean
theorem le_antisymm' {α : Type*} [Dioid α] {a b : α}
    (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [le_iff_add_eq_right] at hab hba
  rw [← hab, add_comm, hba]
```

*Proof.* From $`a \oplus b = b`, $`b \oplus a = a`:
$$`b = a \oplus b = b \oplus a = a. \quad\blacksquare`

_Isotony of the sum_ $`\oplus`: if $`a \preceq b` then $`a \oplus c \preceq b \oplus c`, since
$`(a \oplus c) \oplus (b \oplus c) = (a \oplus b) \oplus (c \oplus c) = b \oplus c`.

```lean
theorem add_le_add_right'
    {α : Type*} [Dioid α] {a b : α}
    (h : a ≤ b) (c : α) : a + c ≤ b + c := by
  rw [le_iff_add_eq_right] at h ⊢
  calc (a + c) + (b + c)
      = (a + b) + (c + c) := by ac_rfl
    _ = b + c := by rw [h, add_idem]
```

*Proof.* From $`a \oplus b = b`, with $`c \oplus c = c`:
$$`(a \oplus c) \oplus (b \oplus c) = (a \oplus b) \oplus (c \oplus c) = b \oplus c. \quad\blacksquare`

The left-handed form $`a \preceq b \Rightarrow c \oplus a \preceq c \oplus b` follows by commutativity:

```lean
theorem add_le_add_left'
    {α : Type*} [Dioid α] {a b : α}
    (h : a ≤ b) (c : α) : c + a ≤ c + b := by
  rw [add_comm c, add_comm c]
  exact add_le_add_right' h c
```

*Proof.* $`c \oplus a = a \oplus c \preceq b \oplus c = c \oplus b` by commutativity and the right form. $`\quad\blacksquare`

_Isotony of the product_ $`\otimes`: if $`a \preceq b` then $`a \otimes c \preceq b \otimes c`, since
$`(a \otimes c) \oplus (b \otimes c) = (a \oplus b) \otimes c = b \otimes c`.

```lean
theorem mul_le_mul_right'
    {α : Type*} [Dioid α] {a b : α}
    (h : a ≤ b) (c : α) : a * c ≤ b * c := by
  rw [le_iff_add_eq_right] at h ⊢
  rw [← add_mul, h]
```

*Proof.* From $`a \oplus b = b`, by right-distributivity:
$$`(a \otimes c) \oplus (b \otimes c) = (a \oplus b) \otimes c = b \otimes c. \quad\blacksquare`

And the left form $`a \preceq b \Rightarrow c \otimes a \preceq c \otimes b`, since $`(c \otimes a) \oplus (c \otimes b) = c \otimes (a \oplus b) = c \otimes b`:

```lean
theorem mul_le_mul_left'
    {α : Type*} [Dioid α] {a b : α}
    (h : a ≤ b) (c : α) : c * a ≤ c * b := by
  rw [le_iff_add_eq_right] at h ⊢
  rw [← mul_add, h]
```

*Proof.* From $`a \oplus b = b`, by left-distributivity:
$$`(c \otimes a) \oplus (c \otimes b) = c \otimes (a \oplus b) = c \otimes b. \quad\blacksquare`

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

```lean
namespace CompleteDioid

theorem sSup_mul {α : Type*} [CompleteDioid α]
    (a : α) (s : Set α) :
    sSup s * a = ⨆ b ∈ s, b * a := by
  rw [mul_comm, mul_sSup]; simp_rw [mul_comm a]
```

*Proof.* By commutativity and `mul_sSup`:
$$`\Bigl(\bigsqcup_{b \in s} b\Bigr) \otimes a = a \otimes \bigsqcup_{b \in s} b = \bigsqcup_{b \in s} a \otimes b = \bigsqcup_{b \in s} b \otimes a. \quad\blacksquare`

The indexed forms `mul_iSup`/`iSup_mul` follow from `mul_sSup`/
`sSup_mul`:

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

*Proof.* Writing $`\bigsqcup_i g(i) = \bigsqcup\,(\operatorname{ran} g)` and applying `mul_sSup` (resp. `sSup_mul`):
$$`a \otimes \bigsqcup_i g(i) = \bigsqcup_i a \otimes g(i), \qquad \Bigl(\bigsqcup_i g(i)\Bigr) \otimes a = \bigsqcup_i g(i) \otimes a. \quad\blacksquare`

The binary special cases distribute $`\otimes` over $`\oplus = \sqcup`:

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

*Proof.* A binary join is a supremum over $`\{0,1\}`; by `mul_iSup` (resp. `iSup_mul`):
$$`a \otimes (b \sqcup c) = (a \otimes b) \sqcup (a \otimes c), \qquad (b \sqcup c) \otimes a = (b \otimes a) \sqcup (c \otimes a). \quad\blacksquare`

Isotony needs no completeness; it is available here
through the `Dioid` superclass.

```lean
end NetworkCalculus
```
