import VersoManual
import Mathlib.Algebra.Order.Kleene
import Mathlib.Order.CompleteLattice.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Dioids and complete dioids" =>

This chapter formalizes §2.1.1 of Bouillard, Boyer and Le Corronc:
the algebra of _dioids_, the _canonical order_ they induce, the order
properties and isotony of Theorem 2.1, and the _complete dioid_ that
adds completeness and lower semi-continuity.

All declarations live in the `NetworkCalculus` namespace.

```lean
namespace NetworkCalculus

open scoped Computability
-- `add_eq_sup : a + b = a ⊔ b`
```

# Definition 2.5: the dioid

A _dioid_ is a semiring `(D, ⊕, ⊗, 𝟘, 𝟙)` whose sum `⊕` is
_idempotent_, `a ⊕ a = a`. We work in the commutative case. Mathlib's
`IdemCommSemiring` is exactly an idempotent commutative semiring whose
order is _defined_ by `a ≤ b ↔ a + b = b`, with `a + b = a ⊔ b`. So a
dioid is precisely an `IdemCommSemiring`: the algebra comes first, the
order is derived from it.

```lean
abbrev Dioid (α : Type*) := IdemCommSemiring α
```

The book's notation maps to Lean as `⊕ = +`, `⊗ = *`, `𝟘 = 0`,
`𝟙 = 1`, and the canonical order `≼` as `≤`.

We can build a dioid from the algebra alone: given a commutative
semiring whose sum is idempotent, this manufactures the entire
structure with the order _derived_, not supplied, via Mathlib's
`IdemSemiring.ofSemiring`. An instance constructed this way _cannot_
invent an unrelated order: `≼`, `⊔`, `⊥` are forced to be
`a ⊕ b = b`, `⊕`, `𝟘`.

```lean
namespace Dioid

abbrev ofCommSemiring {α : Type*} [CommSemiring α]
    (add_idem : ∀ a : α, a + a = a) : Dioid α :=
  { IdemSemiring.ofSemiring add_idem with
    mul_comm := mul_comm }

variable {α : Type*} [Dioid α]
```

# The canonical order

Idempotency of `⊕` induces the _canonical order_ `a ≼ b :⟺ a ⊕ b = b`.
The order is _derived_ from the algebra, not supplied independently:

```lean
theorem le_iff_add_eq_right {a b : α} :
    a ≤ b ↔ a + b = b :=
  add_eq_right_iff_le.symm
```

# Theorem 2.1: order relation and isotony

The canonical relation is a partial order, and both operations are
isotone with respect to it. Each part is restated and proved directly
from the semiring laws.

_Reflexivity_, from idempotency `a ⊕ a = a`:

```lean
theorem le_refl' (a : α) : a ≤ a :=
  le_iff_add_eq_right.mpr (add_idem a)
```

_Transitivity_, following the book
`a ⊕ c = a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c = b ⊕ c = c`:

```lean
theorem le_trans' {a b c : α}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [le_iff_add_eq_right] at hab hbc ⊢
  calc a + c = a + (b + c) := by rw [hbc]
    _ = (a + b) + c := by rw [add_assoc]
    _ = b + c := by rw [hab]
    _ = c := hbc
```

_Antisymmetry_: if `a ≼ b` and `b ≼ a` then `a ⊕ b = a = b`.

```lean
theorem le_antisymm' {a b : α}
    (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [le_iff_add_eq_right] at hab hba
  rw [← hab, add_comm, hba]
```

_Isotony of the sum_ `⊕`: if `a ≼ b` then `a ⊕ c ≼ b ⊕ c`, since
`(a ⊕ c) ⊕ (b ⊕ c) = (a ⊕ b) ⊕ (c ⊕ c) = b ⊕ c`.

```lean
theorem add_le_add_right' {a b : α}
    (h : a ≤ b) (c : α) : a + c ≤ b + c := by
  rw [le_iff_add_eq_right] at h ⊢
  calc (a + c) + (b + c)
      = (a + b) + (c + c) := by ac_rfl
    _ = b + c := by rw [h, add_idem]
```

The left-handed form follows by commutativity:

```lean
theorem add_le_add_left' {a b : α}
    (h : a ≤ b) (c : α) : c + a ≤ c + b := by
  rw [add_comm c, add_comm c]
  exact add_le_add_right' h c
```

_Isotony of the product_ `⊗`: if `a ≼ b` then `a ⊗ c ≼ b ⊗ c`, since
`(a ⊗ c) ⊕ (b ⊗ c) = (a ⊕ b) ⊗ c = b ⊗ c`.

```lean
theorem mul_le_mul_right' {a b : α}
    (h : a ≤ b) (c : α) : a * c ≤ b * c := by
  rw [le_iff_add_eq_right] at h ⊢
  rw [← add_mul, h]
```

And the left form, since `(c ⊗ a) ⊕ (c ⊗ b) = c ⊗ (a ⊕ b) = c ⊗ b`:

```lean
theorem mul_le_mul_left' {a b : α}
    (h : a ≤ b) (c : α) : c * a ≤ c * b := by
  rw [le_iff_add_eq_right] at h ⊢
  rw [← mul_add, h]

end Dioid
```

# The complete dioid

A _complete dioid_ is a dioid that is moreover a complete lattice for
the canonical order, and whose product `⊗` is _lower semi-continuous_:
it distributes over _arbitrary_ sums `⊕` on both sides. This is the
boxed identity `Rₐ(⊕ x) = ⊕ Rₐ(x)` of §2.3.1. The class extends both
the idempotent commutative semiring and a `CompleteLattice`, sharing
the same canonical order. Distributivity is stated over an arbitrary
`Set` to stay in `α`'s universe; the indexed `⨆` forms are derived.

```lean
class CompleteDioid (α : Type*) extends
    IdemCommSemiring α, CompleteLattice α where
  /-- `⊗` distributes over arbitrary `⊕`
  (lower semi-continuity, §2.3.1). Stated on the
  left; the right version follows by commutativity
  of `⊗`. -/
  mul_sSup : ∀ (a : α) (s : Set α),
    a * sSup s = ⨆ b ∈ s, a * b
```

The single distributivity field, stated over an arbitrary set on the
left, is `mul_sSup`. Right distributivity is _derived_ from it and
commutativity of `⊗`, so it need not be a separate axiom:

```lean
namespace CompleteDioid

variable {α : Type*} [CompleteDioid α]

theorem sSup_mul (a : α) (s : Set α) :
    sSup s * a = ⨆ b ∈ s, b * a := by
  rw [mul_comm, mul_sSup]; simp_rw [mul_comm a]
```

The indexed forms `mul_iSup`/`iSup_mul` follow from `mul_sSup`/
`sSup_mul`:

```lean
theorem mul_iSup {ι : Sort*} (a : α) (g : ι → α) :
    a * ⨆ i, g i = ⨆ i, a * g i := by
  rw [← sSup_range, mul_sSup, iSup_range]

theorem iSup_mul {ι : Sort*} (g : ι → α) (a : α) :
    (⨆ i, g i) * a = ⨆ i, g i * a := by
  rw [← sSup_range, sSup_mul, iSup_range]
```

The binary special cases distribute `⊗` over `⊕ = ⊔`:

```lean
theorem mul_sup (a b c : α) :
    a * (b ⊔ c) = a * b ⊔ a * c := by
  have h1 : (⨆ i : Bool, cond i b c) = b ⊔ c := by
    simp [iSup_bool_eq]
  have h2 :
      (⨆ i : Bool, a * cond i b c)
        = a * b ⊔ a * c := by
    simp [iSup_bool_eq]
  rw [← h1, mul_iSup, h2]

theorem sup_mul (a b c : α) :
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

Isotony (Theorem 2.1) needs no completeness; it is available here
through the `Dioid` superclass.

```lean
end NetworkCalculus
```
