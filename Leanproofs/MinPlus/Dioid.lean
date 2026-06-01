import Mathlib.Algebra.Order.Kleene

/-!
# Dioids (§2.1, Definitions 2.1–2.5; Theorem 2.1)

A **dioid** (Definition 2.5) is a semiring `(D, ⊕, ⊗, 𝟘, 𝟙)` whose sum `⊕` is **idempotent**
(`a ⊕ a = a`). Idempotency induces the **canonical order** `a ≼ b :⟺ a ⊕ b = b`, which is a
partial order with `⊕` as the join. Mathlib's `IdemCommSemiring` is exactly this: an idempotent
commutative semiring whose order is *defined* by `a ≤ b ↔ a + b = b` and for which `a + b = a ⊔ b`.
So we take `Dioid := IdemCommSemiring` — the algebra comes first, the order is derived from it.

The book's notation maps as:

| book        | `⊕` | `⊗` | `𝟘` | `𝟙` | `≼` |
|-------------|-----|-----|-----|-----|-----|
| here        | `+` | `*` | `0` | `1` | `≤` |

Completeness and lower semi-continuity are added in `Leanproofs.MinPlus.CompleteDioid`.
-/

namespace NetworkCalculus

open scoped Computability  -- `add_eq_sup : a + b = a ⊔ b`

/-- A **dioid** (Definition 2.5, commutative case): an idempotent commutative semiring. The sum
`⊕ = (+)` is idempotent (`add_idem`), and the canonical order `a ≼ b ↔ a ⊕ b = b` is *derived*
from the algebra (`Dioid.le_iff_add_eq_right`), with `⊕` the lattice join (`add_eq_sup`). -/
abbrev Dioid (α : Type*) := IdemCommSemiring α

namespace Dioid

/-- **Build a dioid from the algebra alone (Definition 2.5).** Given a commutative semiring whose
sum `⊕` is idempotent (`a ⊕ a = a`), this manufactures the entire structure with the order
**derived**, not supplied: `a ≼ b := a ⊕ b = b`, the join `⊔ := ⊕`, and the bottom `⊥ := 𝟘`, with
every order axiom proved from the semiring laws (via Mathlib's `IdemSemiring.ofSemiring`).

This makes the book's "the order is the canonical order induced by idempotency" literal: an
instance constructed this way *cannot* invent an unrelated order — `≼`, `⊔`, `⊥` are forced to be
`a ⊕ b = b`, `⊕`, `𝟘`. -/
abbrev ofCommSemiring {α : Type*} [CommSemiring α] (add_idem : ∀ a : α, a + a = a) : Dioid α :=
  { IdemSemiring.ofSemiring add_idem with mul_comm := mul_comm }

variable {α : Type*} [Dioid α]

/-- The **canonical order** of a dioid: `a ≼ b ↔ a ⊕ b = b` (Definition 2.5). -/
theorem le_iff_add_eq_right {a b : α} : a ≤ b ↔ a + b = b := add_eq_right_iff_le.symm

/-! ### Theorem 2.1 (Order relation of a dioid)

The canonical relation `a ≼ b :⟺ a ⊕ b = b` is an order relation, and `⊕`, `⊗` are isotone with
respect to it. Mathlib's `IdemCommSemiring` already *packages* the order as a `PartialOrder`, but
we restate Theorem 2.1's content explicitly, proved from the algebra exactly as in the book, so the
result is literal rather than implicit in the instance. -/

/-- **Theorem 2.1 — reflexivity.** `a ≼ a`, because `⊕` is idempotent (`a ⊕ a = a`). -/
theorem le_refl' (a : α) : a ≤ a := le_iff_add_eq_right.mpr (add_idem a)

/-- **Theorem 2.1 — transitivity.** Following the book:
`a ⊕ c = a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c = b ⊕ c = c`. -/
theorem le_trans' {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [le_iff_add_eq_right] at hab hbc ⊢
  calc a + c = a + (b + c) := by rw [hbc]
    _ = (a + b) + c := by rw [add_assoc]
    _ = b + c := by rw [hab]
    _ = c := hbc

/-- **Theorem 2.1 — antisymmetry.** If `a ≼ b` and `b ≼ a` then `a ⊕ b = a = b`. -/
theorem le_antisymm' {a b : α} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [le_iff_add_eq_right] at hab hba
  rw [← hab, add_comm, hba]

/-- **Theorem 2.1 — isotony of `⊕`.** If `a ≼ b` then `a ⊕ c ≼ b ⊕ c`, since
`(a ⊕ c) ⊕ (b ⊕ c) = (a ⊕ b) ⊕ (c ⊕ c) = b ⊕ c`. -/
theorem add_le_add_right' {a b : α} (h : a ≤ b) (c : α) : a + c ≤ b + c := by
  rw [le_iff_add_eq_right] at h ⊢
  calc (a + c) + (b + c) = (a + b) + (c + c) := by ac_rfl
    _ = b + c := by rw [h, add_idem]

/-- **Theorem 2.1 — isotony of `⊕` (left).** If `a ≼ b` then `c ⊕ a ≼ c ⊕ b`. -/
theorem add_le_add_left' {a b : α} (h : a ≤ b) (c : α) : c + a ≤ c + b := by
  rw [add_comm c, add_comm c]; exact add_le_add_right' h c

/-- **Theorem 2.1 — isotony of `⊗` (right).** If `a ≼ b` then `a ⊗ c ≼ b ⊗ c`, since
`(a ⊗ c) ⊕ (b ⊗ c) = (a ⊕ b) ⊗ c = b ⊗ c`. -/
theorem mul_le_mul_right' {a b : α} (h : a ≤ b) (c : α) : a * c ≤ b * c := by
  rw [le_iff_add_eq_right] at h ⊢
  rw [← add_mul, h]

/-- **Theorem 2.1 — isotony of `⊗` (left).** If `a ≼ b` then `c ⊗ a ≼ c ⊗ b`, since
`(c ⊗ a) ⊕ (c ⊗ b) = c ⊗ (a ⊕ b) = c ⊗ b`. -/
theorem mul_le_mul_left' {a b : α} (h : a ≤ b) (c : α) : c * a ≤ c * b := by
  rw [le_iff_add_eq_right] at h ⊢
  rw [← mul_add, h]

end Dioid

end NetworkCalculus
