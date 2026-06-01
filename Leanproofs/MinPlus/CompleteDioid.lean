import Leanproofs.MinPlus.Dioid
import Mathlib.Order.CompleteLattice.Lemmas

/-!
# Complete dioids (§2.1, Definitions 2.1–2.5)

Building on the `Dioid` layer of `Leanproofs.MinPlus.Dioid`, a **complete dioid** is a dioid that
is moreover a complete lattice for the canonical order and whose product `⊗` is *lower
semi-continuous*: it distributes over **arbitrary** sums `⊕` on both sides (the boxed identity
`Rₐ(⊕ x) = ⊕ Rₐ(x)` of §2.3.1). Residuation then follows as a theorem.

The book's notation maps as `⊕ = +`, `⊗ = *`, `𝟘 = 0`, `𝟙 = 1`, `≼ = ≤`.

## Concrete model

In `R⁺min` the operations are `⊕ = min`, `⊗ = (+)`, `𝟘 = +∞`, `𝟙 = 0`, and the canonical order
`≼` is the **reverse** of the numeric `≤`. The `ℝ≥0∞` witness therefore enters through this
algebraic interface (`⊕`, `⊗`).
-/

namespace NetworkCalculus

open scoped Computability  -- `add_eq_sup : a + b = a ⊔ b`

/-! ### `CompleteDioid` (completeness + lower semi-continuity)

`CompleteDioid` extends the `Dioid` (`IdemCommSemiring`) with a `CompleteLattice` structure for
the *same* canonical order, plus the lower-semicontinuity laws. The shared `SemilatticeSup`/order
keeps the two views diamond-free. -/

/-- A **complete dioid** (Definition 2.5): a `Dioid` whose canonical order is a complete lattice
and whose product `⊗ = (*)` distributes over arbitrary sums `⊕ = ⨆` on both sides (lower
semi-continuity, §2.3.1).

Distributivity is stated over an arbitrary `Set` to stay in `α`'s universe; the indexed `⨆`
forms are derived below. -/
class CompleteDioid (α : Type*) extends IdemCommSemiring α, CompleteLattice α where
  /-- `⊗` distributes over arbitrary `⊕` (lower semi-continuity, §2.3.1). Stated on the left only;
  the right version `sSup_mul` follows from commutativity of `⊗`. -/
  mul_sSup : ∀ (a : α) (s : Set α), a * sSup s = ⨆ b ∈ s, a * b

namespace CompleteDioid

variable {α : Type*} [CompleteDioid α]

/-! #### Lower semi-continuity: `⊗` distributes over arbitrary `⊕` -/

/-- Right distributivity over an arbitrary sum, **derived** from `mul_sSup` and commutativity of
`⊗` (so it need not be a separate axiom). -/
theorem sSup_mul (a : α) (s : Set α) : sSup s * a = ⨆ b ∈ s, b * a := by
  rw [mul_comm, mul_sSup]; simp_rw [mul_comm a]

/-- Left distributivity over an indexed supremum (any index type), derived from `mul_sSup`. -/
theorem mul_iSup {ι : Sort*} (a : α) (g : ι → α) : a * ⨆ i, g i = ⨆ i, a * g i := by
  rw [← sSup_range, mul_sSup, iSup_range]

/-- Right distributivity over an indexed supremum, derived from `sSup_mul`. -/
theorem iSup_mul {ι : Sort*} (g : ι → α) (a : α) : (⨆ i, g i) * a = ⨆ i, g i * a := by
  rw [← sSup_range, sSup_mul, iSup_range]

/-- Binary left-distributivity of `⊗` over `⊕ = ⊔` (special case of `mul_iSup`). -/
theorem mul_sup (a b c : α) : a * (b ⊔ c) = a * b ⊔ a * c := by
  have h1 : (⨆ i : Bool, cond i b c) = b ⊔ c := by simp [iSup_bool_eq]
  have h2 : (⨆ i : Bool, a * cond i b c) = a * b ⊔ a * c := by simp [iSup_bool_eq]
  rw [← h1, mul_iSup, h2]

/-- Binary right-distributivity of `⊗` over `⊕ = ⊔`. -/
theorem sup_mul (a b c : α) : (b ⊔ c) * a = b * a ⊔ c * a := by
  have h1 : (⨆ i : Bool, cond i b c) = b ⊔ c := by simp [iSup_bool_eq]
  have h2 : (⨆ i : Bool, cond i b c * a) = b * a ⊔ c * a := by simp [iSup_bool_eq]
  rw [← h1, iSup_mul, h2]

/-! #### Isotony (Theorem 2.1)

Isotony of `⊕` and `⊗` holds already at the `Dioid` level (no completeness needed) and is proved
there: `Dioid.add_le_add_right'`, `Dioid.add_le_add_left'`, `Dioid.mul_le_mul_right'`,
`Dioid.mul_le_mul_left'`. They are available here through the `Dioid` superclass. -/

end CompleteDioid

end NetworkCalculus
