import Leanproofs.MinPlus.Builder
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Tactic.GCongr

/-!
# `Rmin = ℝ ∪ {+∞}` is a dioid (Definition 2.5)

We exhibit the (min,plus) structure `Rmin = (ℝ ∪ {+∞}, min, +)` as a `Dioid`
(`Leanproofs.MinPlus.Dioid`), via the reusable builder `Leanproofs.MinPlus.Builder`. This is the
**non-complete** layer: only the idempotent-semiring structure with the canonical order, *not* the
completeness/lower-semicontinuity of `CompleteDioid`.

Indeed `Rmin` cannot be a complete dioid in this sense: `WithTop ℝ` is not a complete lattice (`ℝ`
is unbounded below), and adjoining `−∞` to fix that would break lower semi-continuity — `−∞` makes
`𝟘 = +∞` non-absorbing (`(−∞) + (+∞) = −∞ ≠ +∞`). The complete (min,plus) dioid is `R⁺min` on
`ℝ≥0∞` instead (see `Leanproofs.MinPlus.RplusMinInstance`).

## Order convention

In a dioid the sum `⊕` is the lattice *join* and the neutral `𝟘` is the *least* element. Here
`⊕ = min` and `𝟘 = +∞`, so the canonical order `a ≼ b :⟺ min a b = b ⟺ b ≤ a` is the **reverse**
of the numeric order on `ℝ ∪ {+∞}`, with `+∞` as `⊥`. The carrier is `(WithTop ℝ)ᵒᵈ`, with
`⊕ = min = ⊔`, `𝟘 = +∞ = ⊥`, `⊗ = ` ordinary addition, `𝟙 = 0`.
-/

namespace NetworkCalculus

open scoped Computability

/-- `WithTop ℝ` is a (min,plus) dioid carrier: `+∞ = ⊤` is absorbing for `+`, and addition is
monotone. -/
noncomputable instance : MinPlus.Carrier (WithTop ℝ) where
  add_top' a := by simp
  add_le_add_left' h c := by gcongr

/-- `Rmin = ℝ ∪ {+∞}`, the (min,plus) dioid carried by `WithTop ℝ` under the **reversed** order so
that `⊕ = min` is the join and `𝟘 = +∞` is the bottom. -/
abbrev Rmin := MinPlus.D (WithTop ℝ)

/-- **`Rmin = (ℝ ∪ {+∞}, min, +)` is a dioid** (Definition 2.5), assembled by the builder from the
`MinPlus.Carrier (WithTop ℝ)` instance. -/
noncomputable example : Dioid Rmin := inferInstance

/-- The canonical dioid order on `Rmin` is the **reverse** of the numeric order:
`a ≼ b ↔ b ≤ a` on `WithTop ℝ`. -/
example (a b : Rmin) : a ≤ b ↔ b.toDual ≤ a.toDual := Iff.rfl

end NetworkCalculus
