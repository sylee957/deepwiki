import Leanproofs.MinPlus.Builder
import Mathlib.Data.ENNReal.Operations
import Mathlib.Tactic.GCongr

/-!
# `R⁺min = ℝ≥0 ∪ {+∞}` is a complete dioid (Propositions 2.1–2.2)

We exhibit the book's canonical complete (min,plus) dioid `R⁺min = (ℝ≥0 ∪ {+∞}, min, +)` as a
`CompleteDioid` (`Leanproofs.MinPlus.CompleteDioid`), via the reusable builder
`Leanproofs.MinPlus.Builder`. The carrier is Mathlib's `ℝ≥0∞ = ENNReal`.

## Why `ℝ≥0∞`, and why this is the *complete* one

A `CompleteDioid` needs a complete lattice **and** lower semi-continuity of the product
(`mul_sSup`: `+` distributes over arbitrary infima). `ℝ≥0∞` is the sweet spot:

* it **is** a complete lattice (`0 = ⊥`, `+∞ = ⊤`), unlike `ℝ ∪ {+∞}` which is unbounded below;
* it is `−∞`-free, so `𝟘 = +∞` stays absorbing and there are no `(+∞) + (−∞)` indeterminate forms.
  Adjoining `−∞` (the carrier `EReal`) would make a complete lattice but break `mul_sSup`.

The single concrete input is `ENNReal.add_iInf` (`a + ⨅ i, f i = ⨅ i, a + f i`), exactly the
lower-semicontinuity field `MinPlus.CompleteCarrier.add_iInf'`.

## Order convention

As for `Rmin`: `⊕ = min = ⊔` (the join in the dual order), `𝟘 = +∞ = ⊥`, `⊗ = ` ordinary `ℝ≥0∞`
addition, `𝟙 = 0`; the canonical order `a ≼ b ↔ b ≤ a` is the reverse of the numeric order.
-/

open scoped ENNReal

namespace NetworkCalculus

open scoped Computability

/-- `ℝ≥0∞` is a **complete** (min,plus) dioid carrier: `+∞ = ⊤` is absorbing for `+`, addition is
monotone, and `+` is lower semi-continuous (`ENNReal.add_iInf`). -/
noncomputable instance : MinPlus.CompleteCarrier ℝ≥0∞ where
  add_top' a := by simp
  add_le_add_left' h c := by gcongr
  add_sInf' a s := by rw [sInf_eq_iInf, ENNReal.add_iInf]; exact iInf_congr fun _ => ENNReal.add_iInf

/-- `R⁺min = ℝ≥0 ∪ {+∞}`, the positive (min,plus) complete dioid carried by `ℝ≥0∞` under the
**reversed** order so that `⊕ = min` is the join and `𝟘 = +∞` is the bottom. -/
abbrev RplusMin := MinPlus.D ℝ≥0∞

/-- **Propositions 2.1–2.2.** `R⁺min = (ℝ≥0 ∪ {+∞}, min, +)` is a **complete dioid**, assembled by
the builder from the `MinPlus.CompleteCarrier ℝ≥0∞` instance. -/
noncomputable example : CompleteDioid RplusMin := inferInstance

/-- The canonical dioid order on `R⁺min` is the **reverse** of the numeric order:
`a ≼ b ↔ b ≤ a` on `ℝ≥0∞`. -/
example (a b : RplusMin) : a ≤ b ↔ b.toDual ≤ a.toDual := Iff.rfl

end NetworkCalculus
