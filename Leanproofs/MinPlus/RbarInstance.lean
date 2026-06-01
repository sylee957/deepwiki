import Leanproofs.MinPlus.Builder
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push

/-!
# `R̄min = ℝ ∪ {+∞, −∞}` is a complete dioid (Theorem 2.2, Proposition 2.1)

The book first makes `Rmin = ℝ ∪ {+∞}` a dioid (Theorem 2.2; see `Rmin` in
`Leanproofs.MinPlus.RminInstance`), then *completes* it by adjoining a top
`⊤ = ⋀_{x} x = −∞`, giving `R̄min = ℝ ∪ {+∞, −∞}` (Proposition 2.1). The decisive convention is

  `(+∞) + (−∞) = +∞`,  i.e.  `ε + ⊤ = ε`,

so that the dioid zero `ε = +∞` stays **absorbing** for the product `⊗ = +`. With that convention
addition distributes over arbitrary infima, and `R̄min` is a complete commutative dioid.

## Carrier: `WithTop (WithBot ℝ)`

Mathlib's `WithTop (WithBot ℝ)` realizes exactly this convention: its outer `⊤` is **absorbing**
for `+` (`a + ⊤ = ⊤`, `⊤ + a = ⊤`, including `⊥ + ⊤ = ⊤`). Mapping to the book:

* outer `⊤ = +∞ = ` the dioid zero `ε` (absorbing — the book's `(+∞)+(−∞) = +∞`),
* inner `⊥ = −∞ = ` the dioid top `⊤_dioid`,
* `⊗ = ` the `WithTop`/`WithBot` addition, `𝟙 = 0`.

(Note: this is **not** Mathlib's `EReal` addition, which uses the opposite convention
`(+∞)+(−∞) = −∞` and would make `ε` non-absorbing, breaking the dioid.)

The carrier is then `(WithTop (WithBot ℝ))ᵒᵈ` under the reversed order (`⊕ = min = ⊔`,
`ε = +∞ = ⊥`). The one piece of real content is lower semi-continuity of `+` — that addition
distributes over an arbitrary infimum — proved as `add_iInf'` below.
-/

namespace NetworkCalculus

open scoped Computability

/-- `R̄min = ℝ ∪ {±∞}`, carried by `WithTop (WithBot ℝ)` with the book's absorbing-`+∞`
convention. -/
abbrev Rbar := WithTop (WithBot ℝ)

namespace Rbar

/-- Adding a fixed real number `r` is an order isomorphism of `R̄min` (a shift). -/
noncomputable def shift (r : ℝ) : Rbar ≃o Rbar :=
  ((OrderIso.addLeft r).withBotCongr).withTopCongr

theorem shift_eq (r : ℝ) (x : Rbar) :
    shift r x = (((r : WithBot ℝ) : Rbar)) + x := by
  induction x using WithTop.recTopCoe with
  | top => simp [shift]
  | coe d =>
    induction d using WithBot.recBotCoe with
    | bot =>
      simp only [shift, OrderIso.withTopCongr_apply, WithTop.map_coe,
        OrderIso.withBotCongr_apply, WithBot.map_bot]
      rw [show ((⊥ : WithBot ℝ) : Rbar) = ((↑r : WithBot ℝ) : Rbar) + ((⊥ : WithBot ℝ) : Rbar)
        from ?_]
      · rfl
      · rw [← WithTop.coe_add, WithBot.add_bot]
    | coe s =>
      simp only [shift, OrderIso.withTopCongr_apply, WithTop.map_coe,
        OrderIso.withBotCongr_apply, WithBot.map_coe, OrderIso.addLeft_apply]
      rw [← WithTop.coe_add, ← WithBot.coe_add]

/-- **Lower semi-continuity of `+`** (the heart of Proposition 2.1): addition distributes over an
arbitrary infimum, `a + ⨅ i, f i = ⨅ i, a + f i`. True precisely because `+∞ = ⊤` is absorbing.

The finite case reduces to the shift order-isomorphism (which preserves infima); the `±∞` and
empty-index cases are handled by the absorbing top. -/
theorem add_iInf {ι : Sort*} (a : Rbar) (f : ι → Rbar) :
    (a + ⨅ i, f i) = ⨅ i, a + f i := by
  refine le_antisymm (le_iInf fun i => by gcongr; exact iInf_le _ i) ?_
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [iInf_of_empty]
  · induction a using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      induction b using WithBot.recBotCoe with
      | coe r =>
        -- finite case: use the order isomorphism `shift r`
        have hmap : (shift r) (⨅ i, f i) = ⨅ i, (shift r) (f i) :=
          OrderIso.map_iInf _ _
        simp only [shift_eq] at hmap
        exact hmap.ge
      | bot =>
        -- a = −∞: `↑⊥ + x = ↑⊥` unless `x = ⊤`
        by_cases htop : (⨅ i, f i) = ⊤
        · have hall : ∀ i, f i = ⊤ := fun i => top_le_iff.mp (htop ▸ iInf_le f i)
          simp only [hall, WithTop.add_top, ciInf_const, le_refl]
        · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp htop
          rw [show (⨅ i, f i) = (c : Rbar) from hc, ← WithTop.coe_add]
          have hex : ∃ j, f j ≠ ⊤ := by
            by_contra h
            push Not at h
            exact htop (by simp [h])
          obtain ⟨j, hj⟩ := hex
          rw [show ((⊥ : WithBot ℝ) + c : WithBot ℝ) = ⊥ from WithBot.bot_add c]
          refine iInf_le_of_le j ?_
          obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hj
          rw [show f j = (d : Rbar) from hd, ← WithTop.coe_add, WithBot.bot_add]

end Rbar

/-- `R̄min = WithTop (WithBot ℝ)` is a **complete** (min,plus) dioid carrier: `+∞ = ⊤` is absorbing
for `+`, addition is monotone, and `+` is lower semi-continuous (`Rbar.add_iInf`). -/
noncomputable instance : MinPlus.CompleteCarrier Rbar where
  add_top' a := by simp
  add_le_add_left' h c := by gcongr
  add_sInf' a s := by rw [sInf_eq_iInf, Rbar.add_iInf]; exact iInf_congr fun _ => Rbar.add_iInf _ _

/-- `R̄min` as the (min,plus) dioid carrier `(WithTop (WithBot ℝ))ᵒᵈ` under the reversed order, so
that `⊕ = min` is the join and `ε = +∞` is the bottom. -/
abbrev RbarMin := MinPlus.D Rbar

/-- **Proposition 2.1.** `R̄min = (ℝ ∪ {±∞}, min, +)` is a **complete commutative dioid**, with zero
`ε = +∞`, unit `e = 0`, and top `⊤ = −∞`; absorption of `ε` over the product gives
`(+∞) + (−∞) = +∞`. Assembled by the builder from the `MinPlus.CompleteCarrier Rbar` instance. -/
noncomputable example : CompleteDioid RbarMin := inferInstance

/-- The canonical dioid order on `R̄min` is the **reverse** of the numeric order:
`a ≼ b ↔ b ≤ a` on `WithTop (WithBot ℝ)`. -/
example (a b : RbarMin) : a ≤ b ↔ b.toDual ≤ a.toDual := Iff.rfl

end NetworkCalculus
