import Book.ClosureEReal
import Book.FunctionDioids
import Book.Dioids
import Mathlib.Data.EReal.Operations

/-! # A (min,+) Dioid of `EReal`-valued curves
Bounded-below curves `g : ℝ≥0 → EReal` form a `DeepWiki.Algebra.Dioid` under
`⊕ = ` pointwise `⊓` (min) and `⊗ = minConv`. `IsBddBelowReal` (bounded below by
some real) is the weakest restriction: it is closed under `⊓` and `minConv`
(a uniform real lower bound stops the convolution infima collapsing to `⊥`),
and implies `IsNeverBot`, which the `EReal` bot-absorbing `+` needs for the
zero/unit laws. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- `IsBddBelowReal` is closed under pointwise `min` (the dioid sum `⊕`): a common
real lower bound for `f`, `g` bounds their min. -/
theorem IsBddBelowReal.inf {f g : ℝ≥0 → EReal}
    (hf : IsBddBelowReal f) (hg : IsBddBelowReal g) :
    IsBddBelowReal (fun t => min (f t) (g t)) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  exact ⟨min c d, fun t => le_min
    ((EReal.coe_le_coe_iff.2 (min_le_left c d)).trans (hc t))
    ((EReal.coe_le_coe_iff.2 (min_le_right c d)).trans (hd t))⟩

/-- `IsBddBelowReal` is closed under `minConv` (the dioid product `⊗`): bounds
`c, d` give the bound `c + d`. -/
theorem IsBddBelowReal.minConv {f g : ℝ≥0 → EReal}
    (hf : IsBddBelowReal f) (hg : IsBddBelowReal g) :
    IsBddBelowReal (minConv f g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  exact ⟨c + d, fun t => coe_add_le_minConv hc hd t⟩

/-- `minConv f g t ≠ ⊥` for bounded-below curves. -/
theorem minConv_ne_bot {f g : ℝ≥0 → EReal}
    (hf : IsBddBelowReal f) (hg : IsBddBelowReal g) (t : ℝ≥0) :
    minConv f g t ≠ ⊥ :=
  (hf.minConv hg).isNeverBot t

/-- One direction of associativity for bounded-below curves:
`minConv (minConv f g) h t ≤ minConv f (minConv g h) t`. -/
theorem minConv_assoc_le {f g h : ℝ≥0 → EReal}
    (hf : IsBddBelowReal f) (hg : IsBddBelowReal g) (hh : IsBddBelowReal h) (t : ℝ≥0) :
    minConv (minConv f g) h t ≤ minConv f (minConv g h) t := by
  refine le_minConv fun u s hus => ?_
  -- the inner `minConv g h s` opens via `le_add_minConv_of_ne_bot`
  refine le_add_minConv_of_ne_bot (hf.isNeverBot u) (minConv_ne_bot hg hh s)
    fun a b hab => ?_
  -- elim at the target split `(u+a)+b = t`
  refine (minConv_le_add (minConv f g) h
    (show (u + a) + b = t by rw [add_assoc, hab, hus])).trans ?_
  rw [← add_assoc]
  gcongr
  exact minConv_le_add f g rfl

/-- (min,+) convolution left-distributes over pointwise `min` on `EReal` curves:
`minConv f (g ⊓ h) = minConv f g ⊓ minConv f h`. -/
theorem minConv_min (f g h : ℝ≥0 → EReal) :
    minConv f (fun t => min (g t) (h t))
      = fun t => min (minConv f g t) (minConv f h t) := by
  funext t
  apply le_antisymm
  · exact le_min
      (minConv_le_minConv (fun _ => le_rfl) (fun r => min_le_left _ _) t)
      (minConv_le_minConv (fun _ => le_rfl) (fun r => min_le_right _ _) t)
  · refine le_minConv fun u s hus => ?_
    show min (minConv f g t) (minConv f h t) ≤ f u + min (g s) (h s)
    rw [← min_add_add_left]
    exact min_le_min (minConv_le_add f g hus) (minConv_le_add f h hus)

/-- The (min,+) zero curve, constant `⊤ = +∞`. -/
noncomputable def topCurve : ℝ≥0 → EReal := fun _ => ⊤

/-- `minConv f topCurve = topCurve` for `IsNeverBot f` (the right zero law). -/
theorem minConv_topCurve_right {f : ℝ≥0 → EReal} (hf : IsNeverBot f) :
    minConv f topCurve = topCurve := by
  funext t
  apply le_antisymm le_top
  refine le_minConv fun u s _ => ?_
  show (⊤ : EReal) ≤ f u + (⊤ : EReal)
  rw [EReal.add_top_of_ne_bot (hf u)]

/-- `minConv topCurve f = topCurve` for `IsNeverBot f` (the left zero law). -/
theorem minConv_topCurve_left {f : ℝ≥0 → EReal} (hf : IsNeverBot f) :
    minConv topCurve f = topCurve := by
  rw [minConv_comm]; exact minConv_topCurve_right hf

/-- `topCurve` is bounded below by a real (any constant works). -/
theorem isBddBelowReal_topCurve : IsBddBelowReal topCurve := ⟨0, fun _ => le_top⟩

/-- (min,+) convolution on bounded-below `EReal`-valued curves is associative. -/
theorem minConv_assoc {f g h : ℝ≥0 → EReal}
    (hf : IsBddBelowReal f) (hg : IsBddBelowReal g) (hh : IsBddBelowReal h) :
    minConv (minConv f g) h = minConv f (minConv g h) := by
  funext t
  apply le_antisymm
  · exact minConv_assoc_le hf hg hh t
  · -- reverse via commutativity: `f∗(g∗h) = (h∗g)∗f` etc.
    have hrev := minConv_assoc_le hh hg hf t
    -- `(h∗g)∗f ≤ h∗(g∗f)`; rewrite both sides by `minConv_comm`.
    rw [minConv_comm (minConv h g) f, minConv_comm h g,
      minConv_comm h (minConv g f), minConv_comm g f] at hrev
    exact hrev

/-- `convUnitEReal` is `IsNeverBot`. -/
theorem isNeverBot_convUnitEReal : IsNeverBot convUnitEReal :=
  isBddBelowReal_convUnitEReal.isNeverBot

/-- `convUnitEReal` is a right unit: `minConv f convUnitEReal = f` (`IsNeverBot f`). -/
theorem minConv_convUnitEReal_right {f : ℝ≥0 → EReal} (hf : IsNeverBot f) :
    minConv f convUnitEReal = f := by
  rw [minConv_comm]; exact minConv_convUnitEReal_left f hf

/-- Bounded-below (min,+) curves valued in `R∪{±∞}`: the weakest restriction
making `ℝ≥0 → EReal` a (min,+) `Dioid` (a uniform real lower bound stops the
convolution infima collapsing to `−∞`; weaker than non-negativity). -/
def ECurve := {g : ℝ≥0 → EReal // IsBddBelowReal g}

namespace ECurve

/-- Two `ECurve`s are equal when their underlying curves agree. -/
@[ext] theorem ext {a b : ECurve} (h : a.1 = b.1) : a = b := Subtype.ext h

/-- The (min,+) Dioid of bounded-below `EReal` curves:
`⊕ = ` pointwise `⊓`, `⊗ = minConv`, `𝟘 = topCurve`, `𝟙 = convUnitEReal`. -/
noncomputable instance : Algebra.Dioid ECurve where
  add a b := ⟨fun t => min (a.1 t) (b.1 t), a.2.inf b.2⟩
  zero := ⟨topCurve, isBddBelowReal_topCurve⟩
  mul a b := ⟨minConv a.1 b.1, a.2.minConv b.2⟩
  one := ⟨convUnitEReal, isBddBelowReal_convUnitEReal⟩
  oplus_assoc _ _ _ := ext (funext fun t => min_assoc _ _ _)
  eps_oplus a := ext (funext fun t => min_eq_right (le_top))
  oplus_eps a := ext (funext fun t => min_eq_left (le_top))
  oplus_comm _ _ := ext (funext fun t => min_comm _ _)
  otimes_assoc a b c := ext (minConv_assoc a.2 b.2 c.2)
  one_otimes a := ext (minConv_convUnitEReal_left a.1 a.2.isNeverBot)
  otimes_one a := ext (minConv_convUnitEReal_right a.2.isNeverBot)
  left_distrib a b c := ext (minConv_min a.1 b.1 c.1)
  right_distrib a b c := ext (by
    show minConv (fun t => min (a.1 t) (b.1 t)) c.1
      = fun t => min (minConv a.1 c.1 t) (minConv b.1 c.1 t)
    rw [minConv_comm]
    simp_rw [minConv_comm a.1 c.1, minConv_comm b.1 c.1]
    exact minConv_min c.1 a.1 b.1)
  eps_otimes a := ext (minConv_topCurve_left a.2.isNeverBot)
  otimes_eps a := ext (minConv_topCurve_right a.2.isNeverBot)
  otimes_comm a b := ext (minConv_comm a.1 b.1)
  oplus_idem _ := ext (funext fun t => min_self _)

example (a b : ECurve) :
    (a ⊕ₒ b).1 = fun t => min (a.1 t) (b.1 t) := rfl

example (a b : ECurve) : (a ⊗ₒ b).1 = minConv a.1 b.1 := rfl

example : (εₒ : ECurve).1 = topCurve := rfl

example : (eₒ : ECurve).1 = convUnitEReal := rfl

end ECurve

end DeepWiki
