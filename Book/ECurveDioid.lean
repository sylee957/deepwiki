import Book.ClosureEReal
import Book.FunctionDioids
import Book.Dioids
import Book.SubDioid
import Mathlib.Data.EReal.Operations

/-! # A (min,+) Dioid of `EReal`-valued curves
Bounded-below curves `g : ℝ≥0 → EReal` form a `DeepWiki.Algebra.Dioid` under
`⊕ = ` pointwise `⊓` (min) and `⊗ = minConv`. `BddBelowReal` (bounded below by
some real) is the weakest restriction: it is closed under `⊓` and `minConv`
(a uniform real lower bound stops the convolution infima collapsing to `⊥`),
and implies `NeverBot`, which the `EReal` bot-absorbing `+` needs for the
zero/unit laws. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- For non-`⊥` `a` and a family with non-`⊥` infimum,
`a + ⨅ i, f i = ⨅ i, a + f i` on `EReal`. -/
theorem add_iInf_of_ne_bot {ι : Type*} [Nonempty ι] {a : EReal}
    (ha : a ≠ ⊥) {f : ι → EReal} (hbot : (⨅ i, f i) ≠ ⊥) :
    a + ⨅ i, f i = ⨅ i, a + f i := by
  apply le_antisymm
  · refine le_iInf (fun i => ?_)
    gcongr
    exact iInf_le _ i
  · exact iInf_add_le_add_iInf ha hbot

/-- For a non-`⊥` family infimum and non-`⊥` `a`,
`(⨅ i, f i) + a = ⨅ i, f i + a` on `EReal`. -/
theorem iInf_add_of_ne_bot {ι : Type*} [Nonempty ι] {a : EReal}
    (ha : a ≠ ⊥) {f : ι → EReal} (hbot : (⨅ i, f i) ≠ ⊥) :
    (⨅ i, f i) + a = ⨅ i, f i + a := by
  rw [add_comm, add_iInf_of_ne_bot ha hbot]
  simp_rw [add_comm a]

/-- (min,+) convolution on `EReal`-valued curves is commutative. -/
theorem minConv_comm (f g : ℝ≥0 → EReal) : minConv f g = minConv g f := by
  funext t
  apply le_antisymm <;>
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
    refine iInf_le_of_le ⟨(s, u), by rw [add_comm]; exact hus⟩ ?_
    simp only
    rw [add_comm]

/-- `BddBelowReal` is closed under pointwise `min` (the dioid sum `⊕`): a common
real lower bound for `f`, `g` bounds their min. -/
theorem BddBelowReal.inf {f g : ℝ≥0 → EReal}
    (hf : BddBelowReal f) (hg : BddBelowReal g) :
    BddBelowReal (fun t => min (f t) (g t)) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  exact ⟨min c d, fun t => le_min
    ((EReal.coe_le_coe_iff.2 (min_le_left c d)).trans (hc t))
    ((EReal.coe_le_coe_iff.2 (min_le_right c d)).trans (hd t))⟩

/-- `BddBelowReal` is closed under `minConv` (the dioid product `⊗`): bounds
`c, d` give the bound `c + d`. -/
theorem BddBelowReal.minConv {f g : ℝ≥0 → EReal}
    (hf : BddBelowReal f) (hg : BddBelowReal g) :
    BddBelowReal (minConv f g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  exact ⟨c + d, fun t => minConv_bddBelowReal hc hd t⟩

/-- `minConv f g t ≠ ⊥` for bounded-below curves. -/
theorem minConv_ne_bot {f g : ℝ≥0 → EReal}
    (hf : BddBelowReal f) (hg : BddBelowReal g) (t : ℝ≥0) :
    minConv f g t ≠ ⊥ :=
  (hf.minConv hg).neverBot t

/-- One direction of associativity for bounded-below curves:
`minConv (minConv f g) h t ≤ minConv f (minConv g h) t`. -/
theorem minConv_assoc_le {f g h : ℝ≥0 → EReal}
    (hf : BddBelowReal f) (hg : BddBelowReal g) (hh : BddBelowReal h) (t : ℝ≥0) :
    minConv (minConv f g) h t ≤ minConv f (minConv g h) t := by
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
  simp only
  -- `f u + minConv g h s = ⨅_{a+b=s} (f u + (g a + h b))`
  rw [show minConv g h s
        = ⨅ q : {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = s}, g q.1.1 + h q.1.2 from rfl,
    add_iInf_of_ne_bot (hf.neverBot u) (minConv_ne_bot hg hh s)]
  refine le_iInf ?_
  rintro ⟨⟨a, b⟩, (hab : a + b = s)⟩
  simp only
  -- target split `(u+a)+b = t`
  refine iInf_le_of_le
    ⟨(u + a, b), by rw [add_assoc, hab, hus]⟩ ?_
  simp only
  have hinner : minConv f g (u + a) ≤ f u + g a :=
    iInf_le_of_le
      (⟨(u, a), rfl⟩ : {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = u + a}) (le_refl _)
  calc minConv f g (u + a) + h b
      ≤ (f u + g a) + h b := by gcongr
    _ = f u + (g a + h b) := add_assoc _ _ _

/-- (min,+) convolution left-distributes over pointwise `min` on `EReal` curves:
`minConv f (g ⊓ h) = minConv f g ⊓ minConv f h`. -/
theorem minConv_min (f g h : ℝ≥0 → EReal) :
    minConv f (fun t => min (g t) (h t))
      = fun t => min (minConv f g t) (minConv f h t) := by
  funext t
  apply le_antisymm
  · refine le_min ?_ ?_ <;>
    · refine le_iInf ?_
      rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
      refine iInf_le_of_le ⟨(u, s), hus⟩ ?_
      simp only
      gcongr
      first
      | exact min_le_left _ _
      | exact min_le_right _ _
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
    simp only
    rw [← min_add_add_left]
    refine min_le_min ?_ ?_ <;>
      exact iInf_le_of_le ⟨(u, s), hus⟩ (le_refl _)

/-- The (min,+) zero curve, constant `⊤ = +∞`. -/
noncomputable def topCurve : ℝ≥0 → EReal := fun _ => ⊤

/-- `minConv f topCurve = topCurve` for `NeverBot f` (the right zero law). -/
theorem minConv_topCurve_right {f : ℝ≥0 → EReal} (hf : NeverBot f) :
    minConv f topCurve = topCurve := by
  funext t
  apply le_antisymm le_top
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, _⟩
  show (⊤ : EReal) ≤ f u + (⊤ : EReal)
  rw [EReal.add_top_of_ne_bot (hf u)]

/-- `minConv topCurve f = topCurve` for `NeverBot f` (the left zero law). -/
theorem minConv_topCurve_left {f : ℝ≥0 → EReal} (hf : NeverBot f) :
    minConv topCurve f = topCurve := by
  rw [minConv_comm]; exact minConv_topCurve_right hf

/-- `topCurve` is bounded below by a real (any constant works). -/
theorem bddBelowReal_topCurve : BddBelowReal topCurve := ⟨0, fun _ => le_top⟩

/-- (min,+) convolution on bounded-below `EReal`-valued curves is associative. -/
theorem minConv_assoc {f g h : ℝ≥0 → EReal}
    (hf : BddBelowReal f) (hg : BddBelowReal g) (hh : BddBelowReal h) :
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

/-- `convUnitEReal` is `NeverBot`. -/
theorem neverBot_convUnitEReal : NeverBot convUnitEReal :=
  bddBelowReal_convUnitEReal.neverBot

/-- `convUnitEReal` is a right unit: `minConv f convUnitEReal = f` (`NeverBot f`). -/
theorem minConv_convUnitEReal_right {f : ℝ≥0 → EReal} (hf : NeverBot f) :
    minConv f convUnitEReal = f := by
  rw [minConv_comm]; exact minConv_convUnitEReal_left f hf

/-- Bounded-below (min,+) curves valued in `R∪{±∞}`: the weakest restriction
making `ℝ≥0 → EReal` a (min,+) `Dioid` (a uniform real lower bound stops the
convolution infima collapsing to `−∞`; weaker than non-negativity). -/
def ECurve := {g : ℝ≥0 → EReal // BddBelowReal g}

namespace ECurve

/-- Two `ECurve`s are equal when their underlying curves agree. -/
@[ext] theorem ext {a b : ECurve} (h : a.1 = b.1) : a = b := Subtype.ext h

/-- The (min,+) Dioid of bounded-below `EReal` curves:
`⊕ = ` pointwise `⊓`, `⊗ = minConv`, `𝟘 = topCurve`, `𝟙 = convUnitEReal`. -/
noncomputable instance : Algebra.Dioid ECurve where
  add a b := ⟨fun t => min (a.1 t) (b.1 t), a.2.inf b.2⟩
  zero := ⟨topCurve, bddBelowReal_topCurve⟩
  mul a b := ⟨minConv a.1 b.1, a.2.minConv b.2⟩
  one := ⟨convUnitEReal, bddBelowReal_convUnitEReal⟩
  oplus_assoc _ _ _ := ext (funext fun t => min_assoc _ _ _)
  eps_oplus a := ext (funext fun t => min_eq_right (le_top))
  oplus_eps a := ext (funext fun t => min_eq_left (le_top))
  oplus_comm _ _ := ext (funext fun t => min_comm _ _)
  otimes_assoc a b c := ext (minConv_assoc a.2 b.2 c.2)
  one_otimes a := ext (minConv_convUnitEReal_left a.1 a.2.neverBot)
  otimes_one a := ext (minConv_convUnitEReal_right a.2.neverBot)
  left_distrib a b c := ext (minConv_min a.1 b.1 c.1)
  right_distrib a b c := ext (by
    show minConv (fun t => min (a.1 t) (b.1 t)) c.1
      = fun t => min (minConv a.1 c.1 t) (minConv b.1 c.1 t)
    rw [minConv_comm]
    simp_rw [minConv_comm a.1 c.1, minConv_comm b.1 c.1]
    exact minConv_min c.1 a.1 b.1)
  eps_otimes a := ext (minConv_topCurve_left a.2.neverBot)
  otimes_eps a := ext (minConv_topCurve_right a.2.neverBot)
  otimes_comm a b := ext (minConv_comm a.1 b.1)
  oplus_idem _ := ext (funext fun t => min_self _)

example (a b : ECurve) :
    (a ⊕ₒ b).1 = fun t => min (a.1 t) (b.1 t) := rfl

example (a b : ECurve) : (a ⊗ₒ b).1 = minConv a.1 b.1 := rfl

example : (εₒ : ECurve).1 = topCurve := rfl

example : (eₒ : ECurve).1 = convUnitEReal := rfl

end ECurve

end DeepWiki
