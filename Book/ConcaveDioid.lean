import Book.Concave
import Book.ConcaveProps
import Book.ClosureEReal
import Book.Additivity
import Book.FunctionDioids
import Book.Dioids
import Book.ConvolutionMinimumExt
import Mathlib.Data.EReal.Operations

/-! # A (min,+) Dioid of `EReal`-valued curves
Non-negative curves `g : ℝ≥0 → EReal` form a `DeepWiki.Algebra.Dioid`
under `⊕ = ` pointwise `⊓` (min) and `⊗ = minConv`.  Non-negativity is
the minimal restriction: it is closed under `⊓` and `minConv` (every value
stays `≥ 0`, so the convolution infima never collapse to `⊥`), and it implies
`NeverBot`, which the `EReal` bot-absorbing `+` needs for the zero/unit laws. -/

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

/-- The split-infimum `minConv f g t` of non-negative curves is `≥ 0`. -/
theorem zero_le_minConv {f g : ℝ≥0 → EReal}
    (hf : IsNonneg f) (hg : IsNonneg g) (t : ℝ≥0) :
    (0 : EReal) ≤ minConv f g t :=
  minConv_isNonneg hf hg t

/-- `minConv f g t ≠ ⊥` for non-negative curves. -/
theorem minConv_ne_bot {f g : ℝ≥0 → EReal}
    (hf : IsNonneg f) (hg : IsNonneg g) (t : ℝ≥0) :
    minConv f g t ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.bot_lt_zero.ne') (zero_le_minConv hf hg t)

/-- For non-negative `f`, every value `f t ≠ ⊥`. -/
theorem IsNonneg.ne_bot {f : ℝ≥0 → EReal} (hf : IsNonneg f) (t : ℝ≥0) :
    f t ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.bot_lt_zero.ne') (hf t)

/-- For non-negative `f`, `f` is `NeverBot`. -/
theorem IsNonneg.neverBot {f : ℝ≥0 → EReal} (hf : IsNonneg f) :
    NeverBot f := hf.ne_bot

/-- One direction of associativity for non-negative curves:
`minConv (minConv f g) h t ≤ minConv f (minConv g h) t`. -/
theorem minConv_assoc_le {f g h : ℝ≥0 → EReal}
    (hf : IsNonneg f) (hg : IsNonneg g) (hh : IsNonneg h) (t : ℝ≥0) :
    minConv (minConv f g) h t ≤ minConv f (minConv g h) t := by
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
  simp only
  -- `f u + minConv g h s = ⨅_{a+b=s} (f u + (g a + h b))`
  rw [show minConv g h s
        = ⨅ q : {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = s}, g q.1.1 + h q.1.2 from rfl,
    add_iInf_of_ne_bot (hf.ne_bot u) (minConv_ne_bot hg hh s)]
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

/-- `+` left-distributes over `min` on `EReal`: `a + min b c = min (a+b) (a+c)`. -/
theorem EReal.add_min (a b c : EReal) :
    a + min b c = min (a + b) (a + c) := by
  rcases le_total b c with hbc | hbc
  · rw [min_eq_left hbc, min_eq_left (by gcongr)]
  · rw [min_eq_right hbc, min_eq_right (by gcongr)]

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
    rw [EReal.add_min]
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

/-- `topCurve` is non-negative. -/
theorem isNonneg_topCurve : IsNonneg topCurve := fun _ => le_top

/-- (min,+) convolution on non-negative `EReal`-valued curves is associative. -/
theorem minConv_assoc {f g h : ℝ≥0 → EReal}
    (hf : IsNonneg f) (hg : IsNonneg g) (hh : IsNonneg h) :
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
  isNonneg_convUnitEReal.neverBot

/-- `convUnitEReal` is a right unit: `minConv f convUnitEReal = f` (`NeverBot f`). -/
theorem minConv_convUnitEReal_right {f : ℝ≥0 → EReal} (hf : NeverBot f) :
    minConv f convUnitEReal = f := by
  rw [minConv_comm]; exact minConv_convUnitEReal_left f hf

/-- Non-negative (min,+) curves valued in `R∪{±∞}`. -/
def ECurve := {g : ℝ≥0 → EReal // IsNonneg g}

namespace ECurve

/-- Two `ECurve`s are equal when their underlying curves agree. -/
@[ext] theorem ext {a b : ECurve} (h : a.1 = b.1) : a = b := Subtype.ext h

/-- `IsNonneg` is closed under pointwise `min` (the dioid sum `⊕`). -/
theorem isNonneg_min {f g : ℝ≥0 → EReal} (hf : IsNonneg f) (hg : IsNonneg g) :
    IsNonneg (fun t => min (f t) (g t)) := fun t => le_min (hf t) (hg t)

/-- The (min,+) Dioid of non-negative `EReal` curves:
`⊕ = ` pointwise `⊓`, `⊗ = minConv`, `𝟘 = topCurve`, `𝟙 = convUnitEReal`. -/
noncomputable instance : Algebra.Dioid ECurve where
  add a b := ⟨fun t => min (a.1 t) (b.1 t), isNonneg_min a.2 b.2⟩
  zero := ⟨topCurve, isNonneg_topCurve⟩
  mul a b := ⟨minConv a.1 b.1, minConv_isNonneg a.2 b.2⟩
  one := ⟨convUnitEReal, isNonneg_convUnitEReal⟩
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

/-! ## Concavity is closed under the (min,+) Dioid operations
The four closure facts witnessing that the **concave** non-negative curves form
a sub-`Dioid` of `ECurve`: `⊕ = ` pointwise `min`, `⊗ = minConv`, `𝟘 = topCurve`,
`𝟙 = convUnitEReal`. The `minConv` case is the inf-convolution-of-concave-is-
concave fact; it is proved without any attainment/left-continuity hypothesis by
a dichotomy on the (necessarily finite-or-`⊤`) origin value. -/

/-- `topCurve` (constant `⊤ = +∞`) is concave: every chord lands `≤ ⊤`. -/
theorem ConcaveE_topCurve : ConcaveE topCurve := by
  intro s t p _; exact le_top

/-- A non-negative concave curve with `f 0 = ⊤` is identically `⊤`: the chord
through the origin at any positive point forces `f x = ⊤`. Hence such an `f`
equals `topCurve`. -/
theorem eq_topCurve_of_concaveE_of_zero_top
    {f : ℝ≥0 → EReal} (hf : ConcaveE f) (hnn : IsNonneg f) (h0 : f 0 = ⊤) :
    f = topCurve := by
  funext x
  show f x = ⊤
  rcases eq_or_ne x 0 with rfl | hx
  · exact h0
  · -- chord at `s = 2x`, `t = 0`, weight `p = 1/2`: midpoint is `x`
    have hx0 : (0 : ℝ≥0) < x := pos_iff_ne_zero.2 hx
    set s : ℝ≥0 := 2 * x with hsdef
    have hhalf : ((2 : ℝ≥0)⁻¹) ≤ 1 := by
      rw [inv_le_one₀ (by norm_num : (0:ℝ≥0) < 2)]; norm_num
    have hchord := hf s 0 (2 : ℝ≥0)⁻¹ hhalf
    -- the convex-combination point is `x`
    have hpt : ((2 : ℝ≥0)⁻¹) * s + (1 - (2 : ℝ≥0)⁻¹) * 0 = x := by
      rw [mul_zero, add_zero, hsdef, ← mul_assoc, inv_mul_cancel₀ (by norm_num), one_mul]
    rw [hpt, h0] at hchord
    -- `1 - 1/2 = 1/2 > 0`, so its coercion is `> 0` in `EReal`
    have h1p : (1 : ℝ≥0) - (2 : ℝ≥0)⁻¹ = (2 : ℝ≥0)⁻¹ := by
      rw [← NNReal.coe_inj]; push_cast [NNReal.coe_sub hhalf]; norm_num
    rw [h1p] at hchord
    have hpos : (0 : EReal) < ((((2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) : EReal) := by
      rw [EReal.coe_pos]; positivity
    rw [EReal.mul_top_of_pos hpos] at hchord
    -- LHS `↑(1/2) * f s + ⊤`: the first summand is `≥ 0`, so `≠ ⊥`, hence sum `= ⊤`
    have hmul0 : (0 : EReal) ≤ ((((2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) : EReal) * f s :=
      EReal.mul_nonneg hpos.le (hnn s)
    rw [EReal.add_top_of_ne_bot
        (ne_bot_of_le_ne_bot EReal.bot_lt_zero.ne' hmul0)] at hchord
    exact top_le_iff.1 hchord

/-- The inf-convolution of two non-negative concave curves is concave — the
inf-convolution-of-concave-is-concave closure fact. No attainment / left-
continuity hypothesis is required: if either origin value is `⊤` that curve is
`topCurve` (so `minConv` is `topCurve`, concave); otherwise both origin values
are finite reals and the decomposition `minConv f g = ((f − f 0) ⊓ (g − g 0)) +
(f 0 + g 0)` exhibits `minConv f g` as a concave meet shifted by a constant. -/
theorem ConcaveE_minConv
    {f g : ℝ≥0 → EReal} (hf : ConcaveE f) (hg : ConcaveE g)
    (hnf : IsNonneg f) (hng : IsNonneg g) :
    ConcaveE (minConv f g) := by
  -- `⊤`-origin dichotomy: handle `f 0 = ⊤` or `g 0 = ⊤` first
  rcases eq_or_ne (f 0) ⊤ with hf0 | hf0
  · rw [eq_topCurve_of_concaveE_of_zero_top hf hnf hf0,
      minConv_topCurve_left hng.neverBot]
    exact ConcaveE_topCurve
  rcases eq_or_ne (g 0) ⊤ with hg0 | hg0
  · rw [eq_topCurve_of_concaveE_of_zero_top hg hng hg0,
      minConv_topCurve_right hnf.neverBot]
    exact ConcaveE_topCurve
  -- both origin values finite: name them as reals
  set a : ℝ := (f 0).toReal with hadef
  set b : ℝ := (g 0).toReal with hbdef
  have ha : f 0 = (a : EReal) := (EReal.coe_toReal hf0 (hnf 0 |> ne_bot_of_le_ne_bot
    EReal.bot_lt_zero.ne')).symm
  have hb : g 0 = (b : EReal) := (EReal.coe_toReal hg0 (hng 0 |> ne_bot_of_le_ne_bot
    EReal.bot_lt_zero.ne')).symm
  rw [minConv_eq_inf_sub_add f g a b ha hb hf hg]
  -- the meet of the two finite shifts is concave; adding the constant keeps it so
  have hcm : ConcaveE
      ((f - Function.const ℝ≥0 (a : EReal)) ⊓ (g - Function.const ℝ≥0 (b : EReal))) :=
    ConcaveE.inf _ _ (ConcaveE_sub_const f hf a) (ConcaveE_sub_const g hg b)
  have hconst : Function.const ℝ≥0 ((a : EReal) + (b : EReal))
      = Function.const ℝ≥0 (((a + b : ℝ)) : EReal) := by
    rw [EReal.coe_add]
  rw [hconst]
  exact ConcaveE.add _ _ hcm (ConcaveE_const (a + b))

/-- `convUnitEReal` (`0` at the origin, `⊤` elsewhere) is concave. The only
non-trivial chord is one landing on the origin, which forces both nonzero-weight
endpoints to the origin, where the chord value is `0`; the `EReal` rule
`0 * ⊤ = 0` settles the boundary weights `p ∈ {0, 1}`. -/
theorem ConcaveE_convUnitEReal : ConcaveE convUnitEReal := by
  intro s t p hp
  -- the convex-combination point
  show ((p : ℝ) : EReal) * convUnitEReal s
      + (((1 - p : ℝ≥0) : ℝ) : EReal) * convUnitEReal t
      ≤ convUnitEReal (p * s + (1 - p) * t)
  rcases eq_or_ne (p * s + (1 - p) * t) 0 with hpt | hpt
  · -- combined point is the origin: `convUnitEReal` there is `0`
    obtain ⟨hps, hpt'⟩ := add_eq_zero.1 hpt
    rw [hpt]
    conv_rhs => rw [convUnitEReal, if_pos rfl]
    -- split on whether each weight is zero, using `0 * ⊤ = 0` at the boundary
    have term1 : ((p : ℝ) : EReal) * convUnitEReal s = 0 := by
      rcases eq_or_ne p 0 with hp0 | hp0
      · rw [hp0]; simp
      · -- `p ≠ 0` and `p*s = 0` ⇒ `s = 0` ⇒ `convUnitEReal s = 0`
        have hs0 : s = 0 := by
          rcases mul_eq_zero.1 hps with h | h
          · exact absurd h hp0
          · exact h
        rw [hs0]; simp [convUnitEReal]
    have term2 : (((1 - p : ℝ≥0) : ℝ) : EReal) * convUnitEReal t = 0 := by
      rcases eq_or_ne (1 - p : ℝ≥0) 0 with hq0 | hq0
      · rw [hq0]; simp
      · have ht0 : t = 0 := by
          rcases mul_eq_zero.1 hpt' with h | h
          · exact absurd h hq0
          · exact h
        rw [ht0]; simp [convUnitEReal]
    rw [term1, term2, add_zero]
  · -- combined point nonzero: `convUnitEReal` there is `⊤`
    conv_rhs => rw [convUnitEReal, if_neg hpt]
    exact le_top

/-! ## Sub-`Dioid` packaging
A predicate-builder `IsSubDioid` (the `Dioid`-level analogue of
`IsSubCompleteDioid`, with **no** `iSup` field), and its instantiation on the
concave non-negative curves. -/

/-- `P` is closed under `⊕ₒ`, `⊗ₒ`, `εₒ`, `eₒ` — a sub-`Dioid` predicate
(the `Dioid`-level analogue of `IsSubCompleteDioid`, with no `iSup`). -/
structure IsSubDioid {T : Type*} [Algebra.Dioid T] (P : T → Prop) : Prop where
  add : ∀ {a b}, P a → P b → P (a ⊕ₒ b)
  mul : ∀ {a b}, P a → P b → P (a ⊗ₒ b)
  eps : P εₒ
  one : P eₒ

/-- `Algebra.Dioid` on the subtype `{x // P x}` of a sub-`Dioid` predicate `P`. -/
@[reducible] noncomputable def IsSubDioid.toDioid
    {T : Type*} [Algebra.Dioid T] {P : T → Prop} (h : IsSubDioid P) :
    Algebra.Dioid {x : T // P x} where
  add a b := ⟨a.1 ⊕ₒ b.1, h.add a.2 b.2⟩
  zero := ⟨εₒ, h.eps⟩
  mul a b := ⟨a.1 ⊗ₒ b.1, h.mul a.2 b.2⟩
  one := ⟨eₒ, h.one⟩
  oplus_assoc _ _ _ := Subtype.ext (add_assoc _ _ _)
  eps_oplus _ := Subtype.ext (zero_add _)
  oplus_eps _ := Subtype.ext (add_zero _)
  oplus_comm _ _ := Subtype.ext (add_comm _ _)
  otimes_assoc _ _ _ := Subtype.ext (mul_assoc _ _ _)
  one_otimes _ := Subtype.ext (one_mul _)
  otimes_one _ := Subtype.ext (mul_one _)
  left_distrib _ _ _ := Subtype.ext (mul_add _ _ _)
  right_distrib _ _ _ := Subtype.ext (add_mul _ _ _)
  eps_otimes _ := Subtype.ext (zero_mul _)
  otimes_eps _ := Subtype.ext (mul_zero _)
  otimes_comm _ _ := Subtype.ext (mul_comm _ _)
  oplus_idem _ := Subtype.ext (Algebra.Dioid.oplus_idem _)

/-- The concave non-negative curves are closed under the `ECurve` operations:
`⊕ₒ` (`ConcaveE.inf`), `⊗ₒ` (`ConcaveE_minConv`), `εₒ = topCurve`
(`ConcaveE_topCurve`), `eₒ = convUnitEReal` (`ConcaveE_convUnitEReal`). -/
theorem isSubDioid_concaveE :
    IsSubDioid (fun a : ECurve => ConcaveE a.1) where
  add ha hb := ConcaveE.inf _ _ ha hb
  mul {a b} ha hb := ConcaveE_minConv ha hb a.2 b.2
  eps := ConcaveE_topCurve
  one := ConcaveE_convUnitEReal

/-- The (min,+) Dioid of **concave** non-negative `EReal` curves. -/
noncomputable instance : Algebra.Dioid {a : ECurve // ConcaveE a.1} :=
  isSubDioid_concaveE.toDioid

end DeepWiki
