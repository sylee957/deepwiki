import Book.Concave
import Book.ConcaveProps
import Book.CurveDioidEReal
import Mathlib.Data.EReal.Operations

/-! # The concave sub-`Dioid` of `EReal` curves
The concave bounded-below curves form a sub-`Dioid` of `ECurve`
(`Book.CurveDioidEReal`): closed under `⊕ = ` pointwise `min`, `⊗ = minConv`, and
containing `𝟘 = topCurve`, `𝟙 = convUnitEReal`. The `minConv` case is the
inf-convolution-of-concave-is-concave fact, proved without any attainment /
left-continuity hypothesis by a dichotomy on the (finite-or-`⊤`) origin value. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

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
    {f : ℝ≥0 → EReal} (hf : ConcaveE f) (hnn : NeverBot f) (h0 : f 0 = ⊤) :
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
    -- LHS `↑(1/2) * f s + ⊤`: multiplying `f s ≠ ⊥` by a positive real stays
    -- `≠ ⊥`, so the sum `= ⊤`
    have hmulbot : ((((2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) : EReal) * f s ≠ ⊥ := by
      induction hfs : f s with
      | bot => exact absurd hfs (hnn s)
      | top => rw [EReal.mul_top_of_pos hpos]; simp
      | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
    rw [EReal.add_top_of_ne_bot hmulbot] at hchord
    exact top_le_iff.1 hchord

/-- The inf-convolution of two non-negative concave curves is concave — the
inf-convolution-of-concave-is-concave closure fact. No attainment / left-
continuity hypothesis is required: if either origin value is `⊤` that curve is
`topCurve` (so `minConv` is `topCurve`, concave); otherwise both origin values
are finite reals and the decomposition `minConv f g = ((f − f 0) ⊓ (g − g 0)) +
(f 0 + g 0)` exhibits `minConv f g` as a concave meet shifted by a constant. -/
theorem ConcaveE_minConv
    {f g : ℝ≥0 → EReal} (hf : ConcaveE f) (hg : ConcaveE g)
    (hnf : BddBelowReal f) (hng : BddBelowReal g) :
    ConcaveE (minConv f g) := by
  -- `⊤`-origin dichotomy: handle `f 0 = ⊤` or `g 0 = ⊤` first
  rcases eq_or_ne (f 0) ⊤ with hf0 | hf0
  · rw [eq_topCurve_of_concaveE_of_zero_top hf hnf.neverBot hf0,
      minConv_topCurve_left hng.neverBot]
    exact ConcaveE_topCurve
  rcases eq_or_ne (g 0) ⊤ with hg0 | hg0
  · rw [eq_topCurve_of_concaveE_of_zero_top hg hng.neverBot hg0,
      minConv_topCurve_right hnf.neverBot]
    exact ConcaveE_topCurve
  -- both origin values finite: name them as reals
  set a : ℝ := (f 0).toReal with hadef
  set b : ℝ := (g 0).toReal with hbdef
  have ha : f 0 = (a : EReal) := (EReal.coe_toReal hf0 (hnf.neverBot 0)).symm
  have hb : g 0 = (b : EReal) := (EReal.coe_toReal hg0 (hng.neverBot 0)).symm
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

/-! ## The concave sub-`Dioid`
Instantiating the `IsSubDioid` builder (from `Book.SubDioid`) on the concave
non-negative curves. -/

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
