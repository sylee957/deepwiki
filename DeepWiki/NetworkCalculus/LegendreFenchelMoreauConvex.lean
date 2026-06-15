import DeepWiki.NetworkCalculus.LegendreFenchelMoreau
import DeepWiki.NetworkCalculus.Convex
import Mathlib.Analysis.Convex.Slope

/-! # Supporting-line existence for convex non-decreasing curves
Discharges the analytic step left open by `LegendreFenchelMoreau`: a finite,
convex, non-decreasing curve admits a supporting line of non-negative slope at
every point, so its Fenchel–Moreau involution `𝓛(𝓛 f) = f` holds unconditionally.
The slope is `sInf` of the right-hand secant slopes — bounded below by `0` since
`f` is non-decreasing, below every right slope by `csInf_le`, and above every
left slope by `slope_mono_adjacent`; no derivatives or interior/boundary
case-split are needed. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Set

/-- **Supporting slope for a real convex non-decreasing function**: at any
`x ≥ 0`, the infimum of the right-hand secant slopes is a non-negative subgradient
— the affine map of that slope through `(x, g x)` stays below `g` on `[0,∞)`. -/
theorem exists_supporting_slope_real {g : ℝ → ℝ} (hcv : ConvexOn ℝ (Ici 0) g)
    (hmono : MonotoneOn g (Ici 0)) {x : ℝ} (hx : 0 ≤ x) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ y : ℝ, 0 ≤ y → g x + ρ * (y - x) ≤ g y := by
  set S : Set ℝ := (fun w => (g w - g x) / (w - x)) '' Ioi x with hS
  have hSne : S.Nonempty := ⟨(g (x + 1) - g x) / ((x + 1) - x), x + 1, by simp, rfl⟩
  have hlb : ∀ r ∈ S, (0 : ℝ) ≤ r := by
    rintro r ⟨w, (hw : x < w), rfl⟩
    have hwnn : (0 : ℝ) ≤ w := hx.trans hw.le
    have : g x ≤ g w := hmono hx hwnn hw.le
    exact div_nonneg (by linarith) (by linarith)
  have hbdd : BddBelow S := ⟨0, hlb⟩
  refine ⟨sInf S, le_csInf hSne hlb, ?_⟩
  intro y hy
  rcases lt_trichotomy y x with hyx | hyx | hyx
  · -- `y < x`: every right slope dominates the `(y,x)` slope, so it is `≤ sInf S`
    have hub : (g y - g x) / (y - x) ≤ sInf S := by
      refine le_csInf hSne ?_
      rintro r ⟨w, (hw : x < w), rfl⟩
      have hadj := hcv.slope_mono_adjacent (mem_Ici.mpr hy)
        (mem_Ici.mpr (hx.trans hw.le)) hyx hw
      have heq : (g y - g x) / (y - x) = (g x - g y) / (x - y) := by
        rw [← neg_div_neg_eq]; ring_nf
      rw [heq]; exact hadj
    have hlt : y - x < 0 := by linarith
    have hcancel : (g y - g x) / (y - x) * (y - x) = g y - g x :=
      div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_lt hyx))
    have := mul_le_mul_of_nonpos_right hub hlt.le
    rw [hcancel] at this
    linarith
  · subst hyx; simp
  · -- `x < y`: `sInf S ≤` this right slope directly
    have hmem : (g y - g x) / (y - x) ∈ S := ⟨y, hyx, rfl⟩
    have hle : sInf S ≤ (g y - g x) / (y - x) := csInf_le hbdd hmem
    have hpos : (0 : ℝ) < y - x := by linarith
    have hcancel : (g y - g x) / (y - x) * (y - x) = g y - g x :=
      div_mul_cancel₀ _ (ne_of_gt hpos)
    have := mul_le_mul_of_nonneg_right hle hpos.le
    rw [hcancel] at this
    linarith

/-- The real shadow `x ↦ (f ⌜x⌝).toReal` of a finite convex curve is convex on
`[0,∞)` — the chord inequality of `IsConvexEReal` read through `EReal.toReal`. -/
theorem convexOn_toReal_of_isConvexEReal {f : ℝ≥0 → EReal}
    (hfin : ∀ x, f x ≠ ⊤ ∧ f x ≠ ⊥) (hcv : IsConvexEReal f) :
    ConvexOn ℝ (Ici 0) (fun x : ℝ => (f x.toNNReal).toReal) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hx0 : (0 : ℝ) ≤ x := mem_Ici.mp hx
  have hy0 : (0 : ℝ) ≤ y := mem_Ici.mp hy
  have ha1 : a ≤ 1 := by linarith
  set p : ℝ≥0 := a.toNNReal with hp
  have hpa : (p : ℝ) = a := Real.coe_toNNReal a ha
  have hple1 : p ≤ 1 := by rw [← NNReal.coe_le_coe, hpa, NNReal.coe_one]; exact ha1
  have hqb : ((1 - p : ℝ≥0) : ℝ) = b := by rw [NNReal.coe_sub hple1, NNReal.coe_one, hpa]; linarith
  have hxc : (x.toNNReal : ℝ) = x := Real.coe_toNNReal x hx0
  have hyc : (y.toNNReal : ℝ) = y := Real.coe_toNNReal y hy0
  have hxy0 : (0 : ℝ) ≤ a * x + b * y := by positivity
  -- the convex-combination argument matches
  have hcombo : p * x.toNNReal + (1 - p) * y.toNNReal = (a * x + b * y).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul, hpa, hqb, hxc, hyc,
      Real.coe_toNNReal _ hxy0]
  have hconv := hcv x.toNNReal y.toNNReal p hple1
  rw [hcombo, hpa, hqb] at hconv
  -- read off the finite values as genuine reals
  obtain ⟨Br, hBr⟩ : ∃ r : ℝ, f x.toNNReal = (r : EReal) :=
    ⟨(f x.toNNReal).toReal, (EReal.coe_toReal (hfin _).1 (hfin _).2).symm⟩
  obtain ⟨Cr, hCr⟩ : ∃ r : ℝ, f y.toNNReal = (r : EReal) :=
    ⟨(f y.toNNReal).toReal, (EReal.coe_toReal (hfin _).1 (hfin _).2).symm⟩
  rw [hBr, hCr, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hconv
  have hle := EReal.toReal_le_toReal hconv (hfin _).2 (EReal.coe_ne_top _)
  rw [EReal.toReal_coe] at hle
  rw [hBr, hCr, EReal.toReal_coe, EReal.toReal_coe]
  exact hle

/-- The real shadow of a non-decreasing finite curve is non-decreasing on `[0,∞)`. -/
theorem monotoneOn_toReal_of_monotone {f : ℝ≥0 → EReal}
    (hfin : ∀ x, f x ≠ ⊤ ∧ f x ≠ ⊥) (hmono : Monotone f) :
    MonotoneOn (fun x : ℝ => (f x.toNNReal).toReal) (Ici 0) := by
  intro x _ y _ hxy
  exact EReal.toReal_le_toReal (hmono (Real.toNNReal_mono hxy)) (hfin _).2 (hfin _).1

/-- **Supporting line from convexity**: a finite, convex, non-decreasing curve has
a supporting line of non-negative slope at every point — the real-shadow
subgradient (`exists_supporting_slope_real`) transported back to `f`. -/
theorem exists_hasSupportingLineAt_of_isConvexEReal {f : ℝ≥0 → EReal}
    (hfin : ∀ x, f x ≠ ⊤ ∧ f x ≠ ⊥) (hcv : IsConvexEReal f) (hmono : Monotone f) (x : ℝ≥0) :
    ∃ ρ : ℝ≥0, HasSupportingLineAt f x ρ := by
  obtain ⟨ρ, hρ0, hρ⟩ := exists_supporting_slope_real
    (convexOn_toReal_of_isConvexEReal hfin hcv) (monotoneOn_toReal_of_monotone hfin hmono)
    (x := (x : ℝ)) x.coe_nonneg
  refine ⟨ρ.toNNReal, fun y => ?_⟩
  have hg : ∀ z : ℝ≥0, f z = (((f z).toReal : ℝ) : EReal) :=
    fun z => (EReal.coe_toReal (hfin z).1 (hfin z).2).symm
  have h := hρ (y : ℝ) y.coe_nonneg
  simp only [Real.toNNReal_coe] at h
  -- `h : (f x).toReal + ρ * (↑y - ↑x) ≤ (f y).toReal`
  rw [hg x, hg y, Real.coe_toNNReal ρ hρ0, ← EReal.coe_add, EReal.coe_le_coe_iff]
  exact h

/-- **The Fenchel–Moreau involution** (Proposition 3.15, item 4): a finite,
convex, non-decreasing curve equals its own biconjugate, `𝓛(𝓛 f) = f`. The
supporting lines required by `legendre_legendre_eq_of_forall_hasSupportingLine`
exist by `exists_hasSupportingLineAt_of_isConvexEReal`. -/
theorem legendre_legendre_eq_of_isConvexEReal {f : ℝ≥0 → EReal}
    (hfin : ∀ x, f x ≠ ⊤ ∧ f x ≠ ⊥) (hcv : IsConvexEReal f) (hmono : Monotone f) :
    legendre (legendre f) = f :=
  legendre_legendre_eq_of_forall_hasSupportingLine hfin
    (exists_hasSupportingLineAt_of_isConvexEReal hfin hcv hmono)

end DeepWiki
