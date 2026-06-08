import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Concave curves
Concavity for curves `f : ℝ≥0 → EReal`, stated faithfully as "lies above its
chords" using `EReal`'s own multiplication and addition (there is no
`SMul ℝ EReal`, so the chord weights enter as the real→`EReal` coercion of a
`ℝ≥0`). The convex combination of the domain points is taken in `ℝ≥0` with
truncated subtraction, keeping `p * s + (1 - p) * t` in `ℝ≥0` cleanly. The
main result is that a finite concave curve is continuous on `(0, ∞)`, obtained
by bridging to Mathlib's real-valued `ConcaveOn` and `ConcaveOn.continuousOn`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Set

/-- A curve `f : ℝ≥0 → EReal` is concave when it lies above each of its chords:
for `p ≤ 1`, `↑p * f s + ↑(1 - p) * f t ≤ f (p * s + (1 - p) * t)`, with the
weights coerced `ℝ≥0 → ℝ → EReal` and `EReal` multiplication/addition. -/
def ConcaveE (f : ℝ≥0 → EReal) : Prop :=
  ∀ s t : ℝ≥0, ∀ p : ℝ≥0, p ≤ 1 →
    ((p : ℝ) : EReal) * f s + (((1 - p : ℝ≥0) : ℝ) : EReal) * f t
      ≤ f (p * s + (1 - p) * t)

/-- A curve `f : ℝ≥0 → EReal` is finite on the positive ray: `f x ≠ ⊤` and
`f x ≠ ⊥` for every `x > 0`. -/
def FiniteOnPos (f : ℝ≥0 → EReal) : Prop :=
  ∀ x : ℝ≥0, 0 < x → f x ≠ ⊤ ∧ f x ≠ ⊥

/-- The real-curve shadow `x ↦ (f x.toNNReal).toReal` of a curve `f`, the
ℝ-domain/ℝ-codomain form on which Mathlib's `ConcaveOn` is stated. -/
noncomputable def toRealCurve (f : ℝ≥0 → EReal) : ℝ → ℝ :=
  fun x => (f x.toNNReal).toReal

/-- A finite concave curve has a concave real shadow on `(0, ∞) ⊆ ℝ`. -/
theorem concaveOn_toRealCurve_of_concaveE
    (f : ℝ≥0 → EReal) (hf : ConcaveE f)
    (hfin : FiniteOnPos f) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (toRealCurve f) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  -- carry the chord weight into `ℝ≥0`
  have ha1 : a ≤ 1 := by linarith
  set p : ℝ≥0 := a.toNNReal with hp
  have hpa : (p : ℝ) = a := Real.coe_toNNReal a ha
  have hp1 : p ≤ 1 := by
    rw [← NNReal.coe_le_coe, hpa, NNReal.coe_one]; exact ha1
  have h1p : ((1 - p : ℝ≥0) : ℝ) = b := by
    rw [NNReal.coe_sub hp1, hpa, NNReal.coe_one]; linarith
  -- domain points as positive `ℝ≥0`
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  set s : ℝ≥0 := x.toNNReal with hs
  set t : ℝ≥0 := y.toNNReal with ht
  have hsx : (s : ℝ) = x := Real.coe_toNNReal x hx0.le
  have hty : (t : ℝ) = y := Real.coe_toNNReal y hy0.le
  have hs0 : 0 < s := by rw [← NNReal.coe_pos, hsx]; exact hx0
  have ht0 : 0 < t := by rw [← NNReal.coe_pos, hty]; exact hy0
  -- combined domain point is positive
  set z : ℝ≥0 := p * s + (1 - p) * t with hz
  have hzval : (z : ℝ) = a • x + b • y := by
    rw [hz]; push_cast [NNReal.coe_add, NNReal.coe_mul, hpa, h1p, hsx, hty]
    simp [smul_eq_mul]
  have hz0 : 0 < z := by
    rw [← NNReal.coe_pos, hzval]
    simp only [smul_eq_mul]
    rcases le_total x y with hxy | hxy
    · nlinarith [mul_nonneg ha hx0.le, mul_nonneg hb hy0.le,
        mul_le_mul_of_nonneg_left hxy hb]
    · nlinarith [mul_nonneg ha hx0.le, mul_nonneg hb hy0.le,
        mul_le_mul_of_nonneg_left hxy ha]
  -- finiteness facts
  obtain ⟨hsT, hsB⟩ := hfin s hs0
  obtain ⟨htT, htB⟩ := hfin t ht0
  obtain ⟨hzT, hzB⟩ := hfin z hz0
  -- the EReal chord inequality at these points
  have hchord := hf s t p hp1
  -- the combined point inside `toRealCurve (a•x+b•y)`
  have hcomb : (a • x + b • y).toNNReal = z := by
    rw [← hzval, Real.toNNReal_coe]
  -- rewrite both EReal sides of the chord as coercions of reals
  have hLeq : ((p : ℝ) : EReal) * f s + (((1 - p : ℝ≥0) : ℝ) : EReal) * f t
      = (((p : ℝ) * (f s).toReal + ((1 - p : ℝ≥0) : ℝ) * (f t).toReal : ℝ) : EReal) := by
    rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul,
      EReal.coe_toReal hsT hsB, EReal.coe_toReal htT htB]
  have hReq : f (p * s + (1 - p) * t) = (((f z).toReal : ℝ) : EReal) := by
    rw [EReal.coe_toReal hzT hzB]
  rw [hLeq, hReq, EReal.coe_le_coe_iff] at hchord
  -- now translate to `toRealCurve` and the `a•/b•` form
  show a • toRealCurve f x + b • toRealCurve f y ≤ toRealCurve f (a • x + b • y)
  rw [toRealCurve, toRealCurve, toRealCurve, hcomb]
  show a • (f s).toReal + b • (f t).toReal ≤ (f z).toReal
  simp only [smul_eq_mul]
  rw [← hpa, ← h1p]
  exact hchord

/-- A finite concave curve `f : ℝ≥0 → EReal` is continuous on `(0, ∞)`. -/
theorem continuousOn_of_concaveE_of_finite
    (f : ℝ≥0 → EReal) (hf : ConcaveE f)
    (hfin : FiniteOnPos f) :
    ContinuousOn f {x : ℝ≥0 | 0 < x} := by
  -- the real shadow is concave, hence continuous, on the open ray `(0, ∞) ⊆ ℝ`
  have hconc : ConcaveOn ℝ (Ioi (0 : ℝ)) (toRealCurve f) :=
    concaveOn_toRealCurve_of_concaveE f hf hfin
  have hRcont : ContinuousOn (toRealCurve f) (Ioi (0 : ℝ)) :=
    hconc.continuousOn isOpen_Ioi
  -- post-compose with the continuous coercion `ℝ → EReal`
  have hEcont : ContinuousOn (fun r : ℝ => ((toRealCurve f r : ℝ) : EReal)) (Ioi (0 : ℝ)) :=
    continuous_coe_real_ereal.comp_continuousOn hRcont
  -- pre-compose with the coercion `ℝ≥0 → ℝ`, which sends `(0,∞)` into `(0,∞)`
  have hmaps : MapsTo ((↑) : ℝ≥0 → ℝ) {x : ℝ≥0 | 0 < x} (Ioi (0 : ℝ)) := by
    intro x hx; exact NNReal.coe_pos.mpr hx
  have hcomp : ContinuousOn
      (fun x : ℝ≥0 => ((toRealCurve f (x : ℝ) : ℝ) : EReal)) {x : ℝ≥0 | 0 < x} :=
    hEcont.comp NNReal.continuous_coe.continuousOn hmaps
  -- and on `(0,∞)` this composite equals `f`, since `f x` is finite there
  refine hcomp.congr ?_
  intro x hx
  have hx0 : 0 < x := hx
  obtain ⟨hxT, hxB⟩ := hfin x hx0
  show f x = ((toRealCurve f (x : ℝ) : ℝ) : EReal)
  rw [toRealCurve, Real.toNNReal_coe, EReal.coe_toReal hxT hxB]

/-- `Ioi`-set restatement: a finite concave curve is continuous on `(0, ∞)`. -/
theorem continuousOn_Ioi_of_concaveE_of_finite
    (f : ℝ≥0 → EReal) (hf : ConcaveE f)
    (hfin : FiniteOnPos f) :
    ContinuousOn f (Ioi (0 : ℝ≥0)) :=
  continuousOn_of_concaveE_of_finite f hf hfin
