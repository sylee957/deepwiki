import DeepWiki.NetworkCalculus.Concave

/-! # Convex curves
Convexity for curves `f : ℝ≥0 → EReal`, the order-dual of `IsConcaveEReal`
(`DeepWiki.NetworkCalculus.Concave`): `f` lies *below* each of its chords. The
chord weights enter as the real→`EReal` coercion of a `ℝ≥0`, exactly as in the
concave development. Closure under pointwise sum (`+`) and pointwise `max`
(`⊔`) — the duals of `IsConcaveEReal.add` and `IsConcaveEReal.inf`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- A curve `f : ℝ≥0 → EReal` is convex when it lies below each of its chords:
for `p ≤ 1`, `f (p * s + (1 - p) * t) ≤ ↑p * f s + ↑(1 - p) * f t`, with the
weights coerced `ℝ≥0 → ℝ → EReal` and `EReal` multiplication/addition. -/
def IsConvexEReal (f : ℝ≥0 → EReal) : Prop :=
  ∀ s t : ℝ≥0, ∀ p : ℝ≥0, p ≤ 1 →
    f (p * s + (1 - p) * t)
      ≤ ((p : ℝ) : EReal) * f s + (((1 - p : ℝ≥0) : ℝ) : EReal) * f t

/-- Pointwise sum of two convex curves is convex (dual of `IsConcaveEReal.add`):
`EReal` left-distributivity expands each weighted sum, the four scaled summands
regroup by `add_add_add_comm`, and `EReal` addition is monotone. -/
theorem IsConvexEReal.add (f g : ℝ≥0 → EReal) (hf : IsConvexEReal f) (hg : IsConvexEReal g) :
    IsConvexEReal (f + g) := by
  intro s t p hp
  have hp0 : (0 : EReal) ≤ ((p : ℝ) : EReal) := by exact_mod_cast p.coe_nonneg
  have hq0 : (0 : EReal) ≤ (((1 - p : ℝ≥0) : ℝ) : EReal) := by
    exact_mod_cast (1 - p : ℝ≥0).coe_nonneg
  have hptop : ((p : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hqtop : (((1 - p : ℝ≥0) : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hchf := hf s t p hp
  have hchg := hg s t p hp
  show f (p * s + (1 - p) * t) + g (p * s + (1 - p) * t)
      ≤ ((p : ℝ) : EReal) * (f s + g s)
        + (((1 - p : ℝ≥0) : ℝ) : EReal) * (f t + g t)
  rw [EReal.left_distrib_of_nonneg_of_ne_top hp0 hptop,
      EReal.left_distrib_of_nonneg_of_ne_top hq0 hqtop, add_add_add_comm]
  exact add_le_add hchf hchg

/-- Pointwise `max` (`EReal` `⊔`) of two convex curves is convex (dual of
`IsConcaveEReal.inf`): each chord of `f` and of `g` lies below the corresponding
chord of `f ⊔ g`, and the join of the two is below it too. -/
theorem IsConvexEReal.sup (f g : ℝ≥0 → EReal) (hf : IsConvexEReal f) (hg : IsConvexEReal g) :
    IsConvexEReal (f ⊔ g) := by
  intro s t p hp
  simp only [Pi.sup_apply]
  refine sup_le ?_ ?_
  · refine le_trans (hf s t p hp) ?_
    exact add_le_add
      (mul_le_mul_of_nonneg_left le_sup_left (EReal.coe_nonneg.2 p.coe_nonneg))
      (mul_le_mul_of_nonneg_left le_sup_left (EReal.coe_nonneg.2 (1 - p : ℝ≥0).coe_nonneg))
  · refine le_trans (hg s t p hp) ?_
    exact add_le_add
      (mul_le_mul_of_nonneg_left le_sup_right (EReal.coe_nonneg.2 p.coe_nonneg))
      (mul_le_mul_of_nonneg_left le_sup_right (EReal.coe_nonneg.2 (1 - p : ℝ≥0).coe_nonneg))

end DeepWiki
