import DeepWiki.NetworkCalculus.ConvexConvolution
import DeepWiki.NetworkCalculus.LegendreFenchelMoreauConvex
import DeepWiki.NetworkCalculus.LegendreFenchelConv

/-! # Convex (min,plus) convolution computed in the Legendre–Fenchel domain
For finite, convex, non-decreasing curves the (min,plus) convolution is obtained by
**adding the Legendre–Fenchel transforms and transforming back**:
`f ⊗ g = 𝓛(𝓛 f + 𝓛 g)`. Since the transform `𝓛 h(s) = ⨆_t (s·t − h(t))` is indexed by the
*slope* `s`, pointwise addition of the transforms is exactly the "merge the segments by
slope" rule for piecewise-affine convex curves. The proof composes the Fenchel–Moreau
involution `𝓛(𝓛 h) = h` (for finite convex non-decreasing `h`) with
`𝓛(f ⊗ g) = 𝓛 f + 𝓛 g`, using that `f ⊗ g` is itself finite, convex and non-decreasing. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Convex convolution via the transform** (the slope-domain computation behind Theorem
4.1's segment-merge): for finite, convex, non-decreasing, non-negative curves `f, g`,
`f ⊗ g = 𝓛(𝓛 f + 𝓛 g)`. Adding the slope-indexed Legendre transforms and inverting is the
"merge segments by increasing slope" rule. -/
theorem minConv_eq_legendre_add_legendre {f g : ℝ≥0 → EReal}
    (hf : IsConvexEReal f) (hg : IsConvexEReal g) (hmf : Monotone f) (hmg : Monotone g)
    (hfin_f : ∀ x, f x ≠ ⊤ ∧ f x ≠ ⊥) (hfin_g : ∀ x, g x ≠ ⊤ ∧ g x ≠ ⊥)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    minConv f g = legendre (legendre f + legendre g) := by
  -- `f ⊗ g` is convex, non-decreasing and finite, so Fenchel–Moreau applies to it.
  have hconv : IsConvexEReal (minConv f g) := isConvexEReal_minConv hf hg hf0 hg0
  have hmono : Monotone (minConv f g) := monotone_minConv hmf hmg
  have hfin : ∀ x, minConv f g x ≠ ⊤ ∧ minConv f g x ≠ ⊥ := by
    intro x
    refine ⟨?_, ?_⟩
    · -- `f ⊗ g x ≤ f x + g 0`, a sum of two finite values, hence `≠ ⊤`
      have hle : minConv f g x ≤ f x + g 0 := minConv_le_add f g (add_zero x)
      have hsum : f x + g 0 ≠ ⊤ := by
        obtain ⟨a, ha⟩ : ∃ a : ℝ, f x = (a : EReal) :=
          ⟨(f x).toReal, (EReal.coe_toReal (hfin_f x).1 (hfin_f x).2).symm⟩
        obtain ⟨b, hb⟩ : ∃ b : ℝ, g 0 = (b : EReal) :=
          ⟨(g 0).toReal, (EReal.coe_toReal (hfin_g 0).1 (hfin_g 0).2).symm⟩
        rw [ha, hb, ← EReal.coe_add]; exact EReal.coe_ne_top _
      exact ne_top_of_le_ne_top hsum hle
    · -- `0 ≤ f ⊗ g x`, hence `≠ ⊥`
      have h0le : (0 : EReal) ≤ minConv f g x :=
        le_minConv (fun u s _ => add_nonneg (hf0 u) (hg0 s))
      intro hbot; rw [hbot] at h0le; simp at h0le
  -- `𝓛(f ⊗ g) = 𝓛 f + 𝓛 g` (`minConv` is defeq to `legendreConv`).
  have hL : legendre (minConv f g) = legendre f + legendre g :=
    legendre_legendreConv (fun u => (hfin_f u).2) (fun v => (hfin_g v).2)
  -- Fenchel–Moreau on `f ⊗ g`, then rewrite its transform.
  have hMoreau : legendre (legendre (minConv f g)) = minConv f g :=
    legendre_legendre_eq_of_isConvexEReal hfin hconv hmono
  rw [← hMoreau, hL]

end DeepWiki
