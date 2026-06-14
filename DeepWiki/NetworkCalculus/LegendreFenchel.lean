import DeepWiki.NetworkCalculus.Convex

/-! # The Legendre–Fenchel transform
The (min,plus) Legendre–Fenchel transform `𝓛(f)(t) = ⨆_{u≥0} (t·u − f(u))`
on curves `ℝ≥0 → EReal`. It is the pointwise supremum of the affine maps
`t ↦ t·u − f(u)`, so it is non-decreasing and convex, and it turns the
pointwise `min` into a `max`. (Its examples on the catalog curves and the
biconjugate involution `𝓛(𝓛 f) = f` on convex non-decreasing curves are the
deeper Fenchel–Moreau content, not formalized here.) -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The (min,plus) Legendre–Fenchel transform `𝓛(f)(t) = ⨆_{u≥0} (t·u − f(u))`
of a curve `f : ℝ≥0 → EReal`. -/
noncomputable def legendre (f : ℝ≥0 → EReal) : ℝ≥0 → EReal :=
  fun t => ⨆ u : ℝ≥0, (((t * u : ℝ≥0) : ℝ) : EReal) - f u

/-- `𝓛(f) t = ⨆_{u} (↑(t·u) − f u)` (the defining supremum). -/
theorem legendre_apply (f : ℝ≥0 → EReal) (t : ℝ≥0) :
    legendre f t = ⨆ u : ℝ≥0, (((t * u : ℝ≥0) : ℝ) : EReal) - f u := rfl

/-- The Legendre–Fenchel transform is non-decreasing: each affine slice
`t ↦ t·u − f u` grows with `t`, so does their supremum. -/
theorem monotone_legendre (f : ℝ≥0 → EReal) : Monotone (legendre f) := by
  intro a b hab
  refine iSup_mono fun u => ?_
  refine EReal.sub_le_sub ?_ (le_refl (f u))
  have huv : a * u ≤ b * u := by gcongr
  exact_mod_cast huv

/-- A lower-bounding affine slice: `↑(t·u) − f u ≤ 𝓛(f) t` for every `u`. -/
theorem le_legendre (f : ℝ≥0 → EReal) (t u : ℝ≥0) :
    (((t * u : ℝ≥0) : ℝ) : EReal) - f u ≤ legendre f t :=
  le_iSup (fun u => (((t * u : ℝ≥0) : ℝ) : EReal) - f u) u

/-- `𝓛` is antitone: a pointwise-larger curve has a pointwise-smaller
transform (the subtracted term grows). -/
theorem legendre_antitone {f g : ℝ≥0 → EReal} (h : ∀ x, f x ≤ g x) (t : ℝ≥0) :
    legendre g t ≤ legendre f t := by
  refine iSup_mono fun u => ?_
  exact EReal.sub_le_sub (le_refl _) (h u)

end DeepWiki
