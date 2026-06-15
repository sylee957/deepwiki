import DeepWiki.NetworkCalculus.Convex

/-! # The Legendre–Fenchel transform
The (min,plus) Legendre–Fenchel transform `𝓛(f)(t) = ⨆_{u≥0} (t·u − f(u))`
on curves `ℝ≥0 → EReal`. It is the pointwise supremum of the affine maps
`t ↦ t·u − f(u)`, so it is non-decreasing (`monotone_legendre`) and convex
(`legendre_convex`, for a proper `f`), and it turns the pointwise `min` into a
`max` (`legendre_inf`). (Its examples on the catalog curves and the biconjugate
involution `𝓛(𝓛 f) = f` on convex non-decreasing curves are the deeper
Fenchel–Moreau content, not formalized here.) -/

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

/-- **Fenchel–Young inequality**: `↑(t·u) ≤ 𝓛(f) t + f u` for every finite
`f u` — rearranging the defining lower bound `le_legendre`. -/
theorem fenchel_young (f : ℝ≥0 → EReal) (t u : ℝ≥0) (hb : f u ≠ ⊥) (ht : f u ≠ ⊤) :
    (((t * u : ℝ≥0) : ℝ) : EReal) ≤ legendre f t + f u := by
  have h := le_legendre f t u
  rwa [EReal.sub_le_iff_le_add (.inl hb) (.inl ht)] at h

/-- **The Legendre–Fenchel transform is convex** (for a proper curve `f`, never
`⊥`): it is the pointwise supremum of the affine slices `t ↦ ↑(t·u) − f u`, and
a supremum of affine maps is convex. For each `u` the slice lies below the
convex combination of `𝓛(f) s` and `𝓛(f) t` (via `le_legendre`), and the
supremum inherits the bound. -/
theorem legendre_convex {f : ℝ≥0 → EReal} (hf : ∀ u, f u ≠ ⊥) :
    IsConvexEReal (legendre f) := by
  intro s t p hp
  rw [legendre_apply]
  refine iSup_le fun u => ?_
  have hP0 : (0 : EReal) ≤ ((p : ℝ) : EReal) := by exact_mod_cast p.coe_nonneg
  have hQ0 : (0 : EReal) ≤ (((1 - p : ℝ≥0) : ℝ) : EReal) := by
    exact_mod_cast (1 - p : ℝ≥0).coe_nonneg
  have hPtop : ((p : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hQtop : (((1 - p : ℝ≥0) : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  rcases eq_or_ne (f u) ⊤ with hCtop | hCtop
  · rw [hCtop, EReal.sub_top]; exact bot_le
  · obtain ⟨c, hc⟩ : ∃ c : ℝ, f u = (c : EReal) :=
      ⟨(f u).toReal, (EReal.coe_toReal hCtop (hf u)).symm⟩
    have hhead : ((((p * s + (1 - p) * t) * u : ℝ≥0) : ℝ) : EReal)
        = ((p : ℝ) : EReal) * (((s * u : ℝ≥0) : ℝ) : EReal)
          + (((1 - p : ℝ≥0) : ℝ) : EReal) * (((t * u : ℝ≥0) : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      push_cast [NNReal.coe_sub hp]
      ring
    have hAs : (((s * u : ℝ≥0) : ℝ) : EReal) ≤ legendre f s + (c : EReal) := by
      have h := le_legendre f s u
      rw [hc, EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c)) (.inl (EReal.coe_ne_top c))] at h
      exact h
    have hBt : (((t * u : ℝ≥0) : ℝ) : EReal) ≤ legendre f t + (c : EReal) := by
      have h := le_legendre f t u
      rw [hc, EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c)) (.inl (EReal.coe_ne_top c))] at h
      exact h
    rw [hhead, hc]
    refine (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c)) (.inl (EReal.coe_ne_top c))).mpr ?_
    calc ((p : ℝ) : EReal) * (((s * u : ℝ≥0) : ℝ) : EReal)
          + (((1 - p : ℝ≥0) : ℝ) : EReal) * (((t * u : ℝ≥0) : ℝ) : EReal)
        ≤ ((p : ℝ) : EReal) * (legendre f s + (c : EReal))
          + (((1 - p : ℝ≥0) : ℝ) : EReal) * (legendre f t + (c : EReal)) :=
          add_le_add (mul_le_mul_of_nonneg_left hAs hP0)
            (mul_le_mul_of_nonneg_left hBt hQ0)
      _ = (((p : ℝ) : EReal) * legendre f s + (((1 - p : ℝ≥0) : ℝ) : EReal) * legendre f t)
          + (((p : ℝ) : EReal) * (c : EReal) + (((1 - p : ℝ≥0) : ℝ) : EReal) * (c : EReal)) := by
          rw [EReal.left_distrib_of_nonneg_of_ne_top hP0 hPtop,
            EReal.left_distrib_of_nonneg_of_ne_top hQ0 hQtop, add_add_add_comm]
      _ = (((p : ℝ) : EReal) * legendre f s + (((1 - p : ℝ≥0) : ℝ) : EReal) * legendre f t)
          + (c : EReal) := by
          congr 1
          rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
          congr 1
          push_cast [NNReal.coe_sub hp]
          ring

/-- `𝓛` is antitone: a pointwise-larger curve has a pointwise-smaller
transform (the subtracted term grows). -/
theorem legendre_antitone {f g : ℝ≥0 → EReal} (h : ∀ x, f x ≤ g x) (t : ℝ≥0) :
    legendre g t ≤ legendre f t := by
  refine iSup_mono fun u => ?_
  exact EReal.sub_le_sub (le_refl _) (h u)

/-- **The biconjugate lies below the function**: `𝓛(𝓛 f) ≤ f` pointwise — always,
with no convexity hypothesis (the reverse `f ≤ 𝓛(𝓛 f)`, completing the
Fenchel–Moreau involution `𝓛(𝓛 f) = f`, needs `f` convex non-decreasing and is
not formalized). Each slice `↑(u·s) − 𝓛(f) s ≤ f u` by `le_legendre`. -/
theorem legendre_legendre_le (f : ℝ≥0 → EReal) (u : ℝ≥0) :
    legendre (legendre f) u ≤ f u := by
  rw [legendre_apply]
  refine iSup_le fun s => ?_
  have h : (((s * u : ℝ≥0) : ℝ) : EReal) - f u ≤ legendre f s := le_legendre f s u
  have key : (((s * u : ℝ≥0) : ℝ) : EReal)
      - ((((s * u : ℝ≥0) : ℝ) : EReal) - f u) = f u := by
    rcases eq_or_ne (f u) ⊤ with hf | hf
    · rw [hf, EReal.sub_top, EReal.coe_sub_bot]
    · rcases eq_or_ne (f u) ⊥ with hb | hb
      · rw [hb, EReal.coe_sub_bot, EReal.sub_top]
      · obtain ⟨c, hc⟩ : ∃ c : ℝ, f u = (c : EReal) :=
          ⟨(f u).toReal, (EReal.coe_toReal hf hb).symm⟩
        rw [hc, ← EReal.coe_sub, ← EReal.coe_sub, sub_sub_cancel]
  rw [show (((u * s : ℝ≥0) : ℝ) : EReal) = (((s * u : ℝ≥0) : ℝ) : EReal) by rw [mul_comm]]
  calc (((s * u : ℝ≥0) : ℝ) : EReal) - legendre f s
      ≤ (((s * u : ℝ≥0) : ℝ) : EReal) - ((((s * u : ℝ≥0) : ℝ) : EReal) - f u) :=
        EReal.sub_le_sub (le_refl _) h
    _ = f u := key

/-- **The Legendre–Fenchel transform is idempotent on its range**:
`𝓛(𝓛(𝓛 g)) = 𝓛 g`. So every transform `𝓛 g` is its own biconjugate — the
Fenchel–Moreau fixed points are exactly the transforms. (No convexity needed:
`≤` is `legendre_legendre_le` at `𝓛 g`; `≥` applies the antitone `𝓛` to
`𝓛(𝓛 g) ≤ g`.) -/
theorem legendre_legendre_legendre (g : ℝ≥0 → EReal) :
    legendre (legendre (legendre g)) = legendre g := by
  funext u
  exact le_antisymm (legendre_legendre_le (legendre g) u)
    (legendre_antitone (legendre_legendre_le g) u)

/-- The Legendre–Fenchel transform turns the pointwise `min` into a `max`:
`𝓛(f ⊓ g) = 𝓛(f) ⊔ 𝓛(g)`. Subtracting the smaller of `f u, g u` gives the
larger of the two slices, and the supremum distributes over the join. -/
theorem legendre_inf (f g : ℝ≥0 → EReal) :
    legendre (f ⊓ g) = legendre f ⊔ legendre g := by
  funext t
  show (⨆ u : ℝ≥0, (((t * u : ℝ≥0) : ℝ) : EReal) - (f u ⊓ g u))
      = (⨆ u : ℝ≥0, (((t * u : ℝ≥0) : ℝ) : EReal) - f u)
        ⊔ (⨆ u : ℝ≥0, (((t * u : ℝ≥0) : ℝ) : EReal) - g u)
  rw [← iSup_sup_eq]
  refine iSup_congr fun u => ?_
  set c : EReal := (((t * u : ℝ≥0) : ℝ) : EReal)
  rcases le_total (f u) (g u) with h | h
  · rw [inf_eq_left.mpr h, sup_eq_left.mpr (EReal.sub_le_sub (le_refl c) h)]
  · rw [inf_eq_right.mpr h, sup_eq_right.mpr (EReal.sub_le_sub (le_refl c) h)]

end DeepWiki
