import DeepWiki.NetworkCalculus.LegendreFenchel

/-! # Fenchel–Moreau via supporting lines
The reverse biconjugate inequality `f ≤ 𝓛(𝓛 f)` — completing the
Fenchel–Moreau involution `𝓛(𝓛 f) = f` — follows from the book's supporting-line
argument. A curve `f` has a *supporting line* at `x` of slope `ρ` when the affine
map through `(x, f x)` of slope `ρ` lies below `f` (`HasSupportingLineAt`). The
content here is purely algebraic and needs no convexity: if `f` has a supporting
line at `x` of slope `ρ` (and `f x` is finite), then `𝓛(f)` has a supporting line
at `ρ` of slope `x`, so applying the same step twice recovers `𝓛(𝓛 f) x = f x`.
The involution `𝓛(𝓛 f) = f` then holds for any curve admitting a (finite-valued)
supporting line at every point. The one remaining analytic fact — that a convex
non-decreasing curve does admit supporting lines everywhere — is the standard
subgradient existence statement and is not formalized here. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- `f` has a **supporting line** at `x` of slope `ρ`: the affine map through
`(x, f x)` of slope `ρ` lies below `f`, `f x + ρ·(y − x) ≤ f y` for all `y`
(the displacement `y − x` is taken in `ℝ`, so the line may dip below `f x`
for `y < x`). -/
def HasSupportingLineAt (f : ℝ≥0 → EReal) (x ρ : ℝ≥0) : Prop :=
  ∀ y : ℝ≥0, f x + (((ρ : ℝ) * ((y : ℝ) - (x : ℝ)) : ℝ) : EReal) ≤ f y

/-- **The transform value at a supporting slope**: if `f` has a supporting line at
`x` of slope `ρ` and `f x` is finite, then `𝓛(f) ρ = ↑(ρ·x) − f x` — the supremum
defining `𝓛(f) ρ` is attained at `u = x`. -/
theorem legendre_apply_eq_of_hasSupportingLineAt {f : ℝ≥0 → EReal} {x ρ : ℝ≥0}
    (hsupp : HasSupportingLineAt f x ρ) (htop : f x ≠ ⊤) (hbot : f x ≠ ⊥) :
    legendre f ρ = (((ρ * x : ℝ≥0) : ℝ) : EReal) - f x := by
  obtain ⟨cr, hcr⟩ : ∃ cr : ℝ, f x = (cr : EReal) := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  apply le_antisymm
  · rw [legendre_apply]
    refine iSup_le fun u => ?_
    rcases eq_or_ne (f u) ⊤ with hfu | hfu
    · rw [hfu, EReal.sub_top]; exact bot_le
    · -- `f u` is finite (supporting line keeps it `> ⊥`)
      have hlb : ((cr + (ρ : ℝ) * ((u : ℝ) - (x : ℝ)) : ℝ) : EReal) ≤ f u := by
        have := hsupp u; rwa [hcr, ← EReal.coe_add] at this
      have hfu_bot : f u ≠ ⊥ := fun h => by rw [h] at hlb; exact (EReal.coe_ne_bot _) (le_bot_iff.mp hlb)
      obtain ⟨du, hdu⟩ : ∃ du : ℝ, f u = (du : EReal) :=
        ⟨(f u).toReal, (EReal.coe_toReal hfu hfu_bot).symm⟩
      rw [hdu, hcr, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      rw [hdu] at hlb
      rw [EReal.coe_le_coe_iff] at hlb
      push_cast at hlb ⊢
      nlinarith [hlb]
  · exact le_legendre f ρ x

/-- **The transform inherits a supporting line**: if `f` has a supporting line at
`x` of slope `ρ` (with `f x` finite), then `𝓛(f)` has a supporting line at `ρ` of
slope `x`. The affine minorant of `𝓛(f)` is realized by the single slice `u = x`
of the defining supremum. -/
theorem hasSupportingLineAt_legendre {f : ℝ≥0 → EReal} {x ρ : ℝ≥0}
    (hsupp : HasSupportingLineAt f x ρ) (htop : f x ≠ ⊤) (hbot : f x ≠ ⊥) :
    HasSupportingLineAt (legendre f) ρ x := by
  obtain ⟨cr, hcr⟩ : ∃ cr : ℝ, f x = (cr : EReal) := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  intro ρ'
  rw [legendre_apply_eq_of_hasSupportingLineAt hsupp htop hbot, hcr]
  -- LHS `(↑(ρx) − ↑cr) + ↑(x(ρ'−ρ))` equals `↑(ρ'x) − ↑cr`, a slice lower bound
  have hLHS : (((ρ * x : ℝ≥0) : ℝ) : EReal) - (cr : EReal)
        + (((x : ℝ) * ((ρ' : ℝ) - (ρ : ℝ)) : ℝ) : EReal)
      = (((ρ' * x : ℝ≥0) : ℝ) : EReal) - (cr : EReal) := by
    rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_sub]
    congr 1
    push_cast
    ring
  rw [hLHS]
  have h := le_legendre f ρ' x
  rwa [hcr] at h

/-- **The biconjugate recovers `f` at a supporting point**: if `f` has a supporting
line at `x` of slope `ρ` and `f x` is finite, then `𝓛(𝓛 f) x = f x`. Apply the
supporting-line step twice: `𝓛(f)` supports at `ρ` (slope `x`), so the value
formula at that slope gives `𝓛(𝓛 f) x = ↑(x·ρ) − 𝓛(f) ρ = f x`. -/
theorem legendre_legendre_apply_eq_of_hasSupportingLineAt {f : ℝ≥0 → EReal} {x ρ : ℝ≥0}
    (hsupp : HasSupportingLineAt f x ρ) (htop : f x ≠ ⊤) (hbot : f x ≠ ⊥) :
    legendre (legendre f) x = f x := by
  obtain ⟨cr, hcr⟩ : ∃ cr : ℝ, f x = (cr : EReal) := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  have hval : legendre f ρ = (((ρ * x : ℝ≥0) : ℝ) : EReal) - f x :=
    legendre_apply_eq_of_hasSupportingLineAt hsupp htop hbot
  have htop' : legendre f ρ ≠ ⊤ := by
    rw [hval, hcr, ← EReal.coe_sub]; exact EReal.coe_ne_top _
  have hbot' : legendre f ρ ≠ ⊥ := by
    rw [hval, hcr, ← EReal.coe_sub]; exact EReal.coe_ne_bot _
  have hsupp2 : HasSupportingLineAt (legendre f) ρ x :=
    hasSupportingLineAt_legendre hsupp htop hbot
  rw [legendre_apply_eq_of_hasSupportingLineAt hsupp2 htop' hbot', hval, hcr]
  rw [← EReal.coe_sub, ← EReal.coe_sub]
  rw [show (((x * ρ : ℝ≥0) : ℝ) - (((ρ * x : ℝ≥0) : ℝ) - cr) : ℝ) = cr by push_cast; ring]

/-- **Reverse Fenchel–Moreau via supporting lines**: a curve `f` that is finite
everywhere and admits a supporting line at every point equals its own biconjugate,
`𝓛(𝓛 f) = f`. (For a convex non-decreasing `f` the supporting lines exist by the
standard subgradient argument; that analytic step is not formalized.) -/
theorem legendre_legendre_eq_of_forall_hasSupportingLine {f : ℝ≥0 → EReal}
    (hfin : ∀ x, f x ≠ ⊤ ∧ f x ≠ ⊥) (hsupp : ∀ x, ∃ ρ, HasSupportingLineAt f x ρ) :
    legendre (legendre f) = f := by
  funext x
  obtain ⟨ρ, hρ⟩ := hsupp x
  exact legendre_legendre_apply_eq_of_hasSupportingLineAt hρ (hfin x).1 (hfin x).2

end DeepWiki
