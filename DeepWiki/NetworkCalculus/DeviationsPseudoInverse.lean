import DeepWiki.NetworkCalculus.Deviations
import DeepWiki.NetworkCalculus.PseudoInverse

/-! # Deviations and (min,plus) operators
The deviations in terms of (min,plus) operators, on the `ℝ≥0∞` domain
where the pseudo-inverse lives. Pointwise, at a finite time the horizontal
deviation is the first time non-decreasing `g` reaches `f t`, shifted back
by `t`: `hDevAt f g t = pseudoInv g (f t) - t` (truncated subtraction
absorbs the `f t ≤ g t` case). Globally the deviations are deconvolutions:
`hDev f g = ((g⁻¹ ∘ f) ⊘ λ₁) 0` with `λ₁` the unit-rate curve `rateENN 1`,
proved here, restated alongside `vDev_eq_deconv_zero` from
`Book.Deviations`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Horizontal deviation from the pseudo-inverse.** For non-decreasing `g`
and `g t < f t` at a finite `t`, the pointwise horizontal deviation is
`hDevAt f g t = g⁻¹(f t) - t`: every time admissible for `g⁻¹(f t)` lies at
or above `t` (below `t`, `g` is still below `f t`), and the shift by `t`
matches the admissible-shift infimum. -/
theorem hDevAt_eq_pseudoInv_sub_of_lt {V : Type*} [Preorder V]
    {f g : ℝ≥0∞ → V} (hg : Monotone g) {t : ℝ≥0∞} (ht : t ≠ ⊤)
    (hgt : g t < f t) :
    (hDevAt f g t : ℝ≥0∞) = pseudoInv g (f t) - t := by
  apply le_antisymm
  · -- `hDevAt + t` is below every admissible time, hence below `g⁻¹(f t)`
    refine (ENNReal.cancel_of_ne ht).le_tsub_of_add_le_right
      (le_pseudoInv fun d' hd' => ?_)
    have htd' : t ≤ d' := by
      by_contra hcon
      exact absurd ((hd'.trans (hg (not_le.mp hcon).le)).trans_lt hgt)
        (lt_irrefl _)
    calc (hDevAt f g t : ℝ≥0∞) + t
        ≤ (d' - t) + t :=
          add_le_add
            (hDevAt_le (show f t ≤ g (t + (d' - t)) by
              rwa [add_tsub_cancel_of_le htd']))
            le_rfl
      _ = d' := tsub_add_cancel_of_le htd'
  · -- conversely each admissible shift `d` makes `t + d` admissible for `g⁻¹`
    exact tsub_le_iff_right.mpr
      (le_hDevAt_add fun d hd =>
        pseudoInv_le_of_le_apply (by rw [add_comm]; exact hd))

/-- The pointwise identity without strictness: truncated subtraction
absorbs the `f t ≤ g t` case, where both sides vanish (`d = 0` is an
admissible shift, and `t` is admissible for `g⁻¹(f t)`). -/
theorem hDevAt_eq_pseudoInv_sub {V : Type*} [LinearOrder V]
    {f g : ℝ≥0∞ → V} (hg : Monotone g) {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    (hDevAt f g t : ℝ≥0∞) = pseudoInv g (f t) - t := by
  rcases le_or_gt (f t) (g t) with hle | hgt
  · have h1 : (hDevAt f g t : ℝ≥0∞) ≤ 0 :=
      hDevAt_le (d := 0) (by rwa [add_zero])
    rw [tsub_eq_zero_of_le (pseudoInv_le_of_le_apply hle)]
    exact le_antisymm h1 zero_le
  · exact hDevAt_eq_pseudoInv_sub_of_lt hg ht hgt

/-- **The horizontal deviation is a deconvolution**:
`hDev f g = ((g⁻¹ ∘ f) ⊘ λ₁) 0` with `λ₁` the unit-rate curve `rateENN 1`.
At the added point `⊤` (absent from the book's `ℝ⁺` domain) the two sides
need `f ⊤ ≤ g ⊤` — truncated subtraction zeroes the deconvolution term
there. -/
theorem hDev_eq_deconv_pseudoInv_zero {V : Type*} [LinearOrder V]
    {f g : ℝ≥0∞ → V} (hg : Monotone g) (htop : f ⊤ ≤ g ⊤) :
    (hDev f g : ℝ≥0∞) = minDeconv (pseudoInv g ∘ f) (rateENN 1) 0 := by
  have hrate : ∀ s : ℝ≥0∞, rateENN 1 s = s := fun s => one_mul s
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rcases eq_or_ne t ⊤ with rfl | ht
    · exact le_trans (hDevAt_le (d := 0) (by rwa [add_zero])) zero_le
    · rw [hDevAt_eq_pseudoInv_sub hg ht]
      have h := sub_le_minDeconv (pseudoInv g ∘ f) (rateENN 1) 0 t
      rwa [zero_add, Function.comp_apply, hrate] at h
  · refine minDeconv_le fun s => ?_
    rcases eq_or_ne s ⊤ with rfl | hs
    · rw [hrate, ENNReal.sub_top]
      exact zero_le
    · rw [zero_add, Function.comp_apply, hrate,
        ← hDevAt_eq_pseudoInv_sub hg hs]
      exact hDevAt_le_hDev f g s

/-! ## Book restatement (deviations are deconvolutions)
For non-decreasing `f, g`: pointwise at finite `t` with `f t > g t`,
`hDev(f, g, t) = g⁻¹(f(t)) - t`; globally `vDev(f, g) = (f ⊘ g)(0)` and
`hDev(f, g) = ((g⁻¹ ∘ f) ⊘ λ₁)(0)`. -/
example {f g : ℝ≥0∞ → ℝ≥0∞} (_hf : Monotone f) (hg : Monotone g)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) (hgt : g t < f t) :
    (hDevAt f g t : ℝ≥0∞) = pseudoInv g (f t) - t :=
  hDevAt_eq_pseudoInv_sub_of_lt hg ht hgt

example {f g : ℝ≥0∞ → ℝ≥0∞} (_hf : Monotone f) (_hg : Monotone g) :
    vDev f g = minDeconv f g 0 :=
  vDev_eq_deconv_zero f g

example {f g : ℝ≥0∞ → ℝ≥0∞} (_hf : Monotone f) (hg : Monotone g)
    (htop : f ⊤ ≤ g ⊤) :
    (hDev f g : ℝ≥0∞) = minDeconv (pseudoInv g ∘ f) (rateENN 1) 0 :=
  hDev_eq_deconv_pseudoInv_zero hg htop

end DeepWiki
