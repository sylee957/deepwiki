import Book.Deviations
import Book.PseudoInverse

/-! # Deviations and (min,plus) operators
The horizontal deviation in terms of the pseudo-inverse: at a finite time
where `f` sits strictly above `g`, the pointwise horizontal deviation is
the first time non-decreasing `g` reaches `f t`, shifted back by `t`:
`hDevAt f g t = pseudoInv g (f t) - t` (on the `ℝ≥0∞` domain, where the
pseudo-inverse lives). -/

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
    rcases isEmpty_or_nonempty {d : ℝ≥0∞ // f t ≤ g (t + d)} with he | hne
    · rw [hDevAt_eq_top ℝ≥0∞ f g t fun d hd => he.elim ⟨d, hd⟩]
      exact le_top
    · refine tsub_le_iff_right.mpr ?_
      calc pseudoInv g (f t)
          ≤ ⨅ d : {d : ℝ≥0∞ // f t ≤ g (t + d)}, (d.1 + t) :=
            le_iInf fun d =>
              pseudoInv_le_of_le_apply (by rw [add_comm]; exact d.2)
        _ = (hDevAt f g t : ℝ≥0∞) + t := ENNReal.iInf_add.symm

/-! ## Book restatement (horizontal deviation from pseudo-inverse)
For non-decreasing `f, g` and finite `t` with `f t > g t`,
`hDev(f, g, t) = g⁻¹(f(t)) - t`. -/
example {f g : ℝ≥0∞ → ℝ≥0∞} (_hf : Monotone f) (hg : Monotone g)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) (hgt : g t < f t) :
    (hDevAt f g t : ℝ≥0∞) = pseudoInv g (f t) - t :=
  hDevAt_eq_pseudoInv_sub_of_lt hg ht hgt

end DeepWiki
