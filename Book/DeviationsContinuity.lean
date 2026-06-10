import Book.Deviations
import Mathlib.Topology.Order.LeftRightLim

/-! # Deviations are continuity insensitive
The horizontal and vertical deviations do not distinguish the left- and
right-closures of their arguments: `hDev (leftLim f) (leftLim g) =
hDev (rightLim f) (rightLim g)` and likewise for `vDev`. Monotonicity
alone suffices (the book additionally assumes piecewise continuity): the
infima and suprema absorb the limiting arguments through the cross
inequality `rightLim h x ≤ leftLim h y` for `x < y`. -/

namespace DeepWiki

open Function Set Topology Filter
open scoped Classical NNReal ENNReal

/-- The left-below filter at a positive point of `ℝ≥0` is non-trivial. -/
theorem nhdsLT_ne_bot_of_pos {t : ℝ≥0} (ht : 0 < t) : 𝓝[<] t ≠ ⊥ :=
  Filter.neBot_iff.mp <|
    (nhdsLT_basis_of_exists_lt ⟨0, ht⟩).neBot_iff.mpr
      fun hl => Set.nonempty_Ioo.mpr hl

/-- The right-above filter at any point of `ℝ≥0` is non-trivial. -/
theorem nhdsGT_ne_bot (t : ℝ≥0) : 𝓝[>] t ≠ ⊥ :=
  Filter.neBot_iff.mp <|
    (nhdsGT_basis t).neBot_iff.mpr fun hl => Set.nonempty_Ioo.mpr hl

/-- **Variation of the horizontal deviation**: shifting the time forward by
`s` lowers the deviation by at most `s`,
`hDevAt f g t ≤ s + hDevAt f g (t + s)` (for non-decreasing `f`). -/
theorem hDevAt_le_add_hDevAt {f g : ℝ≥0 → ℝ≥0∞} (hf : Monotone f)
    (t s : ℝ≥0) :
    (hDevAt f g t : ℝ≥0∞) ≤ ↑s + hDevAt f g (t + s) := by
  rcases isEmpty_or_nonempty {d : ℝ≥0 // f (t + s) ≤ g (t + s + d)} with
    he | hne
  · rw [hDevAt_eq_top ℝ≥0∞ f g (t + s) fun d hd => he.elim ⟨d, hd⟩, add_top]
    exact le_top
  · calc (hDevAt f g t : ℝ≥0∞)
        ≤ ⨅ d : {d : ℝ≥0 // f (t + s) ≤ g (t + s + d)},
            ((s : ℝ≥0∞) + ↑d.1) :=
          le_iInf fun d => by
            rw [← ENNReal.coe_add]
            exact hDevAt_le (show f t ≤ g (t + (s + d.1)) by
              rw [← add_assoc]
              exact (hf le_self_add).trans d.2)
      _ = (s : ℝ≥0∞)
            + ⨅ d : {d : ℝ≥0 // f (t + s) ≤ g (t + s + d)},
                (↑d.1 : ℝ≥0∞) :=
          ENNReal.add_iInf.symm
      _ = ↑s + hDevAt f g (t + s) := rfl

/-- Core insensitivity: an admissible time for `rightLim g` makes every
later time admissible for `leftLim g`, so the two infima agree,
`hDevAt f (leftLim g) t ≤ hDevAt f (rightLim g) t`. -/
theorem hDevAt_leftLim_le_hDevAt_rightLim {f g : ℝ≥0 → ℝ≥0∞}
    (hg : Monotone g) (t : ℝ≥0) :
    (hDevAt f (leftLim g) t : ℝ≥0∞) ≤ hDevAt f (rightLim g) t := by
  refine le_iInf fun d => ?_
  show (hDevAt f (leftLim g) t : ℝ≥0∞) ≤ ((d.1 : ℝ≥0) : ℝ≥0∞)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [← ENNReal.coe_add]
  exact hDevAt_le (d.2.trans (hg.rightLim_le_leftLim
    ((add_lt_add_iff_left t).mpr (lt_add_of_pos_right d.1 hε))))

/-- The pointwise horizontal deviation is insensitive to left-closing its
second argument: `hDevAt f (leftLim g) t = hDevAt f g t` for non-decreasing
`g` (no continuity needed). -/
theorem hDevAt_leftLim_right_eq {f g : ℝ≥0 → ℝ≥0∞} (hg : Monotone g)
    (t : ℝ≥0) :
    (hDevAt f (leftLim g) t : ℝ≥0∞) = hDevAt f g t :=
  le_antisymm
    ((hDevAt_leftLim_le_hDevAt_rightLim hg t).trans
      (hDevAt_mono le_rfl (fun _ => hg.le_rightLim le_rfl) t))
    (hDevAt_mono le_rfl (fun _ => hg.leftLim_le le_rfl) t)

/-- The pointwise horizontal deviation is insensitive to right-closing its
second argument: `hDevAt f (rightLim g) t = hDevAt f g t` for non-decreasing
`g`. -/
theorem hDevAt_rightLim_right_eq {f g : ℝ≥0 → ℝ≥0∞} (hg : Monotone g)
    (t : ℝ≥0) :
    (hDevAt f (rightLim g) t : ℝ≥0∞) = hDevAt f g t :=
  le_antisymm
    (hDevAt_mono le_rfl (fun _ => hg.le_rightLim le_rfl) t)
    ((hDevAt_mono le_rfl (fun _ => hg.leftLim_le le_rfl) t).trans
      (hDevAt_leftLim_le_hDevAt_rightLim hg t))

/-- The shifted comparison of the two closures: the right-closed deviation
at `t` is at most `δ` more than the left-closed one at `t + δ` (the cross
inequality `rightLim f t ≤ leftLim f (t + δ)` transfers admissibility). -/
theorem hDevAt_rightLim_le_add_hDevAt_leftLim {f g : ℝ≥0 → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) (t : ℝ≥0) {δ : ℝ≥0} (hδ : 0 < δ) :
    (hDevAt (rightLim f) (rightLim g) t : ℝ≥0∞)
      ≤ ↑δ + hDevAt (leftLim f) (leftLim g) (t + δ) := by
  rcases isEmpty_or_nonempty
      {d : ℝ≥0 // leftLim f (t + δ) ≤ leftLim g (t + δ + d)} with he | hne
  · rw [hDevAt_eq_top ℝ≥0∞ (leftLim f) (leftLim g) (t + δ)
      fun d hd => he.elim ⟨d, hd⟩, add_top]
    exact le_top
  · calc (hDevAt (rightLim f) (rightLim g) t : ℝ≥0∞)
        ≤ ⨅ d : {d : ℝ≥0 // leftLim f (t + δ) ≤ leftLim g (t + δ + d)},
            ((δ : ℝ≥0∞) + ↑d.1) :=
          le_iInf fun d => by
            rw [← ENNReal.coe_add]
            refine hDevAt_le (show rightLim f t ≤ rightLim g (t + (δ + d.1))
              from ?_)
            calc rightLim f t
                ≤ leftLim f (t + δ) :=
                  hf.rightLim_le_leftLim (lt_add_of_pos_right t hδ)
              _ ≤ leftLim g (t + δ + d.1) := d.2
              _ ≤ rightLim g (t + δ + d.1) := hg.leftLim_le_rightLim le_rfl
              _ = rightLim g (t + (δ + d.1)) := by rw [add_assoc]
      _ = (δ : ℝ≥0∞)
            + ⨅ d : {d : ℝ≥0 // leftLim f (t + δ) ≤ leftLim g (t + δ + d)},
                (↑d.1 : ℝ≥0∞) :=
          ENNReal.add_iInf.symm
      _ = ↑δ + hDevAt (leftLim f) (leftLim g) (t + δ) := rfl

/-- **The horizontal deviation is continuity insensitive**: the left- and
right-closures of a non-decreasing pair have the same horizontal deviation
(no piecewise continuity needed). -/
theorem hDev_leftLim_eq_hDev_rightLim {f g : ℝ≥0 → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) :
    (hDev (leftLim f) (leftLim g) : ℝ≥0∞)
      = hDev (rightLim f) (rightLim g) := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    calc (hDevAt (leftLim f) (leftLim g) t : ℝ≥0∞)
        = hDevAt (leftLim f) (rightLim g) t := by
          rw [hDevAt_leftLim_right_eq hg, hDevAt_rightLim_right_eq hg]
      _ ≤ hDevAt (rightLim f) (rightLim g) t :=
          hDevAt_mono (fun _ => hf.leftLim_le_rightLim le_rfl) le_rfl t
      _ ≤ hDev (rightLim f) (rightLim g) := hDevAt_le_hDev _ _ t
  · refine iSup_le fun t => ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    calc (hDevAt (rightLim f) (rightLim g) t : ℝ≥0∞)
        ≤ ↑ε + hDevAt (leftLim f) (leftLim g) (t + ε) :=
          hDevAt_rightLim_le_add_hDevAt_leftLim hf hg t hε
      _ ≤ ↑ε + hDev (leftLim f) (leftLim g) :=
          add_le_add le_rfl (hDevAt_le_hDev _ _ _)
      _ = hDev (leftLim f) (leftLim g) + ↑ε := add_comm _ _

/-- **The vertical deviation is continuity insensitive**: the left- and
right-closures of a non-decreasing pair with `f 0 = 0` have the same
vertical deviation. -/
theorem vDev_leftLim_eq_vDev_rightLim {f g : ℝ≥0 → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) (hf0 : f 0 = 0) :
    vDev (leftLim f) (leftLim g) = vDev (rightLim f) (rightLim g) := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rcases eq_or_ne t 0 with rfl | ht
    · show leftLim f 0 - leftLim g 0 ≤ _
      rw [leftLim_eq_of_isBot (f := f) fun b => zero_le', hf0, zero_tsub]
      exact zero_le'
    · show leftLim f t - leftLim g t ≤ _
      rw [hf.leftLim_eq_sSup (nhdsLT_ne_bot_of_pos (pos_iff_ne_zero.mpr ht)),
        tsub_le_iff_right]
      refine sSup_le ?_
      rintro b ⟨y, (hy : y < t), rfl⟩
      rw [← tsub_le_iff_right]
      calc f y - leftLim g t
          ≤ rightLim f y - rightLim g y :=
            tsub_le_tsub (hf.le_rightLim le_rfl)
              (hg.rightLim_le_leftLim hy)
        _ ≤ vDev (rightLim f) (rightLim g) := vDevAt_le_vDev _ _ y
  · refine iSup_le fun t => ?_
    show rightLim f t - rightLim g t ≤ _
    rw [tsub_le_iff_right]
    calc rightLim f t
        ≤ ⨅ δ : {δ : ℝ≥0 // 0 < δ},
            (vDev (leftLim f) (leftLim g) + leftLim g (t + δ.1)) :=
          le_iInf fun δ => by
            calc rightLim f t
                ≤ leftLim f (t + δ.1) :=
                  hf.rightLim_le_leftLim (lt_add_of_pos_right t δ.2)
              _ ≤ (leftLim f (t + δ.1) - leftLim g (t + δ.1))
                    + leftLim g (t + δ.1) := le_tsub_add
              _ ≤ vDev (leftLim f) (leftLim g) + leftLim g (t + δ.1) :=
                  add_le_add (vDevAt_le_vDev _ _ _) le_rfl
      _ = vDev (leftLim f) (leftLim g)
            + ⨅ δ : {δ : ℝ≥0 // 0 < δ}, leftLim g (t + δ.1) :=
          ENNReal.add_iInf.symm
      _ ≤ vDev (leftLim f) (leftLim g) + rightLim g t := by
          refine add_le_add le_rfl ?_
          rw [hg.rightLim_eq_sInf (nhdsGT_ne_bot t)]
          refine le_sInf ?_
          rintro b ⟨z, (hz : t < z), rfl⟩
          refine iInf_le_of_le ⟨z - t, tsub_pos_of_lt hz⟩ ?_
          rw [add_tsub_cancel_of_le hz.le]
          exact hg.leftLim_le le_rfl

/-! ## Book restatement (performance operators are continuity insensitive)
For non-decreasing `f, g ∈ ℱ₀↑` with left- and right-closures
`fₗ, fᵣ, gₗ, gᵣ`: `hDev(fᵣ, gᵣ) = hDev(fₗ, gₗ)` and
`vDev(fᵣ, gᵣ) = vDev(fₗ, gₗ)`, with the intermediate lemmas: the
variation bound `hDev(f, g, t + s) ≥ hDev(f, g, t) - s`, the second-slot
insensitivity `hDev(f, g, t) = hDev(f, gₗ, t) = hDev(f, gᵣ, t)`, and
`hDev(fₗ, g, t) ≤ hDev(fᵣ, g, t)`. The book's piecewise-continuity
hypothesis is not needed; null-at-origin enters only on the vertical
side (for `f`, at `t = 0`). -/
example {f g : ℝ≥0 → ℝ≥0∞} (hf : Monotone f) (_hg : Monotone g)
    (t s : ℝ≥0) :
    (hDevAt f g t : ℝ≥0∞) - ↑s ≤ hDevAt f g (t + s) :=
  tsub_le_iff_left.mpr (hDevAt_le_add_hDevAt hf t s)

example {f g : ℝ≥0 → ℝ≥0∞} (_hf : Monotone f) (hg : Monotone g)
    (t : ℝ≥0) :
    (hDevAt f g t : ℝ≥0∞) = hDevAt f (leftLim g) t ∧
      (hDevAt f g t : ℝ≥0∞) = hDevAt f (rightLim g) t :=
  ⟨(hDevAt_leftLim_right_eq hg t).symm,
    (hDevAt_rightLim_right_eq hg t).symm⟩

example {f g : ℝ≥0 → ℝ≥0∞} (hf : Monotone f) (_hg : Monotone g)
    (t : ℝ≥0) :
    (hDevAt (leftLim f) g t : ℝ≥0∞) ≤ hDevAt (rightLim f) g t :=
  hDevAt_mono (fun _ => hf.leftLim_le_rightLim le_rfl) le_rfl t

example {f g : ℝ≥0 → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g)
    (hf0 : f 0 = 0) (_hg0 : g 0 = 0) :
    (hDev (rightLim f) (rightLim g) : ℝ≥0∞)
        = hDev (leftLim f) (leftLim g) ∧
      vDev (rightLim f) (rightLim g) = vDev (leftLim f) (leftLim g) :=
  ⟨(hDev_leftLim_eq_hDev_rightLim hf hg).symm,
    (vDev_leftLim_eq_vDev_rightLim hf hg hf0).symm⟩

end DeepWiki
