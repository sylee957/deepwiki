import DeepWiki.NetworkCalculus.ContinuityClosure
import DeepWiki.NetworkCalculus.Deviations
import Mathlib.Topology.Order.LeftRightLim

/-! # Deviations are continuity insensitive
The horizontal and vertical deviations do not distinguish the left- and
right-closures of their arguments: `hDev (leftLim f) (leftLim g) =
hDev (rightLim f) (rightLim g)` for monotone `f, g`, and likewise for
`vDev` when also `f 0 = 0` (needed at the origin). The book additionally
assumes piecewise continuity; the infima and suprema absorb the limiting
arguments through the cross inequality `rightLim h x ≤ leftLim h y` for
`x < y` alone. Combined with the closure fixed points
(`Book.ContinuityClosure`), switching a left-continuous pair to its
right-continuous closures does not change the deviations. -/

namespace DeepWiki

open Function Set Topology Filter
open scoped Classical NNReal ENNReal

/-- **Variation of the horizontal deviation**: shifting the time forward by
`s` lowers the deviation by at most `s`,
`hDevAt f g t ≤ s + hDevAt f g (t + s)` (for non-decreasing `f`). -/
theorem hDevAt_le_add_hDevAt {f g : ℝ≥0 → ℝ≥0∞} (hf : Monotone f)
    (t s : ℝ≥0) :
    (hDevAt f g t : ℝ≥0∞) ≤ ↑s + hDevAt f g (t + s) :=
  le_add_hDevAt fun d hd =>
    hDevAt_le (show f t ≤ g (t + (s + d)) by
      rw [← add_assoc]
      exact (hf le_self_add).trans hd)

/-- Core insensitivity: every shift strictly larger than an admissible
shift for `rightLim g` is admissible for `leftLim g`, so the left-closed
infimum is no larger: `hDevAt f (leftLim g) t ≤ hDevAt f (rightLim g) t`. -/
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
theorem hDevAt_leftLim_eq_hDevAt {f g : ℝ≥0 → ℝ≥0∞} (hg : Monotone g)
    (t : ℝ≥0) :
    (hDevAt f (leftLim g) t : ℝ≥0∞) = hDevAt f g t :=
  le_antisymm
    ((hDevAt_leftLim_le_hDevAt_rightLim hg t).trans
      (hDevAt_mono le_rfl (fun _ => hg.le_rightLim le_rfl) t))
    (hDevAt_mono le_rfl (fun _ => hg.leftLim_le le_rfl) t)

/-- The pointwise horizontal deviation is insensitive to right-closing its
second argument: `hDevAt f (rightLim g) t = hDevAt f g t` for non-decreasing
`g`. -/
theorem hDevAt_rightLim_eq_hDevAt {f g : ℝ≥0 → ℝ≥0∞} (hg : Monotone g)
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
      ≤ ↑δ + hDevAt (leftLim f) (leftLim g) (t + δ) :=
  le_add_hDevAt fun d hd =>
    hDevAt_le (show rightLim f t ≤ rightLim g (t + (δ + d)) from
      calc rightLim f t
          ≤ leftLim f (t + δ) :=
            hf.rightLim_le_leftLim (lt_add_of_pos_right t hδ)
        _ ≤ leftLim g (t + δ + d) := hd
        _ ≤ rightLim g (t + δ + d) := hg.leftLim_le_rightLim le_rfl
        _ = rightLim g (t + (δ + d)) := by rw [add_assoc])

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
          rw [hDevAt_leftLim_eq_hDevAt hg, hDevAt_rightLim_eq_hDevAt hg]
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

/-- The closures have the same horizontal deviation as the original pair:
`hDev (leftLim f) (leftLim g) = hDev f g` (the book's practical corollary
for cumulative pairs). -/
theorem hDev_leftLim_eq_hDev {f g : ℝ≥0 → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) :
    (hDev (leftLim f) (leftLim g) : ℝ≥0∞) = hDev f g := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    calc (hDevAt (leftLim f) (leftLim g) t : ℝ≥0∞)
        = hDevAt (leftLim f) g t := hDevAt_leftLim_eq_hDevAt hg t
      _ ≤ hDevAt f g t :=
          hDevAt_mono (fun x => hf.leftLim_le le_rfl) le_rfl t
      _ ≤ hDev f g := hDevAt_le_hDev _ _ t
  · rw [hDev_leftLim_eq_hDev_rightLim hf hg]
    refine iSup_le fun t => ?_
    calc (hDevAt f g t : ℝ≥0∞)
        = hDevAt f (rightLim g) t := (hDevAt_rightLim_eq_hDevAt hg t).symm
      _ ≤ hDevAt (rightLim f) (rightLim g) t :=
          hDevAt_mono (fun x => hf.le_rightLim le_rfl) le_rfl t
      _ ≤ hDev (rightLim f) (rightLim g) := hDevAt_le_hDev _ _ t

/-- The closures have the same horizontal deviation as the original pair,
right-closed form: `hDev (rightLim f) (rightLim g) = hDev f g`. -/
theorem hDev_rightLim_eq_hDev {f g : ℝ≥0 → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) :
    (hDev (rightLim f) (rightLim g) : ℝ≥0∞) = hDev f g :=
  (hDev_leftLim_eq_hDev_rightLim hf hg).symm.trans
    (hDev_leftLim_eq_hDev hf hg)

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
      rw [leftLim_eq_of_isBot (f := f) fun b => zero_le, hf0, zero_tsub]
      exact zero_le
    · show leftLim f t - leftLim g t ≤ _
      letI : (𝓝[<] t).NeBot :=
        nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
      rw [hf.leftLim_eq_sSup, tsub_le_iff_right]
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
          letI : (𝓝[>] t).NeBot := nhdsGT_neBot t
          rw [hg.rightLim_eq_sInf]
          refine le_sInf ?_
          rintro b ⟨z, (hz : t < z), rfl⟩
          refine iInf_le_of_le ⟨z - t, tsub_pos_of_lt hz⟩ ?_
          rw [add_tsub_cancel_of_le hz.le]
          exact hg.leftLim_le le_rfl

/-- Left-closing both arguments never increases the vertical deviation:
`vDev (leftLim f) (leftLim g) ≤ vDev f g` for non-decreasing `f, g` (no
continuity needed; each closed term is a supremum of original terms). -/
theorem vDev_leftLim_le_vDev {f g : ℝ≥0 → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) :
    vDev (leftLim f) (leftLim g) ≤ vDev f g := by
  refine iSup_le fun t => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · show leftLim f 0 - leftLim g 0 ≤ _
    rw [leftLim_zero_eq f, leftLim_zero_eq g]
    exact vDevAt_le_vDev f g 0
  · show leftLim f t - leftLim g t ≤ _
    letI : (𝓝[<] t).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    rw [hf.leftLim_eq_sSup, tsub_le_iff_right]
    refine sSup_le ?_
    rintro b ⟨y, (hy : y < t), rfl⟩
    rw [← tsub_le_iff_right]
    calc f y - leftLim g t
        ≤ f y - g y := tsub_le_tsub le_rfl (hg.le_leftLim hy)
      _ ≤ vDev f g := vDevAt_le_vDev f g y

/-- **Right-continuous cumulative functions do not change the bounds**: for
non-decreasing `f, g` with `f` left-continuous and `f 0 = 0`, the right
closures have the same vertical deviation,
`vDev (rightLim f) (rightLim g) = vDev f g` (the closure insensitivity
`vDev_leftLim_eq_vDev_rightLim` bridges to the left closures, which fix `f`
and only lower `g`). -/
theorem vDev_rightLim_eq_vDev_of_isLeftContinuous {f g : ℝ≥0 → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) (hflc : IsLeftContinuous f)
    (hf0 : f 0 = 0) :
    vDev (rightLim f) (rightLim g) = vDev f g := by
  rw [← vDev_leftLim_eq_vDev_rightLim hf hg hf0]
  apply le_antisymm (vDev_leftLim_le_vDev hf hg)
  rw [(isLeftContinuous_iff_leftLim_eq hf).mp hflc]
  exact iSup_le fun t => le_trans
    (tsub_le_tsub le_rfl (hg.leftLim_le le_rfl))
    (vDevAt_le_vDev _ _ t)

/-- The dual reading: for non-decreasing `f, g` with `g` right-continuous,
the left closures have the same vertical deviation,
`vDev (leftLim f) (leftLim g) = vDev f g` (no null-at-origin needed: the
`δ`-shifted left closures squeeze onto `rightLim g = g`). -/
theorem vDev_leftLim_eq_vDev_of_isRightContinuous {f g : ℝ≥0 → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) (hgrc : IsRightContinuous g) :
    vDev (leftLim f) (leftLim g) = vDev f g := by
  apply le_antisymm (vDev_leftLim_le_vDev hf hg)
  refine iSup_le fun t => ?_
  show f t - g t ≤ _
  rw [tsub_le_iff_right]
  calc f t
      ≤ ⨅ δ : {δ : ℝ≥0 // 0 < δ},
          (vDev (leftLim f) (leftLim g) + leftLim g (t + δ.1)) :=
        le_iInf fun δ => by
          calc f t
              ≤ leftLim f (t + δ.1) :=
                hf.le_leftLim (lt_add_of_pos_right t δ.2)
            _ ≤ (leftLim f (t + δ.1) - leftLim g (t + δ.1))
                  + leftLim g (t + δ.1) := le_tsub_add
            _ ≤ vDev (leftLim f) (leftLim g) + leftLim g (t + δ.1) :=
                add_le_add (vDevAt_le_vDev _ _ _) le_rfl
    _ = vDev (leftLim f) (leftLim g)
          + ⨅ δ : {δ : ℝ≥0 // 0 < δ}, leftLim g (t + δ.1) :=
        ENNReal.add_iInf.symm
    _ ≤ vDev (leftLim f) (leftLim g) + g t := by
        refine add_le_add le_rfl ?_
        letI : (𝓝[>] t).NeBot := nhdsGT_neBot t
        rw [← congrFun ((isRightContinuous_iff_rightLim_eq hg).mp hgrc) t,
          hg.rightLim_eq_sInf]
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
  ⟨(hDevAt_leftLim_eq_hDevAt hg t).symm,
    (hDevAt_rightLim_eq_hDevAt hg t).symm⟩

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

/-! ## Book restatement (right-continuous cumulative functions)
"If `(A, D) ∈ C` (then `A` and `D` are left-continuous), then
`hDev(Aᵣ, Dᵣ) = hDev(A, D)` and `vDev(Aᵣ, Dᵣ) = vDev(A, D)`": the
worst-case backlog and delay bounds are the same as with left-continuous
cumulative functions. The horizontal half does not even need
left-continuity; the vertical half consumes it for `A` through the closure
fixed point, plus null at the origin (the class `C`). Causality `D ≤ A`,
left-continuity of `D`, and `D 0 = 0` are carried unused for fidelity to
`C`. -/
example {A D : ℝ≥0 → ℝ≥0∞} (hAmono : Monotone A) (hDmono : Monotone D)
    (hAlc : IsLeftContinuous A) (_hDlc : IsLeftContinuous D)
    (hA0 : A 0 = 0) (_hD0 : D 0 = 0) (_hc : ∀ t, D t ≤ A t) :
    (hDev (rightLim A) (rightLim D) : ℝ≥0∞) = hDev A D ∧
      vDev (rightLim A) (rightLim D) = vDev A D :=
  ⟨hDev_rightLim_eq_hDev hAmono hDmono,
    vDev_rightLim_eq_vDev_of_isLeftContinuous hAmono hDmono hAlc hA0⟩

end DeepWiki
