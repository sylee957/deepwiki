import Book.ArrivalCurves
import Book.Continuity
import Book.ConvolutionReal
import Mathlib.Topology.Order.LeftRightLim

/-! # Properties of a minimal arrival curve
The minimal arrival curves of `A` (`A ≥ A ⊼ α`, max-plus) are the order-duals of
the maximal-curve properties (`Book.ArrivalCurvesMaximal`): closed under
pointwise `max`, under the (max,+) super-additive closure, and downward-closed; the
max-plus deconvolution `A ⊘̄ A` is the greatest one; and the right-continuous
extension is again minimal (for left- or right-continuous `A`). -/

namespace DeepWiki

open scoped Classical NNReal

/-! ## Lattice and order closure -/

/-- The pointwise maximum of two minimal arrival curves is a minimal arrival
curve: if `A ≥ A ⊼ α` and `A ≥ A ⊼ α'` then `A ≥ A ⊼ (α ⊔ α')`. Stated under
monotone `A, α, α'` (the book's `𝒞`/`ℱ↑` setting), where the increment
characterization controls the junk supremum. -/
theorem IsMinimalArrivalBound.sup {A α α' : ℝ≥0 → ℝ≥0}
    (hA : Monotone A) (hα : Monotone α) (hα' : Monotone α')
    (h : IsMinimalArrivalBound A α) (h' : IsMinimalArrivalBound A α') :
    IsMinimalArrivalBound A (α ⊔ α') := by
  rw [isMinimalArrivalBound_iff_increment_of_monotone A α hA hα] at h
  rw [isMinimalArrivalBound_iff_increment_of_monotone A α' hA hα'] at h'
  rw [isMinimalArrivalBound_iff_increment_of_monotone A (α ⊔ α') hA
    (hα.sup hα')]
  intro t d
  rw [Pi.sup_apply, ← max_add_add_left]
  exact max_le (h t d) (h' t d)

/-- Any function below a minimal arrival curve is again a minimal arrival
curve: if `A ≥ A ⊼ α` and `α' ≤ α` then `A ≥ A ⊼ α'`. Stated under monotone
`A, α, α'`, where the increment characterization controls the junk supremum. -/
theorem IsMinimalArrivalBound.mono {A α α' : ℝ≥0 → ℝ≥0}
    (hA : Monotone A) (hα : Monotone α) (hα' : Monotone α')
    (h : IsMinimalArrivalBound A α) (hle : α' ≤ α) :
    IsMinimalArrivalBound A α' := by
  rw [isMinimalArrivalBound_iff_increment_of_monotone A α hA hα] at h
  rw [isMinimalArrivalBound_iff_increment_of_monotone A α' hA hα']
  intro t d
  refine le_trans ?_ (h t d)
  gcongr
  exact hle d

/-! ## The deconvolution `A ⊘̄ A` -/

/-- Every minimal arrival curve is below `A ⊘̄ A`: if `α` is a minimal arrival
curve for non-decreasing `A`, `α`, then `α ≤ maxDeconv A A`. This is the
"`A ⊘̄ A` is the best (greatest) minimal arrival curve" bound. -/
theorem le_maxDeconv_self_of_isMinimalArrivalBound {A α : ℝ≥0 → ℝ≥0}
    (hA : Monotone A) (hα : Monotone α)
    (h : IsMinimalArrivalBound A α) :
    α ≤ maxDeconv A A := by
  rw [isMinimalArrivalBound_iff_increment_of_monotone A α hA hα] at h
  intro d
  refine le_ciInf (fun s => ?_)
  rw [le_tsub_iff_left (hA (le_add_left le_rfl))]
  have := h s d
  rwa [add_comm s d] at this

/-- `A ⊘̄ A` is itself a minimal arrival curve (for non-decreasing `A`); with
`le_maxDeconv_self_of_isMinimalArrivalBound` this makes it the greatest one. -/
theorem isMinimalArrivalBound_maxDeconv_self {A : ℝ≥0 → ℝ≥0}
    (hA : Monotone A) :
    IsMinimalArrivalBound A (maxDeconv A A) := by
  refine isMinimalArrivalBound_of_increment A (maxDeconv A A) (fun t d => ?_)
  have hterm : maxDeconv A A d ≤ A (d + t) - A t :=
    maxDeconv_le_sub A A d t
  calc A t + maxDeconv A A d
      ≤ A t + (A (d + t) - A t) := by gcongr
    _ = A (d + t) := add_tsub_cancel_of_le (hA (le_add_left le_rfl))
    _ = A (t + d) := by rw [add_comm]

/-! ## Super-additive closure -/

/-- The increment bound iterated through the (max,+) powers: if
`A t + α d ≤ A (t + d)` for all `t, d`, then
`A t + (maxConvProjPow α n) d ≤ A (t + d)` for every power `n`. -/
theorem increment_maxConvProjPow_of_increment {A α : ℝ≥0 → ℝ≥0}
    (h : ∀ t d : ℝ≥0, A t + α d ≤ A (t + d)) (n : ℕ) (t d : ℝ≥0) :
    A t + maxConvProjPow α n d ≤ A (t + d) := by
  induction n generalizing t d with
  | zero => exact h t d
  | succ n ih =>
    show A t + maxConvProj (maxConvProjPow α n) (maxConvProjPow α n) d
        ≤ A (t + d)
    refine add_maxConvProj_le (maxConvProjPow α n) d (A t) (A (t + d)) ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = d)⟩
    calc A t + (maxConvProjPow α n u + maxConvProjPow α n s)
          = (A t + maxConvProjPow α n u) + maxConvProjPow α n s := by ring
      _ ≤ A (t + u) + maxConvProjPow α n s := by gcongr; exact ih t u
      _ ≤ A ((t + u) + s) := ih (t + u) s
      _ = A (t + d) := by rw [add_assoc, hus]

/-- Each (max,+) self-convolution power of a minimal arrival curve is again a
minimal arrival curve, for non-decreasing `A`, `α`: if `A ≥ A ⊼ α` then
`A ≥ A ⊼ (maxConvProjPow α n)`. -/
theorem isMinimalArrivalBound_maxConvProjPow_of_monotone
    {A α : ℝ≥0 → ℝ≥0} (hA : Monotone A) (hα : Monotone α)
    (h : IsMinimalArrivalBound A α) (n : ℕ) :
    IsMinimalArrivalBound A (maxConvProjPow α n) := by
  have hinc := (isMinimalArrivalBound_iff_increment_of_monotone A α hA hα).mp h
  exact isMinimalArrivalBound_of_increment A _
    (fun t d => increment_maxConvProjPow_of_increment hinc n t d)

/-- The (max,+) super-additive closure of a minimal arrival curve is again a
minimal arrival curve, for non-decreasing `A`, `α`: if `A ≥ A ⊼ α` then
`A ≥ A ⊼ superadditiveClosureMax α`, with the closure `≥ α`. The per-power
increment bound also bounds the closure supremum above by `A (t + d) - A t`. -/
theorem IsMinimalArrivalBound.superadditiveClosureMax {A α : ℝ≥0 → ℝ≥0}
    (hA : Monotone A) (hα : Monotone α)
    (h : IsMinimalArrivalBound A α) :
    IsMinimalArrivalBound A (superadditiveClosureMax α) := by
  have hinc := (isMinimalArrivalBound_iff_increment_of_monotone A α hA hα).mp h
  refine isMinimalArrivalBound_of_increment A _ (fun t d => ?_)
  have hbd : ∀ n : ℕ, maxConvProjPow α n d ≤ A (t + d) - A t := fun n =>
    le_tsub_of_add_le_left (increment_maxConvProjPow_of_increment hinc n t d)
  have hsup : DeepWiki.superadditiveClosureMax α d ≤ A (t + d) - A t := ciSup_le hbd
  have hle : A t ≤ A (t + d) := hA le_self_add
  calc A t + DeepWiki.superadditiveClosureMax α d
        ≤ A t + (A (t + d) - A t) := by gcongr
    _ = A (t + d) := add_tsub_cancel_of_le hle

/-! ## Right-continuous extension
The right-continuous extension `Function.rightLim α` of a minimal arrival
curve (`A ≥ A ⊼ α`, max-plus) is again a minimal arrival curve when the
cumulative function `A` is right-continuous. This is the dual of the
maximal-curve `leftLim` results, but with a genuine boundary asymmetry: the
needed limit passes from the right of `t + d` (right-continuous `A`) and has
no `t = 0` edge; the left-continuous analogue must take a left limit at `t`,
which is empty at `t = 0`, so it carries an explicit boundary hypothesis. -/

open Set Filter Topology

/-- The right-continuous extension `Function.rightLim α` of a minimal
arrival curve is minimal for a right-continuous cumulative function: if
`A` is right-continuous, `A` and `α` non-decreasing, and `α` a minimal
arrival curve for `A`, then `Function.rightLim α` is one too. -/
theorem isMinimalArrivalBound_rightLim_of_rightContinuous
    {A α : ℝ≥0 → ℝ≥0} (hA : IsRightContinuous A) (hAmono : Monotone A)
    (hα : Monotone α) (h : IsMinimalArrivalBound A α) :
    IsMinimalArrivalBound A (Function.rightLim α) := by
  rw [isMinimalArrivalBound_iff_increment_of_monotone A α hAmono hα] at h
  refine isMinimalArrivalBound_of_increment A (Function.rightLim α) ?_
  intro t d
  -- For `s ∈ (t+d, ?)` (eventually within `Ioi (t+d)`), bound
  -- `A t + (rightLim α) d ≤ A s`, then pass `A s → A (t+d)` (right limit).
  have hlim : Tendsto A (𝓝[>] (t + d)) (𝓝 (A (t + d))) :=
    tendsto_nhdsWithin_Ioi_of_rightContinuous hA (t + d)
  haveI : (𝓝[>] (t + d)).NeBot :=
    nhdsGT_neBot_of_exists_gt ⟨t + d + 1, lt_add_of_pos_right _ one_pos⟩
  have hev : ∀ᶠ s in 𝓝[>] (t + d),
      A t + Function.rightLim α d ≤ A s := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards with s hts
    have hts' : t + d < s := hts
    have htle : t ≤ s := le_of_lt (lt_of_le_of_lt le_self_add hts')
    have hsub : t + (s - t) = s := add_tsub_cancel_of_le htle
    have hltd : d < s - t := by
      rw [lt_tsub_iff_left]
      simpa [add_comm] using hts'
    have key : A t + α (s - t) ≤ A s := by
      have := h t (s - t)
      rwa [hsub] at this
    refine le_trans ?_ key
    gcongr
    exact hα.rightLim_le hltd
  exact ge_of_tendsto hlim hev

/-- The right-continuous extension `Function.rightLim α` of a minimal
arrival curve is minimal for a left-continuous cumulative function, given
the boundary row `A 0 + (rightLim α) d ≤ A d` (which left-continuity
cannot supply on `ℝ≥0` since `Iio 0 = ∅`): if `A` is left-continuous, `A`
and `α` non-decreasing, `α` a minimal arrival curve for `A`, and the
boundary bound holds, then `Function.rightLim α` is one too. -/
theorem isMinimalArrivalBound_rightLim_of_leftContinuous
    {A α : ℝ≥0 → ℝ≥0} (hA : IsLeftContinuous A) (hAmono : Monotone A)
    (hα : Monotone α) (h : IsMinimalArrivalBound A α)
    (hbdry : ∀ d : ℝ≥0, A 0 + Function.rightLim α d ≤ A d) :
    IsMinimalArrivalBound A (Function.rightLim α) := by
  rw [isMinimalArrivalBound_iff_increment_of_monotone A α hAmono hα] at h
  refine isMinimalArrivalBound_of_increment A (Function.rightLim α) ?_
  intro t d
  -- `t = 0` is the boundary row supplied by `hbdry`; for `t > 0` pass
  -- to the left limit `A s → A t` over `s ∈ Iio t`.
  rcases eq_or_lt_of_le (zero_le' (a := t)) with ht | ht
  · rw [← ht, zero_add]; exact hbdry d
  have hlim : Tendsto (fun s => A s + Function.rightLim α d)
      (𝓝[<] t) (𝓝 (A t + Function.rightLim α d)) :=
    (tendsto_nhdsWithin_Iio_of_leftContinuous hA t).add tendsto_const_nhds
  haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hev : ∀ᶠ s in 𝓝[<] t,
      A s + Function.rightLim α d ≤ A (t + d) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards with s hst
    have hst' : s < t := hst
    -- `s + ((t+d) - s) = t + d`, with `(t+d) - s > d`, so
    -- `rightLim α d ≤ α ((t+d) - s)`.
    have hsle : s ≤ t + d := le_of_lt (lt_of_lt_of_le hst' le_self_add)
    have hsub : s + ((t + d) - s) = t + d := add_tsub_cancel_of_le hsle
    have hltd : d < (t + d) - s := by
      rw [lt_tsub_iff_left]
      simpa [add_comm] using add_lt_add_right hst' d
    have key : A s + α ((t + d) - s) ≤ A (t + d) := by
      have := h s ((t + d) - s)
      rwa [hsub] at this
    refine le_trans ?_ key
    gcongr
    exact hα.rightLim_le hltd
  exact le_of_tendsto hlim hev

end DeepWiki
