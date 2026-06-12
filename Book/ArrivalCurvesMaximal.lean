import Book.ArrivalCurves
import Book.Closures
import Book.Continuity
import Book.ClosuresReal
import Mathlib.Topology.Order.LeftRightLim

/-! # Properties of a maximal arrival curve
The maximal arrival curves of `A` (`A ≤ A ∗ α`, min-plus) are closed under
pointwise `min`, under the (min,+) sub-additive closure, and upward-closed; the
min-plus deconvolution `A ⊘ A` is the least one; and the left-continuous
extension is again maximal (for left- or right-continuous `A`). -/

namespace DeepWiki

open scoped Classical NNReal

/-! ## Lattice and order closure -/

/-- The pointwise minimum of two maximal arrival curves is a maximal arrival
curve: if `A ≤ A ∗ α` and `A ≤ A ∗ α'` then `A ≤ A ∗ (α ⊓ α')` (over any
conditionally complete linear order with `⊥` and monotone `+`, e.g. `ℝ≥0`
or `ℝ≥0∞`). -/
theorem IsMaximalArrivalBound.inf {T : Type*} [Add T]
    [ConditionallyCompleteLinearOrder T] [OrderBot T] [AddLeftMono T]
    {A α α' : ℝ≥0 → T}
    (h : IsMaximalArrivalBound A α) (h' : IsMaximalArrivalBound A α') :
    IsMaximalArrivalBound A (α ⊓ α') := by
  rw [isMaximalArrivalBound_iff_increment] at h h' ⊢
  intro t d
  rw [Pi.inf_apply, ← min_add_add_left]
  exact le_min (h t d) (h' t d)

/-- **Maximal arrival bounds through a one-sided sandwich**: a process
within `c` below `A` keeps `A`'s maximal arrival bound up to `+ c`. -/
theorem isMaximalArrivalBound_of_sandwich {A D α : ℝ≥0 → ℝ≥0} {c : ℝ≥0}
    (hc : ∀ t, D t ≤ A t) (hsand : ∀ t, A t ≤ D t + c)
    (h : IsMaximalArrivalBound A α) :
    IsMaximalArrivalBound D (fun d => α d + c) := by
  rw [isMaximalArrivalBound_iff_increment] at h ⊢
  intro t d
  calc D (t + d) ≤ A (t + d) := hc _
    _ ≤ A t + α d := h t d
    _ ≤ (D t + c) + α d := add_le_add (hsand t) le_rfl
    _ = D t + (α d + c) := by rw [add_assoc, add_comm c (α d)]

/-- Any function above a maximal arrival curve is again a maximal arrival curve:
if `A ≤ A ∗ α` and `α ≤ α'` then `A ≤ A ∗ α'` (over any conditionally
complete lattice with `⊥` and monotone `+`, e.g. `ℝ≥0` or `ℝ≥0∞`). -/
theorem IsMaximalArrivalBound.mono {T : Type*} [Add T]
    [ConditionallyCompleteLattice T] [OrderBot T] [AddLeftMono T]
    {A α α' : ℝ≥0 → T}
    (h : IsMaximalArrivalBound A α) (hle : α ≤ α') :
    IsMaximalArrivalBound A α' := by
  rw [isMaximalArrivalBound_iff_increment] at h ⊢
  intro t d
  refine le_trans (h t d) ?_
  gcongr
  exact hle d

/-! ## The deconvolution `A ⊘ A` -/

/-- The deconvolution `A ⊘ A` is below every maximal arrival curve: if `α` is a
maximal arrival curve for `A` then `A ⊘ A ≤ α`. This is the "`A ⊘ A` is the best
(least) maximal arrival curve" bound. -/
theorem minDeconv_self_le_of_isMaximalArrivalBound {A α : ℝ≥0 → ℝ≥0}
    (h : IsMaximalArrivalBound A α) :
    minDeconv A A ≤ α := by
  rw [isMaximalArrivalBound_iff_increment] at h
  intro d
  refine ciSup_le (fun s => ?_)
  -- `A (d + s) - A s ≤ α d` since `A (d + s) ≤ A s + α d` (increment at `s, d`)
  rw [tsub_le_iff_right, add_comm d s, add_comm (α d) (A s)]
  exact h s d

/-- When `A` admits some maximal arrival curve, `A ⊘ A` is itself one. The
witness `α` bounds the deconvolution supremum (`A ⊘ A ≤ α`), so each increment
term lies below it. Together with `minDeconv_self_le_of_isMaximalArrivalBound`
this makes `A ⊘ A` the least maximal arrival curve, and `α ≥ A ⊘ A` an
equivalent definition of a maximal arrival curve. -/
theorem isMaximalArrivalBound_minDeconv_self {A : ℝ≥0 → ℝ≥0}
    (hex : ∃ α : ℝ≥0 → ℝ≥0, IsMaximalArrivalBound A α) :
    IsMaximalArrivalBound A (minDeconv A A) := by
  obtain ⟨α, hα⟩ := hex
  -- the witness bounds the deconvolution family above by `α d` at each `d`
  have hbdd : ∀ d : ℝ≥0,
      BddAbove (Set.range (fun s : ℝ≥0 => A (d + s) - A s)) := by
    intro d
    refine ⟨α d, ?_⟩
    rintro x ⟨s, rfl⟩
    rw [isMaximalArrivalBound_iff_increment] at hα
    rw [tsub_le_iff_right, add_comm d s, add_comm (α d) (A s)]
    exact hα s d
  rw [isMaximalArrivalBound_iff_increment]
  intro t d
  -- `A (t + d) - A t ≤ (A ⊘ A) d`, the `s = t` term of the supremum
  have hterm : A (t + d) - A t ≤ minDeconv A A d :=
    le_ciSup_of_le (hbdd d) t (by rw [add_comm d t])
  rw [tsub_le_iff_right, add_comm (minDeconv A A d) (A t)] at hterm
  exact hterm

/-! ## Sub-additive closure
Each (min,+) self-convolution power of `α` and their pointwise infimum (the
(min,+) sub-additive closure `subadditiveClosureMin`, from `Book.ConvolutionReal`)
are again maximal arrival curves for `A`, and the closure is `≤ α`. -/

/-- The increment bound iterated through the (min,+) powers: if `α` is a
maximal arrival curve for `A`, then `A (t + d) ≤ A t + (minConvProjPow α n) d`
for every power `n`. -/
theorem increment_minConvProjPow_of_isMaximalArrivalBound {A α : ℝ≥0 → ℝ≥0}
    (h : IsMaximalArrivalBound A α) (n : ℕ) (t d : ℝ≥0) :
    A (t + d) ≤ A t + minConvProjPow α n d := by
  rw [isMaximalArrivalBound_iff_increment] at h
  induction n generalizing t d with
  | zero => exact h t d
  | succ n ih =>
    -- `minConvProjPow α (n+1) d = ⨅_{u+s=d} α u + (minConvProjPow α n) s`
    show A (t + d) ≤ A t + minConvProj α (minConvProjPow α n) d
    rw [minConvProj_eq, add_comm (A t), ← tsub_le_iff_right]
    refine le_ciInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = d)⟩
    -- `A (t+d) = A ((t+u)+s) ≤ A (t+u) + (minConvProjPow α n) s`, and
    -- `A (t+u) ≤ A t + α u`, so `A (t+d) - A t ≤ α u + (minConvProjPow α n) s`
    rw [tsub_le_iff_right]
    calc A (t + d) = A ((t + u) + s) := by rw [add_assoc, hus]
      _ ≤ A (t + u) + minConvProjPow α n s := ih (t + u) s
      _ ≤ (A t + α u) + minConvProjPow α n s := by gcongr; exact h t u
      _ = A t + (α u + minConvProjPow α n s) := by ring
      _ = (α u + minConvProjPow α n s) + A t := by ring

/-- Each self-convolution power of a maximal arrival curve is again a maximal
arrival curve: if `A ≤ A ∗ α` then `A ≤ A ∗ (minConvProjPow α n)`. -/
theorem IsMaximalArrivalBound.minConvProjPow
    {A α : ℝ≥0 → ℝ≥0} (h : IsMaximalArrivalBound A α) (n : ℕ) :
    IsMaximalArrivalBound A (minConvProjPow α n) := by
  rw [isMaximalArrivalBound_iff_increment]
  exact fun t d => increment_minConvProjPow_of_isMaximalArrivalBound h n t d

/-- The (min,+) sub-additive closure of a maximal arrival curve is again a
maximal arrival curve: if `A ≤ A ∗ α` then `A ≤ A ∗ subadditiveClosureMin α`,
with the closure `≤ α`. The increment bound through every power passes to the
infimum defining the closure. -/
theorem IsMaximalArrivalBound.subadditiveClosureMin {A α : ℝ≥0 → ℝ≥0}
    (h : IsMaximalArrivalBound A α) :
    IsMaximalArrivalBound A (subadditiveClosureMin α) := by
  rw [isMaximalArrivalBound_iff_increment]
  intro t d
  -- `A (t+d) - A t ≤ (minConvProjPow α n) d` for every `n`, so `≤ ⨅ₙ`
  rw [show DeepWiki.subadditiveClosureMin α d
      = ⨅ n : ℕ, DeepWiki.minConvProjPow α n d from rfl,
    add_comm (A t), ← tsub_le_iff_right]
  refine le_ciInf (fun n => ?_)
  rw [tsub_le_iff_right, add_comm (DeepWiki.minConvProjPow α n d)]
  exact increment_minConvProjPow_of_isMaximalArrivalBound h n t d

/-- Any function above the sub-additive closure of a maximal arrival curve is a
maximal arrival curve: if `A ≤ A ∗ α` and `subadditiveClosureMin α ≤ α'`, then
`α'` is a maximal arrival curve for `A`. Combines closure-maximality with upward
closure. -/
theorem isMaximalArrivalBound_of_subadditiveClosure_le {A α α' : ℝ≥0 → ℝ≥0}
    (h : IsMaximalArrivalBound A α) (hle : subadditiveClosureMin α ≤ α') :
    IsMaximalArrivalBound A α' :=
  h.subadditiveClosureMin.mono hle

/-! ## Sub-additive closure on the `ℝ≥0∞` carrier
The same family for `ℝ≥0∞`-valued curves, against the dioid closure
`subadditiveClosureENN` (from `Book.Closures`): the closure of a maximal
arrival curve is again one, sub-additive, and `≤ α`. -/

open scoped ENNReal

/-- The increment bound iterated through the (min,+) powers on `ℝ≥0∞`:
`A (t + d) ≤ A t + minConvPow α n d` for every power `n`. -/
theorem increment_minConvPow_of_isMaximalArrivalBound {A α : ℝ≥0 → ℝ≥0∞}
    (h : IsMaximalArrivalBound A α) (n : ℕ) (t d : ℝ≥0) :
    A (t + d) ≤ A t + minConvPow α n d := by
  rw [isMaximalArrivalBound_iff_increment] at h
  induction n generalizing t d with
  | zero =>
      rw [minConvPow_zero]
      split_ifs with hd
      · rw [hd, add_zero, add_zero]
      · rw [add_top]
        exact le_top
  | succ n ih =>
      rw [minConvPow_succ, add_comm (A t), ← tsub_le_iff_right]
      refine le_minConv fun u s hus => ?_
      rw [tsub_le_iff_right]
      calc A (t + d) = A ((t + u) + s) := by rw [add_assoc, hus]
        _ ≤ A (t + u) + α s := h (t + u) s
        _ ≤ (A t + minConvPow α n u) + α s :=
            add_le_add (ih t u) le_rfl
        _ = A t + (minConvPow α n u + α s) := add_assoc _ _ _
        _ = (minConvPow α n u + α s) + A t := add_comm _ _

/-- The (min,+) sub-additive closure on `ℝ≥0∞` of a maximal arrival curve is
again a maximal arrival curve: if `A ≤ A ∗ α` then
`A ≤ A ∗ subadditiveClosureENN α`. -/
theorem IsMaximalArrivalBound.subadditiveClosureENN {A α : ℝ≥0 → ℝ≥0∞}
    (h : IsMaximalArrivalBound A α) :
    IsMaximalArrivalBound A (DeepWiki.subadditiveClosureENN α) := by
  rw [isMaximalArrivalBound_iff_increment]
  intro t d
  rw [subadditiveClosureENN_eq_iInf, ENNReal.add_iInf]
  exact le_iInf fun n =>
    increment_minConvPow_of_isMaximalArrivalBound h n t d

/-- The sub-additive closure of a maximal arrival curve (book form) is
again one: monotonicity transports through the closure powers. -/
theorem IsMaximalArrivalCurve.subadditiveClosureENN {A α : ℝ≥0 → ℝ≥0∞}
    (h : IsMaximalArrivalCurve A α) :
    IsMaximalArrivalCurve A (DeepWiki.subadditiveClosureENN α) :=
  ⟨monotone_subadditiveClosureENN h.1, h.2.subadditiveClosureENN⟩

/-! Any `ℝ≥0∞` maximal arrival curve can be replaced by its sub-additive
closure: still a maximal arrival curve, sub-additive, and below `α`. -/
example {A α : ℝ≥0 → ℝ≥0∞} (h : IsMaximalArrivalBound A α) :
    IsMaximalArrivalBound A (subadditiveClosureENN α)
      ∧ IsSubadditive (subadditiveClosureENN α)
      ∧ ∀ t, subadditiveClosureENN α t ≤ α t :=
  ⟨h.subadditiveClosureENN, subadditiveClosureENN_subadditive α,
    subadditiveClosureENN_le α⟩

/-! ## Left-continuous extension
The left-continuous extension of a non-decreasing `α` — its left limit
`Function.leftLim α` (`lim_{y → x⁻} α y`, equal to `sSup (α '' Iio x)` for
monotone `α` by `Monotone.leftLim_eq_sSup`) — is again a maximal arrival curve
when the cumulative function `A` is left-continuous. -/

open Set Filter Topology

/-- The left-continuous extension `Function.leftLim α` of a maximal arrival
curve is maximal: if `A` is left-continuous, `α` non-decreasing, and `α` a
maximal arrival curve for `A`, then `Function.leftLim α` is one too. -/
theorem isMaximalArrivalBound_leftLim_of_isLeftContinuous
    {A α : ℝ≥0 → ℝ≥0} (hA : IsLeftContinuous A) (hα : Monotone α)
    (h : IsMaximalArrivalBound A α) :
    IsMaximalArrivalBound A (Function.leftLim α) := by
  rw [isMaximalArrivalBound_iff_increment] at h ⊢
  intro t d
  -- Edge case `d = 0`: `A (t + 0) = A t ≤ A t + (leftLim α) 0`.
  rcases eq_or_lt_of_le (zero_le' (a := d)) with hd | hd
  · rw [← hd, add_zero]; exact le_self_add
  -- For `s ∈ (t, t + d)` (eventually within `Iio (t+d)`), bound
  -- `A s ≤ A t + (leftLim α) d`, then pass to the left limit `A s → A (t+d)`.
  have hlim : Tendsto A (𝓝[<] (t + d)) (𝓝 (A (t + d))) :=
    tendsto_nhdsWithin_Iio_of_isLeftContinuous hA (t + d)
  have htlt : t < t + d := lt_add_of_pos_right t hd
  haveI : (𝓝[<] (t + d)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨t, htlt⟩
  have hev : ∀ᶠ s in 𝓝[<] (t + d), A s ≤ A t + Function.leftLim α d := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds htlt] with s hts hslt
    -- `s = t + (s - t)`, `s - t < d`, so `α (s - t) ≤ (leftLim α) d`.
    have hslt' : s < t + d := hslt
    have hsub : t + (s - t) = s := by
      rw [add_tsub_cancel_of_le (le_of_lt hts)]
    have hltd : s - t < d := by
      rw [tsub_lt_iff_left (le_of_lt hts)]
      exact hslt'
    have key : A s ≤ A t + α (s - t) := by
      have := h t (s - t)
      rwa [hsub] at this
    refine le_trans key ?_
    gcongr
    exact hα.le_leftLim hltd
  -- Pass the closed condition `A s ≤ c` to the limit.
  exact le_of_tendsto hlim hev

/-- The left-continuous extension `Function.leftLim α` of a maximal arrival
curve is maximal also for a right-continuous cumulative function: if `A` is
right-continuous, `α` non-decreasing, and `α` a maximal arrival curve for `A`,
then `Function.leftLim α` is one too. -/
theorem isMaximalArrivalBound_leftLim_of_isRightContinuous
    {A α : ℝ≥0 → ℝ≥0} (hA : IsRightContinuous A) (hα : Monotone α)
    (h : IsMaximalArrivalBound A α) :
    IsMaximalArrivalBound A (Function.leftLim α) := by
  rw [isMaximalArrivalBound_iff_increment] at h ⊢
  intro t d
  -- Edge case `d = 0`: `A (t + 0) = A t ≤ A t + (leftLim α) 0`.
  rcases eq_or_lt_of_le (zero_le' (a := d)) with hd | hd
  · rw [← hd, add_zero]; exact le_self_add
  -- For `s ∈ (t, t + d)` (eventually within `Ioi t`), bound
  -- `A (t+d) ≤ A s + (leftLim α) d`, then pass `A s → A t` (right limit at `t`).
  have hlim : Tendsto (fun s => A s + Function.leftLim α d)
      (𝓝[>] t) (𝓝 (A t + Function.leftLim α d)) :=
    (tendsto_nhdsWithin_Ioi_of_isRightContinuous hA t).add tendsto_const_nhds
  haveI : (𝓝[>] t).NeBot :=
    nhdsGT_neBot_of_exists_gt ⟨t + d, lt_add_of_pos_right t hd⟩
  have hev : ∀ᶠ s in 𝓝[>] t, A (t + d) ≤ A s + Function.leftLim α d := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (lt_add_of_pos_right t hd)] with s hslt hts
    -- `s = t + (s - t)`, write `d' = (t+d) - s < d`, so `α d' ≤ (leftLim α) d`.
    have hts' : t < s := hts
    have hsub : s + ((t + d) - s) = t + d :=
      add_tsub_cancel_of_le (le_of_lt hslt)
    have hltd : (t + d) - s < d := by
      rw [tsub_lt_iff_left (le_of_lt hslt)]
      exact (add_lt_add_iff_right d).mpr hts'
    -- increment bound at the split `s + ((t+d) - s) = t + d`
    have key : A (t + d) ≤ A s + α ((t + d) - s) := by
      have := h s ((t + d) - s)
      rwa [hsub] at this
    refine le_trans key ?_
    gcongr
    exact hα.le_leftLim hltd
  -- Pass the closed condition `A (t+d) ≤ A s + c` to the limit `A s → A t`.
  exact ge_of_tendsto hlim hev

end DeepWiki
