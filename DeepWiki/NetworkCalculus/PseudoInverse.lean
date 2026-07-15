import DeepWiki.NetworkCalculus.RealCurvesConv
import DeepWiki.NetworkCalculus.LevelSet
import Mathlib.Topology.Order.LeftRightLim

/-! # Pseudo-inverse
The (lower) pseudo-inverse of a non-decreasing `f : α → β`,
`f⁻¹(x) = inf {t | f t ≥ x}`, with the infimum taken in a `CompleteLattice`
domain `α` (so "no admissible `t`" yields `⊤`). The admissible/strict level
sets `𝓘_{≥x}`, `𝓘_{<x}` live in `Book.LevelSet`. Core API over
`[CompleteLattice α] [Preorder β]`: the admissibility/Galois bounds,
monotonicity, value at `⊥`. Over a densely-ordered complete linear `α` and
linearly-ordered `β`, the `sup {t | f t < x}` characterization. A worked
first-crossing computation on the `ℝ≥0∞`-domain `delayENN` curve. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

variable {α β : Type*}

/-- Lower pseudo-inverse `f⁻¹(x) = inf {t | f t ≥ x}`. -/
noncomputable def pseudoInv [CompleteLattice α] [LE β] (f : α → β) : β → α :=
  fun x => sInf (levelGeSet f x)

/-- Admissibility: if `x ≤ f t` then `f⁻¹ x ≤ t`. -/
theorem pseudoInv_le_of_le_apply [CompleteLattice α] [LE β] {f : α → β} {x : β}
    {t : α} (h : x ≤ f t) : pseudoInv f x ≤ t :=
  sInf_le (mem_levelGeSet.mpr h)

/-- `d ≤ f⁻¹ x` when every admissible time is above `d`. -/
theorem le_pseudoInv [CompleteLattice α] [LE β] {f : α → β} {x : β} {d : α}
    (h : ∀ t : α, x ≤ f t → d ≤ t) : d ≤ pseudoInv f x :=
  le_sInf h

/-- The pseudo-inverse is monotone in `x` (antitone admissible sets). -/
theorem pseudoInv_mono [CompleteLattice α] [Preorder β] (f : α → β) :
    Monotone (pseudoInv f) := by
  intro x y hxy
  refine sInf_le_sInf (fun t ht => ?_)
  exact le_trans hxy ht

/-- `f⁻¹ ⊥ = ⊥` (`⊥` is admissible for every `t`). -/
theorem pseudoInv_bot [CompleteLattice α] [LE β] [OrderBot β] (f : α → β) :
    pseudoInv f ⊥ = ⊥ :=
  le_antisymm (pseudoInv_le_of_le_apply (t := ⊥) bot_le) bot_le

example (f : ℝ≥0∞ → ℝ≥0∞) : pseudoInv f 0 = 0 := pseudoInv_bot f
example (f : ℝ≥0∞ → ℝ≥0) : pseudoInv f 0 = 0 := pseudoInv_bot f

/-! ## The `sup`-of-`<` characterization

For a non-decreasing `f`, `f⁻¹(x) = inf {t | f t ≥ x} = sup {t | f t < x}`.
The index sets `I_{≥x}` and `I_{<x}` partition `α`; monotonicity makes `I_{≥x}`
up-closed and `I_{<x}` down-closed, so on a densely-ordered complete linear
order their inf and sup coincide. -/

/-- Every strict time lies below every admissible time (for monotone `f`):
`f a < x ≤ f b ⇒ a ≤ b`. -/
theorem levelLtSet_le_levelGeSet [LinearOrder α] [Preorder β]
    {f : α → β} (hf : Monotone f) (x : β)
    {a b : α} (ha : a ∈ levelLtSet f x)
    (hb : b ∈ levelGeSet f x) : a ≤ b := by
  rw [mem_levelLtSet] at ha
  rw [mem_levelGeSet] at hb
  by_contra hlt
  rw [not_le] at hlt
  -- `b < a ⇒ f b ≤ f a`, contradicting `f a < x ≤ f b`.
  have hfab : f b ≤ f a := hf hlt.le
  exact absurd (lt_of_lt_of_le (lt_of_lt_of_le ha hb) hfab) (lt_irrefl _)

/-- `sup {t | f t < x} ≤ f⁻¹ x` for monotone `f` (easy partition direction). -/
theorem sSup_levelLtSet_le [CompleteLinearOrder α] [Preorder β]
    (f : α → β) (hf : Monotone f) (x : β) :
    sSup (levelLtSet f x) ≤ pseudoInv f x :=
  sSup_le (fun _ ha => le_sInf (fun _ hb =>
    levelLtSet_le_levelGeSet hf x ha hb))

/-- `f⁻¹(x) = sup {t | f t < x}` for non-decreasing `f` (on a densely-ordered
complete linear order). -/
theorem pseudoInv_eq_sSup_lt [CompleteLinearOrder α] [DenselyOrdered α]
    [LinearOrder β] (f : α → β) (hf : Monotone f) (x : β) :
    pseudoInv f x = sSup (levelLtSet f x) := by
  refine le_antisymm ?_ (sSup_levelLtSet_le f hf x)
  -- `inf I_{≥} ≤ sup I_{<}`: every value below the inf is below a strict time.
  refine le_of_forall_lt fun c hc => ?_
  -- density: pick a time `t` with `c < t < inf I_{≥}`.
  obtain ⟨t, hct, htlt⟩ := exists_between hc
  -- `t < inf I_{≥}` forces `t ∉ I_{≥}`, so by the partition `f t < x`.
  have hnotmem : t ∉ levelGeSet f x := fun hmem =>
    absurd (sInf_le hmem) (not_le.mpr htlt)
  have hflt : f t < x := by
    by_contra hge
    exact hnotmem (mem_levelGeSet.mpr (not_lt.mp hge))
  -- so `t ∈ I_{<}`, hence `c < t ≤ sup I_{<}`.
  exact lt_of_lt_of_le hct (le_sSup (mem_levelLtSet.mpr hflt))

/-! ## Pseudo-inversion relations

The four `t`–`x` implications relating `f` to `f⁻¹`. The `x ≤ f t ⇒ f⁻¹ x ≤ t`
direction is the Galois bound `pseudoInv_le_of_le_apply` (above); the three
here add the converse `t > f⁻¹ x ⇒ x ≤ f t` (up-closedness of `𝓘_{≥x}` for
monotone `f`) and the two contrapositives. Stated over
`[CompleteLinearOrder α] [Preorder β]`. -/

/-- `t > f⁻¹ x ⇒ x ≤ f t` (`𝓘_{≥x}` is up-closed for monotone `f`). -/
theorem le_apply_of_pseudoInv_lt [CompleteLinearOrder α] [Preorder β]
    {f : α → β} (hf : Monotone f) {x : β} {t : α}
    (ht : pseudoInv f x < t) : x ≤ f t := by
  -- `inf 𝓘_{≥x} < t` gives an admissible `s ≤ t`; monotonicity lifts it to `t`.
  obtain ⟨s, hs, hst⟩ := sInf_lt_iff.mp ht
  exact le_trans (mem_levelGeSet.mp hs) (hf hst.le)

/-- `t < f⁻¹ x ⇒ f t < x` (contrapositive of `x ≤ f t ⇒ f⁻¹ x ≤ t`). -/
theorem apply_lt_of_lt_pseudoInv [CompleteLattice α] [LinearOrder β]
    {f : α → β} {x : β} {t : α} (ht : t < pseudoInv f x) : f t < x := by
  by_contra h
  exact absurd (lt_of_lt_of_le ht (pseudoInv_le_of_le_apply (not_lt.mp h)))
    (lt_irrefl t)

/-- `f t < x ⇒ t ≤ f⁻¹ x` (contrapositive of `t > f⁻¹ x ⇒ x ≤ f t`). -/
theorem le_pseudoInv_of_apply_lt [CompleteLinearOrder α] [LinearOrder β]
    {f : α → β} (hf : Monotone f) {x : β} {t : α} (ht : f t < x) :
    t ≤ pseudoInv f x := by
  by_contra h
  exact absurd (le_apply_of_pseudoInv_lt hf (not_le.mp h)) (not_le.mpr ht)

/-! ## Left-continuity of the pseudo-inverse

`f⁻¹` is left-continuous: `sup_{x' < x} f⁻¹(x') = f⁻¹(x)`. The `≤` direction is
monotonicity; the `≥` direction is the density argument — if `s < f⁻¹(x)` then
`f s < x` (`apply_lt_of_lt_pseudoInv`), and a level `x'` strictly between `f s`
and `x` has `s ≤ f⁻¹(x')`, so no such `s` exceeds the sup. Combined with
`pseudoInv_mono` and `leftLim`/`continuousWithinAt_Iio` this yields
left-continuity in the order topology. -/

/-- `sup_{x' < x} f⁻¹(x') = f⁻¹(x)`: the pseudo-inverse equals its own left
limit (for non-decreasing `f` over a densely-ordered level axis `β`). -/
theorem sSup_pseudoInv_image_Iio [CompleteLinearOrder α] [DenselyOrdered α]
    [LinearOrder β] [DenselyOrdered β] (f : α → β) (hf : Monotone f) (x : β) :
    sSup (pseudoInv f '' Iio x) = pseudoInv f x := by
  apply le_antisymm
  · -- monotonicity: every `x' < x` has `f⁻¹ x' ≤ f⁻¹ x`.
    refine sSup_le ?_
    rintro a ⟨x', hx', rfl⟩
    exact pseudoInv_mono f hx'.le
  · -- `≥`: rewrite `f⁻¹ x = sup 𝓘_{<x}` and bound each strict time.
    rw [pseudoInv_eq_sSup_lt f hf x]
    refine sSup_le fun t ht => ?_
    -- `f t < x`; pick a level `f t < x' < x`, then `t ≤ f⁻¹ x' ≤ sup`.
    have hft : f t < x := mem_levelLtSet.mp ht
    obtain ⟨x', hftx', hx'x⟩ := exists_between hft
    exact le_trans (le_pseudoInv_of_apply_lt hf hftx') (le_sSup ⟨x', hx'x, rfl⟩)

/-- The left limit of `f⁻¹` at `x` is `f⁻¹ x` (it equals its own left limit). -/
theorem leftLim_pseudoInv [CompleteLinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α]
    [LinearOrder β] [DenselyOrdered β] [TopologicalSpace β] [OrderTopology β]
    (f : α → β) (hf : Monotone f) (x : β) :
    Function.leftLim (pseudoInv f) x = pseudoInv f x := by
  rcases eq_or_ne (𝓝[<] x) ⊥ with hbot | hbot
  · -- empty left neighbourhood: `leftLim` is the value by convention.
    exact leftLim_eq_of_eq_bot _ hbot
  · -- otherwise `leftLim = sup_{x'<x} f⁻¹ x' = f⁻¹ x`.
    letI : (𝓝[<] x).NeBot := neBot_iff.2 hbot
    rw [(pseudoInv_mono f).leftLim_eq_sSup,
      sSup_pseudoInv_image_Iio f hf x]

/-- `f⁻¹` is left-continuous (in the order topologies) for non-decreasing `f`. -/
theorem continuousWithinAt_Iio_pseudoInv [CompleteLinearOrder α]
    [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
    [LinearOrder β] [DenselyOrdered β] [TopologicalSpace β] [OrderTopology β]
    (f : α → β) (hf : Monotone f) (x : β) :
    ContinuousWithinAt (pseudoInv f) (Iio x) x :=
  (pseudoInv_mono f).continuousWithinAt_Iio_iff_leftLim_eq.mpr
    (leftLim_pseudoInv f hf x)

/-! ## First-crossing of a delay

For the pure-delay curve `delay d` (`0` up to `d`, `⊤` beyond), `f⁻¹(x)` is the
first time the level `x` is reached. Over a densely-ordered complete linear
domain, every positive level is first reached just past `d`, so `f⁻¹ x = d`
for `x > 0`, while `f⁻¹ ⊥ = ⊥`. The `delayENN`/`delayNN` curves are witnesses. -/

/-- First-crossing for the pure delay: `(delay d)⁻¹ x = d` for `0 < x`. -/
theorem pseudoInv_delay_pos [CompleteLinearOrder α] [DenselyOrdered α]
    [PartialOrder β] [Zero β] [OrderTop β]
    (d : α) {x : β} (hx : 0 < x) :
    pseudoInv (delay d) x = d := by
  apply le_antisymm
  · -- `d` is approached from above: every `d < c` is admissible.
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    exact pseudoInv_le_of_le_apply ((le_delay_iff d hx c).mpr hc)
  · -- `d` lower-bounds the admissible set (`d < t ⇒ d ≤ t`).
    exact le_pseudoInv (fun t ht => le_of_lt ((le_delay_iff d hx t).mp ht))

/-- First-crossing: `(delayENN d)⁻¹ x = d` for `0 < x`. -/
theorem pseudoInv_delayENN_pos (d : ℝ≥0∞) {x : ℝ≥0∞} (hx : 0 < x) :
    pseudoInv (delayENN d) x = d :=
  pseudoInv_delay_pos d hx

/-- `(delayENN d)⁻¹ 0 = 0`. -/
theorem pseudoInv_delayENN_zero (d : ℝ≥0∞) : pseudoInv (delayENN d) 0 = 0 :=
  pseudoInv_bot (delayENN d)

end DeepWiki
