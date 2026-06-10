import Book.Additivity
import Book.Continuity
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Convolution attains its minimum

For nondecreasing, left-continuous real curves the convolution is lower
semicontinuous on a compact interval, hence attains its minimum.
-/

namespace DeepWiki

open Topology Filter Set
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- Monotone + left-continuous `g : ℝ≥0 → T` (order-topology codomain) is
lower semicontinuous. -/
theorem lowerSemicontinuous_of_mono_leftCont
    {T : Type*} [LinearOrder T] [TopologicalSpace T] [OrderTopology T]
    (g : ℝ≥0 → T) (hmono : Monotone g)
    (hlc : IsLeftContinuous g) :
    LowerSemicontinuous g := by
  intro t y hy
  rw [← nhdsLT_sup_nhdsGE t, eventually_sup]
  refine ⟨(hlc t).eventually (Ioi_mem_nhds hy), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact lt_of_lt_of_le hy (hmono hz)

/-- The split objective `u ↦ g u + h (t - u)` minimized by convolution. -/
noncomputable def splitMap {D T : Type*} [Sub D]
    [_root_.Add T] (g h : D → T) (t : D) : D → T :=
  fun u => g u + h (t - u)

/-- `splitMap g h t` is lower semicontinuous when `g`, `h` are. -/
theorem lowerSemicontinuous_splitMap
    {T : Type*} [_root_.AddCommMonoid T] [LinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T]
    [OrderTopology T] [ContinuousAdd T]
    (g h : ℝ≥0 → T)
    (hg : LowerSemicontinuous g)
    (hh : LowerSemicontinuous h) (t : ℝ≥0) :
    LowerSemicontinuous (splitMap g h t) := by
  have hsub : Continuous (fun u : ℝ≥0 => t - u) := by
    continuity
  exact hg.add (hh.comp hsub)

/-- `splitMap g h t` attains its minimum on `Icc 0 t` (lsc on compact). -/
theorem exists_isMinOn_splitMap
    {T : Type*} [_root_.AddCommMonoid T] [LinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T]
    [OrderTopology T] [ContinuousAdd T]
    (g h : ℝ≥0 → T)
    (hg : LowerSemicontinuous g)
    (hh : LowerSemicontinuous h) (t : ℝ≥0) :
    ∃ u ∈ Set.Icc (0 : ℝ≥0) t,
      IsMinOn (splitMap g h t) (Set.Icc 0 t) u :=
  LowerSemicontinuousOn.exists_isMinOn ⟨0, by simp⟩
    isCompact_Icc
    ((lowerSemicontinuous_splitMap g h hg hh t)
      |>.lowerSemicontinuousOn _)

/-- Minimum attained on `Icc 0 t` for monotone left-continuous curves. -/
theorem exists_isMinOn_splitMap_of_curves
    {T : Type*} [_root_.AddCommMonoid T] [LinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T]
    [OrderTopology T] [ContinuousAdd T]
    (g h : ℝ≥0 → T)
    (hgm : Monotone g) (hhm : Monotone h)
    (hgc : IsLeftContinuous g)
    (hhc : IsLeftContinuous h) (t : ℝ≥0) :
    ∃ u ∈ Set.Icc (0 : ℝ≥0) t,
      IsMinOn (splitMap g h t) (Set.Icc 0 t) u :=
  exists_isMinOn_splitMap g h
    (lowerSemicontinuous_of_mono_leftCont g hgm hgc)
    (lowerSemicontinuous_of_mono_leftCont h hhm hhc) t

/-- The convolution value `minConv g h t` equals the split objective at any
minimizer `u₀ ∈ [0,t]`: the defining infimum is attained. -/
theorem minConv_eq_splitMap_of_isMinOn
    {T : Type*} [_root_.AddCommMonoid T] [CompleteLinearOrder T]
    [IsOrderedAddMonoid T] (g h : ℝ≥0 → T) (t : ℝ≥0) {u₀ : ℝ≥0}
    (hu₀ : u₀ ∈ Set.Icc (0 : ℝ≥0) t)
    (hmin : IsMinOn (splitMap g h t) (Set.Icc 0 t) u₀) :
    minConv g h t = splitMap g h t u₀ := by
  unfold minConv splitMap
  apply le_antisymm
  · refine iInf_le_of_le
      ⟨(u₀, t - u₀), add_tsub_cancel_of_le hu₀.2⟩ le_rfl
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
    have hut : u ≤ t := hus ▸ le_self_add
    have hsu : t - u = s := by rw [← hus, add_tsub_cancel_left]
    have := hmin (show u ∈ Set.Icc (0 : ℝ≥0) t from ⟨zero_le', hut⟩)
    simpa [splitMap, hsu] using this

/-- For nondecreasing left-continuous curves `g, h`, the convolution
`minConv g h t` is attained at some `u₀ ∈ [0,t]`:
`minConv g h t = g u₀ + h (t - u₀)`. -/
theorem exists_minConv_eq_split_of_curves
    {T : Type*} [_root_.AddCommMonoid T] [CompleteLinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T] [OrderTopology T]
    [ContinuousAdd T] (g h : ℝ≥0 → T)
    (hgm : Monotone g) (hhm : Monotone h)
    (hgc : IsLeftContinuous g) (hhc : IsLeftContinuous h) (t : ℝ≥0) :
    ∃ u₀ ∈ Set.Icc (0 : ℝ≥0) t, minConv g h t = g u₀ + h (t - u₀) := by
  obtain ⟨u₀, hu₀, hmin⟩ :=
    exists_isMinOn_splitMap_of_curves g h hgm hhm hgc hhc t
  exact ⟨u₀, hu₀, minConv_eq_splitMap_of_isMinOn g h t hu₀ hmin⟩

end DeepWiki
