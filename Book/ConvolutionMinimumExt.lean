import Book.ConvolutionMinimum
import Book.MinPlusExtTopology
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Convolution minimum over the extended reals

On two-sided extended reals addition is not globally continuous — it fails at
`(+∞,−∞)` — so the `ContinuousAdd`-based minimum-attainment of
`Book.ConvolutionMinimum` does not instantiate directly. These variants take an
explicit pointwise `ContinuousAt (+)` hypothesis instead, instantiated on both
`EReal = WithBot (WithTop ℝ)` and the book's `R̄min = WithTop (WithBot ℝ)`
(see `Book.MinPlusExtTopology`).
-/

namespace DeepWiki

open Topology Filter Set
open scoped Classical NNReal ENNReal Algebra.Bridge DeepWiki.MinPlusExt

/-- `a + b` is at a continuity point of `EReal` addition: the pair avoids the
two discontinuities `(⊤,⊥)`, `(⊥,⊤)` (i.e. no `(+∞)+(−∞)` collision). -/
def AddDefined (a b : EReal) : Prop :=
  (a ≠ ⊤ ∨ b ≠ ⊥) ∧ (a ≠ ⊥ ∨ b ≠ ⊤)

/-- `AddDefined a b` makes `(+)` continuous at `(a, b)`. -/
theorem AddDefined.continuousAt {a b : EReal} (h : AddDefined a b) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, b) :=
  EReal.continuousAt_add h.1 h.2

/-- `splitMap` lsc with an explicit pointwise `ContinuousAt (+)` hypothesis
(for carriers like `EReal`/`ℝ̄` where `+` is not globally continuous). -/
theorem lowerSemicontinuous_splitMap_of_contAt
    {T : Type*} [_root_.AddCommMonoid T] [LinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T] [OrderTopology T]
    (g h : ℝ≥0 → T) (hg : LowerSemicontinuous g)
    (hh : LowerSemicontinuous h) (t : ℝ≥0)
    (hcont : ∀ u : ℝ≥0,
      ContinuousAt (fun p : T × T => p.1 + p.2) (g u, h (t - u))) :
    LowerSemicontinuous (splitMap g h t) := by
  have hsub : Continuous (fun u : ℝ≥0 => t - u) := by continuity
  exact hg.add' (hh.comp hsub) hcont

/-- `splitMap g h t` attains its minimum on `Icc 0 t` (lsc-on-compact),
pointwise-`ContinuousAt (+)` form. -/
theorem exists_isMinOn_splitMap_of_contAt
    {T : Type*} [_root_.AddCommMonoid T] [LinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T] [OrderTopology T]
    (g h : ℝ≥0 → T) (hg : LowerSemicontinuous g)
    (hh : LowerSemicontinuous h) (t : ℝ≥0)
    (hcont : ∀ u : ℝ≥0,
      ContinuousAt (fun p : T × T => p.1 + p.2) (g u, h (t - u))) :
    ∃ u ∈ Set.Icc (0 : ℝ≥0) t,
      IsMinOn (splitMap g h t) (Set.Icc 0 t) u :=
  LowerSemicontinuousOn.exists_isMinOn ⟨0, by simp⟩
    isCompact_Icc
    ((lowerSemicontinuous_splitMap_of_contAt g h hg hh t hcont)
      |>.lowerSemicontinuousOn _)

/-- `minConv g h t = g u₀ + h (t - u₀)` at some `u₀ ∈ [0,t]` for nondecreasing
left-continuous curves, pointwise-`ContinuousAt (+)` form (so `EReal` and
`WithTop (WithBot ℝ)` instantiate where `ContinuousAdd` fails). -/
theorem exists_minConv_eq_split_of_curves_of_contAt
    {T : Type*} [_root_.AddCommMonoid T] [CompleteLinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T] [OrderTopology T]
    (g h : ℝ≥0 → T) (hgm : Monotone g) (hhm : Monotone h)
    (hgc : IsLeftContinuous g) (hhc : IsLeftContinuous h) (t : ℝ≥0)
    (hcont : ∀ u : ℝ≥0,
      ContinuousAt (fun p : T × T => p.1 + p.2) (g u, h (t - u))) :
    ∃ u₀ ∈ Set.Icc (0 : ℝ≥0) t, minConv g h t = g u₀ + h (t - u₀) := by
  obtain ⟨u₀, hu₀, hmin⟩ :=
    exists_isMinOn_splitMap_of_contAt g h
      (lowerSemicontinuous_of_mono_isLeftContinuous g hgm hgc)
      (lowerSemicontinuous_of_mono_isLeftContinuous h hhm hhc) t hcont
  exact ⟨u₀, hu₀, minConv_eq_splitMap_of_isMinOn g h t hu₀ hmin⟩

/-! ## Attainment over `EReal`
Over the extended reals `ℝ̄ = EReal`: for nondecreasing, left-continuous
`g, h : ℝ⁺ → ℝ̄` with `AddDefined (g u) (h (t−u))` at every split (no
`(+∞)+(−∞)` collision), the min-plus convolution is attained:
`minConv g h t = g u₀ + h (t − u₀)` for some `u₀ ∈ [0,t]`.
Note: `EReal`'s `+` uses `(+∞)+(−∞) = −∞`, *not* the book's `R̄min` dioid
addition (gotcha #2); this is the order/topology content (the infimum is a
minimum), instantiated on the carrier Mathlib gives the topology for. -/
example (g h : ℝ≥0 → EReal)
    (hgm : Monotone g) (hhm : Monotone h)
    (hgc : IsLeftContinuous g) (hhc : IsLeftContinuous h) (t : ℝ≥0)
    (hpair : ∀ u : ℝ≥0, AddDefined (g u) (h (t - u))) :
    ∃ u₀ ∈ Set.Icc (0 : ℝ≥0) t, minConv g h t = g u₀ + h (t - u₀) :=
  exists_minConv_eq_split_of_curves_of_contAt g h hgm hhm hgc hhc t
    (fun u => (hpair u).continuousAt)

/-! ## Attainment over the book's carrier
Over the book's carrier `R̄min = WithTop (WithBot ℝ)` (top-absorbing `+`,
`(+∞)+(−∞) = +∞`): for nondecreasing, left-continuous `g, h : ℝ⁺ → R̄min` with
`AddDefinedExt (g u) (h (t−u))` at every split (no `(+∞)+(−∞)` collision), the
min-plus convolution is attained: `minConv g h t = g u₀ + h (t − u₀)` for some
`u₀ ∈ [0,t]`. This is the book's `R̄min` addition (unlike the `EReal` example),
via the order topology + add-continuity of `Book.MinPlusExtTopology`. -/
example (g h : ℝ≥0 → WithTop (WithBot ℝ))
    (hgm : Monotone g) (hhm : Monotone h)
    (hgc : IsLeftContinuous g) (hhc : IsLeftContinuous h) (t : ℝ≥0)
    (hpair : ∀ u : ℝ≥0, AddDefinedExt (g u) (h (t - u))) :
    ∃ u₀ ∈ Set.Icc (0 : ℝ≥0) t, minConv g h t = g u₀ + h (t - u₀) :=
  exists_minConv_eq_split_of_curves_of_contAt g h hgm hhm hgc hhc t
    (fun u => (hpair u).continuousAt)

end DeepWiki
