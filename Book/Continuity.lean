import Book.FunctionDioids
import Book.Limits
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Continuity notions for real functions
One-sided continuity and piecewise continuity over `ℝ≥0`,
used by the convolution theory. -/

namespace DeepWiki

open Algebra Topology Filter Set
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- `g` is left-continuous at `t`: `ContinuousWithinAt g (Iio t) t`. -/
def IsLeftContinuousAt {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) (t : ℝ≥0) : Prop :=
  ContinuousWithinAt g (Iio t) t

/-- `g` is left-continuous at every `t : ℝ≥0`. -/
def IsLeftContinuous {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) : Prop :=
  ∀ t : ℝ≥0, IsLeftContinuousAt g t

/-- Every `g` is left-continuous at `0` (since `Iio 0 = ∅`). -/
theorem isLeftContinuousAt_zero {X : Type*}
    [TopologicalSpace X] (g : ℝ≥0 → X) :
    IsLeftContinuousAt g 0 := by
  have hbot : 𝓝[Iio (0 : ℝ≥0)] 0 = ⊥ := by
    rw [show Set.Iio (0 : ℝ≥0) = ∅ by simp,
      nhdsWithin_empty]
  unfold IsLeftContinuousAt ContinuousWithinAt
  rw [hbot]
  exact tendsto_bot

/-- A continuous `g` is left-continuous. -/
theorem leftCont_of_continuous {X : Type*}
    [TopologicalSpace X] (g : ℝ≥0 → X)
    (hg : Continuous g) : IsLeftContinuous g :=
  fun _ => hg.continuousAt.continuousWithinAt

/-- `g` is right-continuous at `t`: `ContinuousWithinAt g (Ioi t) t`. -/
def IsRightContinuousAt {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) (t : ℝ≥0) : Prop :=
  ContinuousWithinAt g (Ioi t) t

/-- `g` is right-continuous at every `t : ℝ≥0`. -/
def IsRightContinuous {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) : Prop :=
  ∀ t : ℝ≥0, IsRightContinuousAt g t

/-- A continuous `g` is right-continuous. -/
theorem rightCont_of_continuous {X : Type*}
    [TopologicalSpace X] (g : ℝ≥0 → X)
    (hg : Continuous g) : IsRightContinuous g :=
  fun _ => hg.continuousAt.continuousWithinAt

/-- `g` is continuous iff it is both left- and right-continuous. -/
theorem continuous_iff_left_right
    {X : Type*} [TopologicalSpace X] (g : ℝ≥0 → X) :
    Continuous g ↔
      IsLeftContinuous g ∧ IsRightContinuous g := by
  rw [continuous_iff_continuousAt]
  unfold IsLeftContinuous IsRightContinuous
    IsLeftContinuousAt IsRightContinuousAt
  constructor
  · intro h
    exact ⟨fun t =>
        (continuousAt_iff_continuous_left'_right'.mp
          (h t)).1,
      fun t =>
        (continuousAt_iff_continuous_left'_right'.mp
          (h t)).2⟩
  · rintro ⟨hl, hr⟩ t
    exact continuousAt_iff_continuous_left'_right'.mpr
      ⟨hl t, hr t⟩

/-- ε–δ left-continuity at `t` for `ℝ≥0∞`-valued `g` (finite/infinite cases). -/
def IsLeftContinuousAtEpsDelta
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : Prop :=
  (g t ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
      g s ≠ ⊤ ∧ |realOf g s - realOf g t| < ε) ∧
  (g t = ⊤ →
    ∀ M : ℝ≥0, ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
      (M : ℝ≥0∞) < g s)

/-- ε–δ right-continuity at `t` for `ℝ≥0∞`-valued `g` (finite/infinite cases). -/
def IsRightContinuousAtEpsDelta
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : Prop :=
  (g t ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
      g s ≠ ⊤ ∧ |realOf g s - realOf g t| < ε) ∧
  (g t = ⊤ →
    ∀ M : ℝ≥0, ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
      (M : ℝ≥0∞) < g s)

/-- For `t > 0`, ε–δ left-continuity agrees with `IsLeftContinuousAt`. -/
theorem isLeftContinuousAtEpsDelta_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t) :
    IsLeftContinuousAtEpsDelta g t ↔ IsLeftContinuousAt g t :=
  tendstoLeftEpsDelta_iff g t ht (g t)

/-- ε–δ right-continuity agrees with `IsRightContinuousAt`. -/
theorem isRightContinuousAtEpsDelta_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    IsRightContinuousAtEpsDelta g t
      ↔ IsRightContinuousAt g t :=
  tendstoRightEpsDelta_iff g t (g t)

/-- Left-continuity at `t` is the left limit equaling `g t`. -/
theorem tendstoLeft_value_iff_leftContinuousAt
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    TendstoLeft g t (g t)
      ↔ IsLeftContinuousAt g t := Iff.rfl

/-- Right-continuity at `t` is the right limit equaling `g t`. -/
theorem tendstoRight_value_iff_rightContinuousAt
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    TendstoRight g t (g t)
      ↔ IsRightContinuousAt g t := Iff.rfl

/-- Left-continuous `g` has left limit `g t` at each `t`. -/
theorem tendstoLeft_value_of_leftContinuous
    (g : ℝ≥0 → ℝ≥0∞) (hlc : IsLeftContinuous g)
    (t : ℝ≥0) : TendstoLeft g t (g t) :=
  (hlc t).tendsto

/-- Right-continuous `g` has right limit `g t` at each `t`. -/
theorem tendstoRight_value_of_rightContinuous
    (g : ℝ≥0 → ℝ≥0∞) (hrc : IsRightContinuous g)
    (t : ℝ≥0) : TendstoRight g t (g t) :=
  (hrc t).tendsto

/-- Left-continuity at `t` iff some left limit `L` equals `g t`. -/
theorem leftContinuousAt_iff_limit_eq_value
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    IsLeftContinuousAt g t
      ↔ ∃ L, TendstoLeft g t L ∧ L = g t := by
  constructor
  · intro h; exact ⟨g t, h, rfl⟩
  · rintro ⟨L, hL, rfl⟩; exact hL

/-- Right-continuity at `t` iff some right limit `L` equals `g t`. -/
theorem rightContinuousAt_iff_limit_eq_value
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    IsRightContinuousAt g t
      ↔ ∃ L, TendstoRight g t L ∧ L = g t := by
  constructor
  · intro h; exact ⟨g t, h, rfl⟩
  · rintro ⟨L, hL, rfl⟩; exact hL

/-- Left-continuous `g` has a left limit at every `t`. -/
theorem hasLeftLimit_of_leftContinuous
    (g : ℝ≥0 → ℝ≥0∞) (h : IsLeftContinuous g)
    (t : ℝ≥0) : ∃ L, TendstoLeft g t L :=
  ⟨g t, h t⟩

/-- Right-continuous `g` has a right limit at every `t`. -/
theorem hasRightLimit_of_rightContinuous
    (g : ℝ≥0 → ℝ≥0∞) (h : IsRightContinuous g)
    (t : ℝ≥0) : ∃ L, TendstoRight g t L :=
  ⟨g t, h t⟩

/-- A positive right limit at `0` forces `f > 0` on some `(0, δ)`. -/
theorem pos_near_zero_of_rightLimit_pos
    (f : ℝ≥0 → ℝ≥0∞) (L : ℝ≥0∞)
    (hL : TendstoRight f 0 L) (hL0 : 0 < L) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t : ℝ≥0, 0 < t → t < δ → 0 < f t := by
  unfold TendstoRight at hL
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ≥0), 0 < f t :=
    hL.eventually (eventually_gt_nhds hL0)
  rw [eventually_nhdsWithin_iff,
    Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  refine ⟨⟨δ, hδ.le⟩, by exact_mod_cast hδ, ?_⟩
  intro t ht htδ
  apply hball (y := t)
  · rw [NNReal.dist_eq]
    simp only [NNReal.coe_zero, sub_zero,
      abs_of_nonneg t.coe_nonneg]
    exact_mod_cast htδ
  · exact ht

/-- Left-continuous `A` has `A` as the left limit at each `t`:
`Tendsto A (𝓝[<] t) (𝓝 (A t))`. -/
theorem tendsto_nhdsWithin_Iio_of_leftContinuous {A : ℝ≥0 → ℝ≥0}
    (hA : IsLeftContinuous A) (t : ℝ≥0) :
    Tendsto A (𝓝[<] t) (𝓝 (A t)) :=
  (hA t).tendsto

/-- Right-continuous `A` has `A` as the right limit at each `t`:
`Tendsto A (𝓝[>] t) (𝓝 (A t))`. -/
theorem tendsto_nhdsWithin_Ioi_of_rightContinuous {A : ℝ≥0 → ℝ≥0}
    (hA : IsRightContinuous A) (t : ℝ≥0) :
    Tendsto A (𝓝[>] t) (𝓝 (A t)) :=
  (hA t).tendsto

/-- The set of points where `g` is not continuous. -/
def discontSet {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) : Set ℝ≥0 :=
  { t | ¬ ContinuousAt g t }

/-- `g` has finitely many discontinuities on each `[0, T]`. -/
def IsPiecewiseContinuous {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) : Prop :=
  ∀ T : ℝ≥0, (discontSet g ∩ Set.Icc 0 T).Finite

/-- A continuous `g` is piecewise continuous. -/
theorem isPiecewiseContinuous_of_continuous
    {X : Type*} [TopologicalSpace X]
    (g : ℝ≥0 → X) (hg : Continuous g) :
    IsPiecewiseContinuous g := by
  intro T
  have hempty : discontSet g = ∅ := by
    ext t
    simp [discontSet, hg.continuousAt]
  rw [hempty, Set.empty_inter]
  exact Set.finite_empty

end DeepWiki
