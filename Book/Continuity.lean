import Book.FunctionDioids
import Book.Limits
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Continuity notions for real functions
One-sided continuity over `ℝ≥0` (`IsLeftContinuous`/`IsRightContinuous`),
its ε–δ characterizations and their bridges to the filter limits
`TendstoLeft`/`TendstoRight`, and piecewise continuity
(`IsPiecewiseContinuous`: finitely many discontinuities on each `[0, T]`)
— the regularity layer of the convolution theory. -/

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
theorem isLeftContinuous_of_continuous {X : Type*}
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
theorem isRightContinuous_of_continuous {X : Type*}
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

/-- A finite sum of left-continuous functions into a commutative
topological additive monoid is left-continuous. -/
theorem isLeftContinuous_sum {ι X : Type*} [TopologicalSpace X]
    [_root_.AddCommMonoid X] [ContinuousAdd X] (s : Finset ι)
    {f : ι → ℝ≥0 → X} (hf : ∀ i ∈ s, IsLeftContinuous (f i)) :
    IsLeftContinuous (fun x => ∑ i ∈ s, f i x) := fun t =>
  tendsto_finsetSum s fun i hi => hf i hi t

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
theorem tendstoLeft_value_iff_isLeftContinuousAt
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    TendstoLeft g t (g t)
      ↔ IsLeftContinuousAt g t := Iff.rfl

/-- Right-continuity at `t` is the right limit equaling `g t`. -/
theorem tendstoRight_value_iff_isRightContinuousAt
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    TendstoRight g t (g t)
      ↔ IsRightContinuousAt g t := Iff.rfl

/-- Left-continuous `g` has left limit `g t` at each `t`. -/
theorem tendstoLeft_value_of_isLeftContinuous
    (g : ℝ≥0 → ℝ≥0∞) (hlc : IsLeftContinuous g)
    (t : ℝ≥0) : TendstoLeft g t (g t) :=
  (hlc t).tendsto

/-- Right-continuous `g` has right limit `g t` at each `t`. -/
theorem tendstoRight_value_of_isRightContinuous
    (g : ℝ≥0 → ℝ≥0∞) (hrc : IsRightContinuous g)
    (t : ℝ≥0) : TendstoRight g t (g t) :=
  (hrc t).tendsto

/-- Left-continuity at `t` iff some left limit `L` equals `g t`. -/
theorem isLeftContinuousAt_iff_limit_eq_value
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    IsLeftContinuousAt g t
      ↔ ∃ L, TendstoLeft g t L ∧ L = g t := by
  constructor
  · intro h; exact ⟨g t, h, rfl⟩
  · rintro ⟨L, hL, rfl⟩; exact hL

/-- Right-continuity at `t` iff some right limit `L` equals `g t`. -/
theorem isRightContinuousAt_iff_limit_eq_value
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    IsRightContinuousAt g t
      ↔ ∃ L, TendstoRight g t L ∧ L = g t := by
  constructor
  · intro h; exact ⟨g t, h, rfl⟩
  · rintro ⟨L, hL, rfl⟩; exact hL

/-- Left-continuous `g` has a left limit at every `t`. -/
theorem hasLeftLimit_of_isLeftContinuous
    (g : ℝ≥0 → ℝ≥0∞) (h : IsLeftContinuous g)
    (t : ℝ≥0) : ∃ L, TendstoLeft g t L :=
  ⟨g t, h t⟩

/-- Right-continuous `g` has a right limit at every `t`. -/
theorem hasRightLimit_of_isRightContinuous
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
theorem tendsto_nhdsWithin_Iio_of_isLeftContinuous {A : ℝ≥0 → ℝ≥0}
    (hA : IsLeftContinuous A) (t : ℝ≥0) :
    Tendsto A (𝓝[<] t) (𝓝 (A t)) :=
  (hA t).tendsto

/-- Right-continuous `A` has `A` as the right limit at each `t`:
`Tendsto A (𝓝[>] t) (𝓝 (A t))`. -/
theorem tendsto_nhdsWithin_Ioi_of_isRightContinuous {A : ℝ≥0 → ℝ≥0}
    (hA : IsRightContinuous A) (t : ℝ≥0) :
    Tendsto A (𝓝[>] t) (𝓝 (A t)) :=
  (hA t).tendsto

/-- **Left limit dominated by a uniform bound**: for left-continuous `A`, if
`A (x − ε) ≤ c` for every `ε > 0`, then `A x ≤ c` — the left limit `A x` is the
limit of the dominated values `A (x − ε)` (and `A 0 = A (0 − ε)` directly). -/
theorem le_of_forall_sub_pos_le_of_isLeftContinuous {A : ℝ≥0 → ℝ≥0}
    (hA : IsLeftContinuous A) {x c : ℝ≥0}
    (h : ∀ ε : ℝ≥0, 0 < ε → A (x - ε) ≤ c) : A x ≤ c := by
  rcases eq_or_lt_of_le (zero_le' : (0 : ℝ≥0) ≤ x) with hx | hx
  · subst hx
    have h0 := h 1 one_pos
    rwa [zero_tsub] at h0
  · haveI : (𝓝[<] x).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hx⟩
    refine le_of_tendsto (tendsto_nhdsWithin_Iio_of_isLeftContinuous hA x) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyx : y < x := hy
    have hb := h (x - y) (tsub_pos_of_lt hyx)
    rwa [tsub_tsub_cancel_of_le hyx.le] at hb

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

/-- A monotone left-continuous `g` with finite image on each `[0, T]`
is piecewise continuous: every discontinuity is a right jump, so `g` is
injective on its discontinuity set, which embeds in the finite image. -/
theorem isPiecewiseContinuous_of_monotone_of_finite_image
    {g : ℝ≥0 → ℝ≥0} (hmono : Monotone g) (hlc : IsLeftContinuous g)
    (hfin : ∀ T, (g '' Set.Icc 0 T).Finite) :
    IsPiecewiseContinuous g := by
  intro T
  refine Set.Finite.of_finite_image
    ((hfin T).subset (Set.image_mono Set.inter_subset_right)) ?_
  have key : ∀ a b : ℝ≥0, a ∈ discontSet g ∩ Set.Icc 0 T → a < b →
      g a < g b := by
    intro a b ha hab
    have hra : g a < Function.rightLim g a := by
      rcases lt_or_eq_of_le (hmono.le_rightLim (le_refl a)) with h | h
      · exact h
      · exact absurd (hmono.continuousAt_iff_leftLim_eq_rightLim.mpr
          (((hmono.continuousWithinAt_Iio_iff_leftLim_eq).mp
            (hlc a)).trans h)) ha.1
    exact lt_of_lt_of_le hra (hmono.rightLim_le hab)
  intro t₁ ht₁ t₂ ht₂ heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd heq (ne_of_lt (key t₁ t₂ ht₁ h))
  · exact absurd heq.symm (ne_of_lt (key t₂ t₁ ht₂ h))

/-- A monotone curve with an additive Lipschitz bound is continuous:
the two one-sided estimates squeeze every approach. -/
theorem continuous_of_monotone_of_lipschitz_bound {f : ℝ≥0 → ℝ≥0}
    {R : ℝ≥0} (hmono : Monotone f)
    (hlip : ∀ v w, w ≤ v → f v ≤ f w + R * (v - w)) :
    Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := R) fun x y => ?_).continuous
  rcases le_total x y with h | h
  · have hfy := hlip y x h
    have hxy : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast h
    have hfxy : ((f x : ℝ≥0) : ℝ) ≤ (f y : ℝ) := by
      exact_mod_cast hmono h
    rw [NNReal.dist_eq, NNReal.dist_eq, abs_sub_comm ((x : ℝ≥0) : ℝ),
      abs_sub_comm ((f x : ℝ≥0) : ℝ),
      abs_of_nonneg (sub_nonneg.mpr hxy),
      abs_of_nonneg (sub_nonneg.mpr hfxy)]
    have hR : ((f y : ℝ≥0) : ℝ)
        ≤ (f x : ℝ) + (R : ℝ) * ((y - x : ℝ≥0) : ℝ) := by
      exact_mod_cast hfy
    rw [NNReal.coe_sub h] at hR
    linarith
  · have hfx := hlip x y h
    have hxy : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
    have hfxy : ((f y : ℝ≥0) : ℝ) ≤ (f x : ℝ) := by
      exact_mod_cast hmono h
    rw [NNReal.dist_eq, NNReal.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hfxy),
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    have hR : ((f x : ℝ≥0) : ℝ)
        ≤ (f y : ℝ) + (R : ℝ) * ((x - y : ℝ≥0) : ℝ) := by
      exact_mod_cast hfx
    rw [NNReal.coe_sub h] at hR
    linarith

/-- A monotone left-continuous `ℝ≥0`-curve is lower semicontinuous:
the left side converges by left-continuity, the right side only sees
larger values. -/
theorem Monotone.lowerSemicontinuous_of_isLeftContinuous
    {f : ℝ≥0 → ℝ≥0} (hmono : Monotone f) (hlc : IsLeftContinuous f) :
    LowerSemicontinuous f := by
  intro x y hy
  rw [← nhdsLT_sup_nhdsGE x, Filter.eventually_sup]
  constructor
  · exact (hlc x).eventually (eventually_gt_nhds hy)
  · filter_upwards [self_mem_nhdsWithin] with v (hv : x ≤ v)
    exact lt_of_lt_of_le hy (hmono hv)

end DeepWiki
