import DeepWiki.NetworkCalculus.Continuity
import Mathlib.Topology.Order.LeftRightLim

/-! # Left- and right-continuous closures
The closures `fₗ(t) = f(t−)` and `fᵣ(t) = f(t+)` are `Function.leftLim` and
`Function.rightLim`. For non-decreasing `f` the closure values exist as
genuine one-sided limits (`TendstoLeft`/`TendstoRight`), the closures are
themselves left- and right-continuous, and they fix exactly the left- and
right-continuous functions. -/

namespace DeepWiki

open Function Set Topology Filter
open scoped Classical NNReal ENNReal

/-- A non-decreasing `f` is left-continuous iff the left closure fixes it:
`IsLeftContinuous f ↔ leftLim f = f`. -/
theorem isLeftContinuous_iff_leftLim_eq
    {T : Type*} [ConditionallyCompleteLinearOrder T] [TopologicalSpace T]
    [OrderTopology T] {f : ℝ≥0 → T} (hmono : Monotone f) :
    IsLeftContinuous f ↔ leftLim f = f :=
  ⟨fun h => funext fun t =>
      hmono.continuousWithinAt_Iio_iff_leftLim_eq.mp (h t),
    fun h t =>
      hmono.continuousWithinAt_Iio_iff_leftLim_eq.mpr (congrFun h t)⟩

/-- A non-decreasing `f` is right-continuous iff the right closure fixes
it: `IsRightContinuous f ↔ rightLim f = f`. -/
theorem isRightContinuous_iff_rightLim_eq
    {T : Type*} [ConditionallyCompleteLinearOrder T] [TopologicalSpace T]
    [OrderTopology T] {f : ℝ≥0 → T} (hmono : Monotone f) :
    IsRightContinuous f ↔ rightLim f = f :=
  ⟨fun h => funext fun t =>
      hmono.continuousWithinAt_Ioi_iff_rightLim_eq.mp (h t),
    fun h t =>
      hmono.continuousWithinAt_Ioi_iff_rightLim_eq.mpr (congrFun h t)⟩

/-- The left closure of a non-decreasing `f` is left-continuous. -/
theorem isLeftContinuous_leftLim
    {T : Type*} [ConditionallyCompleteLinearOrder T] [TopologicalSpace T]
    [OrderTopology T] {f : ℝ≥0 → T} (hmono : Monotone f) :
    IsLeftContinuous (leftLim f) :=
  fun t => (continuousWithinAt_leftLim_Iic (hmono.tendsto_leftLim t)).mono
    Iio_subset_Iic_self

/-- The right closure of a non-decreasing `f` is right-continuous. -/
theorem isRightContinuous_rightLim
    {T : Type*} [ConditionallyCompleteLinearOrder T] [TopologicalSpace T]
    [OrderTopology T] {f : ℝ≥0 → T} (hmono : Monotone f) :
    IsRightContinuous (rightLim f) :=
  fun t => (continuousWithinAt_rightLim_Ici (hmono.tendsto_rightLim t)).mono
    Ioi_subset_Ici_self

/-- The left closure is idempotent: `leftLim (leftLim f) = leftLim f` for
non-decreasing `f`. -/
theorem leftLim_leftLim_eq_leftLim
    {T : Type*} [ConditionallyCompleteLinearOrder T] [TopologicalSpace T]
    [OrderTopology T] {f : ℝ≥0 → T} (hmono : Monotone f) :
    leftLim (leftLim f) = leftLim f :=
  funext fun t => leftLim_leftLim (hmono.tendsto_leftLim t)

/-- The right closure is idempotent: `rightLim (rightLim f) = rightLim f`
for non-decreasing `f`. -/
theorem rightLim_rightLim_eq_rightLim
    {T : Type*} [ConditionallyCompleteLinearOrder T] [TopologicalSpace T]
    [OrderTopology T] {f : ℝ≥0 → T} (hmono : Monotone f) :
    rightLim (rightLim f) = rightLim f :=
  funext fun t => rightLim_rightLim (hmono.tendsto_rightLim t)

/-- A non-decreasing `f` is continuous iff both closures fix it. -/
theorem continuous_iff_leftLim_eq_and_rightLim_eq
    {T : Type*} [ConditionallyCompleteLinearOrder T] [TopologicalSpace T]
    [OrderTopology T] {f : ℝ≥0 → T} (hmono : Monotone f) :
    Continuous f ↔ leftLim f = f ∧ rightLim f = f := by
  rw [continuous_iff_left_right, isLeftContinuous_iff_leftLim_eq hmono,
    isRightContinuous_iff_rightLim_eq hmono]

/-- On the `ℝ≥0` domain the left filter at `0` is trivial and the left
closure takes the fallback value, `leftLim f 0 = f 0` (the book, over `ℝ`
with curves null on negatives, reads `f(0−) = 0` instead). -/
theorem leftLim_zero_eq {X : Type*} [TopologicalSpace X] (f : ℝ≥0 → X) :
    leftLim f 0 = f 0 :=
  leftLim_eq_of_isBot fun _ => zero_le

/-- For non-decreasing `f`, the closure value `leftLim f t` is a left limit
of `f` at every `t`: `TendstoLeft f t (leftLim f t)` — monotonicity replaces
the book's piecewise continuity (degenerately at `t = 0`, where `𝓝[<] 0 = ⊥`
and `leftLim f 0 = f 0`). -/
theorem tendstoLeft_leftLim {f : ℝ≥0 → ℝ≥0∞} (hmono : Monotone f)
    (t : ℝ≥0) :
    TendstoLeft f t (leftLim f t) :=
  hmono.tendsto_leftLim t

/-- For non-decreasing `f`, the closure value `rightLim f t` is a right
limit of `f` at every `t`: `TendstoRight f t (rightLim f t)`. -/
theorem tendstoRight_rightLim {f : ℝ≥0 → ℝ≥0∞} (hmono : Monotone f)
    (t : ℝ≥0) :
    TendstoRight f t (rightLim f t) :=
  hmono.tendsto_rightLim t

/-- Any left limit at `t > 0` is the closure value: `TendstoLeft f t L`
forces `leftLim f t = L` (no monotonicity needed). -/
theorem leftLim_eq_of_tendstoLeft {f : ℝ≥0 → ℝ≥0∞} {t : ℝ≥0} {L : ℝ≥0∞}
    (ht : 0 < t) (hL : TendstoLeft f t L) : leftLim f t = L := by
  letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  exact leftLim_eq_of_tendsto hL

/-- Any right limit is the closure value: `TendstoRight f t L` forces
`rightLim f t = L` (no monotonicity needed). -/
theorem rightLim_eq_of_tendstoRight {f : ℝ≥0 → ℝ≥0∞} {t : ℝ≥0} {L : ℝ≥0∞}
    (hL : TendstoRight f t L) : rightLim f t = L := by
  letI : (𝓝[>] t).NeBot := nhdsGT_neBot t
  exact rightLim_eq_of_tendsto hL

/-! ## Book restatement (right- and left-continuous closure)
For `f ∈ ℱ`, the right-continuous extension `fᵣ(x) = f(x+)` and the
left-continuous extension `fₗ(x) = f(x−)` are `rightLim f` and `leftLim f`:
the closure values exist as one-sided limits at every point for
non-decreasing `f` (monotonicity replaces the book's piecewise continuity)
and are unique — on the right everywhere, on the left for `x > 0`; at
`x = 0` the left filter on `ℝ≥0` is trivial and `leftLim f 0 = f 0`. The
extensions are right- and left-continuous. Cf. `Book.DeviationsContinuity`,
where the deviations are shown insensitive to these closures. -/
example {f : ℝ≥0 → ℝ≥0∞} (hf : Monotone f) (x : ℝ≥0) :
    TendstoLeft f x (leftLim f x) ∧ TendstoRight f x (rightLim f x) :=
  ⟨tendstoLeft_leftLim hf x, tendstoRight_rightLim hf x⟩

example {f : ℝ≥0 → ℝ≥0∞} {x : ℝ≥0} {L L' : ℝ≥0∞} (hx : 0 < x)
    (hL : TendstoLeft f x L) (hL' : TendstoRight f x L') :
    leftLim f x = L ∧ rightLim f x = L' :=
  ⟨leftLim_eq_of_tendstoLeft hx hL, rightLim_eq_of_tendstoRight hL'⟩

example {f : ℝ≥0 → ℝ≥0∞} : leftLim f 0 = f 0 :=
  leftLim_zero_eq f

example {f : ℝ≥0 → ℝ≥0∞} (hf : Monotone f) :
    IsLeftContinuous (leftLim f) ∧ IsRightContinuous (rightLim f) :=
  ⟨isLeftContinuous_leftLim hf, isRightContinuous_rightLim hf⟩

end DeepWiki
