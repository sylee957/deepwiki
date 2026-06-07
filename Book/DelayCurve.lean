import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Delay curve
The pure-delay curve `delay d = (t ↦ if t ≤ d then 0 else ⊤)`, defined once
over any ordered domain `D` and value type `V` with `0`/`⊤`. Specialize by the
result type: `delayNN` over `ℝ≥0 → ℝ≥0∞`, `delayE` over `ℝ≥0∞ → ℝ≥0∞`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- Pure-delay curve, defined once over any ordered domain `D` and value type
`V` with `0`/`⊤`: `0` for `t ≤ d`, `⊤` afterwards. Specialize by the result
type — e.g. `delay d : ℝ≥0 → ℝ≥0∞` or `delay d : ℝ≥0∞ → ℝ≥0∞`. -/
noncomputable def delay {D V : Type*} [Preorder D] [Zero V] [Top V]
    (d : D) : D → V :=
  fun t => if t ≤ d then 0 else ⊤

/-- `delay d t = if t ≤ d then 0 else ⊤`. -/
@[simp] theorem delay_apply {D V : Type*} [Preorder D] [Zero V] [Top V]
    (d t : D) : (delay d : D → V) t = if t ≤ d then 0 else ⊤ := rfl

/-- `delay d` vanishes at any `t ≤ d`. -/
theorem delay_eq_zero {D V : Type*} [Preorder D] [Zero V] [Top V]
    (d : D) {t : D} (ht : t ≤ d) : (delay d : D → V) t = 0 := by
  rw [delay_apply, if_pos ht]

/-- `delay d` is `⊤` past `d`. -/
theorem delay_eq_top {D V : Type*} [Preorder D] [Zero V] [Top V]
    (d : D) {t : D} (ht : d < t) : (delay d : D → V) t = ⊤ := by
  rw [delay_apply, if_neg (not_le_of_gt ht)]

/-- First-crossing: for `0 < x`, `x ≤ delay d t ↔ d < t`. -/
theorem le_delay_iff {D V : Type*} [LinearOrder D]
    [PartialOrder V] [Zero V] [OrderTop V]
    (d : D) {x : V} (hx : 0 < x) (t : D) :
    x ≤ (delay d : D → V) t ↔ d < t := by
  rcases le_or_gt t d with ht | ht
  · rw [delay_eq_zero d ht]
    exact ⟨fun h => absurd (le_antisymm h hx.le) hx.ne',
      fun h => absurd ht (not_le.mpr h)⟩
  · rw [delay_eq_top d ht]
    exact ⟨fun _ => ht, fun _ => le_top⟩

/-- Pure-delay curve over `ℝ≥0 → ℝ≥0∞`. -/
noncomputable abbrev delayNN (d : ℝ≥0) : ℝ≥0 → ℝ≥0∞ := delay d

/-- Pure-delay curve over `ℝ≥0∞ → ℝ≥0∞`. -/
noncomputable abbrev delayE (d : ℝ≥0∞) : ℝ≥0∞ → ℝ≥0∞ := delay d

/-- `delayNN d 0 = 0`. -/
theorem delayNN_zero_eq (d : ℝ≥0) : delayNN d 0 = 0 := by
  simp [delayNN]

/-- `delayE d 0 = 0`. -/
theorem delayE_zero_eq (d : ℝ≥0∞) : delayE d 0 = 0 := by
  simp [delayE]

/-- On finite arguments, `delayE ↑d` agrees with `delayNN d`. -/
theorem delayE_coe (d t : ℝ≥0) :
    delayE (d : ℝ≥0∞) (t : ℝ≥0∞) = delayNN d t := by
  simp only [delayE, delayNN, delay_apply, ENNReal.coe_le_coe]; convert rfl

end DeepWiki
