import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Delay as a requirement
The pure-delay shape abstracted as a property `IsDelay f d` — `f` is `0` up to
`d` and `⊤` beyond — over any ordered domain `D` and value type `V` with
`0`/`⊤`. The generic delay theory (vanishing below `d`, blow-up above, the
first-crossing characterization) is proved once against `IsDelay`. The
`ℝ≥0∞`-domain curve `delayE` is a concrete witness; the `ℝ≥0`-domain `delay`
(in `RealCurves`) is another. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- `f` is a pure delay at `d`: `0` for `t ≤ d`, `⊤` for `d < t`. -/
def IsDelay {D V : Type*} [Preorder D] [Zero V] [Top V]
    (f : D → V) (d : D) : Prop :=
  (∀ t, t ≤ d → f t = 0) ∧ (∀ t, d < t → f t = ⊤)

/-- A delay vanishes at any `t ≤ d`; in particular `f 0 = 0` when `0 ≤ d`. -/
theorem IsDelay.eq_zero {D V : Type*} [Preorder D] [Zero V] [Top V]
    {f : D → V} {d : D} (hf : IsDelay f d) {t : D} (ht : t ≤ d) : f t = 0 :=
  hf.1 t ht

/-- A delay is `⊤` past `d`. -/
theorem IsDelay.eq_top {D V : Type*} [Preorder D] [Zero V] [Top V]
    {f : D → V} {d : D} (hf : IsDelay f d) {t : D} (ht : d < t) : f t = ⊤ :=
  hf.2 t ht

/-- First-crossing: for `0 < x`, a delay satisfies `x ≤ f t ↔ d < t` — the
level `x` is first reached just past `d`. -/
theorem IsDelay.le_iff {D V : Type*} [LinearOrder D]
    [PartialOrder V] [Zero V] [OrderTop V]
    {f : D → V} {d : D} (hf : IsDelay f d) {x : V} (hx : 0 < x) (t : D) :
    x ≤ f t ↔ d < t := by
  rcases le_or_gt t d with ht | ht
  · rw [hf.eq_zero ht]
    exact ⟨fun h => absurd (le_antisymm h hx.le) hx.ne',
      fun h => absurd ht (not_le.mpr h)⟩
  · rw [hf.eq_top ht]
    exact ⟨fun _ => ht, fun _ => le_top⟩

/-- Pure-delay curve: `0` for `t ≤ d`, `⊤` afterwards. -/
noncomputable def delay (d : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => if t ≤ d then 0 else ⊤

/-- Pure-delay curve on the `ℝ≥0∞` domain: `0` for `t ≤ d`, `⊤` afterwards. -/
noncomputable def delayE (d : ℝ≥0∞) : ℝ≥0∞ → ℝ≥0∞ :=
  fun t => if t ≤ d then 0 else ⊤

/-- `delay d 0 = 0`. -/
theorem delay_zero_eq (d : ℝ≥0) : delay d 0 = 0 := by
  simp [delay]

/-- `delayE d 0 = 0`. -/
theorem delayE_zero_eq (d : ℝ≥0∞) : delayE d 0 = 0 := by
  simp [delayE]

/-- On finite arguments, `delayE ↑d` agrees with `delay d`. -/
theorem delayE_coe (d t : ℝ≥0) :
    delayE (d : ℝ≥0∞) (t : ℝ≥0∞) = delay d t := by
  simp only [delayE, delay, ENNReal.coe_le_coe]

/-- `delay d` is a delay at `d`. -/
theorem delay_isDelay (d : ℝ≥0) : IsDelay (delay d) d :=
  ⟨fun _ ht => by simp [delay, ht],
   fun _ ht => by simp [delay, not_le.mpr ht]⟩

/-- `delayE d` is a delay at `d`. -/
theorem delayE_isDelay (d : ℝ≥0∞) : IsDelay (delayE d) d :=
  ⟨fun _ ht => by simp [delayE, ht],
   fun _ ht => by simp [delayE, not_le.mpr ht]⟩

end DeepWiki
