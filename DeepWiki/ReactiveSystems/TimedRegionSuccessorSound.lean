import DeepWiki.ReactiveSystems.TimedRegionSuccessor

/-! # Soundness of the region time-successor (Alur–Dill §4.3)
Each elapse step `regionCodeStep` on a region code is **realized by an actual delay**:
for every valuation `w` there is a `δ` with `fp (w + δ) = regionCodeStep (fp w)`. Composing
along the orbit gives `SuccSound` for `regionCodeDelaySucc` — every code it lists is the
fingerprint of `w` after some delay. (The converse, `SuccComplete`, is the deep direction.)
This file builds step soundness case by case (Alur–Dill's three cases). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {C : Type*} [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
/-- Delaying by `0` is the identity valuation. -/
theorem Valuation.add_zero (w : Valuation C) : w.add 0 = w := by
  funext x; simp [Valuation.add_apply]

omit [DecidableEq C] in
/-- **Step soundness, case A** (all clocks saturated): when every clock already exceeds its
clamp, the elapse step is the identity, realized by the zero delay. -/
theorem regionCodeStep_sound_allUnbounded {cmax : C → ℕ} {w : Valuation C}
    (h : ∀ x, (cmax x : ℝ≥0) < w x) :
    regionFingerprint cmax (w.add 0) = regionCodeStep (regionFingerprint cmax w) := by
  have hcond : decide (∀ x, ((regionFingerprint cmax w).1 x).val = cmax x + 1) = true := by
    rw [decide_eq_true_iff]
    intro x
    rw [regionFingerprint_floor]
    unfold regionFloor
    rw [if_neg (not_le.mpr (h x))]
  rw [Valuation.add_zero]
  show regionFingerprint cmax w = regionCodeStep (regionFingerprint cmax w)
  unfold regionCodeStep
  rw [if_pos hcond]

end DeepWiki.ReactiveSystems
