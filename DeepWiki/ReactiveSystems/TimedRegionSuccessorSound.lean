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

omit [Fintype C] [DecidableEq C] in
open Classical in
/-- **Saturated states stay put.** If every clock already exceeds its clamp, the region is
unchanged by any delay — `fp (w + t) = fp w`. (The fixpoint base case of completeness: a
saturated region is its own only time-successor.) -/
theorem regionFingerprint_add_of_allUnbounded {cmax : C → ℕ} {w : Valuation C}
    (h : ∀ x, (cmax x : ℝ≥0) < w x) (t : ℝ≥0) :
    regionFingerprint cmax (w.add t) = regionFingerprint cmax w := by
  have hub : ∀ x, ¬ ((w.add t) x ≤ (cmax x : ℝ≥0)) := fun x => by
    rw [Valuation.add_apply]; exact not_le.mpr (lt_of_lt_of_le (h x) le_self_add)
  have hub0 : ∀ x, ¬ (w x ≤ (cmax x : ℝ≥0)) := fun x => not_le.mpr (h x)
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => funext fun y => ?_⟩
  · apply Fin.ext
    show regionFloor cmax (w.add t) x = regionFloor cmax w x
    unfold regionFloor; rw [if_neg (hub x), if_neg (hub0 x)]
  · rw [regionFingerprint_fracZero, regionFingerprint_fracZero,
      decide_eq_false_iff_not.mpr (fun hc => hub x hc.1),
      decide_eq_false_iff_not.mpr (fun hc => hub0 x hc.1)]
  · rw [regionFingerprint_fracOrder, regionFingerprint_fracOrder,
      decide_eq_false_iff_not.mpr (fun hc => hub x hc.1),
      decide_eq_false_iff_not.mpr (fun hc => hub0 x hc.1)]

/-! ## Orbit-structure lemmas (for the completeness induction) -/

omit [DecidableEq C] in
/-- The starting region is the head of its own orbit. -/
theorem mem_regionCodeOrbit_self {cmax : C → ℕ} (fuel : ℕ) (γ : RegionCode cmax) :
    γ ∈ regionCodeOrbit fuel γ := by
  cases fuel with
  | zero => simp [regionCodeOrbit]
  | succ n => simp only [regionCodeOrbit]; split <;> simp

omit [DecidableEq C] in
/-- The orbit of the next region is contained in the orbit of `γ` (its tail), when `γ` is
not already a fixpoint. -/
theorem regionCodeOrbit_step_subset {cmax : C → ℕ} (fuel : ℕ) {γ : RegionCode cmax}
    (h : regionCodeStep γ ≠ γ) :
    regionCodeOrbit fuel (regionCodeStep γ) ⊆ regionCodeOrbit (fuel + 1) γ := by
  simp only [regionCodeOrbit, if_neg h]
  exact List.subset_cons_self _ _

omit [DecidableEq C] in
/-- The next region is in `γ`'s orbit (when `γ` is not a fixpoint). -/
theorem step_mem_regionCodeOrbit {cmax : C → ℕ} (fuel : ℕ) {γ : RegionCode cmax}
    (h : regionCodeStep γ ≠ γ) :
    regionCodeStep γ ∈ regionCodeOrbit (fuel + 1) γ :=
  regionCodeOrbit_step_subset fuel h (mem_regionCodeOrbit_self fuel _)

end DeepWiki.ReactiveSystems
