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

/-! ## Fixpoint detection (a non-saturated region genuinely advances) -/

omit [DecidableEq C] in
open Classical in
/-- **A region is a `step`-fixpoint only if fully saturated.** If `regionCodeStep (fp w) =
fp w` then every clock exceeds its clamp — a non-saturated region always advances (case B
flips an integral clock's frac-zero bit; case C bumps a maximal-fraction clock's floor). -/
theorem regionCodeStep_eq_self_imp_allUnbounded {cmax : C → ℕ} {w : Valuation C}
    (h : regionCodeStep (regionFingerprint cmax w) = regionFingerprint cmax w) :
    ∀ x, (cmax x : ℝ≥0) < w x := by
  set γ := regionFingerprint cmax w with hγ
  by_contra hcon
  simp only [not_forall, not_lt] at hcon
  obtain ⟨x₀, hx₀⟩ := hcon
  have hnotA : ¬ (decide (∀ x, (γ.1 x).val = cmax x + 1) = true) := by
    rw [decide_eq_true_iff]
    intro hall
    have he := hall x₀
    rw [hγ, regionFingerprint_floor] at he
    have hle : regionFloor cmax w x₀ ≤ cmax x₀ := (regionFloor_le_clamp_iff w x₀).mpr hx₀
    omega
  by_cases hdB : decide (∃ x, γ.2.1 x = true) = true
  · obtain ⟨x₁, hx₁⟩ := decide_eq_true_iff.mp hdB
    have hstepB : (regionCodeStep γ).2.1 x₁ = false := by
      unfold regionCodeStep; rw [if_neg hnotA, if_pos hdB]
    have hcontra : γ.2.1 x₁ = false := h ▸ hstepB
    rw [hx₁] at hcontra
    exact absurd hcontra (by decide)
  · set S : Finset C := Finset.univ.filter (fun x => w x ≤ (cmax x : ℝ≥0)) with hS
    have hx₀S : x₀ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₀⟩
    obtain ⟨x₁, hx₁S, hx₁max⟩ := S.exists_max_image (fun x => fracPart (w x)) ⟨x₀, hx₀S⟩
    have hbnd1 : w x₁ ≤ (cmax x₁ : ℝ≥0) := (Finset.mem_filter.mp hx₁S).2
    have hfl1 : (γ.1 x₁).val ≤ cmax x₁ := by
      rw [hγ, regionFingerprint_floor]; exact (regionFloor_le_clamp_iff w x₁).mpr hbnd1
    have hisMax : (decide ((γ.1 x₁).val ≤ cmax x₁) &&
        decide (∀ y, (γ.1 y).val ≤ cmax y → γ.2.2 y x₁ = true)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_iff]
      refine ⟨hfl1, fun y hy => ?_⟩
      have hbndy : w y ≤ (cmax y : ℝ≥0) := by
        rw [hγ, regionFingerprint_floor] at hy; exact (regionFloor_le_clamp_iff w y).mp hy
      rw [hγ, regionFingerprint_fracOrder, decide_eq_true_iff]
      exact ⟨hbndy, hbnd1, hx₁max y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbndy⟩)⟩
    have hstepC : (regionCodeStep γ).1 x₁ = bumpFloor cmax x₁ ((γ.1 x₁).val + 1) := by
      unfold regionCodeStep; rw [if_neg hnotA, if_neg hdB]; exact if_pos hisMax
    have hval : ((regionCodeStep γ).1 x₁).val = min ((γ.1 x₁).val + 1) (cmax x₁ + 1) := by
      rw [hstepC]; rfl
    have heq : (γ.1 x₁).val = ((regionCodeStep γ).1 x₁).val := by rw [h]
    rw [hval] at heq
    omega

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

/-! ## The well-founded measure for the orbit -/

/-- The **descent measure** of a region code: `2·Σ(room below saturation) + #(integral
clocks)`. It strictly decreases along `regionCodeStep` (case C bumps a floor — room down 1,
weight 2 — while only adding one integral clock; case B clears an integral bit), bounding the
orbit length and well-founding the completeness induction. -/
def codeMeasure {cmax : C → ℕ} (γ : RegionCode cmax) : ℕ :=
  2 * (∑ x, (cmax x + 1 - (γ.1 x).val)) + (Finset.univ.filter (fun x => γ.2.1 x = true)).card

omit [DecidableEq C] in
/-- A region of zero descent measure is fully saturated (no room, no integral clocks). -/
theorem codeMeasure_eq_zero_imp {cmax : C → ℕ} {w : Valuation C}
    (h : codeMeasure (regionFingerprint cmax w) = 0) : ∀ x, (cmax x : ℝ≥0) < w x := by
  intro x
  have hsum : (∑ y, (cmax y + 1 - ((regionFingerprint cmax w).1 y).val)) = 0 := by
    unfold codeMeasure at h; omega
  have hroom : cmax x + 1 - ((regionFingerprint cmax w).1 x).val = 0 :=
    (Finset.sum_eq_zero_iff).mp hsum x (Finset.mem_univ x)
  rw [regionFingerprint_floor] at hroom
  have hfl : regionFloor cmax w x ≤ cmax x + 1 := regionFloor_le cmax w x
  have hsat : regionFloor cmax w x = cmax x + 1 := by omega
  by_contra hb
  rw [not_lt] at hb
  have := (regionFloor_le_clamp_iff w x).mpr hb
  omega

end DeepWiki.ReactiveSystems
